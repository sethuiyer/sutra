#define _POSIX_C_SOURCE 200809L
/*=====================================================================
  SUTRA — MaxSAT approximator
  Search Under Time, Recounted, Attested.
  Author: Sethu Iyer (github.com/sethuiyer)

  WHAT THIS FILE IS
  -----------------
  This is the engine. It reads a CNF (plain SAT) or WCNF (weighted MaxSAT)
  file, finds the best assignment it can within a time budget, and prints
  the result together with the assignment ("witness") that produced it.

  If you are new to the area, read the following three ideas first:

    * A CNF file lists "clauses": ORs of literals, e.g. (x1 OR NOT x3).
      A SAT solver looks for a true/false value for every variable that
      makes ALL clauses true at once.

    * A WCNF file additionally gives every clause a weight. Clauses with
      weight >= the header's "top" value are HARD (must be satisfied).
      The rest are SOFT: violating one costs its weight. MaxSAT asks for
      an assignment that satisfies all hard clauses and minimises the
      total weight of violated soft clauses.

    * MaxSAT is NP-hard. SUTRA does not try to prove optimality (an exact
      solver does that). It tries to get the cost as low as possible, as
      fast as possible, and to never lie about what it achieved.

  HOW THE SEARCH WORKS (top to bottom)
  ------------------------------------
    1. parse_input()      read the file into flat arrays (CSR layout).
    2. continuous phase   relax booleans to [0,1] and descend a smooth
                          energy with Adam-style updates; this only picks
                          a promising starting point for step 3.
    3. repair_nuwls()     the real work: local search that flips one
                          variable at a time, always trying to reduce the
                          weighted number of violated clauses.
    4. certification      optional: if an UNSAT claim is requested, a
                          CDCL or a GF(2) parity argument produces a
                          machine-checkable proof (see sutra_cert.h).
    5. output             every number printed is recounted from the
                          witness, never taken from internal bookkeeping.

  READING ORDER
  -------------
    Formula, Options  -> the data model
    parse_input       -> how a file becomes arrays
    gradient_step     -> the continuous warm start
    repair_nuwls      -> the actual optimiser (in sutra_nuwls.h)
    main              -> the orchestration: parse, search, certify, print

  Exit codes: 10 = SAT (cost 0), 20 = certified UNSAT, 0 = best effort,
              1 = error.
=====================================================================*/
#include "navokoj_checkpoint.h"
#include <ctype.h>
#include <errno.h>
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/wait.h>
#include "cdcl_internal.h"

#define SUTRA_VERSION "1.0.0"
#define SUTRA_EPS 1e-9

/* ------------------------------------------------------------------ */
/* Options                                                             */
/* ------------------------------------------------------------------ */
typedef struct {
    const char *input;
    const char *solution_path;
    const char *warm_start_path;   /* DIMACS assignment to seed x from
                                      (bridge to another engine's
                                      continuous phase, e.g. sutra v2) */
    const char *residual_cmd;      /* when the heuristic stalls on a small
                                      unsat core, extract the residual
                                      sub-formula and delegate to this
                                      command (%F=file %S=solution), then
                                      merge + verify the witness */
    uint32_t steps;          /* continuous steps per restart        */
    uint32_t restarts;       /* max restarts (0 = budget-driven)   */
    uint64_t repair_flips;   /* discrete repair budget per restart  */
    double time_budget;      /* seconds; 0 = unlimited              */
    uint64_t seed;
    int json;                /* json stdout (default)               */
    double lr;               /* optimizer learning rate             */
    double tau;              /* relax hinge temperature             */
    double dec_threshold;    /* decimation confidence threshold    */
    uint32_t dec_freq;       /* decimate every N steps              */
    double soft_phase;       /* init bias toward planted/soft opt   */
    uint64_t tabu;           /* repair tabu tenure, in flips (0 off) */
    NavokojCheckpoint checkpoint;   /* anytime SIGKILL salvage       */
    const char *kissat_path;        /* portfolio: external CDCL      */
    const char *checker_path;       /* verifier for delegated proofs */
    const char *proof_path;         /* emit refutation certificate   */
    const char *proof_format;       /* auto | gfp | drat             */
    uint32_t exact_conflicts;       /* CDCL budget; 0 disables       */
    int no_parity;                  /* disable GF(2) preprocessing   */
    int walk;                       /* legacy WalkSAT repair (opt-in)  */
} Options;

/* ------------------------------------------------------------------ */
/* Formula (CSR)                                                       */
/* ------------------------------------------------------------------ */
typedef struct {
    uint32_t vars;
    uint64_t clauses;
    uint64_t literals;
    uint64_t *offset;        /* clauses+1                            */
    int32_t *lits;
    double *weight;          /* soft weight (hard => unused)         */
    uint8_t *hard;
    double total_soft_weight;
    /* occurrence index: var -> clause list (CSR)                    */
    uint64_t *occ_offset;
    uint64_t *occ_clause;
    int64_t *occ_delta;      /* positive minus negative multiplicity, per (var, clause) */
} Formula;

#include "sutra_cert.h"
#include "sutra_nuwls.h"

/* Print a fatal input/problem error and stop.  Used only for conditions
   the caller cannot recover from (unreadable file, malformed header). */
static void die(const char *msg) {
    fprintf(stderr, "SUTRA input error: %s\n", msg);
    exit(1);
}

/* ---- W2: lenient DIMACS/WCNF parser ------------------------------ */
/* Format is decided GLOBALLY (header word, or presence of 'h' clause
   prefixes), never per-line: a plain CNF clause "1 2 3 0" is
   indistinguishable from a WCNF clause of weight 1, so guessing per
   line silently turns hard clauses into weight-1 soft clauses. */
/* ------------------------------------------------------------------
   parse_input — turn a DIMACS file into arrays.

   A DIMACS line looks like:   1 -5 3 0
   meaning "x1 OR NOT x5 OR x3".  The trailing 0 terminates the clause.

   WCNF (weighted MaxSAT) puts a weight first:
       weight  lits...  0
   and clauses whose weight is >= the header's "top" are hard.

   We store everything in a CSR ("compressed sparse row") layout:
       offset[c] .. offset[c+1]   gives the range of literals of clause c
       lits[j]                     the j-th literal (positive/negative var)
   That is cache friendly and needs only two allocations.

   The parser is deliberately lenient (comments, missing trailing newline,
   'h' prefixes, CNF headers on weighted files) because DIMACS in the wild
   is not as regular as the spec suggests.
   ------------------------------------------------------------------ */
static void parse_input(const char *path, Formula *f) {
    FILE *fp = fopen(path, "r");
    if (!fp) die(strerror(errno));
    /* read whole file to decide format */
    fseek(fp, 0, SEEK_END);
    long fsz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    if (fsz < 0) fsz = 1 << 20;
    char *buf = malloc((size_t)fsz + 2);
    if (!buf) die("out of memory");
    size_t got = fread(buf, 1, (size_t)fsz, fp);
    buf[got] = '\0';
    fclose(fp);

    int is_wcnf = 0, have_header = 0;
    uint32_t nvars = 0; uint64_t nclauses = 0;
    long long top_weight = -1;   /* WCNF TOP: weights >= TOP are hard */
    /* scan for header and h-prefixed clause lines */
    for (char *p = buf; *p; ) {
        char *nl = strchr(p, '\n');
        size_t len = nl ? (size_t)(nl - p) : strlen(p);
        char *line = p;
        while (*line == ' ' || *line == '\t' || *line == '\r') line++;
        if (*line && *line != '\n') {
            char *header = line;
            if (have_header == 0 && (*line == 'h' || *line == 'H') &&
                (line[1] == ' ' || line[1] == '\t')) {
                char *q = line + 1;
                while (*q == ' ' || *q == '\t') q++;
                if (*q == 'p' || *q == 'P') {
                    is_wcnf = 1;              /* 'h p wcnf ...' style */
                    header = q;
                }
                else is_wcnf = 1;            /* 'h <lits>' clause prefix */
            }
            if (*header == 'p' || *header == 'P') {
                char fmt[32] = {0};
                char *q = header + 1;
                uint32_t v; uint64_t c;
                int got = sscanf(q, "%31s %" SCNu32 " %" SCNu64 " %lld",
                                 fmt, &v, &c, &top_weight);
                if (got >= 3) {
                    nvars = v; nclauses = c; have_header = 1;
                    if (!strcmp(fmt, "wcnf")) is_wcnf = 1;
                    if (got < 4) top_weight = -1;
                }
            }
        }
        if (!nl) break;
        p = nl + 1;
    }

    uint64_t cap = 1024, cnt = 0;
    uint64_t lit_cap = 4096, lit_cnt = 0;
    int32_t *cl_lits = malloc(lit_cap * sizeof(int32_t));
    double *weights = malloc(cap * sizeof(double));
    uint8_t *hards = malloc(cap);
    uint64_t *sizes = malloc(cap * sizeof(uint64_t));
    if (!cl_lits || !weights || !hards || !sizes) die("out of memory");

    for (char *p = buf; *p; ) {
        char *nl = strchr(p, '\n');
        char *line = p;
        if (nl) *nl = '\0';
        p = nl ? nl + 1 : p + strlen(p);
        char *q = line;
        while (*q == ' ' || *q == '\t' || *q == '\r') q++;
        if (*q == '\0' || *q == 'c' || *q == 'C' || *q == 'p' || *q == 'P') continue;
        if ((*q == 'h' || *q == 'H') && (q[1] == ' ' || q[1] == '\t')) {
            char *header = q + 1;
            while (*header == ' ' || *header == '\t') header++;
            if (*header == 'p' || *header == 'P') continue;
        }
        int is_hard_line = 0;
        if (*q == 'h' || *q == 'H') { is_hard_line = 1; q++; while (*q==' '||*q=='\t') q++; }
        else if (*q == 's' || *q == 'S') { q++; while (*q==' '||*q=='\t') q++; }
        double w = 1.0; int is_hard = 1;
        if (is_wcnf && !is_hard_line) {
            char *end = NULL;
            long long first = strtoll(q, &end, 10);
            if (end != q && first >= 0 && (*end == ' ' || *end == '\t')) {
                w = (double)first;
                /* Hard iff weight 0 (navokoj legacy 'h' convention handled
                   above) or weight >= TOP (standard WCNF hard encoding). */
                is_hard = (first <= 0) || (top_weight > 0 && first >= top_weight);
                q = end;
            }
        }
        if (is_hard_line) is_hard = 1;
        uint64_t nsz = 0;
        int terminated = 0;
        for (;;) {
            while (*q == ' ' || *q == '\t' || *q == '\r') q++;
            if (*q == '\0') break;
            char *le = NULL;
            errno = 0;
            long long lit = strtoll(q, &le, 10);
            if (le == q || errno == ERANGE || lit < -INT32_MAX || lit > INT32_MAX)
                die("invalid or out-of-range literal");
            q = le;
            if (lit == 0) {
                terminated = 1;
                while (*q == ' ' || *q == '\t' || *q == '\r') q++;
                if (*q) die("expected one complete clause per line; data after terminator");
                break;
            }
            if (lit_cnt == lit_cap) {
                lit_cap *= 2;
                cl_lits = realloc(cl_lits, lit_cap * sizeof(int32_t));
                if (!cl_lits) die("out of memory");
            }
            cl_lits[lit_cnt++] = (int32_t)lit;
            nsz++;
            uint32_t av = (uint32_t)(lit < 0 ? -lit : lit);
            if (av > nvars) nvars = av;
        }
        if (!terminated) die("expected one complete clause per line ending in 0");
        if (cnt == cap) {
            cap *= 2;
            weights = realloc(weights, cap * sizeof(double));
            hards = realloc(hards, cap);
            sizes = realloc(sizes, cap * sizeof(uint64_t));
            if (!weights || !hards || !sizes) die("out of memory");
        }
        weights[cnt] = w;
        hards[cnt] = (uint8_t)is_hard;
        sizes[cnt] = nsz;
        cnt++;
    }
    free(buf);
    (void)nclauses;
    f->vars = nvars ? nvars : 1;
    f->clauses = cnt;
    f->literals = lit_cnt;
    f->offset = malloc((cnt + 1) * sizeof(uint64_t));
    f->lits = malloc((lit_cnt ? lit_cnt : 1) * sizeof(int32_t));
    f->weight = malloc((cnt ? cnt : 1) * sizeof(double));
    f->hard = malloc(cnt ? cnt : 1);
    if (!f->offset || !f->lits || !f->weight || !f->hard) die("out of memory");
    uint64_t off = 0;
    for (uint64_t c = 0; c < cnt; c++) {
        f->offset[c] = off;
        memcpy(f->lits + off, cl_lits + off, sizes[c] * sizeof(int32_t));
        off += sizes[c];
        f->weight[c] = weights[c];
        f->hard[c] = hards[c];
    }
    f->offset[cnt] = off;
    f->total_soft_weight = 0;
    for (uint64_t c = 0; c < cnt; c++)
        if (!f->hard[c]) f->total_soft_weight += f->weight[c];
    free(cl_lits); free(weights); free(hards); free(sizes);

    /* occurrence index */
    uint64_t *deg = calloc(f->vars + 1, sizeof(uint64_t));
    for (uint64_t j = 0; j < lit_cnt; j++) {
        int32_t l = f->lits[j];
        deg[l < 0 ? -l : l]++;
    }
    f->occ_offset = calloc(f->vars + 2, sizeof(uint64_t));
    for (uint32_t v = 1; v <= f->vars; v++) f->occ_offset[v + 1] = f->occ_offset[v] + deg[v];
    free(deg);
    f->occ_clause = malloc((lit_cnt ? lit_cnt : 1) * sizeof(uint64_t));
    f->occ_delta = malloc((lit_cnt ? lit_cnt : 1) * sizeof(int64_t));
    uint64_t *filler = calloc(f->vars + 2, sizeof(uint64_t));
    if (!f->occ_offset || !f->occ_clause || !f->occ_delta || !filler) die("out of memory");
    for (uint64_t c = 0; c < cnt; c++) {
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
            int32_t l = f->lits[j];
            uint32_t v = (uint32_t)(l < 0 ? -l : l);
            uint64_t k = f->occ_offset[v] + filler[v]++;
            f->occ_clause[k] = c;
            f->occ_delta[k] = l > 0 ? 1 : -1;
        }
    }
    free(filler);
    /* Entries are clause-ordered within each variable. Coalesce repeated
       literals, including opposite signs, without changing the formula or
       its continuous gradient. Each affected clause is updated exactly once. */
    uint64_t out = 0;
    for (uint32_t v = 1; v <= f->vars; v++) {
        uint64_t begin = f->occ_offset[v], end = f->occ_offset[v + 1];
        f->occ_offset[v] = out;
        for (uint64_t k = begin; k < end; ) {
            uint64_t c = f->occ_clause[k];
            int64_t delta = 0;
            do { delta += f->occ_delta[k++]; }
            while (k < end && f->occ_clause[k] == c);
            f->occ_clause[out] = c;
            f->occ_delta[out++] = delta;
        }
    }
    f->occ_offset[f->vars + 1] = out;
}

/* ------------------------------------------------------------------ */
/* RNG (xorshift64*)                                                    */
/* ------------------------------------------------------------------ */
/* ------------------------------------------------------------------
   RNG — xorshift64.

   Local search needs millions of cheap random numbers.  xorshift is a
   few shifts and XORs, has no state beyond one word, and is completely
   deterministic given the seed, which makes runs reproducible.
   ------------------------------------------------------------------ */
static uint64_t rng_state;
static inline uint64_t rng_next(void) {
    uint64_t x = rng_state;
    x ^= x >> 12; x ^= x << 25; x ^= x >> 27;
    rng_state = x;
    return x * 0x2545F4914F6CDD1DULL;
}
static inline double rng_double(void) { return (double)(rng_next() >> 11) / 9007199254740992.0; }
static inline uint32_t rng_below(uint32_t n) { return n ? (uint32_t)(rng_next() % n) : 0; }

/* ------------------------------------------------------------------ */
/* Evaluation / bookkeeping                                             */
/* ------------------------------------------------------------------ */
typedef struct {
    uint64_t *sat_count;      /* per clause satisfied-literal count   */
    uint64_t hard_unsat;      /* # hard clauses with sat_count == 0   */
    double soft_cost;         /* weight sum of unsat soft clauses     */
    uint64_t soft_unsat;      /* # unsat soft clauses                 */
} Score;

/* Does literal `lit` evaluate to true under the continuous assignment?
   A literal is an integer: +7 means x7, -7 means NOT x7.  The continuous
   phase keeps x in [0,1], so "true" means x[var] > 0.5 for a positive
   literal and x[var] <= 0.5 for a negative one. */
static inline int lit_true(int32_t lit, const double *x) {
    uint32_t v = (uint32_t)(lit < 0 ? -lit : lit);
    return lit > 0 ? x[v] > 0.5 : x[v] <= 0.5;
}

/* Score a continuous assignment: how many clauses are satisfied, how
   many hard clauses are violated, and what soft weight is unpaid.  Used
   only to compare candidate starting points before the discrete phase. */
static void rescore(const Formula *f, const double *x, Score *s) {
    memset(s->sat_count, 0, f->clauses * sizeof(uint64_t));
    s->hard_unsat = 0; s->soft_cost = 0; s->soft_unsat = 0;
    for (uint64_t c = 0; c < f->clauses; c++) {
        uint64_t k = 0;
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++)
            if (lit_true(f->lits[j], x)) k++;
        s->sat_count[c] = k;
        if (k == 0) {
            if (f->hard[c]) s->hard_unsat++;
            else { s->soft_cost += f->weight[c]; s->soft_unsat++; }
        }
    }
}

/* Lexicographic comparison of two solutions.

   Hard clauses are promises; soft clauses are preferences.  So a
   solution with fewer hard violations always wins, no matter how bad its
   soft cost is.  Only when the hard counts tie do we compare soft cost.
   This one-line ordering is the whole semantics of partial MaxSAT. */
static inline int lex_better(uint64_t h1, double c1, uint64_t h2, double c2) {
    if (h1 != h2) return h1 < h2;
    return c1 < c2 - 1e-12;
}

/* ------------------------------------------------------------------ */
/* W6: verified recount — the ONLY source of reported numbers          */
/* ------------------------------------------------------------------ */
/* Recount every statistic directly from the assignment.

   The solver maintains counters while it searches, but counters can
   drift.  Anything that is about to be printed is recomputed here from
   `asn` and the clauses, so the JSON can never report a number that the
   witness does not actually support. */
static void verified_recount(const Formula *f, const uint8_t *asn, uint64_t *satisfied,
                             uint64_t *hard_unsat, uint64_t *soft_unsat, double *soft_cost) {
    *satisfied = 0; *hard_unsat = 0; *soft_unsat = 0; *soft_cost = 0;
    for (uint64_t c = 0; c < f->clauses; c++) {
        int sat = 0;
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
            int32_t l = f->lits[j];
            uint32_t v = (uint32_t)(l < 0 ? -l : l);
            if ((l > 0) == (asn[v] != 0)) { sat = 1; break; }
        }
        if (sat) (*satisfied)++;
        else if (f->hard[c]) (*hard_unsat)++;
        else { (*soft_unsat)++; *soft_cost += f->weight[c]; }
    }
}

/* ------------------------------------------------------------------ */
/* Continuous phase (relax-v2 energy, kept from v2)                    */
/* ------------------------------------------------------------------ */
/* Energy/gradient.  Soft width!=2: tau*log(1+exp(u/tau)) hinge on
   u = 1 - sum(signed truth).  Soft width==2: product form (validated).
   Hard: -lambda*log(1 - V_c) log barrier.  Annealed crispness
   regularizer mu(t)*x*(1-x) with mu ramping up so the relaxation
   crystallizes late.                                                  */
/* ------------------------------------------------------------------
   gradient_step — one step of the continuous relaxation.

   Why relax at all?  Local search is very sensitive to where it starts.
   Instead of starting from random bits, we let each variable be a real
   number x[v] in [0,1] (its "probability of being true"), define a smooth
   penalty for violated clauses, and descend it with an Adam-style
   optimiser.  Rounding that continuous point gives repair_nuwls() a much
   better starting assignment.

   The penalty has two layers:
     * hard clauses: a log barrier -log(1 - p), where p is the probability
       that the clause is false.  It explodes as p -> 1, which pushes the
       solution away from violating a hard clause.
     * soft clauses: a squared penalty on the same probability, weighted
       by the clause's weight.

   This phase is a heuristic initialiser, nothing more.  It is not
   required for correctness and it is skipped when the budget is tiny.
   ------------------------------------------------------------------ */
static void gradient_step(const Formula *f, double *x, double *g,
                          double *m, double *v, uint32_t step, uint32_t steps,
                          const Options *o) {
    const double beta1 = 0.9, beta2 = 0.999;
    memset(g, 0, (f->vars + 1) * sizeof(double));
    for (uint64_t c = 0; c < f->clauses; c++) {
        uint64_t width = f->offset[c + 1] - f->offset[c];
        if (width == 0) continue;                  /* empty clause: no grad */
        if (f->hard[c]) {
            double viol = 1.0;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                viol *= (l > 0) ? 1.0 - x[var] : x[var];
            }
            double slack = 1.0 - viol;
            if (slack < SUTRA_EPS) slack = SUTRA_EPS;
            double coef = 64.0 / slack;            /* barrier strength */
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                double fp = (l > 0) ? 1.0 - x[var] : x[var];   /* lit false prob */
                if (fp < SUTRA_EPS) fp = SUTRA_EPS;
                g[var] += coef * (viol / fp) * (l > 0 ? -1.0 : 1.0);
            }
        } else if (width == 2) {
            /* product form (v2 validated exception for width 2) */
            double viol = 1.0;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                viol *= (l > 0) ? 1.0 - x[var] : x[var];
            }
            double coef = 2.0 * f->weight[c] * viol;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                double fp = (l > 0) ? 1.0 - x[var] : x[var];
                if (fp < SUTRA_EPS) fp = SUTRA_EPS;
                g[var] += coef * (viol / fp) * (l > 0 ? -1.0 : 1.0);
            }
        } else {
            /* LP-hybrid hinge: keeps O(1) gradient for any width */
            double sum_signed = 0.0;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                sum_signed += (l > 0) ? x[var] : 1.0 - x[var];
            }
            double u = 1.0 - sum_signed;
            double tau = o->tau > 1e-3 ? o->tau : 1e-3;
            double vv = u / tau;
            double soft_viol = vv > 0 ? u + tau * log1p(exp(-vv)) : tau * log1p(exp(vv));
            double sig = vv >= 0 ? 1.0 / (1.0 + exp(-vv)) : exp(vv) / (1.0 + exp(vv));
            double coef = 2.0 * f->weight[c] * soft_viol;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
                int32_t l = f->lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                g[var] += coef * ((l > 0) ? -sig : sig);
            }
        }
    }
    /* annealed crispness regularizer + Adam update */
    double anneal = steps ? pow((double)step / steps, 2.0) : 1.0;
    double mu = 0.05 * anneal;
    double lr = o->lr * (0.5 + 0.5 * (1.0 - (double)step / (steps ? steps : 1)));
    /* Bias corrections depend on the step, never on the variable. Keep
       divisions (rather than reciprocal multiplication) for identical math. */
    const double bias1 = 1 - pow(beta1, (double)step + 1);
    const double bias2 = 1 - pow(beta2, (double)step + 1);
    for (uint32_t var = 1; var <= f->vars; var++) {
        g[var] += mu * (1.0 - 2.0 * x[var]);
        m[var] = beta1 * m[var] + (1 - beta1) * g[var];
        v[var] = beta2 * v[var] + (1 - beta2) * g[var] * g[var];
        double mh = m[var] / bias1;
        double vh = v[var] / bias2;
        x[var] -= lr * mh / (sqrt(vh) + 1e-8);
        if (x[var] < 1e-4) x[var] = 1e-4;
        if (x[var] > 1 - 1e-4) x[var] = 1 - 1e-4;
    }
}

/* ------------------------------------------------------------------ */
/* W3/W5-fixed discrete repair: lexicographic hard-first greedy        */
/* with soft-improving flips and honest convergence detection          */
/* ------------------------------------------------------------------ */
/* Dense violated-clause list: [0, hard_count) is hard, the rest soft.
   Its inverse index makes insertion/removal O(1), and the hard prefix
   permits direct random selection without a reservoir scan per flip.
   Only one additional uint64_t per clause is needed. */
/* Maintain a set of "currently violated clauses" in O(1).

   We need to pick a random violated clause quickly, so the set is stored
   as a dense array `list` plus a reverse index `pos` that remembers where
   each clause sits.  Adding and removing are swap-with-last operations:
       add:    list[count] = c; pos[c] = count; count++
       remove: last = list[--count]; list[pos[c]] = last; pos[last] = pos[c]
   The order is destroyed, but that does not matter for random choice. */
static void unsat_add(uint64_t *list, uint64_t *pos, uint64_t *count,
                      uint64_t *hard_count, uint64_t clause, int hard) {
    uint64_t slot = *count;
    if (hard) {
        slot = (*hard_count)++;
        if (slot < *count) {
            list[*count] = list[slot];
            pos[list[*count]] = *count;
        }
    }
    list[slot] = clause;
    pos[clause] = slot;
    (*count)++;
}

static void unsat_remove(uint64_t *list, uint64_t *pos, uint64_t *count,
                         uint64_t *hard_count, uint64_t clause, int hard) {
    uint64_t slot = pos[clause];
    if (hard) {
        uint64_t last_hard = --(*hard_count);
        list[slot] = list[last_hard];
        pos[list[slot]] = slot;
        slot = last_hard;
    }
    --(*count);
    if (slot < *count) {
        list[slot] = list[*count];
        pos[list[slot]] = slot;
    }
    pos[clause] = UINT64_MAX;
}

/* Net effect of flipping `v` on the current assignment: net hard fixes
   (weighted by the dynamic hard multipliers) and the soft-cost delta.
   Every candidate pass scores through this one function, so the rule
   cannot drift between passes. */
/* Exact change in (hard violations, soft cost) if variable v is flipped.
   Walks only the clauses that contain v, using the cached true-literal
   count `cnt` to know whether each clause breaks or becomes satisfied. */
static inline void flip_delta(const Formula *f, const uint8_t *asn, const uint64_t *cnt,
                              const double *hmult, uint32_t v,
                              int64_t *hard_delta, double *soft_delta) {
    int64_t hd = 0; double sd = 0;
    for (uint64_t k = f->occ_offset[v]; k < f->occ_offset[v + 1]; k++) {
        uint64_t c = f->occ_clause[k];
        uint64_t base = cnt[c];
        int64_t delta = f->occ_delta[k];
        uint64_t after = (uint64_t)((int64_t)base + (asn[v] ? -delta : delta));
        if (base == 0 && after > 0) { if (f->hard[c]) hd += (int64_t)hmult[c]; else sd -= f->weight[c]; }
        else if (base > 0 && after == 0) { if (f->hard[c]) hd -= (int64_t)hmult[c]; else sd += f->weight[c]; }
    }
    *hard_delta = hd; *soft_delta = sd;
}

/* ------------------------------------------------------------------
   repair — the legacy WalkSAT-style repair (kept behind --repair-walk).

   It walks like this: pick a random violated clause, pick a variable in
   it (weighted by ProbSAT's break-count heuristic), flip it, repeat, with
   a tabu list to stop it flipping the same variable back immediately.

   It is simple and it is what SUTRA used before.  It is NOT the default
   any more: repair_nuwls() (sutra_nuwls.h) takes global ascent steps and
   is dramatically better on weighted instances.  Keeping the old engine
   costs nothing and makes A/B comparisons possible.
   ------------------------------------------------------------------ */
static uint64_t repair(const Formula *f, uint8_t *asn, uint64_t flips_budget,
                       int *converged, double time_budget, clock_t t0,
                       uint64_t stall_limit, uint64_t tabu_tenure) {
    int dbg = getenv("SUTRA_DEBUG") != NULL;
    /* incremental satisfaction via per-clause counts and occurrence lists */
    uint64_t *cnt = calloc(f->clauses, sizeof(uint64_t));
    if (!cnt) die("out of memory");
    for (uint64_t c = 0; c < f->clauses; c++)
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; j++) {
            int32_t l = f->lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
            if ((l > 0) == (asn[v] != 0)) cnt[c]++;
        }
    /* unsat lists split hard/soft for lexicographic priority */
    uint64_t hard_unsat = 0, soft_cost = 0;
    uint64_t *unsat = malloc((f->clauses ? f->clauses : 1) * sizeof(uint64_t));
    uint64_t *unsat_pos = malloc((f->clauses ? f->clauses : 1) * sizeof(uint64_t));
    if (!unsat || !unsat_pos) die("out of memory");
    uint64_t n_unsat = 0;
    for (uint64_t c = 0; c < f->clauses; c++) {
        unsat_pos[c] = UINT64_MAX;
        if (cnt[c] == 0) {
            unsat_add(unsat, unsat_pos, &n_unsat, &hard_unsat, c, f->hard[c]);
            if (!f->hard[c]) soft_cost += f->weight[c];
        }
    }
    uint64_t used = 0;
    double noise = 0.5;                     /* constant WalkSAT noise — the
                                              reference-validated setting */
    *converged = 0;
    /* tabu memory: a var flipped recently cannot be re-flipped for T steps;
       without it the greedy oscillates between two assignments.  The tenure
       is an option (--tabu, default 10) because as written it was 0, which
       made every guard below dead code. */
    uint64_t *tabu_until = calloc(f->vars + 1, sizeof(uint64_t));
    if (!tabu_until) die("out of memory");
    uint64_t best_hard_seen = hard_unsat;
    double best_soft_seen = soft_cost;
    uint64_t since_improve = 0;
    /* track the lexicographic best assignment inside the repair itself;
       the terminal state of a noisy random walk is NOT the answer */
    uint8_t *r_best = malloc(f->vars + 1);
    if (!r_best) die("out of memory");
    memcpy(r_best, asn, f->vars + 1);
    /* Commit only variables touched since the last incumbent. A variable
       occurs at most once in this journal, so storage is bounded by vars. */
    uint32_t *dirty = malloc(((size_t)f->vars + 1) * sizeof(uint32_t));
    uint8_t *marked = calloc((size_t)f->vars + 1, 1);
    uint32_t n_dirty = 0;
    if (!dirty || !marked) die("out of memory");
    /* dynamic weight growth: when hard repair plateaus, boost the weights
       of the STILL-unsat hard clauses so they dominate break-scoring and
       force the search off the plateau (v2's validated escape). */
    double *hmult = calloc(f->clauses ? f->clauses : 1, sizeof(double));
    if (!hmult) die("out of memory");
    for (uint64_t c = 0; c < f->clauses; c++) hmult[c] = 1.0;
    uint64_t since_boost = 0;
    while (n_unsat > 0 && used < flips_budget) {
        if (time_budget > 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > time_budget) break;
        /* pick a violated clause: hard first, RANDOM among them (v2's
           fixed first-choice cycles; randomization is the classic
           WalkSAT fix for greedy traps) */
        uint64_t pick = hard_unsat ? unsat[rng_next() % hard_unsat] : UINT64_MAX;
        if (pick == UINT64_MAX) {
            /* no hard violations: soft polish — pick the heaviest unsat
               soft clause (weighted greedy) with occasional randomness */
            if (rng_double() < 0.25) pick = unsat[rng_below((uint32_t)n_unsat)];
            else {
                double bw = -1;
                for (uint64_t i = 0; i < n_unsat; i++) {
                    double w = f->hard[unsat[i]] ? DBL_MAX : f->weight[unsat[i]];
                    if (w > bw) { bw = w; pick = unsat[i]; }
                }
            }
        }
        /* consider flipping each variable in the clause; score =
           (hard breaks - hard fixes, soft delta); lexicographic hard-first */
        /* probSAT scoring: instead of argmin, sample a clause variable with
           probability proportional to cb^-(break_score - min_score).
           Soft-hard lexicographic score: hard breaks dominate, soft delta
           breaks ties.  Tabu vars are excluded unless all are tabu. */
        int32_t best_var = 0;
        {
            uint64_t nvars_in = f->offset[pick + 1] - f->offset[pick];
            if (nvars_in == 0) break;                  /* empty clause: unsat */
            if (rng_double() < noise) {
                uint64_t j = f->offset[pick] + rng_below((uint32_t)nvars_in);
                best_var = (int32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
            } else {
                /* Two streaming passes over the clause's literals, so a wide
                   clause is scored in full.  (The array form this replaces
                   capped candidates at MAXC = 32 and silently ignored the
                   rest.)  Pass 1 keeps the best (hd, sd); pass 2 picks
                   uniformly among the ties, which is what the array form
                   did.  Same scoring rule, same tie-break, same RNG use. */
                int64_t bh = 0; double bs = 0; int have = 0;
                for (uint64_t j = f->offset[pick]; j < f->offset[pick + 1]; j++) {
                    int32_t l = f->lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                    if (used < tabu_until[v]) continue;
                    int64_t hd; double sd;
                    flip_delta(f, asn, cnt, hmult, v, &hd, &sd);
                    if (!have || hd > bh || (hd == bh && sd < bs)) { bh = hd; bs = sd; have = 1; }
                }
                if (!have) {
                    uint64_t j = f->offset[pick] + rng_below((uint32_t)nvars_in);
                    best_var = (int32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
                } else {
                    /* max hd (net hard fixes), tie-break min sd, then random */
                    uint64_t ties = 0;
                    for (uint64_t j = f->offset[pick]; j < f->offset[pick + 1]; j++) {
                        int32_t l = f->lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                        if (used < tabu_until[v]) continue;
                        int64_t hd; double sd;
                        flip_delta(f, asn, cnt, hmult, v, &hd, &sd);
                        if (hd == bh && sd == bs) ties++;
                    }
                    uint64_t want = 1 + (ties ? rng_next() % ties : 0), seen = 0;
                    best_var = 0;
                    for (uint64_t j = f->offset[pick]; j < f->offset[pick + 1] && best_var == 0; j++) {
                        int32_t l = f->lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                        if (used < tabu_until[v]) continue;
                        int64_t hd; double sd;
                        flip_delta(f, asn, cnt, hmult, v, &hd, &sd);
                        if (hd == bh && sd == bs && ++seen == want) best_var = (int32_t)v;
                    }
                }
            }
        }
        if (best_var == 0) break;                     /* empty clause: unsatisfiable */
        /* tabu: remember this flip */
        tabu_until[best_var] = used + tabu_tenure;
        /* apply flip — compute was/now from the OLD value.  The toggle
           hasn't happened yet, so the post-flip value is current^1. */
        int newval = (asn[best_var] != 0) ^ 1;   /* value AFTER the flip */
        int oldval = newval ^ 1;                 /* value BEFORE the flip */
        if (!marked[best_var]) {
            marked[best_var] = 1;
            dirty[n_dirty++] = (uint32_t)best_var;
        }
        asn[best_var] ^= 1;
        used++;
        for (uint64_t k = f->occ_offset[best_var]; k < f->occ_offset[best_var + 1]; k++) {
            uint64_t c = f->occ_clause[k];
            uint64_t prev = cnt[c];
            int64_t delta = f->occ_delta[k];
            cnt[c] = (uint64_t)((int64_t)prev + (oldval ? -delta : delta));
            /* transitions decided on prev->post counts only; firing on any
               literal-true event double-counts satisfied clauses and
               underflows the running totals */
            if (prev == 0 && cnt[c] > 0) {            /* became sat */
                unsat_remove(unsat, unsat_pos, &n_unsat, &hard_unsat, c, f->hard[c]);
                if (!f->hard[c]) soft_cost -= f->weight[c];
            } else if (prev > 0 && cnt[c] == 0) {     /* became unsat */
                unsat_add(unsat, unsat_pos, &n_unsat, &hard_unsat, c, f->hard[c]);
                if (!f->hard[c]) soft_cost += f->weight[c];
            }
        }
        if (dbg && used % 10000 == 0) {
            /* integrity check: maintained cnt vs full recount */
            uint64_t mism = 0, true_unsat = 0;
            for (uint64_t c = 0; c < f->clauses; c++) {
                uint64_t real = 0;
                for (uint64_t q = f->offset[c]; q < f->offset[c + 1]; q++) {
                    int32_t l = f->lits[q]; uint32_t vv = (uint32_t)(l < 0 ? -l : l);
                    if ((l > 0) == (asn[vv] != 0)) real++;
                }
                if (real != cnt[c]) mism++;
                if (real == 0) true_unsat++;
            }
            uint64_t list_bad = 0;
            for (uint64_t i = 0; i < n_unsat; i++) {
                uint64_t c = unsat[i];
                uint64_t real = 0;
                for (uint64_t q = f->offset[c]; q < f->offset[c + 1]; q++) {
                    int32_t l = f->lits[q]; uint32_t vv = (uint32_t)(l < 0 ? -l : l);
                    if ((l > 0) == (asn[vv] != 0)) real++;
                }
                if (real != 0) list_bad++;
            }
            fprintf(stderr, "[dbg] flips=%" PRIu64 " n_unsat=%" PRIu64 " hard_unsat=%" PRIu64
                    " | recount: true_unsat=%" PRIu64 " cnt_mismatch=%" PRIu64
                    " stale_in_list=%" PRIu64 "\n",
                    used, n_unsat, hard_unsat, true_unsat, mism, list_bad);
        }
        /* W3: honest convergence — no hard improvement in a long window
           means a genuine plateau; give up with converged=0 (NOT converged) */
        if (hard_unsat < best_hard_seen ||
            (hard_unsat == best_hard_seen && soft_cost < best_soft_seen - 1e-12)) {
            best_hard_seen = hard_unsat; best_soft_seen = soft_cost;
            since_improve = 0;
            for (uint32_t i = 0; i < n_dirty; i++) {
                uint32_t var = dirty[i];
                r_best[var] = asn[var];
                marked[var] = 0;
            }
            n_dirty = 0;
        } else since_improve++;
        if (++since_boost > 1000 && hard_unsat > 0) {
            since_boost = 0;
            for (uint64_t i = 0; i < n_unsat; i++) {
                uint64_t c = unsat[i];
                if (f->hard[c] && hmult[c] < 64.0) hmult[c] *= 1.05;
            }
        }
        if (since_improve > (hard_unsat == 0 ? stall_limit / 6 : stall_limit)) break;
    }
    if (n_unsat == 0) *converged = 1;
    memcpy(asn, r_best, f->vars + 1);      /* return the best state seen */
    free(dirty); free(marked);
    free(cnt); free(unsat); free(unsat_pos); free(r_best); free(hmult); free(tabu_until);
    return used;
}

/* ------------------------------------------------------------------ */
/* Main solve: W4 time budget, W5 diversified restarts, anytime best     */
/* ------------------------------------------------------------------ */
typedef struct {
    uint64_t satisfied, hard_unsat, soft_unsat;
    double soft_cost;
    uint8_t *asn;
    int valid;
} Best;


/* ------------------------------------------------------------------ */
/* Portfolio: delegate to an external CDCL and keep only verified      */
/* answers.  The external solver is trusted for nothing; its witness   */
/* is recounted here and its refutation is checked by sutracert.       */
/* ------------------------------------------------------------------ */
/* ------------------------------------------------------------------
   external_solve — portfolio delegation, with trust removed.

   If the user points at an external CDCL (--kissat), we run it and then
   independently verify whatever it says:

     * SAT   -> read its assignment, then recount every clause ourselves.
                If a single clause fails, the answer is discarded.
     * UNSAT -> keep its DRAT proof only if an external checker
                (drat-trim or sutracert) accepts it.  Otherwise we do not
                report UNSAT at all.

   The external solver is treated exactly like any other untrusted
   component: useful, but never believed without evidence.
   ------------------------------------------------------------------ */
static int external_solve(const Formula *f, const Options *o, FILE *drat,
                          uint8_t *model, int *unsat_verified) {
    if (!o->kissat_path) return 0;
    char proof[512] = "";
    char cmd[2048];
    if (drat) {
        snprintf(proof, sizeof proof, "/tmp/sutra_kissat_%ld.proof", (long)getpid());
        /* kissat takes the proof path as a positional argument */
        snprintf(cmd, sizeof cmd, "\"%s\" \"%s\" \"%s\" >/tmp/sutra_kissat.out 2>/dev/null",
                 o->kissat_path, o->input, proof);
    } else {
        snprintf(cmd, sizeof cmd, "\"%s\" \"%s\" >/tmp/sutra_kissat.out 2>/dev/null",
                 o->kissat_path, o->input);
    }
    int rc = system(cmd);
    int code = (rc >= 0 && WIFEXITED(rc)) ? WEXITSTATUS(rc) : -1;

    if (code == 20) {
        int verified = 0;
        if (drat && o->checker_path) {
            char chk[2048];
            const char *base = strrchr(o->checker_path, '/');
            base = base ? base + 1 : o->checker_path;
            if (strstr(base, "drat-trim")) {
                snprintf(chk, sizeof chk, "\"%s\" \"%s\" \"%s\" 2>/dev/null | grep -q 's VERIFIED'",
                         o->checker_path, o->input, proof);
            } else {
                snprintf(chk, sizeof chk, "\"%s\" check \"%s\" \"%s\" >/dev/null 2>&1",
                         o->checker_path, o->input, proof);
            }
            int crc = system(chk);
            verified = (crc >= 0 && WIFEXITED(crc) && WEXITSTATUS(crc) == 0);
        }
        if (verified && drat) {
            /* hand the verified proof back to the caller */
            FILE *src = fopen(proof, "rb"), *dst = drat;
            if (src && dst) {
                char buf[65536];
                size_t n;
                while ((n = fread(buf, 1, sizeof buf, src)) > 0) fwrite(buf, 1, n, dst);
                fflush(dst);
            }
            if (src) fclose(src);
        }
        if (proof[0]) remove(proof);
        *unsat_verified = verified;
        return 20;
    }
    if (code == 10) {
        FILE *wf = fopen("/tmp/sutra_kissat.out", "r");
        if (!wf) return 0;
        char line[1 << 16];
        while (fgets(line, sizeof line, wf)) {
            char *p = line;
            while (*p == ' ' || *p == '\t') p++;
            if (*p != 'v') continue;
            p++;
            for (char *tok = strtok(p, " \t\r\n"); tok; tok = strtok(NULL, " \t\r\n")) {
                char *e = NULL;
                long l = strtol(tok, &e, 10);
                if (e == tok || l == 0) continue;
                uint32_t v = (uint32_t)(l < 0 ? -l : l);
                if (v <= f->vars) model[v] = (l > 0);
            }
        }
        fclose(wf);
        /* recount: a delegated witness is only accepted if it checks out */
        for (uint64_t c = 0; c < f->clauses; ++c) {
            int sat = 0;
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                int32_t l = f->lits[j];
                uint32_t v = (uint32_t)(l < 0 ? -l : l);
                if ((l > 0) == (model[v] != 0)) { sat = 1; break; }
            }
            if (!sat) return 0;
        }
        return 10;
    }
    if (proof[0]) remove(proof);
    return 0;
}

/* ------------------------------------------------------------------
   main — the pipeline.

     1. parse flags and the input file
     2. parity preprocessing: detect XOR structure, refute or build a model
     3. certified portfolio: optional external CDCL, verified
     4. continuous warm start + NuWLS repair, repeated over restarts
     5. optional CDCL refinement to certify UNSAT
     6. print results, recomputed from the witness

   Every early return corresponds to a proven answer: a parity
   refutation, an external proof that checked out, or a satisfied model.
   ------------------------------------------------------------------ */
int main(int argc, char **argv) {
    Options o;
    memset(&o, 0, sizeof o);
    o.steps = 300; o.restarts = 4; o.repair_flips = 100000;
    o.time_budget = 0; o.seed = 42; o.json = 1; o.lr = 0.02; o.tabu = 10;
    o.tau = 1.0; o.dec_threshold = 0.45; o.dec_freq = 50; o.soft_phase = 0;

    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (!strcmp(a, "--steps") && i + 1 < argc) o.steps = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(a, "--restarts") && i + 1 < argc) o.restarts = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(a, "--repair-flips") && i + 1 < argc) o.repair_flips = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(a, "--time-budget-seconds") && i + 1 < argc) o.time_budget = strtod(argv[++i], NULL);
        else if (!strcmp(a, "--seed") && i + 1 < argc) o.seed = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(a, "--tabu") && i + 1 < argc) o.tabu = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(a, "--solution") && i + 1 < argc) o.solution_path = argv[++i];
        else if (!strcmp(a, "--warm-start") && i + 1 < argc) o.warm_start_path = argv[++i];
        else if (!strcmp(a, "--residual-cmd") && i + 1 < argc) o.residual_cmd = argv[++i];
        else if (!strcmp(a, "--learning-rate") && i + 1 < argc) o.lr = strtod(argv[++i], NULL);
        else if (!strcmp(a, "--relax-tau") && i + 1 < argc) o.tau = strtod(argv[++i], NULL);
        else if (!strcmp(a, "--no-json")) o.json = 0;
        else if (!strcmp(a, "--json")) o.json = 1;
        else if (!strcmp(a, "--checkpoint") && i + 1 < argc) o.checkpoint.path = argv[++i];
        else if (!strcmp(a, "--checkpoint-interval-ms") && i + 1 < argc) {
            double ms = strtod(argv[++i], NULL);
            o.checkpoint.interval_seconds = (ms < 0.0) ? 0.0 : ms / 1000.0;
        }
        else if (!strcmp(a, "--proof") && i + 1 < argc) o.proof_path = argv[++i];
        else if (!strcmp(a, "--proof-format") && i + 1 < argc) o.proof_format = argv[++i];
        else if (!strcmp(a, "--exact-conflicts") && i + 1 < argc) o.exact_conflicts = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(a, "--no-parity")) o.no_parity = 1;
        else if (!strcmp(a, "--repair-nuwls")) o.walk = 0;
        else if (!strcmp(a, "--repair-walk")) o.walk = 1;
        else if (!strcmp(a, "--kissat") && i + 1 < argc) o.kissat_path = argv[++i];
        else if (!strcmp(a, "--checker") && i + 1 < argc) o.checker_path = argv[++i];
        else if (!strcmp(a, "--help") || !strcmp(a, "-h")) {
            printf("SUTRA %s - MaxSAT approximator (witness-first, best-effort)\n"
                   "Usage: %s INPUT.cnf|INPUT.wcnf [options]\n"
                   "  --steps N              continuous steps per restart (default 300)\n"
                   "  --restarts N           max restarts (default: until time budget)\n"
                   "  --repair-flips N       discrete repair budget per restart (default 100000)\n"
                   "  --time-budget-seconds X  wall-clock budget; returns best-so-far (default 0=none)\n"
                   "  --seed N               base RNG seed (restarts derive diverse seeds)\n"
                   "  --tabu N               repair tabu tenure in flips (default 10; 0 disables)\n"
                   "  --learning-rate X      Adam learning rate (default 0.02)\n"
                   "  --relax-tau X          LP-hinge temperature (default 1)\n"
                   "  --solution FILE        write DIMACS witness assignment\n"
                   "  --checkpoint FILE      periodically write best-so-far for SIGKILL salvage\n"
                   "  --checkpoint-interval-ms N   checkpoint cadence (default 0 = disabled)\n"
                   "  --no-json              human output\n"
                   "  --proof FILE           emit a refutation certificate (gfp or DRAT)\n"
                   "  --proof-format FMT     auto (default), gfp, or drat\n"
                   "  --exact-conflicts N    CDCL budget for a certified refutation (default 0=off)\n"
                   "  --no-parity            disable GF(2) parity preprocessing\n"
                   "Statuses: SAT, FEASIBLE (hard ok, soft approx), UNKNOWN (budget), UNSAT (certified).\n"
                   "UNSAT is reported only when a certificate was written.\n",
                   SUTRA_VERSION, argv[0]);
            return 0;
        }
        else if (a[0] != '-' && !o.input) o.input = a;
        else { fprintf(stderr, "unknown option: %s\n", a); return 1; }
    }
    if (!o.input) { fprintf(stderr, "Usage: %s INPUT [options]\n", argv[0]); return 1; }
    if (!o.checker_path) o.checker_path = "sutracert";

    Formula f;
    parse_input(o.input, &f);

    /* ---- preprocessing: GF(2) parity refutation ---------------------
       Detect clause groups that are exactly a parity constraint
       (4 clauses / 3 vars, verified by exhaustive truth table), then
       eliminate over GF(2).  An inconsistent system yields a refutation
       certificate of O(#equations) lines.  If no gfp certificate is
       requested we keep the finding as a diagnostic but do NOT claim
       UNSAT: SUTRA only reports what it can prove. */
    int parity_refuted = 0, parity_certified = 0;
    uint32_t parity_eq = 0, parity_used = 0;
    if (!o.no_parity && f.vars) {
        ParEq *eqs = NULL; uint32_t neq = 0;
        if (sutra_detect_parity(&f, &eqs, &neq)) {
            parity_eq = neq;
            uint32_t *subset = malloc((size_t)neq * sizeof(uint32_t));
            uint32_t cnt = 0;
            if (subset && sutra_gf2_refute(f.vars, eqs, neq, subset, &cnt)) {
                parity_refuted = 1; parity_eq = neq; parity_used = cnt;
                int gfp_ok = !o.proof_format || !strcmp(o.proof_format, "auto") ||
                             !strcmp(o.proof_format, "gfp");
                if (gfp_ok && o.proof_path) {
                    FILE *pf = fopen(o.proof_path, "w");
                    if (pf && sutra_write_gfp(pf, eqs, subset, cnt, f.vars)) parity_certified = 1;
                    if (pf) fclose(pf);
                }
            }
            free(subset); free(eqs);
        }
    }
    /* If the parity system is consistent, one of its solutions may be a
       full model.  Enumerate the nullspace; a hit is a verified witness,
       not a guess. */
    uint8_t *parity_seed = NULL;
    if (!parity_certified && !o.no_parity && f.vars) {
        ParEq *eqs = NULL; uint32_t neq = 0;
        if (sutra_detect_parity(&f, &eqs, &neq) && neq) {
            parity_eq = neq;
            uint8_t *model = calloc(f.vars + 1, 1);
            parity_seed = calloc(f.vars + 1, 1);
            if (model && parity_seed &&
                sutra_parity_model(&f, eqs, neq, model, 16, parity_seed)) {
                uint64_t sat = 0, hu = 0; double sc = 0.0;
                for (uint64_t c = 0; c < f.clauses; ++c) {
                    int ok = 0;
                    for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; ++j) {
                        int32_t l = f.lits[j];
                        uint32_t v = (uint32_t)(l < 0 ? -l : l);
                        if ((l > 0) == (model[v] != 0)) { ok = 1; break; }
                    }
                    if (ok) sat++;
                    else if (f.hard[c]) hu++;
                    else sc += f.weight[c];
                }
                if (o.solution_path) {
                    FILE *sf = fopen(o.solution_path, "w");
                    if (sf) {
                        fprintf(sf, "s SATISFIABLE\n");
                        for (uint32_t v = 1; v <= f.vars; ++v)
                            fprintf(sf, "v %d\n", model[v] ? (int)v : -(int)v);
                        fclose(sf);
                    }
                }
                if (o.proof_path) remove(o.proof_path);
                const char *st = (hu == 0 && sc == 0.0) ? "SAT" : "FEASIBLE";
                if (o.json) {
                    printf("{\"engine\":\"SUTRA\",\"version\":\"%s\",\"input\":\"%s\","
                           "\"status\":\"%s\",\"variables\":%u,\"clauses\":%" PRIu64 ","
                           "\"satisfied\":%" PRIu64 ",\"hard_unsatisfied\":%" PRIu64 ","
                           "\"soft_cost\":%.1f,\"certified\":false,"
                           "\"parity_model\":true,\"wall_seconds\":0.0}\n",
                           SUTRA_VERSION, o.input, st, f.vars, f.clauses, sat, hu, sc);
                } else {
                    printf("SUTRA %s  %s: %s\n  parity model (%u equations), "
                           "%" PRIu64 "/%" PRIu64 " clauses satisfied\n",
                           SUTRA_VERSION, o.input, st, neq, sat, f.clauses);
                }
                return (!strcmp(st, "SAT")) ? 10 : 0;
            }
            free(model);
            free(eqs);
        }
    }

    if (parity_certified) {
        if (o.json) {
            printf("{\"engine\":\"SUTRA\",\"version\":\"%s\",\"input\":\"%s\","
                   "\"status\":\"UNSAT\",\"certified\":true,\"proof\":\"%s\","
                   "\"proof_format\":\"gfp\",\"parity_equations\":%u,\"parity_used\":%u,"
                   "\"variables\":%u,\"clauses\":%" PRIu64 ",\"wall_seconds\":0.0}\n",
                   SUTRA_VERSION, o.input, o.proof_path, parity_eq, parity_used,
                   f.vars, f.clauses);
        } else {
            printf("SUTRA %s  %s: UNSAT (certified, gfp)\n  parity equations %u, "
                   "refutation uses %u\n  proof: %s\n",
                   SUTRA_VERSION, o.input, parity_eq, parity_used, o.proof_path);
        }
        return 20;
    }
    /* ---- certified portfolio -------------------------------------
       Pure CNF only.  The external CDCL is run with a proof, and its
       refutation is accepted only if sutracert verifies it; a SAT
       witness is recounted clause by clause here.  Nothing is trusted. */
    if (o.kissat_path && f.total_soft_weight == 0.0) {
        uint8_t *model = calloc(f.vars + 1, 1);
        FILE *pf = o.proof_path ? fopen(o.proof_path, "w") : NULL;
        int unsat_ok = 0;
        int r = external_solve(&f, &o, pf, model, &unsat_ok);
        if (pf) fclose(pf);
        if (r == 20 && unsat_ok) {
            if (o.json) {
                printf("{\"engine\":\"SUTRA\",\"version\":\"%s\",\"input\":\"%s\","
                       "\"status\":\"UNSAT\",\"certified\":true,\"proof\":\"%s\","
                       "\"proof_format\":\"drat\",\"solver\":\"external+kernel\","
                       "\"variables\":%u,\"clauses\":%" PRIu64 ",\"wall_seconds\":0.0}\n",
                       SUTRA_VERSION, o.input, o.proof_path ? o.proof_path : "",
                       f.vars, f.clauses);
            } else {
                printf("SUTRA %s  %s: UNSAT (certified, drat from external CDCL)\n",
                       SUTRA_VERSION, o.input);
            }
            return 20;
        }
        if (r == 10) {
            uint64_t sat = 0;
            for (uint64_t c = 0; c < f.clauses; ++c) {
                int ok = 0;
                for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; ++j) {
                    int32_t l = f.lits[j];
                    uint32_t v = (uint32_t)(l < 0 ? -l : l);
                    if ((l > 0) == (model[v] != 0)) { ok = 1; break; }
                }
                sat += (uint64_t)ok;
            }
            if (o.solution_path) {
                FILE *sf = fopen(o.solution_path, "w");
                if (sf) {
                    fprintf(sf, "s SATISFIABLE\n");
                    for (uint32_t v = 1; v <= f.vars; ++v)
                        fprintf(sf, "v %d\n", model[v] ? (int)v : -(int)v);
                    fclose(sf);
                }
            }
            if (o.proof_path) remove(o.proof_path);
            if (o.json) {
                printf("{\"engine\":\"SUTRA\",\"version\":\"%s\",\"input\":\"%s\","
                       "\"status\":\"SAT\",\"certified\":false,\"solver\":\"external\","
                       "\"variables\":%u,\"clauses\":%" PRIu64 ",\"satisfied\":%" PRIu64 ","
                       "\"hard_unsatisfied\":0,\"wall_seconds\":0.0}\n",
                       SUTRA_VERSION, o.input, f.vars, f.clauses, sat);
            } else {
                printf("SUTRA %s  %s: SAT (external witness, recounted)\n",
                       SUTRA_VERSION, o.input);
            }
            free(model);
            return 10;
        }
        if (o.proof_path) remove(o.proof_path);
        free(model);
    }

    /* adaptive effort: huge formulas get fewer continuous steps per
       restart (the gradient pass is O(clauses*steps) and dominates);
       the repair phase carries the load.  Explicit flags still win. */
    int steps_explicit = 0, restarts_explicit = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--steps")) steps_explicit = 1;
        if (!strcmp(argv[i], "--restarts")) restarts_explicit = 1;
    }
    if (!steps_explicit && f.clauses > 200000) o.steps = 60;
    if (!restarts_explicit && f.clauses > 200000) o.restarts = 2;
    /* repair budget scales with clause count: 100k flips suffices for
       ~30k clauses, but large planted instances need ~0.4 flips/clause */
    {
        int flips_explicit = 0;
        for (int i = 1; i < argc; i++)
            if (!strcmp(argv[i], "--repair-flips")) flips_explicit = 1;
        if (!flips_explicit) {
            uint64_t want = f.clauses * 2;
            if (want < 100000) want = 100000;
            if (want > 2000000) want = 2000000;
            o.repair_flips = want;
        }
    }

    /* with a wall-clock budget the repair runs until time, unless the
       caller asked for a specific flip budget */
    if (o.time_budget > 0.0) {
        int fe = 0;
        for (int i = 1; i < argc; i++)
            if (!strcmp(argv[i], "--repair-flips")) fe = 1;
        if (!fe) o.repair_flips = UINT64_MAX;
    }

    double *x = malloc((f.vars + 1) * sizeof(double));
    double *g = malloc((f.vars + 1) * sizeof(double));
    double *m = malloc((f.vars + 1) * sizeof(double));
    double *v = malloc((f.vars + 1) * sizeof(double));
    uint8_t *asn = malloc(f.vars + 1);
    Best best; memset(&best, 0, sizeof best);
    best.asn = malloc(f.vars + 1);
    best.hard_unsat = UINT64_MAX; best.soft_cost = DBL_MAX;
    Score sc; sc.sat_count = malloc(f.clauses * sizeof(uint64_t));

    /* Anytime checkpoint: open the periodic-best file so a Python
       watchdog kill (SIGKILL) salvages whatever v3 had found.  Seed it
       with the all-false assignment so a kill before the first
       improvement still leaves a parseable file. */
    if (!navokoj_checkpoint_open(&o.checkpoint,
                                 o.checkpoint.path,
                                 o.checkpoint.interval_seconds)) {
        return 1;
    }
    memset(best.asn, 0, f.vars + 1);
    navokoj_checkpoint_update(&o.checkpoint, f.vars, best.asn, f.clauses);
    navokoj_checkpoint_flush(&o.checkpoint);

    /* warm start: seed x from another engine's witness.  This is the
       bridge that lets v2's (heavier) continuous phase feed v3's (better)
       repair. */
    uint8_t *warm = NULL;
    if (o.warm_start_path) {
        warm = calloc(f.vars + 1, 1);
        if (!warm) die("out of memory");
        FILE *wf = fopen(o.warm_start_path, "r");
        if (!wf) die("cannot open warm-start file");
        char wl[1 << 16];
        uint32_t got = 0;
        int in_v = 0;   /* witness lines can exceed the buffer: keep
                           consuming continuation lines once a v-line starts */
        while (fgets(wl, sizeof wl, wf)) {
            char *p = wl;
            while (*p == ' ' || *p == '\t') p++;
            if (*p == 's' || *p == 'S' || *p == 'c' || *p == 'p') { in_v = 0; continue; }
            if (*p == 'v' || *p == 'V') { in_v = 1; p++; }
            else if (!in_v) continue;
            for (char *tok = strtok(p, " \t\r\n"); tok; tok = strtok(NULL, " \t\r\n")) {
                char *e = NULL;
                long l = strtol(tok, &e, 10);
                if (e == tok || l == 0) continue;
                uint32_t v = (uint32_t)(l < 0 ? -l : l);
                if (v >= 1 && v <= f.vars) { warm[v] = (l > 0); got++; }
            }
        }
        fclose(wf);
        if (got < f.vars)
            fprintf(stderr, "SUTRA warning: warm start covers %u/%u vars\n", got, f.vars);
    }
    if (o.warm_start_path) {
        int steps_explicit = 0;
        for (int i = 1; i < argc; i++)
            if (!strcmp(argv[i], "--steps")) steps_explicit = 1;
        if (!steps_explicit) o.steps = 0;   /* trust the seed, just repair */
        if (!o.restarts) o.restarts = 1;
    }
    clock_t t0 = clock();
    uint32_t restarts_done = 0, restarts_sat = 0;
    uint64_t last_flips = 0; int last_converged = 0;
    int stop_all_sat = 0;

    for (uint32_t r = 0; ; r++) {
        if (o.time_budget > 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > o.time_budget * 0.98) break;
        } else if (o.restarts == 0) o.restarts = 1;   /* safety: never spin forever */
        if (o.restarts && r >= o.restarts) break;
        if (stop_all_sat) break;
        restarts_done = r + 1;
        rng_state = o.seed * 0x9E3779B97F4A7C15ULL ^ (0x1000193ULL * (r + 1)) ^ 0xDB3FCD2C6B0B71FDULL;
        rng_next();

        /* diversified init: pass 0 uniform random; later passes biased by
           signed-degree polarity (spectral-ish) with per-restart noise */
        memset(m, 0, (f.vars + 1) * sizeof(double));
        memset(v, 0, (f.vars + 1) * sizeof(double));
        for (uint32_t var = 1; var <= f.vars; var++)
            x[var] = (warm && r == 0)
                ? (warm[var] ? 0.999 : 0.001)
                : ((parity_seed && r == 0)
                   ? (parity_seed[var] ? 0.9 : 0.1)
                   : 0.5 + 0.4 * (rng_double() - 0.5));
        if (r > 0) {
            double *polarity = calloc(f.vars + 1, sizeof(double));
            for (uint64_t c = 0; c < f.clauses; c++)
                for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                    int32_t l = f.lits[j]; uint32_t var = (uint32_t)(l < 0 ? -l : l);
                    polarity[var] += (l > 0) ? f.weight[c] : -f.weight[c];
                }
            double mix = 0.5 / (double)(r + 1);
            for (uint32_t var = 1; var <= f.vars; var++)
                x[var] = 0.5 + (1 - mix) * 0.4 * (rng_double() - 0.5)
                       + mix * 0.25 * tanh(polarity[var] / 10.0);
            free(polarity);
        }

        /* continuous descent with decimation */
        uint8_t *decim = calloc(f.vars + 1, 1);
        for (uint32_t step = 1; step <= o.steps; step++) {
            if (o.time_budget > 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC > o.time_budget * 0.9) break;
            gradient_step(&f, x, g, m, v, step, o.steps, &o);
            if (step % o.dec_freq == 0)
                for (uint32_t var = 1; var <= f.vars; var++)
                    if (!decim[var] && fabs(x[var] - 0.5) > o.dec_threshold)
                        { x[var] = x[var] > 0.5 ? 0.999 : 0.001; decim[var] = 1; }
        }
        free(decim);

        /* discretize + verify-driven repair */
        for (uint32_t var = 1; var <= f.vars; var++) asn[var] = x[var] > 0.5;
        /* incumbent: with a warm start, the SEED ITSELF is verified and
           registered as best BEFORE repair runs.  Repair may then only
           improve on it — a wandering repair can never degrade the
           answer (v2's witness preserved exactly, gaps only close). */
        if (warm && r == 0) {
            uint64_t s0, h0, u0; double c0;
            verified_recount(&f, asn, &s0, &h0, &u0, &c0);
            memcpy(best.asn, asn, f.vars + 1);
            best.hard_unsat = h0; best.soft_cost = c0;
            best.satisfied = s0; best.soft_unsat = u0; best.valid = 1;
            navokoj_checkpoint_update(&o.checkpoint, f.vars, best.asn, h0);
            navokoj_checkpoint_maybe(&o.checkpoint);
        }
        int converged = 0;
        uint64_t used = !o.walk
            ? repair_nuwls(&f, asn, o.repair_flips, &converged, o.time_budget, t0,
                           o.repair_flips / 4 < 30000 ? 30000 : o.repair_flips / 4, o.tabu)
            : repair(&f, asn, o.repair_flips, &converged, o.time_budget, t0,
                               o.repair_flips / 4 < 30000 ? 30000 : o.repair_flips / 4,
                               o.tabu);
        last_flips = used; last_converged = converged;

        rescore(&f, x, &sc);   /* placeholder to keep sat_count sized use */
        (void)sc;
        uint64_t sat, hu, su; double scc;
        verified_recount(&f, asn, &sat, &hu, &su, &scc);   /* W6 */
        if (lex_better(hu, scc, best.hard_unsat, best.soft_cost)) {
            memcpy(best.asn, asn, f.vars + 1);
            best.hard_unsat = hu; best.soft_cost = scc;
            best.satisfied = sat; best.soft_unsat = su; best.valid = 1;
            navokoj_checkpoint_update(&o.checkpoint, f.vars, best.asn, hu);
            navokoj_checkpoint_maybe(&o.checkpoint);
        }
        if (hu == 0 && scc == 0 && sat == f.clauses) { restarts_sat++; stop_all_sat = 1; }
    }

    /* ---- residual-core delegation -------------------------------------
       When the heuristic stalls on a small hard core (the glassy endgame
       at n >= 1e5 planted), extract the residual sub-formula around the
       unsat clauses and delegate it to an exact CDCL (--residual-cmd).
       The merged witness is fully re-verified; if anything fails the
       heuristic answer stands.  Nothing about this path is trusted. */
    if (o.residual_cmd && best.valid && best.hard_unsat > 0 &&
        best.hard_unsat * 100 < f.clauses) {
        /* closure: ONLY the variables of the unsat hard clauses.  A BFS
           ring expansion pulls in the connected component, which at
           mega scale is the whole formula (the residual must be small
           or the delegated CDCL is as slow as solving the original). */
        uint8_t *in_res = calloc(f.vars + 1, 1);
        uint64_t nres_vars = 0;
        for (uint64_t c = 0; c < f.clauses; c++) {
            if (!f.hard[c]) continue;
            int unsat = 1;
            for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                if ((l > 0) == (best.asn[v] != 0)) { unsat = 0; break; }
            }
            if (!unsat) continue;
            for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                if (!in_res[v]) { in_res[v] = 1; nres_vars++; }
            }
        }
        /* build residual CNF: keep clauses fully inside; for boundary
           clauses substitute the frozen truth of outside vars */
        char res_cnf[] = "/tmp/sutra_resXXXXXX.cnf";
        char res_sol[] = "/tmp/sutra_resXXXXXX.sol";
        int fd1 = mkstemps(res_cnf, 4), fd2 = mkstemps(res_sol, 4);
        if (fd1 >= 0 && fd2 >= 0) {
            close(fd1); close(fd2);
            /* pass 1: count kept clauses; pass 2: write with exact header */
            uint64_t kept = 0, dropped_sat = 0, hopeless = 0;
            for (uint64_t c = 0; c < f.clauses; c++) {
                int outside_sat = 0;
                for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                    int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                    if (!in_res[v] && (l > 0) == (best.asn[v] != 0)) { outside_sat = 1; break; }
                }
                if (outside_sat) { dropped_sat++; continue; }
                int printed = 0;
                for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                    int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                    if (in_res[v]) { printed = 1; break; }
                }
                if (!printed) { hopeless++; continue; }
                kept++;
            }
            FILE *rf = fopen(res_cnf, "w");
            if (rf) {
                fprintf(rf, "p cnf %u %" PRIu64 "\n", (uint32_t)nres_vars, kept);
                for (uint64_t c = 0; c < f.clauses; c++) {
                    int outside_sat = 0;
                    for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                        int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                        if (!in_res[v] && (l > 0) == (best.asn[v] != 0)) { outside_sat = 1; break; }
                    }
                    if (outside_sat) continue;
                    int printed = 0;
                    for (uint64_t j = f.offset[c]; j < f.offset[c + 1]; j++) {
                        int32_t l = f.lits[j]; uint32_t v = (uint32_t)(l < 0 ? -l : l);
                        if (!in_res[v]) continue;   /* false outside literal: strip */
                        fprintf(rf, "%s%d", printed ? " " : "", l);
                        printed = 1;
                    }
                    if (!printed) continue;         /* clause emptied: hopeless */
                    fprintf(rf, " 0\n");
                }
                fclose(rf);
                /* delegate */
                char cmd[4096];
                snprintf(cmd, sizeof cmd, "%s", o.residual_cmd);
                char pct_f[8] = "%F", pct_s[8] = "%S";
                /* naive %F/%S substitution */
                char expanded[8192]; size_t oi = 0;
                for (const char *p = cmd; *p && oi < sizeof expanded - 1; p++) {
                    if (p[0] == '%' && p[1] == 'F') { oi += snprintf(expanded + oi, sizeof expanded - oi, "%s", res_cnf); p++; }
                    else if (p[0] == '%' && p[1] == 'S') { oi += snprintf(expanded + oi, sizeof expanded - oi, "%s", res_sol); p++; }
                    else expanded[oi++] = *p;
                }
                expanded[oi] = '\0';
                int rc = system(expanded);
                /* merge witness: residual solution maps 1:1 to original vars */
                int merged = 0;
                FILE *sf = fopen(res_sol, "r");
                if (rc == 0 && sf) {
                    char sl[1 << 16];
                    uint8_t *newbits = calloc(f.vars + 1, 1);
                    int8_t *seen = calloc(f.vars + 1, sizeof(int8_t));
                    while (fgets(sl, sizeof sl, sf)) {
                        char *p = sl;
                        while (*p == ' ' || *p == '\t') p++;
                        if (*p != 'v' && *p != 'V') continue;
                        p++;
                        for (char *tok = strtok(p, " \t\r\n"); tok; tok = strtok(NULL, " \t\r\n")) {
                            char *e = NULL; long l = strtol(tok, &e, 10);
                            if (e == tok || l == 0) continue;
                            uint32_t v = (uint32_t)(l < 0 ? -l : l);
                            if (v <= f.vars && in_res[v]) { newbits[v] = l > 0; seen[v] = 1; }
                        }
                    }
                    fclose(sf);
                    uint8_t *merged_asn = malloc(f.vars + 1);
                    for (uint32_t v = 1; v <= f.vars; v++)
                        merged_asn[v] = in_res[v] ? (seen[v] ? newbits[v] : best.asn[v]) : best.asn[v];
                    uint64_t s2, h2, u2; double c2;
                    verified_recount(&f, merged_asn, &s2, &h2, &u2, &c2);
                    if (h2 < best.hard_unsat ||
                        (h2 == best.hard_unsat && c2 < best.soft_cost - 1e-12)) {
                        memcpy(best.asn, merged_asn, f.vars + 1);
                        best.hard_unsat = h2; best.soft_cost = c2;
                        best.satisfied = s2; best.soft_unsat = u2;
                        navokoj_checkpoint_update(&o.checkpoint, f.vars, best.asn, h2);
                        navokoj_checkpoint_maybe(&o.checkpoint);
                        merged = 1;
                    }
                    free(newbits); free(seen); free(merged_asn);
                    fprintf(stderr, "SUTRA residual: vars=%" PRIu64 " kept=%" PRIu64
                            " dropped_sat=%" PRIu64 " hopeless=%" PRIu64 " rc=%d merged=%d\n",
                            nres_vars, kept, dropped_sat, hopeless, rc, merged);
                } else {
                    fprintf(stderr, "SUTRA residual: delegation failed (rc=%d)\n", rc);
                }
            }
        } else {
            fprintf(stderr, "SUTRA residual: cannot create temp files\n");
        }
        free(in_res);
    }

    /* Final flush so the on-disk checkpoint matches the in-memory best
       even when the run ends gracefully. */
    navokoj_checkpoint_close(&o.checkpoint);

    /* ---- certified exact fallback ---------------------------------
       If the heuristic left hard clauses unsatisfied, hand the hard
       core to the embedded CDCL.  It emits DRAT as it derives learned
       clauses, so a refutation arrives with a checkable proof.  The
       seed is the heuristic's best assignment (phase saving only). */
    int exact_unsat = 0;
    if (o.exact_conflicts && best.valid && best.hard_unsat > 0) {
        FILE *pf = o.proof_path ? fopen(o.proof_path, "w") : NULL;
        int r = sutra_run_exact(&f, o.exact_conflicts, pf, best.asn);
        if (pf) fclose(pf);
        if (r == 0) exact_unsat = 1;
    }

    /* final verified numbers (never trust in-loop bookkeeping) */
    uint64_t vsat = 0, vhu = 0, vsu = 0; double vsc = 0;
    if (best.valid) verified_recount(&f, best.asn, &vsat, &vhu, &vsu, &vsc);
    const char *status;
    if (exact_unsat) status = "UNSAT";
    else if (vhu == 0 && vsc == 0) status = "SAT";
    else if (vhu == 0) status = "FEASIBLE";
    else status = "UNKNOWN";
    double wall = (double)(clock() - t0) / CLOCKS_PER_SEC;

    /* W1: witness file when requested */
    if (o.solution_path && best.valid) {
        FILE *fp = fopen(o.solution_path, "w");
        if (fp) {
            fprintf(fp, "s SATISFIABLE\n");
            for (uint32_t var = 1; var <= f.vars; var++)
                fprintf(fp, "v %d\n", best.asn[var] ? (int)var : -(int)var);
            fclose(fp);
        } else fprintf(stderr, "SUTRA warning: cannot write %s\n", o.solution_path);
    }

    if (o.json) {
        printf("{\"engine\":\"SUTRA\",\"version\":\"%s\",\"input\":\"%s\","
               "\"status\":\"%s\",\"variables\":%" PRIu32 ",\"clauses\":%" PRIu64 ","
               "\"literals\":%" PRIu64 ",\"satisfied\":%" PRIu64 ",\"hard_unsatisfied\":%" PRIu64 ","
               "\"soft_unsatisfied\":%" PRIu64 ",\"soft_cost\":%.1f,"
               "\"total_soft_weight\":%.1f,\"restarts_used\":%" PRIu32 ","
               "\"repair_flips\":%" PRIu64 ",\"repair_converged\":%s,"
               "\"repair_budget_exhausted\":%s,\"wall_seconds\":%.3f,"
               "\"certified\":%s,\"proof\":\"%s\",\"proof_format\":\"%s\","
               "\"parity_contradiction\":%s,\"parity_equations\":%u,\"parity_used\":%u,"
               "\"verified\":\"recount_from_witness\"}\n",
               SUTRA_VERSION, o.input, status, f.vars, f.clauses, f.literals,
               vsat, vhu, vsu, vsc, f.total_soft_weight, restarts_done,
               last_flips, last_converged ? "true" : "false",
               (last_converged || o.time_budget == 0) ? "false" : "true", wall,
               exact_unsat ? "true" : "false",
               (exact_unsat && o.proof_path) ? o.proof_path : "",
               exact_unsat ? "drat" : "none",
               parity_refuted ? "true" : "false", parity_eq, parity_used);
    } else {
        printf("SUTRA %s  %s: %s\n  %" PRIu64 "/%" PRIu64 " clauses satisfied "
               "(hard unsat %" PRIu64 ", soft cost %.1f)\n  restarts=%u flips=%" PRIu64
               " converged=%d wall=%.3fs\n",
               SUTRA_VERSION, o.input, status, vsat, f.clauses, vhu, vsc,
               restarts_done, last_flips, last_converged, wall);
        if (exact_unsat)
            printf("  certified refutation written to %s (drat)\n", o.proof_path);
        else if (parity_refuted)
            printf("  parity contradiction detected (no certificate requested)\n");
    }
    if (exact_unsat) return 20;
    if (o.proof_path) remove(o.proof_path);   /* no certificate -> no file */
    return (!strcmp(status, "SAT")) ? 10 : 0;
}
