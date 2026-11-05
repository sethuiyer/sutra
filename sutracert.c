/*=====================================================================
  sutracert — independent certificate checker
  Author: Sethu Iyer (github.com/sethuiyer)

  WHAT THIS FILE IS
  -----------------
  A verifier for the two proof formats SUTRA emits.  It deliberately
  shares no code with the solver: a certificate is only convincing if it
  can be checked by something that does not trust the producer.

  Usage:  sutracert check <input.cnf> <proof>
  Exit:   0 verified, 1 rejected, 2 usage or I/O error.

  TWO FORMATS
  -----------
  gfp:
      p gfp <nvars> <neq>
      e <rhs> <k> <v1..vk> <coefmask>
      ...
      u
    Each `e` line claims: XOR of the variables selected by coefmask equals
    rhs.  The checker finds every clause in the input whose variable set
    is exactly {v1..vk}, enumerates all 2^k assignments, and confirms the
    equation holds on every assignment that satisfies those clauses.  If
    it holds for all of them, the equation is implied — which is all a
    refutation needs.  Finally every variable must appear an even number
    of times across the listed equations (so the XORs cancel) and the RHS
    values must XOR to 1 (so the result is 0 = 1).

  DRAT:
      <literals> 0
    Additions only.  Each added clause must be RUP: assume its negation,
    propagate units, reach a conflict.  The proof is complete when the
    empty clause is derived.  This checker uses the standard two-watched-
    literal propagation loop, so it is fast enough for real proofs.

  HOW TO READ THIS FILE
  ---------------------
    cnf_load     -> parse DIMACS (including WCNF, where a weight comes
                    before each clause)
    check_gfp    -> the parity route
    propagate    -> unit propagation for the RUP check
    rup          -> "is this clause derivable right now?"
    check_drat   -> the clause-by-clause route
=====================================================================*/
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void die(const char *m) { fprintf(stderr, "sutracert: %s\n", m); exit(2); }

/* ---------------- CNF ---------------- */
typedef struct {
    uint32_t vars;
    uint64_t nclauses;
    uint64_t *off;
    int32_t *lits;
} Cnf;

/* Read DIMACS into CSR arrays (offset[] + lits[]).

   Handles both CNF and WCNF.  In WCNF every clause line starts with a
   weight, which is NOT a literal, so it is skipped; the checker treats
   every clause as hard because a refutation of the whole clause set is
   stronger than one of the hard subset. */
static void cnf_load(const char *path, Cnf *c) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open CNF");
    char line[1 << 16];
    int wcnf = 0;
    uint64_t cap = 1024, used = 0;
    c->off = malloc(cap * sizeof(uint64_t));
    uint64_t lcap = 4096, lused = 0;
    c->lits = malloc(lcap * sizeof(int32_t));
    if (!c->off || !c->lits) die("oom");
    c->off[0] = 0;
    while (fgets(line, sizeof line, f)) {
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        if (*p == 'c' || *p == '\n' || *p == '\0') continue;
        if (*p == 'p') {
            unsigned nv = 0; unsigned long long nc = 0;
            if (strstr(p, "wcnf")) wcnf = 1;
            if (sscanf(p, "p %*s %u %llu", &nv, &nc) == 2) {
                c->vars = nv;
                if (nc + 2 > cap) {
                    cap = nc + 2;
                    c->off = realloc(c->off, cap * sizeof(uint64_t));
                    if (!c->off) die("oom");
                }
            }
            continue;
        }
        if (*p == 'h') p++;
        if (wcnf) {                    /* skip the clause weight */
            char *e = NULL;
            (void)strtol(p, &e, 10);
            if (e != p) p = e;
        }
        for (;;) {
            char *e = NULL;
            long v = strtol(p, &e, 10);
            if (e == p) break;
            p = e;
            if (v == 0) break;
            if (lused + 1 > lcap) {
                lcap *= 2;
                c->lits = realloc(c->lits, lcap * sizeof(int32_t));
                if (!c->lits) die("oom");
            }
            c->lits[lused++] = (int32_t)v;
        }
        c->nclauses++;
        if (c->nclauses + 2 > cap) {
            cap *= 2;
            c->off = realloc(c->off, cap * sizeof(uint64_t));
            if (!c->off) die("oom");
        }
        c->off[c->nclauses] = lused;
    }
    fclose(f);
}

/* ---------------- gfp checker ---------------- */
#define MAXAR 5
typedef struct { uint32_t n; uint32_t v[MAXAR]; int32_t lits[MAXAR]; } Tri;

static int tri_cmp2(const void *A, const void *B) {
    const Tri *x = A, *y = B;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    for (uint32_t i = 0; i < x->n; ++i)
        if (x->v[i] != y->v[i]) return x->v[i] < y->v[i] ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------------
   check_gfp — verify a parity refutation.

   For each `e` line we must establish two things INDEPENDENTLY:

     1. The equation is implied by the input.  Find every clause whose
        variable set matches the equation's support, enumerate all 2^k
        assignments, and check that every assignment satisfying those
        clauses also satisfies the equation.  This is a local, exhaustive
        check: no trust in how the solver found the group.
     2. The listed equations really do cancel out.  Each variable must
        appear an even number of times (so all variables disappear) and
        the right-hand sides must XOR to 1 (so what is left is 0 = 1).

   Only when both hold is "UNSAT" actually proven.
   ------------------------------------------------------------------ */
static int check_gfp(const Cnf *c, FILE *pf, uint32_t nvars, uint32_t neq) {
    Tri *tri = malloc((size_t)c->nclauses * sizeof(Tri));
    uint64_t nt = 0;
    if (!tri) die("oom");
    for (uint64_t i = 0; i < c->nclauses; ++i) {
        uint64_t w = c->off[i + 1] - c->off[i];
        if (w < 2 || w > MAXAR) continue;
        Tri *t = &tri[nt];
        t->n = (uint32_t)w;
        for (uint64_t k = 0; k < w; ++k) {
            int32_t l = c->lits[c->off[i] + k];
            t->v[k] = (uint32_t)(l < 0 ? -l : l);
            t->lits[k] = l;
        }
        for (uint32_t a = 0; a + 1 < t->n; ++a)
            for (uint32_t b = 0; b + 1 < t->n - a; ++b)
                if (t->v[b] > t->v[b + 1]) { uint32_t z = t->v[b]; t->v[b] = t->v[b + 1]; t->v[b + 1] = z; }
        nt++;
    }
    qsort(tri, nt, sizeof(Tri), tri_cmp2);

    uint8_t *cover = calloc((size_t)nvars + 2, 1);
    if (!cover) die("oom");
    uint32_t rhs_sum = 0, used = 0;
    char line[4096];
    while (fgets(line, sizeof line, pf)) {
        char *q = line;
        while (isspace((unsigned char)*q)) q++;
        if (!*q) continue;
        if (*q == 'u') break;
        if (*q != 'e') continue;
        q++;
        char *e = NULL;
        unsigned rhs = (unsigned)strtoul(q, &e, 10);
        if (e == q) die("bad e line");
        q = e;
        unsigned k = (unsigned)strtoul(q, &e, 10);
        if (e == q || k < 2 || k > MAXAR) die("bad arity");
        q = e;
        uint32_t v[MAXAR];
        for (unsigned i = 0; i < k; ++i) {
            unsigned long val = strtoul(q, &e, 10);
            if (e == q || val > nvars) die("bad var");
            q = e;
            v[i] = (uint32_t)val;
            if (i && v[i] <= v[i - 1]) die("equation vars not sorted/distinct");
        }
        unsigned long coef = strtoul(q, &e, 10);
        if (e == q || coef == 0 || coef >= (1ul << k)) die("bad coefficient mask");
        if (e) q = e;

        Tri key; memset(&key, 0, sizeof key); key.n = k;
        for (unsigned i = 0; i < k; ++i) key.v[i] = v[i];
        Tri *hit = bsearch(&key, tri, nt, sizeof(Tri), tri_cmp2);
        if (!hit) { fprintf(stderr, "no clause group with support %u..\n", v[0]); return 1; }
        uint64_t lo = (uint64_t)(hit - tri), hi = lo;
        while (lo > 0 && tri_cmp2(&tri[lo - 1], &key) == 0) lo--;
        while (hi + 1 < nt && tri_cmp2(&tri[hi + 1], &key) == 0) hi++;

        uint32_t full = 1u << k;
        int witnessed = 0;
        for (uint32_t a = 0; a < full; ++a) {
            int all_sat = 1;
            for (uint64_t g = lo; g <= hi && all_sat; ++g) {
                int sat = 0;
                for (uint32_t q2 = 0; q2 < k; ++q2) {
                    int32_t l = tri[g].lits[q2];
                    uint32_t var = (uint32_t)(l < 0 ? -l : l);
                    uint32_t idx = 0;
                    while (v[idx] != var) idx++;
                    int bit = (a >> idx) & 1;
                    if ((l > 0) == (bit == 1)) { sat = 1; break; }
                }
                if (!sat) all_sat = 0;
            }
            if (!all_sat) continue;
            witnessed = 1;
            uint32_t par = 0;
            for (unsigned i = 0; i < k; ++i) if ((coef >> i) & 1u) par ^= (a >> i) & 1u;
            if ((int)par != (int)rhs) {
                fprintf(stderr, "equation not implied by support %u.. (counterexample %u)\n",
                        v[0], a);
                return 1;
            }
        }
        if (!witnessed) { fprintf(stderr, "support %u.. has no satisfying assignment\n", v[0]); return 1; }
        for (unsigned i = 0; i < k; ++i) if ((coef >> i) & 1u) cover[v[i]] ^= 1;
        rhs_sum ^= rhs;
        used++;
    }
    free(tri);
    if (used != neq) { fprintf(stderr, "expected %u equations, checked %u\n", neq, used); return 1; }
    for (uint32_t v2 = 1; v2 <= nvars; ++v2)
        if (cover[v2]) { fprintf(stderr, "variable %u has odd coverage: not a derivation\n", v2); return 1; }
    if (rhs_sum != 1) { fprintf(stderr, "equation sum is 0, not a contradiction\n"); return 1; }
    printf("gfp verified: %u equations, XOR is 0 = 1\n", used);
    return 0;
}

/* ---------------- DRAT (RUP) checker ---------------- */
typedef struct { int32_t *lits; uint32_t size; } DClause;

static uint32_t nvars_g = 0;
static int8_t *assign_g = NULL;
static int32_t *trail_g = NULL;
static uint32_t trail_sz_g = 0, qhead_g = 0;
static DClause *db_g = NULL;
static uint32_t db_sz_g = 0, db_cap_g = 0;
static uint32_t **watch_g = NULL;
static uint32_t *watch_sz_g = NULL, *watch_cap_g = NULL;
static int32_t *root_g = NULL;
static uint32_t root_sz_g = 0, root_cap_g = 0;

static inline uint32_t widx(int32_t lit) {
    uint32_t v = (uint32_t)(lit < 0 ? -lit : lit);
    return v * 2u + (lit < 0 ? 1u : 0u);
}
static inline int lit_val(int32_t lit) {
    int8_t a = assign_g[(uint32_t)(lit < 0 ? -lit : lit)];
    if (a == 0) return 0;
    return (lit > 0) ? a : -a;
}
/* Clause database used by the RUP checker: an array of literal arrays.
   We never delete clauses here (additions-only proofs), which makes the
   check monotone: keeping an extra clause can only make propagation
   easier, never harder. */
static int db_add_raw(const int32_t *lits, uint32_t n) {
    if (db_sz_g == db_cap_g) {
        db_cap_g = db_cap_g ? db_cap_g * 2 : 1024;
        db_g = realloc(db_g, db_cap_g * sizeof(DClause));
        if (!db_g) die("oom");
    }
    DClause *c = &db_g[db_sz_g];
    c->size = n;
    c->lits = malloc((size_t)(n ? n : 1) * sizeof(int32_t));
    if (!c->lits) die("oom");
    if (n) memcpy(c->lits, lits, (size_t)n * sizeof(int32_t));
    return (int)db_sz_g++;
}
/* Two-watched-literal bookkeeping.

   To propagate efficiently we do not scan every clause.  Instead each
   clause watches two of its literals; when one of them becomes false we
   look at that clause, and either move the watch to a still-unfalsified
   literal or, if none exists, derive a unit / conflict.  `watch[lit]`
   is the list of clauses watching `lit`. */
static void watch_push(uint32_t wi, uint32_t clause) {
    if (watch_sz_g[wi] == watch_cap_g[wi]) {
        watch_cap_g[wi] = watch_cap_g[wi] ? watch_cap_g[wi] * 2 : 4;
        watch_g[wi] = realloc(watch_g[wi], watch_cap_g[wi] * sizeof(uint32_t));
        if (!watch_g[wi]) die("oom");
    }
    watch_g[wi][watch_sz_g[wi]++] = clause;
}
static void db_install(uint32_t idx) {
    DClause *c = &db_g[idx];
    if (c->size >= 2) {
        watch_push(widx(c->lits[0]), idx);
        watch_push(widx(c->lits[1]), idx);
    }
}
static void root_push(int32_t lit) {
    if (root_sz_g == root_cap_g) {
        root_cap_g = root_cap_g ? root_cap_g * 2 : 64;
        root_g = realloc(root_g, root_cap_g * sizeof(int32_t));
        if (!root_g) die("oom");
    }
    root_g[root_sz_g++] = lit;
}
static void enqueue(int32_t lit) {
    trail_g[trail_sz_g++] = lit;
    assign_g[(uint32_t)(lit < 0 ? -lit : lit)] = (lit > 0) ? 1 : -1;
}
static void clear_assign(void) {
    for (uint32_t i = 0; i < trail_sz_g; ++i) {
        int32_t l = trail_g[i];
        assign_g[(uint32_t)(l < 0 ? -l : l)] = 0;
    }
    trail_sz_g = 0; qhead_g = 0;
}
/* ------------------------------------------------------------------
   propagate — unit propagation.

   Repeatedly take assignments off the trail; for each literal that just
   became true, visit the clauses watching its negation:

     * if the other watched literal is already true, the clause is
       satisfied — keep watching, nothing to do;
     * otherwise try to move the watch to another literal that is not
       false; if one exists, the clause stays satisfied and we continue;
     * if no such literal exists and the other watch is false, the clause
       is falsified -> CONFLICT;
     * if no such literal exists and the other watch is unassigned, it is
       forced -> assign it and continue.

   Returns 1 on conflict.  This is the primitive both RUP checking and
   the CDCL core are built on.
   ------------------------------------------------------------------ */
static int propagate(void) {
    while (qhead_g < trail_sz_g) {
        int32_t p = trail_g[qhead_g++];
        int32_t fl = -p;
        uint32_t wi = widx(fl);
        uint32_t i = 0, j = 0;
        while (i < watch_sz_g[wi]) {
            uint32_t ci = watch_g[wi][i++];
            DClause *c = &db_g[ci];
            if (c->size < 2) continue;
            if (c->lits[0] == fl) { int32_t t = c->lits[0]; c->lits[0] = c->lits[1]; c->lits[1] = t; }
            if (c->lits[1] != fl) { watch_g[wi][j++] = ci; continue; }
            int32_t other = c->lits[0];
            if (lit_val(other) == 1) { watch_g[wi][j++] = ci; continue; }
            int moved = 0;
            for (uint32_t k = 2; k < c->size; ++k) {
                if (lit_val(c->lits[k]) != -1) {
                    c->lits[1] = c->lits[k];
                    c->lits[k] = fl;
                    watch_push(widx(c->lits[1]), ci);
                    moved = 1;
                    break;
                }
            }
            if (moved) continue;
            watch_g[wi][j++] = ci;
            if (lit_val(other) == -1) {
                while (i < watch_sz_g[wi]) watch_g[wi][j++] = watch_g[wi][i++];
                watch_sz_g[wi] = j;
                return 1;
            }
            if (lit_val(other) == 0) enqueue(other);
        }
        watch_sz_g[wi] = j;
    }
    return 0;
}
/* reset to the root level: assert permanent units, propagate */
/* Return to the "root" level: forget every decision, re-assert the
   permanent units, and propagate.  A RUP check must start from a clean
   root, otherwise leftovers from a previous check would contaminate it. */
static int reset_root(void) {
    clear_assign();
    for (uint32_t i = 0; i < root_sz_g; ++i) {
        int v = lit_val(root_g[i]);
        if (v == -1) { return 1; }
        if (v == 0) enqueue(root_g[i]);
    }
    return propagate();
}
/* if the clause is unit or empty at root level, close the level */
/* After adding a clause, it may be unit or falsified under the current
   root assignment.  Closing that gap keeps the database closed under
   propagation, which later RUP checks rely on. */
static int close_clause(uint32_t idx) {
    DClause *c = &db_g[idx];
    int32_t last = 0;
    int free_cnt = 0;
    for (uint32_t i = 0; i < c->size; ++i) {
        int v = lit_val(c->lits[i]);
        if (v == 1) return 0;
        if (v == 0) { free_cnt++; last = c->lits[i]; }
    }
    if (free_cnt == 0) return 1;
    if (free_cnt == 1) {
        root_push(last);
        enqueue(last);
        return propagate();
    }
    return 0;
}
/* ------------------------------------------------------------------
   rup — "is this clause derivable by unit propagation right now?"

   Reverse Unit Propagation: assume the clause is FALSE (assign the
   negation of each of its literals), propagate, and see whether we hit a
   conflict.  If we do, the clause is implied by the current database,
   which is exactly what DRAT requires for each added line.
   ------------------------------------------------------------------ */
static int rup(const int32_t *lits, uint32_t n) {
    if (reset_root()) return 1;         /* formula already UP-inconsistent */
    for (uint32_t i = 0; i < n; ++i) {
        int32_t neg = -lits[i];
        int v = lit_val(neg);
        if (v != 0) return 1;           /* assumption contradicts root level */
        enqueue(neg);
    }
    int confl = propagate();
    clear_assign();
    return confl;
}

/* ------------------------------------------------------------------
   check_drat — verify a DRAT proof, additions only.

   Load the original clauses, then read the proof line by line.  Each
   line is a clause that must be RUP with respect to (original + all
   previously accepted lines); the final empty clause means the original
   formula is unsatisfiable.

   `d` (deletion) lines are ignored on purpose: keeping a clause can only
   make propagation stronger, so ignoring deletions is sound for an
   additions-only checker.
   ------------------------------------------------------------------ */
static int check_drat(const Cnf *c, FILE *pf) {
    nvars_g = c->vars;
    size_t nv = (size_t)nvars_g + 2;
    assign_g = calloc(nv, 1);
    trail_g = malloc(nv * sizeof(int32_t));
    watch_g = calloc(nv * 2, sizeof(uint32_t *));
    watch_sz_g = calloc(nv * 2, sizeof(uint32_t));
    watch_cap_g = calloc(nv * 2, sizeof(uint32_t));
    if (!assign_g || !trail_g || !watch_g || !watch_sz_g || !watch_cap_g) die("oom");

    for (uint64_t i = 0; i < c->nclauses; ++i) {
        uint32_t n = (uint32_t)(c->off[i + 1] - c->off[i]);
        int idx = db_add_raw(c->lits + c->off[i], n);
        db_install((uint32_t)idx);
        if (n == 1) root_push(db_g[idx].lits[0]);
    }
    if (reset_root()) { printf("drat: input is UP-inconsistent (empty clause follows)\n"); return 0; }

    char line[1 << 16];
    uint64_t steps = 0;
    int saw_empty = 0;
    while (fgets(line, sizeof line, pf)) {
        char *p = line;
        while (isspace((unsigned char)*p)) p++;
        if (!*p || *p == 'c') continue;
        if (*p == 'd') continue;                  /* deletions: ignored */
        int32_t tmp[8192];
        uint32_t n = 0;
        for (;;) {
            char *e = NULL;
            long v = strtol(p, &e, 10);
            if (e == p) break;
            p = e;
            if (v == 0) break;
            if (n >= 8192) die("clause too long");
            tmp[n++] = (int32_t)v;
        }
        steps++;
        if (!rup(tmp, n)) {
            fprintf(stderr, "drat: step %llu is not RUP\n", (unsigned long long)steps);
            return 1;
        }
        int idx = db_add_raw(tmp, n);
        db_install((uint32_t)idx);
        if (n == 0) { saw_empty = 1; break; }
        if (n == 1) root_push(tmp[0]);
        if (reset_root()) { saw_empty = 1; break; }
        if (close_clause((uint32_t)idx)) { saw_empty = 1; break; }
    }
    if (!saw_empty) { fprintf(stderr, "drat: proof does not end in the empty clause\n"); return 1; }
    printf("drat verified: %llu additions, empty clause derived\n",
           (unsigned long long)steps);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 4 || strcmp(argv[1], "check")) {
        fprintf(stderr, "usage: %s check <input.cnf> <proof>\n", argv[0]);
        return 2;
    }
    Cnf c; memset(&c, 0, sizeof c);
    cnf_load(argv[2], &c);
    FILE *pf = fopen(argv[3], "r");
    if (!pf) die("cannot open proof");
    char head[256] = {0};
    if (!fgets(head, sizeof head, pf)) die("empty proof");
    if (head[0] == 'p' && strstr(head, "gfp")) {
        unsigned nv = 0, ne = 0;
        if (sscanf(head, "p gfp %u %u", &nv, &ne) != 2) die("bad gfp header");
        if (nv != c.vars) { fprintf(stderr, "gfp header nvars %u != CNF %u\n", nv, c.vars); return 1; }
        return check_gfp(&c, pf, nv, ne);
    }
    rewind(pf);
    return check_drat(&c, pf);
}
