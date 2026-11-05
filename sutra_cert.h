/*=====================================================================
  sutra_cert.h — turning "I believe it is UNSAT" into "here is the proof"
  Author: Sethu Iyer (github.com/sethuiyer)

  WHAT THIS FILE IS
  -----------------
  Two independent ways to produce a certificate that a CNF is
  unsatisfiable, plus a way to build a witness from parity structure.

  BACKGROUND FOR NEWCOMERS
  ------------------------
  A SAT solver can answer SAT by showing an assignment (anyone can check
  it in one pass).  Answering UNSAT is harder: you must convince the
  reader that NO assignment exists.  That requires a proof, not a claim.

  SUTRA ships two proof formats:

    gfp  (this file)  A GF(2) parity refutation.  If a group of clauses
         encodes "x1 XOR x2 XOR x3 = b", then the clauses behave like a
         linear equation over the two-element field.  XOR-ing several
         equations can produce "0 = 1", which is a contradiction.  The
         certificate lists which equations were XOR-ed together; the
         checker re-derives every one of them from the actual clauses.
         Tiny (one line per equation) and checkable in seconds.

    drat (cdcl_internal.h + sutracert.c)  The standard format emitted by
         CDCL solvers.  Every added clause must be derivable from the
         previous ones by unit propagation (RUP) or by resolution (RAT).

  WHY PARITY IS DETECTED ON 4-CLAUSE GROUPS
  -----------------------------------------
  A single binary clause (a OR b) looks like an implication, not an XOR
  equation, so it cannot be used soundly.  But the full truth-table
  encoding of an XOR over k variables is 2^(k-1) clauses over the same k
  variables; if those clauses are present, they are *exactly* the parity
  constraint and can be treated as one linear equation.  Detection is
  verified exhaustively over 2^k assignments, so it cannot be fooled by
  an accidental look-alike.

  The certificate checker (sutracert.c) shares no code with this file:
  it re-detects the group and re-runs the implication check itself.
=====================================================================*/
#ifndef SUTRA_CERT_H
#define SUTRA_CERT_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PAR_MAX_ARITY 5      /* XOR over at most 5 vars (16 clauses) */
#define PAR_MAX_CLAUSES 16   /* 2^(k-1) */

/* ------------------------------------------------------------------ */
/* Parity detection                                                    */
/* ------------------------------------------------------------------ */
typedef struct {
    uint32_t n;              /* arity, 2..PAR_MAX_ARITY */
    uint32_t v[PAR_MAX_ARITY];
    uint32_t coef;           /* bit i selects v[i] in the XOR */
    uint8_t rhs;
} ParEq;

typedef struct {
    uint32_t n;                  /* clause width */
    uint32_t v[PAR_MAX_ARITY];   /* sorted vars, 1-based */
    uint64_t clause;
    int32_t lits[PAR_MAX_ARITY];
} TriClause;

static int tri_cmp(const void *A, const void *B) {
    const TriClause *x = (const TriClause *)A;
    const TriClause *y = (const TriClause *)B;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    for (uint32_t i = 0; i < x->n; ++i)
        if (x->v[i] != y->v[i]) return x->v[i] < y->v[i] ? -1 : 1;
    return 0;
}

/* Linear-algebra helpers over GF(2)^k, k <= 5. */
/* Tiny linear algebra over GF(2): is the bit-vector `f` in the span of
   `basis`?  A vector is in the span when reducing it by the basis leaves
   zero.  Here vectors are just integers whose bits are coefficients. */
static int form_in_span(const uint32_t *basis, int nb, uint32_t f) {
    for (int i = 0; i < nb; ++i) {
        uint32_t lead = basis[i] & (~basis[i] + 1u);
        if (f & lead) f ^= basis[i];
    }
    return f == 0;
}

/* Extract every parity equation implied by a group of clauses sharing a
   support.  R is the set of assignments satisfying all of them; a linear
   form f is implied exactly when f.a is constant over R.  This subsumes
   exact 4-clause XOR encodings, tolerates redundant clauses, and yields
   several independent equations when the group is stronger than parity. */
/* ------------------------------------------------------------------
   group_implied_forms — which parity equations does this clause group
   actually imply?

   `R` is a bitmask of the 2^k assignments that satisfy every clause in
   the group.  A linear form f (also a bitmask) is implied exactly when
   f·a is CONSTANT over all a in R.  We test that by brute force over at
   most 32 assignments, which is why k is capped at 5.

   Why implication and not equality?  Soundness only needs "the clauses
   imply the equation": if we can derive 0 = 1 from implied equations,
   the original formula is unsatisfiable.  Implication also tolerates
   redundant clauses that would defeat a strict pattern matcher.
   ------------------------------------------------------------------ */
static int group_implied_forms(uint32_t k, uint32_t R, uint32_t *basis, int *nb) {
    uint32_t full = 1u << k;
    uint32_t first = 0;
    for (uint32_t a = 0; a < full; ++a)
        if ((R >> a) & 1u) { first = a; break; }
    *nb = 0;
    for (uint32_t f = 1; f < full; ++f) {
        int val = -1, constant = 1;
        for (uint32_t a = 0; a < full && constant; ++a) {
            if (!((R >> a) & 1u)) continue;
            int v = __builtin_parity(f & a);
            if (val < 0) val = v;
            else if (v != val) constant = 0;
        }
        if (!constant) continue;
        if (form_in_span(basis, *nb, f)) continue;
        basis[(*nb)++] = f;
    }
    (void)first;
    return *nb;
}

/* ------------------------------------------------------------------
   sutra_detect_parity — find the hidden linear structure.

   We group clauses by the set of variables they mention ("support").
   A group is interesting when its satisfying assignments are few enough
   to be contained in an affine subspace: a form can only be constant on
   a set of at most 2^(k-1) assignments.

   For every such group we extract a basis of implied parity equations.
   A canonical 4-clause XOR encoding yields exactly one equation; a group
   that forces several variables yields several.

   Only HARD clauses participate.  A soft clause may be violated, so it
   can never justify "this is impossible" — using it would be unsound.
   ------------------------------------------------------------------ */
static int sutra_detect_parity(const Formula *f, ParEq **out, uint32_t *out_n) {
    TriClause *tc = NULL;
    uint64_t ntc = 0, cap = 0;

    for (uint64_t c = 0; c < f->clauses; ++c) {
        if (!f->hard[c]) continue;   /* soft clauses are violable */
        uint64_t w = f->offset[c + 1] - f->offset[c];
        if (w < 2 || w > PAR_MAX_ARITY) continue;
        if (ntc == cap) {
            cap = cap ? cap * 2 : 1024;
            TriClause *nt = realloc(tc, cap * sizeof(*nt));
            if (!nt) { free(tc); return 0; }
            tc = nt;
        }
        TriClause *t = &tc[ntc];
        t->n = (uint32_t)w;
        t->clause = c;
        for (uint64_t k = 0; k < w; ++k) {
            int32_t l = f->lits[f->offset[c] + k];
            t->v[k] = (uint32_t)(l < 0 ? -l : l);
            t->lits[k] = l;
        }
        for (uint32_t i = 0; i + 1 < t->n; ++i)
            for (uint32_t j = 0; j + 1 < t->n - i; ++j)
                if (t->v[j] > t->v[j + 1]) {
                    uint32_t tv = t->v[j]; t->v[j] = t->v[j + 1]; t->v[j + 1] = tv;
                }
        ntc++;
    }
    if (!ntc) { free(tc); return 0; }
    qsort(tc, ntc, sizeof(*tc), tri_cmp);

    ParEq *eqs = NULL;
    uint32_t neq = 0, eqcap = 0;
    uint64_t i = 0;
    while (i < ntc) {
        uint64_t j = i;
        while (j < ntc && tri_cmp(&tc[j], &tc[i]) == 0) j++;
        uint32_t k = tc[i].n;
        uint32_t full = 1u << k;
        uint64_t n = j - i;
        if (n >= 1 && n <= 64) {
            uint32_t R = (full == 32) ? 0xFFFFFFFFu : ((1u << full) - 1u);
            for (uint64_t g = i; g < j; ++g) {
                for (uint32_t a = 0; a < full; ++a) {
                    int sat = 0;
                    for (uint32_t q = 0; q < k; ++q) {
                        int32_t l = tc[g].lits[q];
                        uint32_t var = (uint32_t)(l < 0 ? -l : l);
                        uint32_t idx = 0;
                        while (tc[i].v[idx] != var) idx++;
                        int bit = (a >> idx) & 1;
                        if ((l > 0) == (bit == 1)) { sat = 1; break; }
                    }
                    if (!sat) R &= ~(1u << a);
                }
            }
            /* a form is constant on R only if |R| <= half the cube */
            uint32_t rc = (uint32_t)__builtin_popcount(R);
            if (R && rc <= full / 2) {
                uint32_t basis[PAR_MAX_ARITY];
                int nb = 0;
                group_implied_forms(k, R, basis, &nb);
                uint32_t first = 0;
                for (uint32_t a = 0; a < full; ++a)
                    if ((R >> a) & 1u) { first = a; break; }
                for (int b = 0; b < nb; ++b) {
                    if (neq == eqcap) {
                        eqcap = eqcap ? eqcap * 2 : 64;
                        ParEq *ne = realloc(eqs, eqcap * sizeof(*ne));
                        if (!ne) { free(eqs); free(tc); return 0; }
                        eqs = ne;
                    }
                    eqs[neq].n = k;
                    eqs[neq].coef = basis[b];
                    for (uint32_t q = 0; q < k; ++q) eqs[neq].v[q] = tc[i].v[q] - 1;
                    eqs[neq].rhs = (uint8_t)__builtin_parity(basis[b] & first);
                    neq++;
                }
            }
        }
        i = j;
    }
    free(tc);
    *out = eqs;
    *out_n = neq;
    return neq > 0;
}

/* ------------------------------------------------------------------ */
/* GF(2) elimination with dependency tracking                          */
/* ------------------------------------------------------------------ */
typedef struct {
    uint64_t *bits;
    uint64_t *dep;
    uint8_t rhs;
} GRow;

/* Returns 1 and fills subset[] when the system is inconsistent. */
/* ------------------------------------------------------------------
   sutra_gf2_refute — Gaussian elimination over GF(2).

   Each equation is a bitmask of variables plus a right-hand side bit.
   We reduce every row against the rows already stored (one per pivot
   variable).  If a row reduces to "0 = 1", the system is inconsistent:
   the XOR of the equations recorded in `dep` is the contradiction, and
   that subset is what the certificate will contain.

   `dep` is itself a bitmask (equation indices), maintained with the same
   XOR operations as the rows, so every elimination step carries the
   provenance of the result.
   ------------------------------------------------------------------ */
static int sutra_gf2_refute(uint32_t nvars, const ParEq *eq, uint32_t neq,
                            uint32_t *subset, uint32_t *out_count) {
    uint32_t nw = (nvars + 63) / 64;
    uint32_t ndw = (neq + 63) / 64;
    if (nw == 0 || ndw == 0) return 0;

    GRow *tab = calloc(neq ? neq : 1, sizeof(GRow));
    int32_t *prow = malloc((size_t)nvars * sizeof(int32_t));
    if (!tab || !prow) { free(tab); free(prow); return 0; }
    for (uint32_t v = 0; v < nvars; ++v) prow[v] = -1;

    uint32_t nrows = 0;
    int refuted = 0;
    for (uint32_t i = 0; i < neq && !refuted; ++i) {
        uint64_t *bits = calloc(nw, sizeof(uint64_t));
        uint64_t *dep = calloc(ndw, sizeof(uint64_t));
        if (!bits || !dep) { free(bits); free(dep); break; }
        for (uint32_t k = 0; k < eq[i].n; ++k) {
            if (!((eq[i].coef >> k) & 1u)) continue;
            uint32_t v = eq[i].v[k];
            bits[v >> 6] ^= 1ULL << (v & 63);
        }
        uint8_t rhs = eq[i].rhs;
        dep[i >> 6] ^= 1ULL << (i & 63);

        for (uint32_t v = 0; v < nvars; ++v) {
            if (!((bits[v >> 6] >> (v & 63)) & 1)) continue;
            if (prow[v] < 0) {
                tab[nrows].bits = bits;
                tab[nrows].dep = dep;
                tab[nrows].rhs = rhs;
                prow[v] = (int32_t)nrows;
                nrows++;
                bits = NULL; dep = NULL;
                break;
            }
            GRow *p = &tab[prow[v]];
            for (uint32_t w = 0; w < nw; ++w) bits[w] ^= p->bits[w];
            for (uint32_t w = 0; w < ndw; ++w) dep[w] ^= p->dep[w];
            rhs ^= p->rhs;
        }
        if (bits) {
            if (rhs) {
                uint32_t cnt = 0;
                for (uint32_t j = 0; j < neq; ++j)
                    if ((dep[j >> 6] >> (j & 63)) & 1) subset[cnt++] = j;
                *out_count = cnt;
                refuted = 1;
            }
            free(bits);
            free(dep);
        }
    }
    for (uint32_t r = 0; r < nrows; ++r) { free(tab[r].bits); free(tab[r].dep); }
    free(tab);
    free(prow);
    return refuted;
}

/* ------------------------------------------------------------------ */
/* Model construction from a consistent parity system                  */
/* ------------------------------------------------------------------ */
/* If the detected XOR system is consistent, a solution of it satisfies
   every clause it was derived from.  Enumerate the free variables (the
   nullspace is usually tiny) and return the first model that satisfies
   all hard clauses.  Returns 1 on success.

   Variables outside the parity system are fixed to 0; if that breaks a
   hard clause the caller falls back to the heuristic with a seed. */
/* ------------------------------------------------------------------
   sutra_parity_model — the other half: build a model, not a refutation.

   A consistent XOR system has 2^(n - rank) solutions.  The nullspace is
   usually tiny, so we enumerate the free variables, back-substitute the
   pivots, and test the resulting full assignment against the real
   clauses.  If one satisfies everything, we have a verified witness with
   no search at all.

   If none does, the free-vars-zero solution is still a good seed for the
   local search, so it is copied into `seed`.
   ------------------------------------------------------------------ */
static int sutra_parity_model(const Formula *f, const ParEq *eq, uint32_t neq,
                              uint8_t *model, uint32_t max_free, uint8_t *seed) {
    uint32_t nvars = f->vars;
    uint32_t nw = (nvars + 63) / 64;
    if (!neq || !nw) return 0;

    uint64_t *rows = calloc((size_t)neq * nw, sizeof(uint64_t));
    uint8_t *rr = calloc(neq, 1);
    int32_t *prow = malloc((size_t)nvars * sizeof(int32_t));
    uint32_t *pivvar = malloc((size_t)neq * sizeof(uint32_t));
    if (!rows || !rr || !prow || !pivvar) {
        free(rows); free(rr); free(prow); free(pivvar);
        return 0;
    }
    for (uint32_t v = 0; v < nvars; ++v) prow[v] = -1;

    uint32_t nrows = 0;
    int consistent = 1;
    for (uint32_t i = 0; i < neq && consistent; ++i) {
        uint64_t *row = calloc(nw, sizeof(uint64_t));
        if (!row) { consistent = 0; break; }
        for (uint32_t k = 0; k < eq[i].n; ++k) {
            if (!((eq[i].coef >> k) & 1u)) continue;
            uint32_t v = eq[i].v[k];
            row[v >> 6] ^= 1ULL << (v & 63);
        }
        uint8_t rhs = eq[i].rhs;
        for (uint32_t v = 0; v < nvars; ++v) {
            if (!((row[v >> 6] >> (v & 63)) & 1)) continue;
            if (prow[v] < 0) {
                memcpy(rows + (size_t)nrows * nw, row, (size_t)nw * sizeof(uint64_t));
                rr[nrows] = rhs;
                pivvar[nrows] = v;
                prow[v] = (int32_t)nrows;
                nrows++;
                row = NULL;
                break;
            }
            const uint64_t *pr = rows + (size_t)prow[v] * nw;
            for (uint32_t w = 0; w < nw; ++w) row[w] ^= pr[w];
            rhs ^= rr[prow[v]];
        }
        if (row) {
            if (rhs) consistent = 0;     /* contradiction: not a model path */
            free(row);
        }
    }

    int found = 0;
    if (consistent) {
        uint32_t *freev = malloc((size_t)nvars * sizeof(uint32_t));
        uint32_t nfree = 0;
        if (freev) {
            for (uint32_t v = 0; v < nvars; ++v)
                if (prow[v] < 0) freev[nfree++] = v;
            if (nfree <= max_free) {
                uint64_t total = 1ull << nfree;
                for (uint64_t m = 0; m < total && !found; ++m) {
                    memset(model, 0, (size_t)nvars + 1);
                    for (uint32_t q = 0; q < nfree; ++q)
                        model[freev[q] + 1] = (uint8_t)((m >> q) & 1);
                    /* back-substitute pivots, highest first */
                    for (int32_t r = (int32_t)nrows - 1; r >= 0; --r) {
                        const uint64_t *pr = rows + (size_t)r * nw;
                        uint32_t pv = pivvar[r];
                        uint8_t val = rr[r];
                        for (uint32_t w = 0; w < nw; ++w) {
                            uint64_t bits = pr[w];
                            while (bits) {
                                uint32_t v = w * 64 + (uint32_t)__builtin_ctzll(bits);
                                bits &= bits - 1;
                                if (v != pv) val ^= model[v + 1];
                            }
                        }
                        model[pv + 1] = val;
                    }
                    int ok = 1;
                    for (uint64_t c = 0; c < f->clauses && ok; ++c) {
                        if (!f->hard[c]) continue;
                        int sat = 0;
                        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                            int32_t l = f->lits[j];
                            uint32_t v = (uint32_t)(l < 0 ? -l : l);
                            if ((l > 0) == (model[v] != 0)) { sat = 1; break; }
                        }
                        if (!sat) ok = 0;
                    }
                    if (ok) found = 1;
                }
            }
            if (!found && seed) {
                /* seed the heuristic with the free-vars-zero solution */
                memset(model, 0, (size_t)nvars + 1);
                for (int32_t r = (int32_t)nrows - 1; r >= 0; --r) {
                    const uint64_t *pr = rows + (size_t)r * nw;
                    uint32_t pv = pivvar[r];
                    uint8_t val = rr[r];
                    for (uint32_t w = 0; w < nw; ++w) {
                        uint64_t bits = pr[w];
                        while (bits) {
                            uint32_t v = w * 64 + (uint32_t)__builtin_ctzll(bits);
                            bits &= bits - 1;
                            if (v != pv) val ^= model[v + 1];
                        }
                    }
                    model[pv + 1] = val;
                }
                memcpy(seed, model, (size_t)nvars + 1);
            }
            free(freev);
        }
    }
    free(rows); free(rr); free(prow); free(pivvar);
    return found;
}

/* ------------------------------------------------------------------ */
/* gfp certificate emission                                            */
/* ------------------------------------------------------------------ */
/* Emit the gfp certificate.  Format:

       p gfp <nvars> <neq>
       e <rhs> <k> <v1..vk> <coefmask>
       ...
       u

   One line per equation; `u` asserts that the XOR of all listed
   equations is 0 = 1.  Variables are written 1-based, like DIMACS. */
static int sutra_write_gfp(FILE *fp, const ParEq *eqs, const uint32_t *subset,
                           uint32_t cnt, uint32_t nvars) {
    if (!fp) return 0;
    if (fprintf(fp, "p gfp %u %u\n", nvars, cnt) < 0) return 0;
    for (uint32_t i = 0; i < cnt; ++i) {
        const ParEq *e = &eqs[subset[i]];
        if (fprintf(fp, "e %u %u", (unsigned)e->rhs, e->n) < 0) return 0;
        for (uint32_t k = 0; k < e->n; ++k)
            if (fprintf(fp, " %u", e->v[k] + 1) < 0) return 0;   /* certificate is 1-based */
        if (fprintf(fp, " %u\n", e->coef) < 0) return 0;
    }
    if (fprintf(fp, "u\n") < 0) return 0;
    if (fflush(fp) != 0) return 0;
    return 1;
}

/* ------------------------------------------------------------------ */
/* Exact CDCL fallback with DRAT emission                              */
/* ------------------------------------------------------------------ */
/* Returns 0 = UNSAT (proof emitted), 1 = SAT, -1 = limit/error. */
/* ------------------------------------------------------------------
   sutra_run_exact — run the embedded CDCL, with proof logging.

   The CDCL gets only the hard clauses: soft clauses are allowed to be
   violated, so they cannot make the formula unsatisfiable.  Its phase
   array is seeded from the heuristic's best assignment, which is just a
   hint about which polarity to try first.

   While it runs, every learned clause and the final empty clause are
   written to `drat`.  If the solver returns 0, that file is a complete
   refutation; the caller still has to have it verified.
   ------------------------------------------------------------------ */
static int sutra_run_exact(const Formula *f, uint32_t conflicts, FILE *drat,
                           const uint8_t *seed_asn) {
    cdcl_t *s = cdcl_new(f->vars, (size_t)2 << 30, conflicts);
    if (!s) return -1;
    s->drat_fp = drat;
    if (seed_asn)
        for (uint32_t v = 1; v <= f->vars; ++v)
            s->phase[v] = seed_asn[v] ? 1 : -1;

    int added = 1;
    for (uint64_t c = 0; c < f->clauses && added; ++c) {
        if (!f->hard[c]) continue;
        uint64_t w = f->offset[c + 1] - f->offset[c];
        if (w == 0) { added = 0; break; }
        int32_t *tmp = malloc((size_t)w * sizeof(int32_t));
        if (!tmp) { added = 0; break; }
        memcpy(tmp, f->lits + f->offset[c], (size_t)w * sizeof(int32_t));
        added = cdcl_add_clause(s, tmp, (uint32_t)w);
        free(tmp);
    }

    int r = cdcl_solve(s);   /* 0 UNSAT, 1 SAT, <0 error/limit */
    cdcl_free(s);
    if (r == 0) return 0;
    if (r == 1) return 1;
    return -1;
}

#endif /* SUTRA_CERT_H */
