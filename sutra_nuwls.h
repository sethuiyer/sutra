/*=====================================================================
  sutra_nuwls.h — the local-search engine
  Author: Sethu Iyer (github.com/sethuiyer)

  WHAT THIS FILE IS
  -----------------
  A from-scratch implementation of the NuWLS algorithm for (weighted)
  MaxSAT local search, written against SUTRA's Formula arrays.  NuWLS is
  the local-search component that makes Aperture strong; this file ports
  its update rules so SUTRA can use them too.

  THE FOUR IDEAS, IN PLAIN WORDS
  ------------------------------
  1. SCORE.  For every variable v, score[v] answers one question:
     "if I flip v right now, how much satisfied weight do I gain?"
     Positive is good, negative is bad.  Scores are updated
     incrementally after each flip, so a step costs O(clause length)
     rather than O(formula).

  2. GOOD-VARIABLE STACK.  Keep every variable with score > 0 in a list.
     While that list is non-empty, every move improves the objective:
     the search descends.  Picking the best member is approximated by
     BMS ("best from multiple selections"): sample a few candidates and
     take the best one, which is O(1) instead of scanning all variables.

  3. WEIGHTS.  When the descent gets stuck (no positive-score variable),
     the clauses that are still violated get heavier, so the next descent
     is forced to pay attention to them.  Weights grow ADDITIVELY and are
     capped relative to their original value, so a heavy clause always
     stays heavier than a light one.  (A multiplicative scheme destroys
     that ordering — that was the bug in SUTRA's old repair.)

  4. ESCAPE.  After re-weighting, flip a variable inside a random
     violated clause: usually the best one in that clause, sometimes a
     random one.  That is the random walk that carries the search out of
     a local minimum.

  THE ONE SUBTLE LINE
  -------------------
  After flipping v, NuWLS sets score[v] = -score_before(v).  If flipping
  v gained g, then flipping it back must lose g.  Every other score is
  updated by the clause transitions; this one line keeps the whole array
  consistent.  Remove it and the "improving" moves stop being improving.

  Algorithm: NuWLS (as used by Aperture, github.com/YamSln/Aperture).
  Code: written from scratch by Sethu Iyer for SUTRA.
=====================================================================*/
#ifndef SUTRA_NUWLS_H
#define SUTRA_NUWLS_H

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define NL_HARD_W 1.0e9          /* hard clauses dominate lexicographically */

typedef struct {
    uint32_t nv;
    uint64_t nc;
    const Formula *f;
    uint64_t *occ_off;
    uint64_t *occ;
    int32_t *sat_count;
    int32_t *sat_var;
    double *score;
    double *w;
    double *tw;                  /* tuned original weight: the cap base */
    int32_t *good;
    int32_t *good_pos;
    int32_t good_n;
    uint64_t *stamp;
    int32_t *hunsat, *hpos, *sunsat, *spos;
    int32_t nh, ns;
    int32_t *large;              /* clauses with w > s_inc (for smoothing) */
    int32_t *large_pos;
    int32_t nlarge;
} NL;

/* The good-variable stack.

   `good` is a dense array of variables with score > 0, and `good_pos`
   remembers each one's index so removal is O(1) (swap with the last
   element).  This is the list the search draws its next move from: while
   it is non-empty, every move improves the objective. */
static inline void nl_good_add(NL *s, int32_t v) {
    if (s->score[v] > 0 && s->good_pos[v] < 0) {
        s->good_pos[v] = s->good_n;
        s->good[s->good_n++] = v;
    }
}
static inline void nl_good_del(NL *s, int32_t v) {
    if (s->good_pos[v] >= 0) {
        int32_t last = s->good[--s->good_n];
        s->good[s->good_pos[v]] = last;
        s->good_pos[last] = s->good_pos[v];
        s->good_pos[v] = -1;
    }
}

static void nl_free(NL *s) {
    free(s->occ_off); free(s->occ); free(s->sat_count); free(s->sat_var);
    free(s->score); free(s->w); free(s->tw); free(s->good); free(s->good_pos);
    free(s->stamp); free(s->hunsat); free(s->hpos); free(s->sunsat); free(s->spos);
    free(s->large); free(s->large_pos);
    memset(s, 0, sizeof *s);
}

/* Recompute score[] from scratch.  Used by the self-check and after init. */
/* Recompute score[] from scratch, straight from the definition:
       +w  for every violated clause containing v
       -w  for every satisfied clause where v is the only true literal
   Used once at start-up, and by the self-check, to make sure the
   incremental updates in nl_flip() have not drifted. */
static void nl_rebuild_scores(NL *s) {
    const Formula *f = s->f;
    for (uint32_t v = 1; v <= s->nv; ++v) s->score[v] = 0.0;
    for (uint64_t c = 0; c < s->nc; ++c) {
        if (s->sat_count[c] == 0) {
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                uint32_t v = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
                s->score[v] += s->w[c];
            }
        } else if (s->sat_count[c] == 1) {
            s->score[s->sat_var[c]] -= s->w[c];
        }
    }
    s->good_n = 0;
    for (uint32_t v = 1; v <= s->nv; ++v) {
        s->good_pos[v] = -1;
        if (s->score[v] > 0) nl_good_add(s, (int32_t)v);
    }
}

/* ------------------------------------------------------------------
   nl_init — build the search state for one run.

   Steps:
     1. build an occurrence index: for each variable, which clauses
        contain it (needed by every flip).
     2. choose clause weights.  Soft weights are rescaled so that their
        average is 1000; the cap is then relative to that scaled value,
        which keeps heavy clauses heavier than light ones.  Hard clauses
        get a huge constant so any hard violation dominates any soft gain.
     3. count true literals per clause, remember each clause's unique
        true variable (if it has exactly one), and fill the violated
        clause stacks.
     4. compute the initial scores and the good-variable stack.
   ------------------------------------------------------------------ */
static int nl_init(NL *s, const Formula *f, const uint8_t *asn) {
    memset(s, 0, sizeof *s);
    s->f = f;
    s->nv = f->vars;
    s->nc = f->clauses;
    uint32_t nv = s->nv;
    uint64_t nc = s->nc;

    s->occ_off = calloc((size_t)nv + 2, sizeof(uint64_t));
    s->sat_count = calloc(nc ? nc : 1, sizeof(int32_t));
    s->sat_var = calloc(nc ? nc : 1, sizeof(int32_t));
    s->score = calloc((size_t)nv + 1, sizeof(double));
    s->w = malloc((nc ? nc : 1) * sizeof(double));
    s->tw = malloc((nc ? nc : 1) * sizeof(double));
    s->good = malloc(((size_t)nv + 1) * sizeof(int32_t));
    s->good_pos = malloc(((size_t)nv + 1) * sizeof(int32_t));
    s->stamp = calloc((size_t)nv + 1, sizeof(uint64_t));
    s->hunsat = malloc((nc ? nc : 1) * sizeof(int32_t));
    s->hpos = malloc((nc ? nc : 1) * sizeof(int32_t));
    s->sunsat = malloc((nc ? nc : 1) * sizeof(int32_t));
    s->spos = malloc((nc ? nc : 1) * sizeof(int32_t));
    s->large = malloc((nc ? nc : 1) * sizeof(int32_t));
    s->large_pos = malloc((nc ? nc : 1) * sizeof(int32_t));
    if (!s->occ_off || !s->sat_count || !s->sat_var || !s->score || !s->w ||
        !s->tw || !s->good || !s->good_pos || !s->stamp || !s->hunsat ||
        !s->hpos || !s->sunsat || !s->spos || !s->large || !s->large_pos) {
        nl_free(s);
        return 0;
    }

    /* occurrence lists */
    for (uint64_t c = 0; c < nc; ++c)
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
            uint32_t v = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
            s->occ_off[v + 1]++;
        }
    for (uint32_t v = 1; v <= nv + 1; ++v) s->occ_off[v] += s->occ_off[v - 1];
    s->occ = malloc((s->occ_off[nv + 1] + 1) * sizeof(uint64_t));
    if (!s->occ) { nl_free(s); return 0; }
    {
        uint64_t *fill = calloc((size_t)nv + 2, sizeof(uint64_t));
        if (!fill) { nl_free(s); return 0; }
        for (uint64_t c = 0; c < nc; ++c)
            for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                uint32_t v = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
                s->occ[s->occ_off[v] + fill[v]++] = c;
            }
        free(fill);
    }

    /* tuned weights: heavy clauses stay above the cap */
    uint64_t nsoft = 0;
    double total = 0.0;
    for (uint64_t c = 0; c < nc; ++c)
        if (!f->hard[c]) { nsoft++; total += f->weight[c]; }
    double avg = nsoft ? total / (double)nsoft : 1.0;
    double coe = nsoft ? 1000.0 / avg : 1.0;
    s->nlarge = 0;
    for (uint64_t c = 0; c < nc; ++c) {
        s->large_pos[c] = -1;
        if (f->hard[c]) { s->tw[c] = NL_HARD_W; s->w[c] = NL_HARD_W; }
        else if (nsoft) { s->tw[c] = f->weight[c] * coe; s->w[c] = s->tw[c]; }
        else { s->tw[c] = 1000.0; s->w[c] = 1000.0; }
    }

    /* assignment, sat counts, unsat stacks */
    s->nh = s->ns = 0;
    for (uint64_t c = 0; c < nc; ++c) {
        s->hpos[c] = s->spos[c] = -1;
        int32_t cnt = 0, sv = 0;
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
            int32_t l = f->lits[j];
            uint32_t v = (uint32_t)(l < 0 ? -l : l);
            if ((l > 0) == (asn[v] != 0)) { cnt++; sv = (int32_t)v; }
        }
        s->sat_count[c] = cnt;
        s->sat_var[c] = sv;
        if (cnt == 0) {
            if (f->hard[c]) { s->hpos[c] = s->nh; s->hunsat[s->nh++] = (int32_t)c; }
            else { s->spos[c] = s->ns; s->sunsat[s->ns++] = (int32_t)c; }
        }
    }
    nl_rebuild_scores(s);
    for (uint64_t c = 0; c < nc; ++c)
        if (s->w[c] > 3.0 && !f->hard[c]) {
            s->large_pos[c] = s->nlarge;
            s->large[s->nlarge++] = (int32_t)c;
        }
    return 1;
}

/* One flip, exactly as NuWLS::flip. */
/* ------------------------------------------------------------------
   nl_flip — flip variable v and repair every affected score.

   Think of each clause as moving between four states as v changes:
       was violated -> now satisfied   (0 -> 1)
       was 1 true    -> now 2 true     (1 -> 2)
       was 2 true    -> now 1 true     (2 -> 1)
       was satisfied -> now violated   (1 -> 0)
   Each transition changes the score of the variables that could fix or
   break that clause; the four branches below implement exactly that.

   The last line is the invariant that keeps the array consistent:
       score[v] = -score_before(v)
   Flipping back must undo the gain.  Miss this and the search believes
   in moves that do not improve anything.
   ------------------------------------------------------------------ */
static inline void nl_flip(NL *s, uint8_t *asn, int32_t v, uint64_t step) {
    const Formula *f = s->f;
    double org = s->score[v];
    asn[v] ^= 1;
    for (uint64_t k = s->occ_off[v]; k < s->occ_off[v + 1]; ++k) {
        uint64_t c = s->occ[k];
        int32_t lit = 0;
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
            int32_t l = f->lits[j];
            if ((uint32_t)(l < 0 ? -l : l) == (uint32_t)v) { lit = l; break; }
        }
        int now_true = ((lit > 0) == (asn[v] != 0));
        if (now_true) {
            /* ---- the clause gained a true literal ---- */
            s->sat_count[c]++;
            if (s->sat_count[c] == 2) {
                /* 1 -> 2: it had exactly one true literal, now two.  The
                   other true variable is no longer the clause's only
                   support, so flipping it would not break anything:
                   its score goes up by the clause weight. */
                s->score[s->sat_var[c]] += s->w[c];
                nl_good_add(s, s->sat_var[c]);
            } else if (s->sat_count[c] == 1) {
                /* 0 -> 1: the clause was violated and is now satisfied.
                   Every variable loses the "if I flip, I satisfy this"
                   bonus it was carrying.  The clause also leaves the
                   violated-clause stack. */
                s->sat_var[c] = v;
                for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                    uint32_t u = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
                    s->score[u] -= s->w[c];
                    if (s->score[u] <= 0) nl_good_del(s, (int32_t)u);
                }
                /* leaf the unsat stack */
                if (f->hard[c]) {
                    int32_t idx = s->hpos[c], last = s->hunsat[--s->nh];
                    s->hunsat[idx] = last; s->hpos[last] = idx; s->hpos[c] = -1;
                } else {
                    int32_t idx = s->spos[c], last = s->sunsat[--s->ns];
                    s->sunsat[idx] = last; s->spos[last] = idx; s->spos[c] = -1;
                }
            }
        } else {
            /* ---- the clause lost a true literal ---- */
            s->sat_count[c]--;
            if (s->sat_count[c] == 1) {
                /* 2 -> 1: exactly one true literal is left.  Flipping it
                   would now violate the clause, so its score drops. */
                for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                    int32_t l2 = f->lits[j];
                    uint32_t u = (uint32_t)(l2 < 0 ? -l2 : l2);
                    if ((l2 > 0) == (asn[u] != 0)) {
                        s->score[u] -= s->w[c];
                        if (s->score[u] <= 0) nl_good_del(s, (int32_t)u);
                        s->sat_var[c] = (int32_t)u;
                        break;
                    }
                }
            } else if (s->sat_count[c] == 0) {
                /* 1 -> 0: the clause just became violated.  Flipping any
                   of its variables would satisfy it, so every one of
                   them gains the clause weight. */
                for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
                    uint32_t u = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
                    s->score[u] += s->w[c];
                    nl_good_add(s, (int32_t)u);
                }
                if (f->hard[c]) { s->hpos[c] = s->nh; s->hunsat[s->nh++] = (int32_t)c; }
                else { s->spos[c] = s->ns; s->sunsat[s->ns++] = (int32_t)c; }
            }
        }
    }
    s->score[v] = -org;                 /* the negation invariant */
    if (s->score[v] > 0) nl_good_add(s, v); else nl_good_del(s, v);
    s->stamp[v] = step;
}


/* ---------------- driver: weights, selection, main loop ---------------- */
static uint64_t nl_state = 0x9E3779B97F4A7C15ULL;
static inline uint64_t nl_rand(void) { nl_state ^= nl_state << 13; nl_state ^= nl_state >> 7; nl_state ^= nl_state << 17; return nl_state; }
static inline double nl_rnd(void) { return (double)(nl_rand() >> 11) * (1.0 / 9007199254740992.0); }

/* Called when no variable has a positive score, i.e. the descent is
   stuck in a local minimum.

   We make the still-violated soft clauses heavier by a fixed amount, so
   the next descent is forced to care about them.  Occasionally (very
   rarely) we instead "smooth": satisfied clauses that had grown heavy
   lose weight again, which prevents the weights from saturating.

   Additive growth plus a cap is what keeps the weights meaningful.  A
   multiplicative scheme (w *= 1.01) makes everything hit the cap and the
   objective stops distinguishing anything. */
static void nl_update_weights(NL *s) {
    const Formula *f = s->f;
    if (nl_rnd() < 1e-3 && s->nlarge > 0) {
        for (int32_t i = 0; i < s->nlarge; ) {
            int32_t c = s->large[i];
            if (s->sat_count[c] > 0) {
                s->w[c] -= 3.0;
                if (s->w[c] <= 3.0) {
                    s->large[i] = s->large[--s->nlarge];
                    s->large_pos[c] = -1;
                    continue;
                }
                if (s->sat_count[c] == 1) {
                    s->score[s->sat_var[c]] += 3.0;
                    nl_good_add(s, s->sat_var[c]);
                }
            }
            i++;
        }
        return;
    }
    for (int32_t i = 0; i < s->ns; ++i) {
        int32_t c = s->sunsat[i];
        if (s->w[c] >= s->tw[c] + 10.0) continue;
        s->w[c] += 3.0;
        if (s->w[c] > 3.0 && s->large_pos[c] < 0) {
            s->large_pos[c] = s->nlarge;
            s->large[s->nlarge++] = c;
        }
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
            uint32_t u = (uint32_t)(f->lits[j] < 0 ? -f->lits[j] : f->lits[j]);
            s->score[u] += 3.0;
            nl_good_add(s, (int32_t)u);
        }
    }
}

/* Decide which variable to flip next — the heart of the search.

   Case A: some variable improves the objective.
       Take the best one.  Scanning all of them is O(n), so we use BMS:
       sample `22` entries from the good-variable stack and keep the best.
       With probability 0.036 pick a random good variable instead, to
       avoid determinism.

   Case B: nothing improves.
       Re-weight (see nl_update_weights), then pick a random violated
       clause.  With probability 0.48 flip a random literal in it;
       otherwise flip the best-scoring literal in it.  This is the random
       walk that leaves the local minimum.

   Ties are broken by `stamp` (least recently flipped first), which stops
   the search from oscillating between two variables. */
static int32_t nl_pick(NL *s) {
    const Formula *f = s->f;
    if (s->good_n > 0) {
        if (nl_rnd() < 0.036)
            return s->good[(uint32_t)(nl_rand() % (uint64_t)s->good_n)];
        int32_t best = s->good[(uint32_t)(nl_rand() % (uint64_t)s->good_n)];
        for (int k = 1; k < 22; ++k) {
            int32_t u = s->good[(uint32_t)(nl_rand() % (uint64_t)s->good_n)];
            if (s->score[u] > s->score[best] ||
                (s->score[u] == s->score[best] && s->stamp[u] < s->stamp[best]))
                best = u;
        }
        return best;
    }
    nl_update_weights(s);
    int32_t c;
    if (s->nh > 0) c = s->hunsat[nl_rand() % (uint64_t)s->nh];
    else if (s->ns > 0) c = s->sunsat[nl_rand() % (uint64_t)s->ns];
    else return 0;
    uint64_t len = f->offset[c + 1] - f->offset[c];
    if (nl_rnd() < 0.48) {
        int32_t l = f->lits[f->offset[c] + nl_rand() % len];
        return l < 0 ? -l : l;
    }
    int32_t best = 0;
    for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
        int32_t l = f->lits[j];
        int32_t u = l < 0 ? -l : l;
        if (!best || s->score[u] > s->score[best] ||
            (s->score[u] == s->score[best] && s->stamp[u] < s->stamp[best]))
            best = u;
    }
    return best;
}

/* Recount cost from scratch.  Scores are maintained incrementally during
   the search; this function is the independent check used to decide what
   the "best seen" assignment actually is. */
static void nl_cost(const NL *s, const uint8_t *asn, uint64_t *hard, double *soft) {
    const Formula *f = s->f;
    uint64_t h = 0;
    double sc = 0.0;
    for (uint64_t c = 0; c < s->nc; ++c) {
        int sat = 0;
        for (uint64_t j = f->offset[c]; j < f->offset[c + 1]; ++j) {
            int32_t l = f->lits[j];
            uint32_t v = (uint32_t)(l < 0 ? -l : l);
            if ((l > 0) == (asn[v] != 0)) { sat = 1; break; }
        }
        if (!sat) { if (f->hard[c]) h++; else sc += f->weight[c]; }
    }
    *hard = h;
    *soft = sc;
}

/* Entry point: same contract as SUTRA's repair(). */
/* ------------------------------------------------------------------
   repair_nuwls — the entry point SUTRA calls.

   Contract (same as the legacy repair):
     in/out  asn           current assignment; overwritten with the best
                           assignment found during the run
     in      flips_budget  stop after this many single-variable flips
     in      time_budget   wall-clock stop (checked every 1024 flips)
     out     converged     1 if every clause was satisfied

   The loop stops as soon as all clauses are satisfied, when the flip
   budget is spent, or when the clock runs out.  Whatever happens, the
   best assignment seen is copied back into `asn`, so an interrupted run
   still returns the best thing it found.
   ------------------------------------------------------------------ */
static uint64_t repair_nuwls(const Formula *f, uint8_t *asn, uint64_t flips_budget,
                             int *converged, double time_budget, clock_t t0,
                             uint64_t stall_limit, uint64_t tabu_tenure) {
    (void)stall_limit; (void)tabu_tenure;
    NL s;
    if (!nl_init(&s, f, asn)) { *converged = 0; return 0; }
    uint8_t *best = malloc(f->vars + 1);
    if (!best) { nl_free(&s); *converged = 0; return 0; }
    memcpy(best, asn, f->vars + 1);
    uint64_t best_h = 0, cur_h = 0;
    double best_s = 0.0, cur_s = 0.0;
    nl_cost(&s, asn, &best_h, &best_s);
    cur_h = best_h; cur_s = best_s;
    uint64_t used = 0;
    *converged = 0;
    while (used < flips_budget) {
        if (s.nh == 0 && s.ns == 0) { *converged = 1; break; }
        if ((used & 1023u) == 0 && time_budget > 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > time_budget) break;
        int32_t v = nl_pick(&s);
        if (!v) break;
        nl_flip(&s, asn, v, used + 1);
        used++;
        if ((used & 255u) == 0) {
            nl_cost(&s, asn, &cur_h, &cur_s);
            if (cur_h < best_h || (cur_h == best_h && cur_s < best_s - 1e-12)) {
                best_h = cur_h; best_s = cur_s;
                memcpy(best, asn, f->vars + 1);
            }
        }
    }
    if (s.nh == 0 && s.ns == 0) { *converged = 1; memcpy(best, asn, f->vars + 1); }
    memcpy(asn, best, f->vars + 1);
    free(best);
    nl_free(&s);
    return used;
}

#endif /* SUTRA_NUWLS_H */
