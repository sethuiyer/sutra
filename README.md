# SUTRA — MaxSAT approximator

*Search Under Time, Recounted, Attested.*

**Author: Sethu Iyer — [github.com/sethuiyer](https://github.com/sethuiyer)**

Best-effort weighted MaxSAT. Anytime, witness-first, no optimality claims.

SUTRA returns a *verified assignment* and its cost as fast as it can, keeps
improving while the budget lasts, and never pretends to have proven
anything it hasn't. For hard-core infeasibility it can optionally emit a
machine-checkable refutation.

```
  status      meaning
  SAT         every clause satisfied (cost 0)
  FEASIBLE    hard clauses satisfied, soft cost > 0
  UNKNOWN     budget exhausted; incumbent still valid
  UNSAT       hard core proven unsatisfiable — only with --proof
```

## Build

```sh
make            # -> ./sutra, ./sutracert
make test       # 17 checks: certificates, soundness, negative controls
```

## Use

```sh
./sutra instance.wcnf --time-budget-seconds 30 --restarts 1
./sutra instance.cnf  --time-budget-seconds 30
```

Output is one JSON line (or `--no-json` for humans):

```json
{"engine":"SUTRA","version":"1.0.0","status":"FEASIBLE","variables":20000,
 "clauses":80000,"satisfied":79986,"hard_unsatisfied":0,"soft_cost":14.0,
 "wall_seconds":30.0,"certified":false,"verified":"recount_from_witness"}
```

Every number in that line is recomputed from the returned assignment before
printing. The solver's own bookkeeping is never trusted.

| flag | meaning |
|---|---|
| `--time-budget-seconds X` | wall-clock budget; returns best-so-far |
| `--restarts N` | restart budget (0 = time-driven) |
| `--solution FILE` | write the witness as a DIMACS assignment |
| `--checkpoint FILE` | anytime checkpoint, salvageable after SIGKILL |
| `--seed N` | deterministic base seed |
| `--proof FILE` | emit a refutation certificate for an UNSAT hard core |
| `--proof-format auto\|gfp\|drat` | certificate format |
| `--exact-conflicts N` | CDCL budget for a certified refutation |
| `--kissat PATH` | portfolio: delegate pure CNF, keep only verified answers |
| `--checker PATH` | verifier for delegated proofs (`sutracert`, `drat-trim`) |
| `--repair-walk` | legacy WalkSAT repair (opt-in) |

## What makes it an approximator worth using

**1. It never regresses.** The repair engine takes global ascent steps on a
weighted objective: gain scores maintained incrementally, a good-variable
stack, BMS sampling, additive capped clause weights. On `contested_20000`
that is the difference between 1572 and 14.

**2. It keeps descending while the budget lasts.** Anytime cost, same
instance, against Aperture:

| budget | Aperture | SUTRA |
|---|---|---|
| 1 s | **158** | 423 |
| 5 s | **68** | 75 |
| 15 s | 68 | **20** |
| 30 s | 68 | **14** |

Aperture plateaus after five seconds; SUTRA keeps going. Crossover ≈ 7 s.
Below that SUTRA is the weaker approximator — it spends its first second
building an assignment, not answering.

**3. The witness is always checkable.** `--solution` writes an assignment
any third-party checker can recount. No trust required.

**4. Optional certified refutation.** If the hard core is unsatisfiable,
`--proof` emits a `gfp` (GF(2) parity) or DRAT refutation, verified by
`sutracert` or `drat-trim`. On parity-structured instances this is
asymptotically better than any resolution solver:

| instance | Kissat 4.0.1 | SUTRA |
|---|---|---|
| Tseitin 4-regular v=60 | timeout >30 s | **UNSAT 2 ms**, certified |
| Tseitin v=300 | timeout >30 s | **UNSAT 2 ms**, certified |

**5. Portfolio mode.** `--kissat PATH` delegates general CNF to an external
CDCL and accepts nothing on faith: SAT witnesses are recounted clause by
clause, UNSAT proofs are checked by `drat-trim`. Coverage on a 44-instance
grid: 43/44 versus Kissat's 38/44.

## Measured MaxSAT results

30 s budget, lower cost is better:

| instance | Aperture | SUTRA |
|---|---|---|
| contested_5000 | 10 | **6** |
| contested_20000 | 68 | **14** |
| random 20k vars / 80k clauses | 97 | **46** |
| random 50k / 200k | 286 | **191** |
| contested_1000 | 0 | 0 |
| pdense / twobasin / phard / plw | 0 | 0 |
| lsm_18_5 | 373 | 373 |

Five wins, five ties, no losses — on ten instances, one seed, default
settings. Directional evidence, not a benchmark suite.

## Architecture

| file | role |
|---|---|
| `sutra.c` | parser, continuous warm start, anytime loop, output |
| `sutra_nuwls.h` | NuWLS repair core: gain scores, good-var stack, BMS, capped weights |
| `sutra_cert.h` | parity detection, GF(2) elimination, model construction, DRAT bridge |
| `cdcl_internal.h` | CDCL used for certified refutations |
| `sutracert.c` | independent certificate checker (gfp + RUP DRAT) |
| `navokoj_checkpoint.*` | anytime checkpoint for SIGKILL salvage |
| `tests.sh` | positive, soundness and negative-control suite |
| `bench/gen_corpus.py`, `bench/run_bench.py` | cnfgen corpus + verification harness |

## The name

**सूत्र** — *sūtra*: a thread; also an aphorism, a maximally compressed
statement whose meaning is unpacked by its commentary.

- **The formula is a weave.** A clause is a string of literals; a CNF file
  is a set of threads, and solving means finding a tension that satisfies
  all of them at once.
- **The derivation is a thread.** CDCL's assignment trail is a thread of
  forced literals; every learned clause is sewn onto the ones before it,
  and a refutation is one continuous thread from the clauses to `0 = 1`.
- **The proof is the thread you can pull.** A certificate unwinds back to
  the original clauses one step at a time — that is exactly what
  `sutracert` does.

The backronym is the three guarantees in order:

> **S**earch **U**nder **T**ime, **R**ecounted, **A**ttested

anytime · witness-first · certificate-checked.

## Limits — read these

- **No optimality proof.** Aperture proves OPTIMUM; SUTRA reports a cost.
- **Weak under ~5 s.** The continuous warm start is not free; below ~7 s
  Aperture is the better approximator.
- **General SAT is not its job.** Without `--kissat` it has no competitive
  CDCL of its own; with it, the SAT win is the external solver's.
- **Evidence is thin.** Ten MaxSAT instances, one seed, one configuration.
  The distributional claim ("best approximator") is not established.
- **No optimality certificates for MaxSAT** — only refutations of
  unsatisfiable hard cores.
