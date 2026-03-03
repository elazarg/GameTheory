# Kuhn-Style Decomposition (Abstract)

Status: exploratory, not final.

## K0. Large Theorem Shape

Given a finite-step stochastic process, two randomization factorizations are outcome-equivalent.

- Factorization A: local sampling at each observable occurrence.
- Factorization B: global pre-sampled assignment map.

Under stronger determinacy, every B admits equivalent A.

## K1. Easy Direction Skeleton

### Goal

`EvalLocal = EvalGlobal`

### Planned Steps

1. Single-step local/global equivalence (`L1`).
2. Tail induction over process list (`L2`).
3. Same-draw/fresh-draw replacement via ignorance (`L1` + `L0`).
4. Use separation to prove required ignorance side conditions (`L2`).

### Assumption Audit

- essential:
  - finite products (for explicit PMF sums)
  - separation
- likely removable:
  - extra decidability not tied to updates
- framework artifact:
  - player-centric naming

## K2. Hard Direction Skeleton

### Goal

`∃ LocalPolicy, EvalLocal = EvalGlobalGiven`

### Planned Steps

1. Disintegrate global bind by current observable branch (`L1`).
2. Apply IH per branch on tail process (`L2`).
3. Recombine branches into one local kernel (`L1` + `L2`).
4. Use determinacy to ensure branchwise constructions depend only on observable (`L2`).
5. Use reachable congruence to swap local kernels where only unreachable observables differ (`L2`).

### Assumption Audit

- essential:
  - finite conditioning/disintegration setup
  - determinacy/strong recall-like condition
- likely removable:
  - full format structure in mid-lemmas
- framework artifact:
  - protocol-specific wrappers

## K3. One-Shot Lemma Candidates (No Hierarchy Commitment)

1. `disintegrate_then_recombine` (`L1`)
2. `tail_determinacy_transport` (`L2`)
3. `reachable_observable_congruence` (`L2`)
4. `curry_update` normalization (`L0`, already present)

## K4. Backtracking Log

- Open.
- Fill each failure with:
  - failing step id (`K1.3`, `K2.4`, etc.)
  - minimal counterexample/obstruction
  - revised local statement
