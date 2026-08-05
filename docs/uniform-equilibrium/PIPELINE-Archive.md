# Uniform-equilibrium pipeline archive

This file is a one-way archive. Items move here from
[`PIPELINE.md`](PIPELINE.md) once their status reaches `DONE` (or they are
explicitly superseded), and they do not move back -- if a `DONE` item needs
further work, that work is tracked under a new ID in `PIPELINE.md`, not by
resurrecting the old entry here. Verbatim preservation of every item's content
applies here exactly as it does in the main pipeline file.

## Lean formalization lane

### `LEAN-P0-1` — landed debt-transport, cycle-mismatch, FTV, and germ-bridge results this cycle

- **Status:** DONE
- **Lane:** P0
- **Record:** this pipeline

**Objective.** Landed this cycle, for the record: the exact debt transport law;
the cycle mismatch characterization in both branches; the conditional reduction
from an admissible absorbing cycle to a uniform payoff, with no strategy-class
gap; the zero-solo branch and the disjunction; the FTV table's uniform payoff
`(1,2,1)`; periodic extension and cycle-pinned nonnegativity; the
quitting-to-analytic-germ bridge; and `Math.AnalyticOrderComparison`.

**State.** `DONE`, all axiom-clean. Recorded here because the lane previously
had no row for any of it.

**Acceptance.** Consumed by the carrier group; the reduction's *completeness* is
refuted, so none of this closes the conjecture.

### `LEAN-P0-3` — pin the matching scaling case in the germ bridge

- **Status:** DONE
- **Lane:** P0
- **Depends:** `QuittingAnalyticGerm`.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** Pin the matching scaling case in the germ bridge: expand the
absorption product to first order so `t^q / absorption` is pinned rather than
squeezed between `1/(n·Σa)` and `1/Σa`.

**State.** `DONE` on `uniform-existence`, axiom-clean. Route: not an explicit
product expansion but the two-sided Bonferroni estimate of
`Math/BonferroniProductBounds.lean` plus a new
`Math.analyticOrderAt_eq_of_tendsto_div_pow`.
`GameTheory.analyticOrderAt_quittingGermAbsorption_eq` gives
`analyticOrderAt (quittingGermAbsorption g) 0 = m` with leading coefficient
exactly `∑ a` and `t^m / absorption → 1/∑ a`, under `1 ≤ m`, which is free in
the matching branch because `g.ramification = m` and the ramification is
positive. All six transfer directions across the three regimes are landed.

**Acceptance.** Completes the three-way scaling comparison on absorption itself,
which the vanishing-branch argument consumes.

### `LEAN-P0-4` — discharge nondegeneracy of the germ quit family

- **Status:** DONE
- **Lane:** P0
- **Depends:** `QuittingAnalyticGerm`.
- **Record:** [signed
  accumulation](../../ideas/AbsorbingCycleCarrier/TheSignedAccumulationIsTheGain.md)

**Objective.** Discharge nondegeneracy of the germ quit family.

**State.** `DONE` at `7d518eb`: degeneracy is not a gap but the zero-solo
branch, so the entry point is restated with the germ-internal hypothesis
replaced by "not zero-solo".

**Acceptance.** Without it the normalized direction is undefined and the
leading-order package is vacuous on that germ.
