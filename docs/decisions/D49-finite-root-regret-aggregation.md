# D49: Aggregate finite local CFR processes at the root

- **Status:** adopted for fixed finite D48 decompositions
- **Date:** 2026-08-11
- **Experiment ID:** EXP-087

## Decision

For a finite family of information sites, retain each D46 process as the
canonical running average of D45 action-regret vectors. If D48 supplies an
exact per-round root-gain decomposition with alternative own-reach
coefficients in `[0,1]`, then positive average root gain is bounded by the sum
of the local vectors' distances from their nonpositive orthants.

The finite-family inequality is game-independent and lives in
`GameTheoryMath.RegretAggregation`. The Protocol layer owns only the named
local average, its exact Cesaro identity, and the specialization whose premise
is an actual scalar root-gain decomposition. It introduces neither a second
runner nor a parallel regret definition.

When every local payoff vector has the ordinary D46 norm bound, all local
orthant distances converge to zero. A finite sum and the root inequality then
give vanishing positive average gain for the fixed root deviation.

## Hostile evidence

The two-stage complementarity Protocol runs simultaneous regret matching at
the first information site and the off-path second-after-true site. Each local
environment is the other site's current law. The mutually recursive state is
proved equal to both actual D46 `avgVec` processes; D47 proves both realization
equations; and D48 proves every canonical behavioral root gain is exactly the
sum of the two selected local coordinates. Under the standard per-site norm
bounds, both D46 limits therefore drive that positive root gain to zero.

The negative control deliberately ignores both regret-matcher laws. It repeats
the `false,false` incumbent against the coordinated `true,true` deviation, so
its canonical positive average root gain is exactly one at every nonempty
horizon. The finite aggregation theorem still detects the unit off-path term,
but no convergence claim is available because realization fails.

## Scope and next gate

This adopts a useful fixed-deviation root-regret seam, not full CFR
exploitability. The remaining gate must enumerate a complete finite
topological site schedule, make the bound uniform over all pure policy
deviations, discharge payoff-vector bounds from a public payoff-range
certificate, and connect the result to canonical strategic external regret.
Two-player zero-sum exploitability follows only after that uniform bridge.

EXP-088/D50 subsequently discharges that uniform strategic bridge for every
deviation carrying a finite D48 upper-decomposition certificate; D49's adopted
scope remains the fixed-deviation theorem recorded here.

Unequal-depth information fibers remain outside D48 and therefore outside this
decision.
