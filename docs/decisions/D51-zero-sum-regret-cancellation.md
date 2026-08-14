# D51: Derive zero-sum equilibrium from canonical external regret

- **Status:** adopted for finite two-player matrix games
- **Date:** 2026-08-11
- **Experiment ID:** EXP-089

## Decision

Represent a finite learning trace by its actual `FinDist` over joint pure
profiles. Derive the row and column empirical marginals from that joint law.
For the canonical two-player zero-sum `UtilityGame`, identify each player's
existing external regret with its signed payoff difference and add the two
identities. The correlated status-quo payoff cancels exactly:

```text
payoff(fixed row, column marginal)
  - payoff(row marginal, fixed column)
= row external regret + column external regret.
```

Uniform bounds on the two canonical regrets therefore control every pure and
mixed saddle deviation gap. Their sum is also a direct tolerance for the
existing canonical `IsεNash` predicate at the independent empirical-marginal
profile. No maximized exploitability definition or matrix-specific proxy
regret is introduced.

## Hostile evidence

The positive Boolean matching-pennies control puts all trace mass on the
mismatched profile `(false, true)`. Deviating the row to `true` has canonical
external regret exactly `2`, the selected column deviation has regret `0`, and
the public cancellation theorem returns the exact nonzero saddle gap `2`.

The cancellation control is deliberately correlated: it assigns equal mass to
`(false, false)` and `(true, true)`, rather than assuming a product trace law.
Both empirical marginals are fair. Every fixed row has signed regret `-1` and
every fixed column has signed regret `1`; these cancel to tolerance zero, and
the public theorem constructs a canonical exact mixed Nash certificate for the
empirical-marginal profile. This also checks that prematurely taking positive
parts would lose a useful exact cancellation.

## Rejected alternatives and kill conditions

Reject a second regret definition, a theorem requiring the joint trace law to
be independent, cancellation without the zero-sum utility, a gap statement
without a positive control, or a Protocol-only proof whose static algebra
cannot be reused. None fired.

The adopted API exposes the exact gap identity, pure and mixed quantitative
bounds, and the canonical approximate-Nash consequence. A new scalar
`exploitability` wrapper would add no theorem-level capability at this gate.

## Scope and next gate

This decision closes the reusable static zero-sum implication for arbitrary
finite correlated traces over rectangular matrix games. It does not prove that
a particular learning process supplies both players' regret bounds.

The next gate is dynamic: build one two-player zero-sum Protocol/CFR schedule
whose two D50 external-regret certificates concern the same round law, then
feed those bounds directly to D51. General schedule synthesis, arbitrary
behavioral replacements, and unequal-depth information fibers remain
separate.

## Validation

- `lake build GameTheory.Analysis.ZeroSumLearning`
- `lake build GameTheory.Analysis.ZeroSumLearningTest`
- `lake build GameTheory.Analysis`
- `lake build GameTheory`
- `scripts/phase2-audit.ps1 -VerifyExpected`
- `scripts/phase3-audit.ps1 -VerifyExpected`

The two responsive narrow builds completed in under 16 seconds, the Analysis
aggregator completed 3,211 jobs in 11.4 seconds, and the cached stable package
gate completed 3,594 jobs in 3.3 seconds. Both fast audits reported
`VERIFIED=1`. Deep reachability was not run.
