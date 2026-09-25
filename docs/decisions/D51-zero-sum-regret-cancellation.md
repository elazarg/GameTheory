# D51: Derive zero-sum equilibrium from canonical external regret

- **Status:** adopted for two-player matrix games with actual-law integration
- **Date:** 2026-08-11
- **Experiment ID:** EXP-089

## Decision

Represent a learning trace by its actual PMF over joint pure
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
regret is introduced. The cancellation identity requires integration of the
correlated incumbent and the compared pure deviations. Its mixed-deviation
extension additionally requires integration of those actual independent laws;
the approximate-Nash consequence certifies every unilateral mixed deviation.
No finite row or column carrier is needed by these guarded statements.

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

## Scope

This decision closes the reusable static zero-sum implication for arbitrary
correlated PMF laws over rectangular matrix games with the stated integration
certificates. Finite carriers supply those certificates automatically. It
does not prove that a particular learning process supplies both players'
regret bounds.

A dynamic Protocol/CFR application must supply both players' D50 external-regret
certificates for the same round law before applying this result; see D52.
General schedule synthesis, arbitrary behavioral replacements, and unequal-depth
information fibers require their own hypotheses.

## Evidence

Exact validation commands and results are recorded under this decision's
experiment IDs in the [experiment log](../ExperimentLog.md).
