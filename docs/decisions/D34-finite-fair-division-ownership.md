# D34: finite fair division consumes the canonical disjoint allocation

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment ID:** EXP-067

## Decision / question

Whether indivisible fair division should reuse
`Mechanism.Combinatorial.Allocation`, expose the comparison design's parallel function-valued
allocation plus feasibility predicate, or compile fairness through a strategic
mechanism model.

## Competing designs

1. Reuse the existing canonical disjoint allocation, add additive valuations
   and fairness predicates in `Mechanism.FairDivision`, and keep completeness
   as a separate certificate.
2. Recreate a public `Agent → Finset Good` allocation and prove both
   disjointness and completeness in a parallel `IsAllocation` predicate.
3. Treat allocations as outcomes of a strategic form before envy or EF1 can be
   stated.

Design 1 is adopted.  Disjoint finite bundles already have an owner.  Fairness
adds valuations and completeness, not a second allocation carrier or an
equilibrium concept.  The combinatorial allocation was first sharpened so it
stores no `Fintype` or `DecidableEq` capability.

## Representative hostile slice

The generic slice has arbitrary nonempty `Fin n` agents, a finite goods
carrier, and nonnegative additive values.  Choice round-robin selects a best
remaining good at each turn, returns a canonical disjoint allocation, proves
every good is assigned, and proves EF1.

The concrete fixture has two agents and three goods with conflicting strict
rankings.  Agent zero receives a two-good bundle and agent one strictly envies
it (`8 < 7 + 3`).  Removing good zero, which agent one values positively,
eliminates the envy.  Thus the witness distinguishes envy-freeness from EF1 and
is not a singleton or zero-value special case.  The general completeness and
EF1 theorems specialize to the same valuation profile.

## Measurements

| Measure | EXP-067 result |
|---|---|
| canonical owner | `Mechanism.Combinatorial.Allocation`; no stored capability after `e1e5052` |
| public recursive surface | none; raw bundle maps and the update helper remain private |

## Kill condition

Reject canonical ownership if general round-robin needs a second public
allocation type, stored finiteness/decidability, raw function updates, a game
wrapper, or measurable probability; if EF1 can only be proved for two agents;
or if the fixture cannot distinguish actual envy from the one-good-removal
guarantee.

## Consequences for the public API

`GameTheory.Mechanism.FairDivision` is available through the opt-in Mechanism
root.  `Allocation` is a transparent domain name for the canonical
combinatorial allocation, `IsComplete` supplies the additional cover
certificate, and fairness predicates remain independent of games and
probability.  The public round-robin result returns this allocation directly;
the predecessor's raw recursive `roundRobinAux` is retired.

Two-agent EFX, envy-cycle elimination, and maximin-share results can use the
same finite allocation semantics. Divisible cake cutting requires the separate
measure boundary in D11.
