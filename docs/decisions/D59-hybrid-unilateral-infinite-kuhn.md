# D59: infinite Kuhn exposes both hybrid unilateral quantifiers

- **Status:** adopted and promoted
- **Date:** 2026-08-20
- **Experiment IDs:** EXP-119; builds on EXP-116, EXP-117, and EXP-118

## Decision / question

How the forward behavioral-to-total-policy-law and reverse
total-policy-law-to-behavioral constructions should compose with unilateral
deviations strongly enough to transport a Nash deviation quantifier.

The required statements are heterogeneous:

1. arbitrary total-policy laws for every opponent plus an arbitrary behavioral
   policy for the focal player; and
2. the original behavioral policy for every opponent plus an arbitrary
   total-policy law for the focal player.

## Competing designs

1. Treat D57's forward whole-profile/update law and D58's reverse
   whole-profile/update law as sufficient by composing them informally.
2. Add explicit hybrid history-law theorems at Protocol, derived through the
   bounded mixed/behavioral unilateral correspondence and finite marginals.
3. Introduce a new equilibrium predicate whose strategies mix behavioral
   policies and ordinary measures directly.
4. State only a horizon-indexed finite-support hybrid witness.

Design 2 is adopted. Design 1 does not preserve the quantified focal object:
composition replaces either the deviation or the opponents by a behavioral or
policy-law round trip. Those round trips need not be pointwise identical at
zero-mass off-path cylinders. Design 3 duplicates the accepted equilibrium
waist, and design 4 has the wrong quantifier order for discounted play.

## Representative hostile slice

EXP-119 uses a two-player perfect-monitoring stochastic game with countably
infinite public histories. A measurable transformation of an infinite product
law forces two distinct policy coordinates to agree, giving genuine
within-policy correlation. In the first direction the other player keeps that
arbitrary law while the focal player makes an off-baseline behavioral
deviation. In the reverse direction the other player keeps its behavioral
policy while the focal player uses the correlated total-policy law. Both
directions consume every finite prefix and a bounded nonconstant discounted
payoff.

## Measurements

Restricting a behavioral policy's infinite product law to any finite site set
and converting the marginal back to `FinDist` is exactly the established
`BehavioralPolicy.toMixedWithin` predraw. The bounded reverse API was
strengthened to retain a caller-supplied zero-mass fallback. This allows a
record-closed finite marginal to agree locally with the single
horizon-independent conditional reading of each arbitrary opponent law.

Each hybrid proof reduces the updated policy-measure profile to record-closed
finite marginals, applies the corresponding bounded heterogeneous unilateral
theorem, and uses counterfactual coverage to replace only the finite internal
readings. The original behavioral deviation or arbitrary focal measure remains
syntactically unchanged in the public conclusion. Pointwise prefix-expectation
laws and summable normalized discounted consequences follow without another
runner or equilibrium predicate.

Build, audit, source-hazard, and axiom measurements are recorded in EXP-119.

## Evidence from existing libraries

Mathlib supplies the ordinary product-measure finite marginal and the existing
finite-discrete measure bridge. GameTheory Protocol already supplies
counterfactual site coverage, record closure, fixed-fallback conditional
reading, bounded mixed/behavioral unilateral realization, and the sole runner.
The new layer composes these APIs rather than introducing a new probability or
equilibrium abstraction.

## Kill condition

Reject promotion if either theorem replaces the quantified focal object by a
round trip, assumes global information-state finiteness, covers only baseline
support, chooses a new policy/behavioral object for each horizon, adds a runner
or equilibrium predicate, introduces visible transport or placeholders, or
states discounted equality without convergence hypotheses.

No kill condition fired.

## Result and public API consequences

`Protocol.PolicyMeasure` now exposes the two explicit hybrid all-prefix laws,
their finite-prefix expectation forms, and their summable discounted forms.
`Protocol.Strategic` exposes the fixed-fallback bounded round-trip and
heterogeneous unilateral lemmas used by the measure layer.
`Stochastic.Kuhn` supplies thin perfect-monitoring all-prefix and bounded
discounted corollaries in both directions.

These theorems are the law equalities needed to move a Nash deviation
quantifier between behavioral policies and ordinary laws over total plans.
They do not introduce a third Nash predicate. Correlated joint laws across
players and infinite-path outcome semantics remain separate gates.
