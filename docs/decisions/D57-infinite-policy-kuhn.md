# D57: infinite Kuhn uses an ordinary product measure over pure policies

- **Status:** adopted and promoted
- **Date:** 2026-08-20
- **Experiment IDs:** EXP-117 and EXP-127; builds on EXP-115 and EXP-116

## Decision / question

How a behavioral policy on an infinite information-state carrier should induce
one ex-ante random pure policy that is valid for every finite prefix and for
discounted payoff comparisons.

## Competing designs

1. Select a separate discrete policy witness for each horizon.
2. Reuse the experimental behavioral infinite-path outcome measure.
3. Use Mathlib's ordinary infinite product measure directly over total pure
   policies and reconnect each finite-coordinate marginal to ordinary PMF
   semantics.
4. Introduce a project-wide probability-law abstraction hiding both `PMF`
   and `Measure`.

Design 3 is adopted. Design 1 has the wrong quantifier order and does not give
one ex-ante mixed object. Design 2 has the wrong sample space. Design 4 adds an
unvalidated universal semantic hub where a narrow bridge suffices.

## Representative hostile slice

EXP-117 uses a finite-action perfect-monitoring stochastic game whose public
histories are countably infinite. Its utility is action-dependent, an
arbitrary behavioral replacement reaches a branch outside the baseline
support, and discount `1/2` exercises a nonconstant bounded payoff series.
The consumer checks probability, regularity, an exact finite marginal, one
measure outside the all-horizons quantifier, unilateral all-prefix equality,
and baseline and unilateral discounted equality.

## Measurements

The finite-coordinate marginal of `Measure.infinitePi` agrees with the
independent PMF product after conversion to an ordinary measure. The choices
and PMF supports need not be finite. Each target history queries only finitely
many coordinates. This gives its exact mass; the behavioral PMF's countable
support supplies almost-everywhere support for the integrated runner kernel.
No global cover of the sites reachable within a horizon is required (EXP-127).

The generic discounted theorem requires integration of each actual stage and
summability of its weighted expected values. Bounded stage utility and
`0 ≤ discount < 1` suffice in the stochastic specialization. Regularity is a
separate operation: it requires countable indices and the
standard Borel, second-countable, completely-pseudometrizable hypotheses.

## Evidence from existing libraries

Mathlib supplies `Measure.infinitePi`, its finite-restriction marginal law,
ordinary measure bind/map, product regularity, and Bochner integration. The
existing GameTheory Protocol supplies the only history runner, finite-site
predrawing, counterfactual site coverage, and behavioral/mixed bounded law.
No new probability abstraction or game evaluator is required.

## Unexpected costs

The original finite-law layer needed explicit theorems showing that `FinDist`
pure, map, bind, and dependent product commute with conversion to `Measure`.
Policy types are transparent abbreviations so Mathlib can synthesize the
canonical dependent product measurable/topological instances. These are API
requirements, not additional semantic objects. D62 replaces the finite-law
wrapper with ordinary PMF semantics while retaining an explicit measure bridge
and named owners for raw weight conversion.

## Kill condition

Reject promotion if the construction selects one witness per horizon, treats
a path law as a policy law, loses arbitrary behavioral unilateral
replacements, adds a runner or equilibrium predicate, hides global finiteness,
introduces a universal probability wrapper, needs a placeholder or visible
transport, or claims discounted equality without convergence hypotheses.

No kill condition fired.

## Result and public API consequences

`Protocol.PolicyMeasure` owns the horizon-independent product probability law,
its exact finite-coordinate marginals, all finite-prefix laws, arbitrary
behavioral unilateral replacements, prefix expectations, discounted equality,
and operation-local regularity. `Stochastic.Kuhn` proves perfect-monitoring
countability/regularity and exposes all-prefix and bounded discounted
corollaries. `Math.Probability.Measure` owns the reusable discrete PMF/measure
and guarded expectation bridges.

Discrete whole-policy predrawing retains explicit finite-site certificates.
This decision does not create an infinite-path outcome law. The
reverse construction from arbitrary per-player pure-policy measures was a
separate gate, subsequently closed by EXP-118/D58 through finite own-record
conditioning.

Deep Phase 2 and Phase 3 reachability gates positively require the new
stochastic and Protocol declarations while rejecting EXP-108's experimental
path-measure declaration from both stable roots.
