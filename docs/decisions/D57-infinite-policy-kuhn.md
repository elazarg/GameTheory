# D57: infinite Kuhn uses an ordinary product measure over pure policies

- **Status:** adopted and promoted
- **Date:** 2026-08-20
- **Experiment IDs:** EXP-117; builds on EXP-115 and EXP-116

## Decision / question

How a behavioral policy on an infinite information-state carrier should induce
one ex-ante random pure policy that is valid for every finite prefix and for
discounted payoff comparisons.

## Competing designs

1. Select a separate finite-support `FinDist` witness for each horizon.
2. Reuse the experimental behavioral infinite-path outcome measure.
3. Use Mathlib's ordinary infinite product measure directly over total pure
   policies and reconnect each finite marginal to the executable `FinDist`
   layer.
4. Introduce a project-wide probability-law abstraction hiding both `FinDist`
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

The finite marginal of `Measure.infinitePi` is exactly the existing nested
`FinDist.pi` after conversion to an ordinary measure. Covered bounded runs
depend only on those coordinates, so the existing Protocol runner proves the
prefix law without another evaluator. The generic discounted theorem assumes
summability; the stochastic specialization derives it from bounded stage
utility and `0 ≤ discount < 1`. Regularity requires countable indices and the
standard Borel, second-countable, completely-pseudometrizable hypotheses. The
focused builds compiled 2,990, 3,001, 3,018, and 3,020 jobs for the bridge,
Protocol layer, stochastic specialization, and hostile consumer respectively.
The integrated target passed 3,048 jobs and the full default target passed
3,995 jobs. Deep Phase 2 and Phase 3 audits both reported `VERIFIED=1`; eight
flagship axiom prints contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Evidence from existing libraries

Mathlib supplies `Measure.infinitePi`, its finite-restriction marginal law,
ordinary measure bind/map, product regularity, and Bochner integration. The
existing GameTheory Protocol supplies the only history runner, finite-site
predrawing, counterfactual site coverage, and behavioral/mixed bounded law.
No new probability abstraction or game evaluator is required.

## Unexpected costs

The finite/executable layer needed explicit theorems showing that `FinDist`
pure, map, bind, and dependent product commute with conversion to `Measure`.
Policy types are transparent abbreviations so Mathlib can synthesize the
canonical dependent product measurable/topological instances. These are API
repairs, not additional semantic objects. The Phase 2 representation audit now
names exactly `FinDist.lean` and `Measure.lean` as representation owners and
continues to reject `PMF`/`toPMF` leakage everywhere else.

## Kill condition

Reject promotion if the construction selects one witness per horizon, treats
a path law as a policy law, loses arbitrary behavioral unilateral
replacements, adds a runner or equilibrium predicate, hides global finiteness,
introduces a universal probability wrapper, needs a placeholder or visible
transport, or claims discounted equality without convergence hypotheses.

No kill condition fired.

## Result and public API consequences

`Protocol.PolicyMeasure` owns the horizon-independent product probability law,
its exact finite marginals, all covered finite-prefix laws, arbitrary
behavioral unilateral replacements, prefix expectations, discounted equality,
and operation-local regularity. `Stochastic.Kuhn` proves perfect-monitoring
countability/regularity and exposes all-prefix and bounded discounted
corollaries. `Math.Probability.Measure` is only the reusable finite-law bridge.

The unbounded `BehavioralPolicy.toMixed : FinDist _` convenience remains
finite. This decision does not create an infinite-path outcome law. The
reverse construction from arbitrary per-player pure-policy measures was a
separate gate, subsequently closed by EXP-118/D58 through finite own-record
conditioning.

Deep Phase 2 and Phase 3 reachability gates positively require the new
stochastic and Protocol declarations while rejecting EXP-108's experimental
path-measure declaration from both stable roots.
