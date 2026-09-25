# D39: general-sum discounted stochastic equilibrium stays in Analysis

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-072; arbitrary-state semantic boundary EXP-138 / D62

## Decision / question

Whether the updated sibling repository's finite general-sum Fink theorem can
be recovered over the successor library's stochastic carrier, probability
law, equilibrium predicate, and fixed-point boundary without importing its
legacy stochastic closure.

## Competing designs

1. Adapt the finite-dimensional Fink map to canonical discrete laws,
   `UtilityGame`, mixed Nash, and the existing one-way Analysis root.
2. Extract or import the sibling's `PMF`/kernel-game/simplex hierarchy.
3. Store discount and finite capabilities in `Stochastic.Game`.
4. Keep general-sum discounted existence in Frontier and recover only the
   independent uniform-payoff perturbation lemmas.

Design 1 is adopted.  Designs 2 and 3 duplicate or reverse accepted owners.
Design 4 remains the fallback for infinite-play and uniform-existence work,
but the finite discounted theorem itself no longer needs that deferral.

## Representative hostile slice

The general theorem uses finitely many states, players, and actions, bounded
stage utilities, and a normalized discount in `[0, 1]`.  It produces a
state-dependent PMF action profile and continuation values such that:

1. the profile is canonical mixed Nash in every statewise auxiliary
   `UtilityGame`; and
2. the auxiliary expected utilities equal the continuation values.

The witness has two states, two players, two actions each, state-dependent
general-sum utilities, and action-dependent mixtures that put positive mass on
both next states.  At discount `1/2`, it invokes the general fixed-point
theorem rather than a hand-solved certificate.

## Measurements

| Measure | Result |
|---|---|
| sibling source | commit `da076851bab19519521aa1e0d2da127e29fcd5c9`; source evidence recorded in EXP-072 |
| successor toolchain | Lean and Mathlib 4.32.2 |
| direct game imports | `Analysis.Nash`, `Core.MixedImprovement`, `Stochastic.Basic` |
| fixed-point dependency | reached transitively through the sole `Analysis.Nash` package import; no second direct package importer |
| probability and equilibrium owners | `FinDist`; canonical `IsNash` on `UtilityGame.mixed` |
| reusable extracted mathematics | one finite positive-part fixed-point theorem in `GameTheory.Math` |
| import boundary | stable Stochastic excludes Analysis; Analysis.Stochastic owns the fixed-point dependency |

The sibling's 1,443-line proof depends directly on four legacy roots.  The
successor proof instead represents stationary choices by the existing product
of standard simplices, represents statewise auxiliary play as an ordinary
`UtilityGame`, and uses the existing payoff polynomial for continuity.  The
only general lemma missing from current owners was the positive-part algebra
that turns a Nash adjustment fixed point plus zero weighted gain into
nonpositive gains.

## Kill condition

Reject promotion if the theorem requires changing the stable stochastic
carrier, storing discount or finiteness, adding a second probability,
equilibrium, or fixed-point stack, importing infinite-path measure theory,
using raw profile updates or user-visible transports, depending on Lean 4.32.0
behavior, or broadening stable imports into Analysis.

No kill condition fired.  Finiteness and boundedness remain theorem-local, and
the stable `GameTheory.Stochastic` root cannot reach the new certificate or
existence theorem.

## Result and consequences

`GameTheory.Stochastic.OneStep` owns the stationary Bellman certificate, and
`GameTheory.Analysis.Stochastic.Fink` owns its finite general-sum existence
theorem. The certificate's strategic half is canonical mixed Nash in each
actual one-step game. Its outcome records joint action and next state; its
realized utility is the normalized stage payoff plus discounted continuation
value. Consequently, constructing the game does not require a total expected
continuation payoff at every joint action. The predicate needs no finite state
space and allows an unrelated joint action to have undefined utility, while
an undefined unilateral deviation prevents equilibrium (EXP-138).

A guarded pure-play expectation identity recovers the scalar auxiliary
coefficients used by the finite fixed-point proof. Finite states and actions
remain local to its compactness and continuity arguments.
`GameTheory.Math.PositivePartFixedPoint` owns
the independently reusable algebraic lemma.  The analytic stochastic root
exports Fink and Shapley side by side; the stable stochastic root excludes
project Analysis and the analytic fixed-point dependency.

This result does not prove optimality against arbitrary infinite-history
strategies and does not prove uniform-equilibrium existence.  Those questions
retain their separate infinite-play and vanishing-discount gates.
