/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic
import GameTheory.Concepts.Stochastic.QuittingWeightedProjectiveLasso

/-!
# Support-witness uniform-equilibrium route

Public umbrella for the witness-retaining quitting-game compiler.

The route has three entry points.

* `QuittingSupportWitnessPathCompiler` consumes an infinite path with
  support-local approximate optimality, continuation-by-continuation
  individual rationality, and divergent total absorption.
* `QuittingSupportWitnessPeriodic` converts a finite periodic witness cycle
  with one positive-absorption phase into precisely such an infinite path.
* `QuittingWeightedProjectiveLasso` corrects a finite projective cycle whose
  survival-weighted Bellman seam is small relative to survival-weighted real
  absorption, uniformly over every cyclic rotation.  The corrected cycle
  yields a divergent support-rational path and hence a uniform payoff.

The principal quantitative conclusions are the path and cycle versions of the
`3ε` theorem, the weighted projective-lasso correction theorem, and
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

This umbrella is independent of `QuittingReducedCapConjecture`: the latter is
a separate, still-open all-player truncated-ledger producer route.
`QuittingRankOneCrossing` is also separate.  It records an abstract stochastic
alternative for situations where support witnesses have been forgotten, but
is not used by the deterministic support-witness compiler.

The projective-lasso layer is a compiler, not the arbitrary-game producer.
The missing producer still consists of analytic packet extraction,
resolved-chart construction and arc lifting, semantic Farkas decoding, and a
rotation-uniform relative-return theorem.  The exact boundary and derivations
are documented in `docs/uniform-equilibrium/ProjectiveLassoProducer.md`.
-/
