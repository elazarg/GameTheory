/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic
import GameTheory.Concepts.Stochastic.QuittingSignedProjectiveLasso

/-!
# Support-witness uniform-equilibrium route

Public umbrella for the witness-retaining quitting-game compiler.

The route has four compatible entry points.

* `QuittingSupportWitnessPathCompiler` consumes an infinite path with
  support-local approximate optimality, continuation-by-continuation
  individual rationality, and divergent total absorption.
* `QuittingSupportWitnessPeriodic` converts a finite periodic witness cycle
  with one positive-absorption phase into precisely such an infinite path.
* `QuittingSignedProjectiveLasso` corrects a finite projective cycle whose
  signed survival-weighted Bellman monodromy is small relative to one-turn
  real absorption, uniformly over every cyclic rotation.  Local seams may
  cancel within a turn.
* `QuittingWeightedProjectiveLasso` remains the stronger compatibility
  interface, bounding the survival-weighted sum of absolute seams and
  embedding into the signed compiler by the triangle inequality.

The principal quantitative conclusions are the path and cycle versions of the
`3ε` theorem, the signed and absolute projective-lasso correction theorems, and
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

This umbrella is independent of the truncated-ledger certificate route.  That
certificate remains sufficient, but is not a universal normal form: a solved
two-player zero-solo game lies outside it.
`QuittingRankOneCrossing` is also separate.  It records an abstract stochastic
alternative for situations where support witnesses have been forgotten, but
is not used by the deterministic support-witness compiler.

The projective-lasso layer is a compiler, not the arbitrary-game producer.
Matching analytic germs supply normalized singleton packets, but resolved
chart construction and arc lifting, semantic Farkas decoding, and a
rotation-uniform signed-monodromy theorem remain independent obligations.
-/
