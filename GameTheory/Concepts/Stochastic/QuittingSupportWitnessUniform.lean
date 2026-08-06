/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic

/-!
# Support-witness uniform-equilibrium route

Public umbrella for the witness-retaining quitting-game compiler.

The route has two entry points.

* `QuittingSupportWitnessPathCompiler` consumes an infinite path with
  support-local approximate optimality, continuation-by-continuation
  individual rationality, and divergent total absorption.
* `QuittingSupportWitnessPeriodic` converts a finite periodic witness cycle
  with one positive-absorption phase into precisely such an infinite path.

The principal quantitative conclusions are the path and cycle versions of the
`3ε` theorem, together with
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

This umbrella is independent of `QuittingReducedCapConjecture`: the latter is
a separate, still-open all-player truncated-ledger producer route.
`QuittingRankOneCrossing` is also separate.  It records an abstract stochastic
alternative for situations where support witnesses have been forgotten, but
is not used by the deterministic support-witness compiler.
-/
