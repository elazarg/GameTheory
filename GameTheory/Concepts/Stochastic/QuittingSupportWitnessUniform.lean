/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic
import GameTheory.Concepts.Stochastic.QuittingProjectiveLassoWeighted

/-!
# Support-witness uniform-equilibrium route

Public umbrella for the witness-retaining quitting-game compilers.

The route has three certificate entry points.

* `QuittingSupportWitnessPathCompiler` consumes an infinite path with
  support-local approximate optimality, continuation-by-continuation
  individual rationality, and divergent total absorption.
* `QuittingSupportWitnessPeriodic` converts a finite periodic witness cycle
  with one positive-absorption phase into precisely such an infinite path.
* `QuittingProjectiveLasso` and `QuittingProjectiveLassoWeighted` correct a
  finite cyclic packet whose Bellman seam is small relative to real absorption
  into an exact periodic witness cycle.  Charged lassos at every positive
  accuracy therefore imply a uniform-equilibrium payoff.

The principal quantitative conclusions are the path and cycle versions of the
`3ε` theorem, the pointwise and weighted projective-lasso correction theorems,
and
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

This umbrella is independent of `QuittingReducedCapConjecture`: the latter is
a separate, still-open all-player truncated-ledger producer route.
`QuittingRankOneCrossing` is also separate.  It records an abstract stochastic
alternative for situations where support witnesses have been forgotten, but
is not used by the deterministic support-witness compiler.

The projective-lasso layer is a complete certificate consumer.  It does not
construct a lasso from an arbitrary vanishing-discount branch.  In particular,
finite repetition of a projective-cell label does not imply a relative return
or charged seam.  The producer boundary is documented in
`docs/uniform-equilibrium/ProjectiveLassoProducer.md`; the broader projective
entry point is `QuittingProjectiveLassoAll.lean`.
-/
