/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPathCompiler
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic
import GameTheory.Concepts.Stochastic.QuittingProjectiveLasso
import Math.FinitePivotOrbit

/-!
# Support-witness uniform-equilibrium route

Public umbrella for the witness-retaining quitting-game compiler.

The route has three entry points.

* `QuittingSupportWitnessPathCompiler` consumes an infinite path with
  support-local approximate optimality, continuation-by-continuation
  individual rationality, and divergent total absorption.
* `QuittingSupportWitnessPeriodic` converts a finite periodic witness cycle
  with one positive-absorption phase into precisely such an infinite path.
* `QuittingProjectiveLasso` corrects a finite projective cycle whose Bellman
  seam is small relative to real absorption into an exact periodic witness
  cycle.  Charged lassos at every positive accuracy therefore imply a
  uniform-equilibrium payoff.

`Math.FinitePivotOrbit` formalizes the finite global recurrence step: once a
physical successor has been selected at every non-output projective cell, the
first `card Cell + 1` iterates either hit an output or contain a nonempty
lasso.

The principal quantitative conclusions are the path and cycle versions of the
`3ε` theorem, the projective-lasso correction theorem, and
`quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`.

This umbrella is independent of `QuittingReducedCapConjecture`: the latter is
a separate, still-open all-player truncated-ledger producer route.
`QuittingRankOneCrossing` is also separate.  It records an abstract stochastic
alternative for situations where support witnesses have been forgotten, but
is not used by the deterministic support-witness compiler.

The projective-lasso layer proves the complete recurrent consumer and the
finite pigeonhole step but does not claim the remaining local physical
pivot-completeness theorem.  The exact honesty boundary and the mathematical
derivation are documented in
`docs/uniform-equilibrium/ProjectiveLassoProducer.md`.
-/
