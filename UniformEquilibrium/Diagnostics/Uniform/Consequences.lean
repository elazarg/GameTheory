/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Uniform.TailWidth
import UniformEquilibrium.Diagnostics.Uniform.TailWidthObstruction
import UniformEquilibrium.Diagnostics.Uniform.BoundedWork
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform.AsymptoticPayoffEquivalence
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform.ExpectedPotentialShaping
import UniformEquilibrium.Diagnostics.Uniform.TransitionPerturbationDiscontinuity

/-!
# Reverse consequences of uniform equilibrium

Production entry point for the reverse-consequence layer:

* arbitrarily thin uniform tail intervals and their positive obstruction;
* bounded-work / semantic ledger certificates;
* transfer under uniformly vanishing finite-average payoff changes;
* bounded expected-potential gauge invariance; and
* discontinuity under transition-kernel perturbations.

The accompanying mathematical guide is
`docs/uniform-equilibrium/ReverseConsequences.md`.
-/


