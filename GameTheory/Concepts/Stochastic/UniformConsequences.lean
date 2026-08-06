/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformTailWidth
import GameTheory.Concepts.Stochastic.UniformTailWidthObstruction
import GameTheory.Concepts.Stochastic.UniformBoundedWork
import GameTheory.Concepts.Stochastic.UniformAsymptoticPayoffEquivalence
import GameTheory.Concepts.Stochastic.UniformExpectedPotentialShaping
import GameTheory.Concepts.Stochastic.TransitionPerturbationDiscontinuity

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


