/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

/-!
# Reverse consequences of uniform equilibrium

Production entry point for the reverse-consequence layer:

* arbitrarily thin uniform tail intervals;
* bounded-work / semantic ledger certificates; and
* discontinuity under transition-kernel perturbations.

The accompanying mathematical guide is
`docs/uniform-equilibrium/ReverseConsequences.md`.
-/

import GameTheory.Concepts.Stochastic.UniformTailWidth
import GameTheory.Concepts.Stochastic.UniformBoundedWork
import GameTheory.Concepts.Stochastic.TransitionPerturbationDiscontinuity
