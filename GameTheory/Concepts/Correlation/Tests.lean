/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.ZeroSum.ConstantSumCounterexamples

/-!
# Correlation Concept Tests

Compilation tests for correlated-equilibrium bridges.
-/

namespace GameTheory.Concepts.Correlation.Tests

open GameTheory.KernelGame
open GameTheory.KernelGame.ThreePlayerZeroSumCoordination
open Math.Probability

noncomputable section

example : game.IsCorrelatedEq (PMF.pure highProfile) :=
  nash_pure_isCorrelatedEq highProfile_isNash

example : game.IsCoarseCorrelatedEq (PMF.pure highProfile) :=
  (nash_pure_isCorrelatedEq highProfile_isNash).toCoarseCorrelatedEq

end

end GameTheory.Concepts.Correlation.Tests
