/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.ConstantSumCounterexamples

/-!
# Zero-Sum Concept Tests

Compilation tests for zero-sum counterexample exports.
-/

namespace GameTheory.Concepts.ZeroSum.Tests

open GameTheory.KernelGame.ThreePlayerZeroSumCoordination

noncomputable section

example : game.IsZeroSum :=
  game_isZeroSum

example : game.IsNash lowProfile :=
  lowProfile_isNash

example : game.IsNash highProfile :=
  highProfile_isNash

example : game.eu lowProfile 0 ≠ game.eu highProfile 0 :=
  low_high_player_zero_payoffs_ne

example :
    ∃ (G : KernelGame (Fin 3)) (σ τ : KernelGame.Profile G),
      G.IsZeroSum ∧ G.IsNash σ ∧ G.IsNash τ ∧ G.eu σ 0 ≠ G.eu τ 0 :=
  exists_threePlayer_zeroSum_nash_payoff_not_unique

end

end GameTheory.Concepts.ZeroSum.Tests
