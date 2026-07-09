/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Theorems.Minimax
import GameTheory.Theorems.CorrelatedEqExistence

/-!
# GameTheory.Theorems.Tests

Compilation validation entrypoint for terminal theorem modules.
-/

namespace GameTheory.Theorems.Tests

open Math.Probability

noncomputable section

/-- A two-player one-strategy zero-sum kernel game. -/
abbrev trivialZeroSumGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ => PUnit) (fun _ _ => 0)

local instance trivialZeroSumGame_strategyFinite (i : Fin 2) :
    Finite (trivialZeroSumGame.Strategy i) := by
  change Finite PUnit
  infer_instance

local instance trivialZeroSumGame_strategyNonempty (i : Fin 2) :
    Nonempty (trivialZeroSumGame.Strategy i) := by
  change Nonempty PUnit
  infer_instance

local instance trivialZeroSumGame_outcomeFinite :
    Finite trivialZeroSumGame.Outcome := by
  change Finite (∀ _ : Fin 2, PUnit)
  infer_instance

theorem trivialZeroSumGame_isZeroSum : trivialZeroSumGame.IsZeroSum := by
  intro σ
  rw [Fin.sum_univ_two]
  change (0 : ℝ) + 0 = 0
  norm_num

example :
    ∃ (v : ℝ) (σ : KernelGame.Profile trivialZeroSumGame.mixedExtension),
      trivialZeroSumGame.mixedExtension.IsNash σ ∧
      trivialZeroSumGame.mixedExtension.eu σ 0 = v ∧
      (∀ s₁, trivialZeroSumGame.mixedExtension.eu (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, trivialZeroSumGame.mixedExtension.eu (Function.update σ 0 s₀) 0 ≤ v) :=
  trivialZeroSumGame.von_neumann_minimax trivialZeroSumGame_isZeroSum

example :
    ∃ μ : PMF (KernelGame.Profile trivialZeroSumGame),
      trivialZeroSumGame.IsCorrelatedEq μ :=
  KernelGame.correlatedEq_exists trivialZeroSumGame

example :
    ∃ μ : PMF (KernelGame.Profile trivialZeroSumGame),
      trivialZeroSumGame.IsCoarseCorrelatedEq μ :=
  KernelGame.coarseCorrelatedEq_exists trivialZeroSumGame

end

end GameTheory.Theorems.Tests
