/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Theorems.Minimax
import GameTheory.Theorems.CorrelatedEqExistence
import GameTheory.Theorems.Zermelo

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

/-! ## Zermelo worked example -/

/-- Information structure for a one-player, one-move game. -/
abbrev oneMoveInfo : EFG.InfoStructure where
  n := 1
  Infoset := fun _ => Unit
  arity := fun _ _ => 2
  arity_pos := fun _ _ => by omega

/-- A concrete finite perfect-information game with one binary move. -/
noncomputable abbrev oneMoveGame : EFG.EFGGame where
  inf := oneMoveInfo
  Outcome := Fin 2
  tree := .decision (p := (0 : Fin 1)) () fun action => .terminal action
  utility := fun outcome _ => outcome.val

theorem oneMoveGame_isPerfectInfo : EFG.IsPerfectInfo oneMoveGame.tree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  rcases EFG.ReachBy_decision_inv hr₁ with hroot₁ | ⟨action₁, _rest₁, _hstep₁, htail₁⟩
  · rcases hroot₁ with ⟨hh₁, _hp₁, _hI₁, hn₁⟩
    rcases EFG.ReachBy_decision_inv hr₂ with hroot₂ |
      ⟨action₂, _rest₂, _hstep₂, htail₂⟩
    · rcases hroot₂ with ⟨hh₂, _hp₂, _hI₂, hn₂⟩
      exact ⟨hh₁.trans hh₂.symm, hn₁.symm.trans hn₂⟩
    · fin_cases action₂ <;> exact False.elim (EFG.ReachBy_terminal_absurd htail₂)
  · fin_cases action₁ <;> exact False.elim (EFG.ReachBy_terminal_absurd htail₁)

/-- `zermelo` supplies a pure SPE for the concrete one-move game. -/
example : ∃ σ : EFG.PureProfile oneMoveGame.inf,
    oneMoveGame.IsSubgamePerfectEq σ :=
  EFG.zermelo oneMoveGame oneMoveGame_isPerfectInfo

end

end GameTheory.Theorems.Tests
