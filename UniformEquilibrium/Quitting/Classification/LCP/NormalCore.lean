/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# The recursively normal-player principal matrix

Solan--Solan do not apply their standard Q-matrix theorem to the full player
set.  Starting with all players, they repeatedly delete a receiver `i` unless
some currently retained sole quitter `j` gives `i` a nonpositive normalized
payoff.  The normal core is the intersection of all finite layers.

This file formalizes that recursion directly and defines the exact principal
matrix used by the non-Q theorem.  It is deliberately separate from the full
normalized matrix used by the AGKRS Q-bar theorem.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Recursive normality layers `I₀ = I` and
`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, M i j ≤ 0}`. -/
def normalLayer (M : ι → ι → ℝ) : ℕ → Finset ι
  | 0 => Finset.univ
  | n + 1 =>
      (normalLayer M n).filter fun i =>
        ∃ j ∈ normalLayer M n, M i j ≤ 0

@[simp] theorem normalLayer_zero (M : ι → ι → ℝ) :
    normalLayer M 0 = Finset.univ := rfl

@[simp] theorem mem_normalLayer_succ
    (M : ι → ι → ℝ) (n : ℕ) (i : ι) :
    i ∈ normalLayer M (n + 1) ↔
      i ∈ normalLayer M n ∧
        ∃ j ∈ normalLayer M n, M i j ≤ 0 := by
  simp [normalLayer]

/-- The normality layers form a decreasing sequence. -/
theorem normalLayer_succ_subset
    (M : ι → ι → ℝ) (n : ℕ) :
    normalLayer M (n + 1) ⊆ normalLayer M n := by
  intro i hi
  exact (mem_normalLayer_succ M n i).mp hi |>.1

/-- The source's normal-player set `I* = ⋂ₙ Iₙ`. -/
def normalCore (M : ι → ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ n : ℕ, i ∈ normalLayer M n

@[simp] theorem mem_normalCore
    (M : ι → ι → ℝ) (i : ι) :
    i ∈ normalCore M ↔ ∀ n : ℕ, i ∈ normalLayer M n := by
  classical
  simp [normalCore]

/-- The exact principal matrix on recursively normal players. -/
def normalPlayerMatrix (M : ι → ι → ℝ) :
    normalCore M → normalCore M → ℝ :=
  principalMatrix M (normalCore M)

/-- Game-facing normal-player matrix, built after the playerwise solo
normalization. -/
def normalizedNormalPlayerMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalCore (normalizedSoloMatrix reward) →
      normalCore (normalizedSoloMatrix reward) → ℝ :=
  normalPlayerMatrix (normalizedSoloMatrix reward)

/-- A nonempty normal core is exactly the source theorem's first side
condition. -/
def HasNormalPlayers (M : ι → ι → ℝ) : Prop :=
  (normalCore M).Nonempty

/-- The all-abnormal simple stationary branch. -/
def AllPlayersAbnormal (M : ι → ι → ℝ) : Prop :=
  normalCore M = ∅

/-- Failure of nonemptiness is equivalent to the all-abnormal branch. -/
theorem allPlayersAbnormal_iff_not_hasNormalPlayers
    (M : ι → ι → ℝ) :
    AllPlayersAbnormal M ↔ ¬HasNormalPlayers M := by
  unfold AllPlayersAbnormal HasNormalPlayers
  constructor
  · intro hempty hnonempty
    rw [hempty] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  · intro h
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact h ⟨i, hi⟩

end QuittingLCPClassification
end GameTheory
