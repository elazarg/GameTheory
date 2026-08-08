/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# The recursively normal-player principal matrix

Solan--Solan's displayed recursion omits the condition that the witness quitter
`j` differ from the receiver `i`:

`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, M i j ≤ 0}`.

Taken literally after their standing zero-diagonal normalization, this recursion
never removes a player: one may always choose `j = i`.  This file formalizes
that printed recursion and proves the collapse.  It then defines the corrected
**distinct-witness** recursion required by the adjacent prose, by the claim that
`I₁` is Simon's normal-player set, and by later proof steps that explicitly
extract `j ≠ i` from membership in `I₁`.

The LCP gate uses the corrected recursion.  The source theorem is correspondingly
kept behind the explicitly named repaired interface in `SourceInterfaces.lean`;
the printed omission is not silently treated as a proved transport.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The recursion exactly as displayed in Solan--Solan, before repairing its
missing distinctness condition. -/
def printedNormalLayer (M : ι → ι → ℝ) : ℕ → Finset ι
  | 0 => Finset.univ
  | n + 1 =>
      (printedNormalLayer M n).filter fun i =>
        ∃ j ∈ printedNormalLayer M n, M i j ≤ 0

/-- With a nonpositive diagonal, the printed recursion retains every player at
every layer. -/
theorem printedNormalLayer_eq_univ_of_diagonal_nonpos
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i ≤ 0) :
    ∀ n : ℕ, printedNormalLayer M n = Finset.univ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      ext i
      simp [printedNormalLayer, ih, hdiag i]

/-- The literal intersection of the printed layers. -/
def printedNormalCore (M : ι → ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ n : ℕ, i ∈ printedNormalLayer M n

/-- The printed core is the full player set whenever the diagonal is
nonpositive. -/
theorem printedNormalCore_eq_univ_of_diagonal_nonpos
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i ≤ 0) :
    printedNormalCore M = Finset.univ := by
  classical
  ext i
  simp [printedNormalCore,
    printedNormalLayer_eq_univ_of_diagonal_nonpos M hdiag]

/-- In particular, the source's normalized matrix makes the literal printed
normal core degenerate. -/
theorem printedNormalCore_normalized_eq_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    printedNormalCore (normalizedSoloMatrix reward) = Finset.univ := by
  apply printedNormalCore_eq_univ_of_diagonal_nonpos
  intro i
  simp

/-- Corrected recursive normality layers `I₀ = I` and
`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, j ≠ i ∧ M i j ≤ 0}`. -/
def normalLayer (M : ι → ι → ℝ) : ℕ → Finset ι
  | 0 => Finset.univ
  | n + 1 =>
      (normalLayer M n).filter fun i =>
        ∃ j ∈ normalLayer M n, j ≠ i ∧ M i j ≤ 0

@[simp] theorem normalLayer_zero (M : ι → ι → ℝ) :
    normalLayer M 0 = Finset.univ := rfl

@[simp] theorem mem_normalLayer_succ
    (M : ι → ι → ℝ) (n : ℕ) (i : ι) :
    i ∈ normalLayer M (n + 1) ↔
      i ∈ normalLayer M n ∧
        ∃ j ∈ normalLayer M n, j ≠ i ∧ M i j ≤ 0 := by
  simp [normalLayer]

/-- The corrected normality layers form a decreasing sequence. -/
theorem normalLayer_succ_subset
    (M : ι → ι → ℝ) (n : ℕ) :
    normalLayer M (n + 1) ⊆ normalLayer M n := by
  intro i hi
  exact (mem_normalLayer_succ M n i).mp hi |>.1

/-- The corrected normal-player set `I* = ⋂ₙ Iₙ`. -/
def normalCore (M : ι → ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ n : ℕ, i ∈ normalLayer M n

@[simp] theorem mem_normalCore
    (M : ι → ι → ℝ) (i : ι) :
    i ∈ normalCore M ↔ ∀ n : ℕ, i ∈ normalLayer M n := by
  classical
  simp [normalCore]

/-- The exact principal matrix on corrected recursively normal players. -/
def normalPlayerMatrix (M : ι → ι → ℝ) :
    normalCore M → normalCore M → ℝ :=
  principalMatrix M (normalCore M)

/-- Game-facing corrected normal-player matrix, built after the playerwise solo
normalization. -/
def normalizedNormalPlayerMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalCore (normalizedSoloMatrix reward) →
      normalCore (normalizedSoloMatrix reward) → ℝ :=
  normalPlayerMatrix (normalizedSoloMatrix reward)

/-- A nonempty corrected normal core is the intended source theorem's first
side condition. -/
def HasNormalPlayers (M : ι → ι → ℝ) : Prop :=
  (normalCore M).Nonempty

/-- The corrected all-abnormal simple stationary branch. -/
def AllPlayersAbnormal (M : ι → ι → ℝ) : Prop :=
  normalCore M = ∅

/-- Failure of corrected normal-core nonemptiness is equivalent to the
all-abnormal branch. -/
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
