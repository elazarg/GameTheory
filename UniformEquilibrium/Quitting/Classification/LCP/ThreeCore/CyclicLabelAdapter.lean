/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ

/-!
# Cyclic coordinates for a three-element corrected core

This is the relabeling adapter between the coordinate-free corrected core and
the explicit directed three-cycle used by the ideal singleton lasso.
-/

noncomputable section

namespace GameTheory
namespace ThreeCoreCyclicLabelAdapter

open QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming

abbrev Player := Fin 3

private def swapOneTwoFun (i : Player) : Player :=
  if i = 0 then 0 else if i = 1 then 2 else 1

private def swapOneTwo : Player ≃ Player where
  toFun := swapOneTwoFun
  invFun := swapOneTwoFun
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] private theorem swapOneTwo_zero : swapOneTwo 0 = 0 := rfl
@[simp] private theorem swapOneTwo_one : swapOneTwo 1 = 2 := rfl
@[simp] private theorem swapOneTwo_two : swapOneTwo 2 = 1 := rfl
@[simp] private theorem swapOneTwo_symm_zero : swapOneTwo.symm 0 = 0 := rfl
@[simp] private theorem swapOneTwo_symm_one : swapOneTwo.symm 1 = 2 := rfl
@[simp] private theorem swapOneTwo_symm_two : swapOneTwo.symm 2 = 1 := rfl

private theorem forward_reindex_of_reverse
    (M : Player → Player → ℝ) (h : ReverseOrientation M) :
    ForwardOrientation (reindexMatrix swapOneTwo M) := by
  rcases h with ⟨h01, h02, h10, h12, h20, h21⟩
  exact ⟨by simpa [reindexMatrix] using h02,
    by simpa [reindexMatrix] using h01,
    by simpa [reindexMatrix] using h20,
    by simpa [reindexMatrix] using h21,
    by simpa [reindexMatrix] using h10,
    by simpa [reindexMatrix] using h12⟩

private theorem eq_directedCycleMatrix_of_forward
    (M : Player → Player → ℝ) (hdiag : ∀ i, M i i = 0) :
    M = directedCycleMatrix (-M 0 1) (M 0 2) (M 1 0)
      (-M 1 2) (-M 2 0) (M 2 1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [directedCycleMatrix, hdiag]

private theorem cycleGap_parameters
    (M : Player → Player → ℝ) :
    cycleGap (-M 0 1) (M 0 2) (M 1 0)
        (-M 1 2) (-M 2 0) (M 2 1) =
      cycleDeterminant M := by
  simp [cycleGap, cycleDeterminant]
  ring

/-- A three-coordinate standard-Q, nonhomogeneous zero-diagonal matrix can
always be relabeled into the explicit positive-parameter directed-cycle form
with positive cycle gap. -/
theorem exists_directedCycle_labeling
    {alpha : Type} [Fintype alpha]
    (M : alpha → alpha → ℝ) (hcard : Fintype.card alpha = 3)
    (hdiag : ∀ i, M i i = 0)
    (hQ : IsStandardQMatrix M)
    (hhom : ¬HasHomogeneousSimplexSolution M) :
    ∃ (label : alpha ≃ Player) (a b c d e f : ℝ),
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      0 < cycleGap a b c d e f ∧
      reindexMatrix label M = directedCycleMatrix a b c d e f := by
  obtain ⟨label, horient, hdet⟩ :=
    (standardQ_and_noHomogeneous_iff_exists_cyclic_labeling
      M hcard hdiag).1 ⟨hQ, hhom⟩
  let N : Player → Player → ℝ := reindexMatrix label M
  have hdiagN : ∀ i, N i i = 0 := by
    intro i
    simp [N, reindexMatrix, hdiag]
  rcases horient with hforward | hreverse
  · refine ⟨label, -N 0 1, N 0 2, N 1 0, -N 1 2, -N 2 0, N 2 1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact neg_pos.mpr hforward.1
    · exact hforward.2.1
    · exact hforward.2.2.1
    · exact neg_pos.mpr hforward.2.2.2.1
    · exact neg_pos.mpr hforward.2.2.2.2.1
    · exact hforward.2.2.2.2.2
    · rw [cycleGap_parameters]
      exact hdet
    · exact eq_directedCycleMatrix_of_forward N hdiagN
  · let label' : alpha ≃ Player := label.trans swapOneTwo
    let N' : Player → Player → ℝ := reindexMatrix swapOneTwo N
    have hforward' : ForwardOrientation N' :=
      forward_reindex_of_reverse N hreverse
    have hdiagN' : ∀ i, N' i i = 0 := by
      intro i
      simp [N', reindexMatrix, hdiagN]
    have hdet' : 0 < cycleDeterminant N' := by
      dsimp [N', N]
      simp [cycleDeterminant, reindexMatrix] at hdet ⊢
      ring_nf at hdet ⊢
      exact hdet
    have hlabel : reindexMatrix label' M = N' := by
      funext i j
      simp [label', N', N, reindexMatrix]
    refine ⟨label', -N' 0 1, N' 0 2, N' 1 0, -N' 1 2,
      -N' 2 0, N' 2 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact neg_pos.mpr hforward'.1
    · exact hforward'.2.1
    · exact hforward'.2.2.1
    · exact neg_pos.mpr hforward'.2.2.2.1
    · exact neg_pos.mpr hforward'.2.2.2.2.1
    · exact hforward'.2.2.2.2.2
    · rw [cycleGap_parameters]
      exact hdet'
    · rw [hlabel]
      exact eq_directedCycleMatrix_of_forward N' hdiagN'

end ThreeCoreCyclicLabelAdapter
end GameTheory
