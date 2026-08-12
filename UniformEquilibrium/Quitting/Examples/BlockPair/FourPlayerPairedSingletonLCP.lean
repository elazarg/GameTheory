/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

/-!
# Singleton-matrix diagnostics for the paired-singleton family

The common paired-singleton comparison matrix has full corrected normal core
and no homogeneous simplex-LCP solution.  These facts depend only on the four
singleton rows, hence apply to every completion of the family.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open QuittingLCPClassification Math.LinearProgramming

/-- A fixed distinct negative witness in each row. -/
def negativeWitness : Player → Player := ![2, 2, 0, 0]

theorem negativeWitness_ne (who : Player) : negativeWitness who ≠ who := by
  fin_cases who <;> decide

@[simp] theorem pairedSingletonMatrix_negativeWitness (who : Player) :
    pairedSingletonMatrix who (negativeWitness who) = -1 := by
  fin_cases who <;> rfl

/-- Every player survives every corrected normal-layer deletion. -/
theorem pairedSingletonMatrix_mem_normalLayer (n : ℕ) (who : Player) :
    who ∈ normalLayer pairedSingletonMatrix n := by
  induction n generalizing who with
  | zero => simp [normalLayer]
  | succ n ih =>
      apply (mem_normalLayer_succ pairedSingletonMatrix n who).2
      exact ⟨ih who, negativeWitness who, ih (negativeWitness who),
        negativeWitness_ne who, by simp⟩

theorem pairedSingletonMatrix_mem_normalCore (who : Player) :
    who ∈ normalCore pairedSingletonMatrix :=
  (mem_normalCore pairedSingletonMatrix who).2
    (fun n => pairedSingletonMatrix_mem_normalLayer n who)

/-- The iterated corrected normal core is all four players. -/
theorem pairedSingletonMatrix_normalCore_eq_univ :
    normalCore pairedSingletonMatrix = Finset.univ := by
  apply Finset.eq_univ_of_forall
  exact pairedSingletonMatrix_mem_normalCore

/-! ## Textbook Q property

After sorting the two coordinates inside each paired block, three
complementary supports suffice: `{0,1,3}`, `{1,2,3}`, and the full support.
The following constructors give the exact solutions on those cones.
-/

private def standardSolution013 (q : Player → ℝ)
    (hz0 : 0 ≤ q 0 - q 1 + 3 * q 3)
    (hz1 : 0 ≤ -q 0 + q 1 + 3 * q 3)
    (hz3 : 0 ≤ q 0 + q 1 + 3 * q 3)
    (hw2 : 0 ≤ 3 * q 0 + 3 * q 1 + 2 * q 2 + 7 * q 3) :
    StandardLCPSolution pairedSingletonMatrix q where
  weight := ![
    (q 0 - q 1 + 3 * q 3) / 6,
    (-q 0 + q 1 + 3 * q 3) / 6,
    0,
    (q 0 + q 1 + 3 * q 3) / 2]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [pairedSingletonMatrix, Fin.sum_univ_succ] <;> linarith
  complementary := by
    intro i
    fin_cases i <;>
      norm_num [pairedSingletonMatrix, Fin.sum_univ_succ] <;>
      ring_nf <;> simp

private def standardSolution123 (q : Player → ℝ)
    (hz1 : 0 ≤ 3 * q 1 + q 2 + q 3)
    (hz2 : 0 ≤ 3 * q 1 + q 2 - q 3)
    (hz3 : 0 ≤ 3 * q 1 - q 2 + q 3)
    (hw0 : 0 ≤ 2 * q 0 + 7 * q 1 + 3 * q 2 + 3 * q 3) :
    StandardLCPSolution pairedSingletonMatrix q where
  weight := ![
    0,
    (3 * q 1 + q 2 + q 3) / 2,
    (3 * q 1 + q 2 - q 3) / 6,
    (3 * q 1 - q 2 + q 3) / 6]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [pairedSingletonMatrix, Fin.sum_univ_succ] <;> linarith
  complementary := by
    intro i
    fin_cases i <;>
      norm_num [pairedSingletonMatrix, Fin.sum_univ_succ] <;>
      ring_nf <;> simp

private def standardSolutionFull (q : Player → ℝ)
    (h0 : 2 * q 0 + 7 * q 1 + 3 * q 2 + 3 * q 3 ≤ 0)
    (h1 : 3 * q 0 + 3 * q 1 + 2 * q 2 + 7 * q 3 ≤ 0)
    (h01 : q 0 ≤ q 1) (h23 : q 2 ≤ q 3) :
    StandardLCPSolution pairedSingletonMatrix q where
  weight := ![
    -(2 * q 0 + 7 * q 1 + 3 * q 2 + 3 * q 3) / 15,
    -(7 * q 0 + 2 * q 1 + 3 * q 2 + 3 * q 3) / 15,
    -(3 * q 0 + 3 * q 1 + 2 * q 2 + 7 * q 3) / 15,
    -(3 * q 0 + 3 * q 1 + 7 * q 2 + 2 * q 3) / 15]
  weight_nonneg := by
    intro i
    fin_cases i <;> simp <;> linarith
  residual_nonneg := by
    intro i
    fin_cases i <;>
      simp [pairedSingletonMatrix, Fin.sum_univ_succ] <;> linarith
  complementary := by
    intro i
    fin_cases i <;>
      norm_num [pairedSingletonMatrix, Fin.sum_univ_succ] <;>
      ring_nf <;> simp

/-- In the chamber where the two coordinates of each pair are ordered,
three explicit complementary cones cover every right-hand side. -/
private theorem pairedSingletonMatrix_hasStandardLCPSolution_of_ordered
    (q : Player → ℝ) (h01 : q 0 ≤ q 1) (h23 : q 2 ≤ q 3) :
    HasStandardLCPSolution pairedSingletonMatrix q := by
  let H := 2 * q 0 + 7 * q 1 + 3 * q 2 + 3 * q 3
  let K := 3 * q 0 + 3 * q 1 + 2 * q 2 + 7 * q 3
  let L := 3 * q 1 + q 2 - q 3
  by_cases hH : 0 ≤ H
  · by_cases hL : 0 ≤ L
    · exact ⟨standardSolution123 q
        (by dsimp [H, L] at *; linarith)
        (by simpa [L] using hL)
        (by dsimp [H, L] at *; linarith)
        (by simpa [H] using hH)⟩
    · exact ⟨standardSolution013 q
        (by dsimp [H, K, L] at *; linarith)
        (by dsimp [H, K, L] at *; linarith)
        (by dsimp [H, K, L] at *; linarith)
        (by dsimp [H, K, L] at *; linarith)⟩
  · have hH' : H ≤ 0 := le_of_not_ge hH
    by_cases hK : K ≤ 0
    · exact ⟨standardSolutionFull q
        (by simpa [H] using hH') (by simpa [K] using hK) h01 h23⟩
    · exact ⟨standardSolution013 q
        (by dsimp [H, K] at *; linarith)
        (by dsimp [H, K] at *; linarith)
        (by dsimp [H, K] at *; linarith)
        (by dsimp [H, K] at *; linarith)⟩

def swapFirstPair : Player ≃ Player := Equiv.swap 0 1

def swapSecondPair : Player ≃ Player := Equiv.swap 2 3

def swapBothPairs : Player ≃ Player :=
  swapFirstPair.trans swapSecondPair

private theorem pairedSingletonMatrix_reindex_swapFirst :
    reindexMatrix swapFirstPair pairedSingletonMatrix = pairedSingletonMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem pairedSingletonMatrix_reindex_swapSecond :
    reindexMatrix swapSecondPair pairedSingletonMatrix = pairedSingletonMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem pairedSingletonMatrix_reindex_swapBoth :
    reindexMatrix swapBothPairs pairedSingletonMatrix = pairedSingletonMatrix := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem hasStandardLCPSolution_of_reindexed
    (e : Player ≃ Player)
    (hM : reindexMatrix e pairedSingletonMatrix = pairedSingletonMatrix)
    (q : Player → ℝ)
    (h : HasStandardLCPSolution pairedSingletonMatrix (fun i => q (e i))) :
    HasStandardLCPSolution pairedSingletonMatrix q := by
  obtain ⟨solution⟩ := h
  have transported := solution.reindex e
  rw [hM] at transported
  exact ⟨transported⟩

/-- The paired singleton-comparison matrix is a textbook standard
`Q`-matrix. -/
theorem pairedSingletonMatrix_standardQ :
    IsStandardQMatrix pairedSingletonMatrix := by
  intro q
  by_cases h01 : q 0 ≤ q 1
  · by_cases h23 : q 2 ≤ q 3
    · exact pairedSingletonMatrix_hasStandardLCPSolution_of_ordered q h01 h23
    · apply hasStandardLCPSolution_of_reindexed swapSecondPair
        pairedSingletonMatrix_reindex_swapSecond q
      apply pairedSingletonMatrix_hasStandardLCPSolution_of_ordered
      · simpa [swapSecondPair, Equiv.swap_apply_of_ne_of_ne] using h01
      · simpa [swapSecondPair, Equiv.swap_apply_of_ne_of_ne] using le_of_not_ge h23
  · by_cases h23 : q 2 ≤ q 3
    · apply hasStandardLCPSolution_of_reindexed swapFirstPair
        pairedSingletonMatrix_reindex_swapFirst q
      apply pairedSingletonMatrix_hasStandardLCPSolution_of_ordered
      · simpa [swapFirstPair, Equiv.swap_apply_of_ne_of_ne] using le_of_not_ge h01
      · simpa [swapFirstPair, Equiv.swap_apply_of_ne_of_ne] using h23
    · apply hasStandardLCPSolution_of_reindexed swapBothPairs
        pairedSingletonMatrix_reindex_swapBoth q
      apply pairedSingletonMatrix_hasStandardLCPSolution_of_ordered
      · simpa [swapBothPairs, swapFirstPair, swapSecondPair,
          Equiv.swap_apply_of_ne_of_ne] using le_of_not_ge h01
      · simpa [swapBothPairs, swapFirstPair, swapSecondPair,
          Equiv.swap_apply_of_ne_of_ne] using le_of_not_ge h23

/-- The paired matrix has no homogeneous simplex-LCP solution. -/
theorem pairedSingletonMatrix_noHomogeneous :
    ¬HasHomogeneousSimplexSolution pairedSingletonMatrix := by
  rintro ⟨weight, hresidual, hcomplementary⟩
  let x : ℝ := weight 0
  let y : ℝ := weight 1
  let z : ℝ := weight 2
  let t : ℝ := weight 3
  have hx : 0 ≤ x := weight.property.1 0
  have hy : 0 ≤ y := weight.property.1 1
  have hz : 0 ≤ z := weight.property.1 2
  have ht : 0 ≤ t := weight.property.1 3
  have htotal : x + y + z + t = 1 := by
    have h := weight.property.2
    have hsum : (∑ i : Player, weight.val i) =
        weight.val 0 + (weight.val 1 + (weight.val 2 + weight.val 3)) := by
      simp [Fin.sum_univ_succ]
    rw [hsum] at h
    change x + (y + (z + t)) = 1 at h
    linarith
  have hr0 : singletonLCPResidual pairedSingletonMatrix weight 0 =
      3 * y - z - t := by
    dsimp only [x, y, z, t]
    simp [singletonLCPResidual, wsum, dotProduct, pairedSingletonMatrix,
      Fin.sum_univ_succ]
    ring
  have hr1 : singletonLCPResidual pairedSingletonMatrix weight 1 =
      3 * x - z - t := by
    dsimp only [x, y, z, t]
    simp [singletonLCPResidual, wsum, dotProduct, pairedSingletonMatrix,
      Fin.sum_univ_succ]
    ring
  have hr2 : singletonLCPResidual pairedSingletonMatrix weight 2 =
      -x - y + 3 * t := by
    dsimp only [x, y, z, t]
    simp [singletonLCPResidual, wsum, dotProduct, pairedSingletonMatrix,
      Fin.sum_univ_succ]
    ring
  have hr3 : singletonLCPResidual pairedSingletonMatrix weight 3 =
      -x - y + 3 * z := by
    dsimp only [x, y, z, t]
    simp [singletonLCPResidual, wsum, dotProduct, pairedSingletonMatrix,
      Fin.sum_univ_succ]
    ring
  have hR0 := hresidual 0
  have hR1 := hresidual 1
  have hR2 := hresidual 2
  have hR3 := hresidual 3
  rw [hr0] at hR0
  rw [hr1] at hR1
  rw [hr2] at hR2
  rw [hr3] at hR3
  have hC0 := hcomplementary 0
  have hC1 := hcomplementary 1
  have hC2 := hcomplementary 2
  have hC3 := hcomplementary 3
  rw [hr0] at hC0
  rw [hr1] at hC1
  rw [hr2] at hC2
  rw [hr3] at hC3
  change x * (3 * y - z - t) = 0 at hC0
  change y * (3 * x - z - t) = 0 at hC1
  change z * (-x - y + 3 * t) = 0 at hC2
  change t * (-x - y + 3 * z) = 0 at hC3
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · nlinarith
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have hC1zero : 3 * x - z - t = 0 :=
        (mul_eq_zero.mp hC1).resolve_left hy0
      nlinarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hC0zero : 3 * y - z - t = 0 :=
      (mul_eq_zero.mp hC0).resolve_left hx0
    by_cases hy0 : y = 0
    · nlinarith
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have hC1zero : 3 * x - z - t = 0 :=
        (mul_eq_zero.mp hC1).resolve_left hy0
      have hxy : x = y := by nlinarith
      have hzt : z + t = 3 * x := by nlinarith
      have hCsum : z * t = x ^ 2 := by
        nlinarith [hC2, hC3]
      have hzLower : 2 * x / 3 ≤ z := by nlinarith
      have htLower : 2 * x / 3 ≤ t := by nlinarith
      have hproduct : 0 ≤ (z - 2 * x / 3) * (t - 2 * x / 3) :=
        mul_nonneg (sub_nonneg.mpr hzLower) (sub_nonneg.mpr htLower)
      nlinarith [sq_pos_of_pos hxpos]

end FourPlayerPairedSingleton
end GameTheory
