import GameTheory.Finite.BimatrixComplementarityCorrectness
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The complementary decoding accepts tied equilibria, excludes the artificial
zero source, and recovers signed games after a positive payoff shift. -/

namespace GameTheory.Tests.BimatrixComplementarity

open GameTheory.Finite
open GameTheory.Math.LinearComplementarity

private def ones : Fin 2 → Fin 2 → ℤ := fun _ _ => 1
private def zeroGame : Fin 2 → Fin 2 → ℤ := fun _ _ => 0
private def mixed : BimatrixCertificate 2 2 := ⟨![1, 1], ![1, 1], 2, 2, 2, 2⟩

example : IsSolution (fun _ => 1) (bimatrixComplementaryMatrix ones ones)
    (bimatrixComplementaryPoint mixed.rowWeights mixed.colWeights 2 2) ∧
    bimatrixComplementaryPoint mixed.rowWeights mixed.colWeights 2 2 ≠ 0 := by
  exact mixed.complementarySolution_of_valid ones ones (by decide)
    (by intro _ _; norm_num [ones]) (by intro _ _; norm_num [ones])

-- The fully degenerate original game is decoded with zero certified utilities.
example : ((complementaryNashCertificate ![1, 1] ![1, 1] 2 2).shiftPayoffs (-1) (-1)).Valid
    zeroGame zeroGame := by decide

-- Zero is a genuine complementary solution but cannot supply normalized strategies.
example : IsSolution (fun _ => 1) (bimatrixComplementaryMatrix ones ones)
    (bimatrixComplementaryPoint ![0, 0] ![0, 0] 2 2) := by
  have hzero : bimatrixComplementaryPoint ![0, 0] ![0, 0] 2 2 = (fun _ => 0) := by
    funext i
    cases i with
    | inl i => fin_cases i <;> norm_num [bimatrixComplementaryPoint]
    | inr j => fin_cases j <;> norm_num [bimatrixComplementaryPoint]
  rw [hzero]
  exact (isSolution_zero_iff (fun _ => (1 : ℚ))
    (bimatrixComplementaryMatrix ones ones)).mpr (by intro _; norm_num)

example : ¬ (complementaryNashCertificate ![0, 0] ![0, 0] 2 2).Valid ones ones := by decide

-- With only one nonzero block the remaining unit slack violates complementarity.
example : ¬ IsSolution (fun _ => 1) (bimatrixComplementaryMatrix ones ones)
    (bimatrixComplementaryPoint ![1, 0] ![0, 0] 2 2) := by
  intro h
  have hz := h.complementary (Sum.inl 0)
  norm_num [slack, bimatrixComplementaryPoint, bimatrixComplementaryMatrix,
    Fintype.sum_sum_type, Fin.sum_univ_two] at hz

private def negativeRow : Fin 1 → Fin 2 → ℤ := fun _ => ![-2, -3]
private def negativeColumn : Fin 1 → Fin 2 → ℤ := fun _ => ![-4, -5]

-- Check the rational inequalities directly with unequal scaling denominators.
example : IsSolution (fun _ => 1)
    (bimatrixComplementaryMatrix (fun i j => negativeRow i j + 9)
      (fun i j => negativeColumn i j + 9))
    (bimatrixComplementaryPoint ![1] ![1, 0] 5 7) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro k <;> cases k with
  | inl i =>
    fin_cases i
    norm_num [bimatrixComplementaryPoint, slack,
      bimatrixComplementaryMatrix, negativeRow, negativeColumn,
      Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
  | inr j =>
    fin_cases j <;> norm_num [bimatrixComplementaryPoint, slack,
      bimatrixComplementaryMatrix, negativeRow, negativeColumn,
      Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]

-- Independent rectangular signed tables are recovered by undoing the constant shift.
example : ((complementaryNashCertificate ![1] ![1, 0] 5 7).shiftPayoffs (-9) (-9)).Valid
    negativeRow negativeColumn := by decide

end GameTheory.Tests.BimatrixComplementarity
