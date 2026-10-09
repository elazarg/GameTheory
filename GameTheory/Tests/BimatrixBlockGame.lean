import GameTheory.Finite.BimatrixBlockGame
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Matching-block equilibrium controls include nonuniform block masses and
unsupported individual actions, despite full block support. -/
namespace GameTheory.Tests.BimatrixBlockGame
open GameTheory.Finite GameTheory.Finite.BimatrixBlockGame
open scoped BigOperators

/-- No perturbation forces exact uniformity for every valid certificate. -/
example (c : BimatrixCertificate 4 4)
    (hc : c.Valid (matchingBlockPayoff (k := 2) 5 (fun _ _ => 0))
      (matchingBlockPayoff (k := 2) (-5) (fun _ _ => 0))) (i : Fin 2) :
    blockMass c.rowWeights c.rowDenominator i = 1 / 2 ∧
      blockMass c.colWeights c.colDenominator i = 1 / 2 := by
  have h := (blockMass_uniform (k := 2) 5 0 (fun _ _ => 0) (fun _ _ => 0) c hc
    (by intros; exact ⟨le_rfl, le_rfl⟩) (by intros; exact ⟨le_rfl, le_rfl⟩) (by norm_num)).2 i
  norm_num only [Int.cast_zero, zero_div, Nat.cast_ofNat, abs_le, neg_zero] at h
  constructor <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

private def rowPerturb (i _j : Fin 4) : ℤ := if pairedBlock (k := 2) i = 1 then 1 else 0
private def colPerturb (_i j : Fin 4) : ℤ := if pairedBlock (k := 2) j = 1 then 1 else 0
private def skewCertificate : BimatrixCertificate 4 4 where
  rowWeights i := ![0, 2, 3, 0] i
  colWeights i := ![3, 0, 0, 2] i
  rowDenominator := 5
  colDenominator := 5
  rowUtilityNumerator := 15
  colUtilityNumerator := -10

private theorem skew_valid : skewCertificate.Valid
    (matchingBlockPayoff (k := 2) 5 rowPerturb)
    (matchingBlockPayoff (k := 2) (-5) colPerturb) := by decide

-- The strict dominance scale applies, although one action of every pair is unsupported.
example :
    (∀ i, 0 < blockMass (k := 2) skewCertificate.rowWeights skewCertificate.rowDenominator i ∧
      0 < blockMass (k := 2) skewCertificate.colWeights skewCertificate.colDenominator i) ∧
    ∀ i, |blockMass (k := 2) skewCertificate.rowWeights skewCertificate.rowDenominator i - 1 / 2| ≤
      (1 : ℚ) / 5 ∧
      |blockMass (k := 2) skewCertificate.colWeights skewCertificate.colDenominator i - 1 / 2| ≤
        (1 : ℚ) / 5 := by
  exact blockMass_uniform (k := 2) 5 1 rowPerturb colPerturb skewCertificate skew_valid
    (by intro i j; unfold rowPerturb; split <;> norm_num)
    (by intro i j; unfold colPerturb; split <;> norm_num) (by norm_num)

example : skewCertificate.rowWeights 0 = 0 ∧ skewCertificate.colWeights 1 = 0 ∧
    blockMass (k := 2) skewCertificate.rowWeights skewCertificate.rowDenominator 0 = (2 : ℚ) / 5 ∧
    blockMass (k := 2) skewCertificate.rowWeights skewCertificate.rowDenominator 1 = (3 : ℚ) / 5 ∧
    blockMass (k := 2) skewCertificate.colWeights skewCertificate.colDenominator 0 = (3 : ℚ) / 5 ∧
    blockMass (k := 2) skewCertificate.colWeights skewCertificate.colDenominator 1 =
      (2 : ℚ) / 5 := by
  norm_num [skewCertificate, blockMass, Fin.sum_univ_two, finProdFinEquiv]

-- Without a dominant matching baseline, individual blocks can be unsupported.
private def boundaryPerturb (i _j : Fin 4) : ℤ := if pairedBlock (k := 2) i = 0 then 1 else 0
private def boundaryCertificate : BimatrixCertificate 4 4 where
  rowWeights i := if i = 0 then 1 else 0
  colWeights i := if i = 2 then 1 else 0
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := 1
  colUtilityNumerator := 0

example : boundaryCertificate.Valid
    (matchingBlockPayoff (k := 2) 1 boundaryPerturb)
    (matchingBlockPayoff (k := 2) (-1) (fun _ _ => 0)) := by decide

example : blockMass (k := 2) boundaryCertificate.rowWeights
      boundaryCertificate.rowDenominator 1 = 0 ∧
    blockMass (k := 2) boundaryCertificate.colWeights
      boundaryCertificate.colDenominator 0 = 0 ∧ ¬ ((2 : ℤ) * 1 < 1) := by
  norm_num [boundaryCertificate, blockMass, Fin.sum_univ_two, finProdFinEquiv]
end GameTheory.Tests.BimatrixBlockGame
