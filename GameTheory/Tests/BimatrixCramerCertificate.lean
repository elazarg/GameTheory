import GameTheory.Finite.BimatrixCramerCertificate
import Mathlib.Data.Fin.VecNotation

/-! A negative-determinant terminal preserves its endpoint through payoff unshifting. -/

namespace GameTheory.Tests.BimatrixCramerCertificate

open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary
open GameTheory.Math.PerturbedDictionary

private def originalA : Fin 1 → Fin 1 → ℤ := fun _ _ => -3
private def originalB : Fin 1 → Fin 1 → ℤ := fun _ _ => -5
private def shiftedA : Fin 1 → Fin 1 → ℤ := fun i j => originalA i j + 9
private def shiftedB : Fin 1 → Fin 1 → ℤ := fun i j => originalB i j + 9
private def payoffVariables : Finset (BimatrixVariable 1 1) :=
  Finset.univ.image (fun i : Fin 2 => toLex (i, true))
private theorem payoff_card : payoffVariables.card = 2 := by decide
private theorem payoffEnumeration : (fun i : Fin 2 => toLex (i, true)) =
    payoffVariables.orderEmbOfFin payoff_card := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro i j hij
    exact Prod.Lex.left _ _ hij

private def terminalMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 6; 4, 0]
private def terminalInverse : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1 / 4; 1 / 6, 0]
private theorem basisMatrix_eq :
    basisMatrix (bimatrixBasisColumns shiftedA shiftedB) payoffVariables payoff_card =
      terminalMatrix := by
  ext i j
  change bimatrixBasisColumns shiftedA shiftedB i
    (payoffVariables.orderEmbOfFin payoff_card j) = terminalMatrix i j
  rw [← congrFun payoffEnumeration j]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem terminal_inverse : terminalMatrix⁻¹ = terminalInverse := by
  apply Matrix.inv_eq_left_inv
  ext i j
  change (∑ k, terminalInverse i k * terminalMatrix k j) = (if i = j then 1 else 0)
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalMatrix, terminalInverse, Fin.sum_univ_two]

private theorem terminal_feasible : IsFeasible (bimatrixBasisColumns shiftedA shiftedB)
    (fun _ => 1) payoffVariables payoff_card := by
  unfold IsFeasible
  rw [basisMatrix_eq]
  constructor
  · rw [Matrix.det_fin_two]
    norm_num [terminalMatrix]
  · intro i
    refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
    change 0 < dictionaryCoefficients terminalMatrix (fun _ => 1) i 0
    rw [coefficient_zero, terminal_inverse]
    fin_cases i <;> norm_num [terminalInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def terminal : BimatrixBasis shiftedA shiftedB :=
  ⟨payoffVariables, payoff_card, terminal_feasible⟩

private theorem terminal_complementary : ComplementaryLabels.IsComplementary terminal.nonbasic := by
  intro i
  rw [terminal.mem_nonbasic, terminal.mem_nonbasic]
  change toLex (i, false) ∉ payoffVariables ↔ ¬toLex (i, true) ∉ payoffVariables
  simp [payoffVariables]

private theorem terminal_not_source : terminal ≠ bimatrixSourceBasis shiftedA shiftedB := by
  intro he
  have hm : toLex ((0 : Fin 2), true) ∈ terminal.basic := by
    change toLex ((0 : Fin 2), true) ∈ payoffVariables
    decide
  rw [he] at hm
  simp [bimatrixSourceBasis, bimatrixSlackVariables] at hm

private theorem integerMatrix_eq : terminal.integerMatrix = (!![0, 6; 4, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  change bimatrixIntegerColumns shiftedA shiftedB i
    (payoffVariables.orderEmbOfFin payoff_card j) = _
  rw [← congrFun payoffEnumeration j]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem determinant_eq : terminal.integerMatrix.det = -24 := by
  rw [integerMatrix_eq, Matrix.det_fin_two]
  norm_num

private theorem denominator_eq : IntegerCramerEncoding.denominator terminal.integerMatrix = 24 := by
  rw [IntegerCramerEncoding.denominator, determinant_eq]
  decide

private theorem weights : terminal.cramerWeight (toLex ((0 : Fin 2), true)) = 6 ∧
    terminal.cramerWeight (toLex ((1 : Fin 2), true)) = 4 := by
  have he (i : Fin 2) : terminal.coordinates (toLex (i, true)) =
      terminalInverse.mulVec (fun _ => 1) i := by
    change BasisCoordinates.inverseCoordinates _ _ payoffVariables payoff_card
      (toLex (i, true)) = _
    rw [congrFun payoffEnumeration i, BasisCoordinates.inverseCoordinates_on_enumeration,
      basisMatrix_eq, terminal_inverse]
  have h0 := terminal.cramerWeight_decode (toLex ((0 : Fin 2), true))
  have h1 := terminal.cramerWeight_decode (toLex ((1 : Fin 2), true))
  rw [denominator_eq, he 0] at h0
  rw [denominator_eq, he 1] at h1
  norm_num [terminalInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  constructor
  · have h : (terminal.cramerWeight (toLex ((0 : Fin 2), true)) : ℚ) = 6 := by linarith
    exact_mod_cast h
  · have h : (terminal.cramerWeight (toLex ((1 : Fin 2), true)) : ℚ) = 4 := by linarith
    exact_mod_cast h

example : terminal.integerMatrix.det = -24 := determinant_eq
example : IntegerCramerEncoding.denominator terminal.integerMatrix = 24 := denominator_eq
example : (terminal.cramerCertificate 9 9).rowWeights 0 = 6 ∧
    (terminal.cramerCertificate 9 9).colWeights 0 = 4 ∧
    (terminal.cramerCertificate 9 9).rowDenominator = 6 ∧
    (terminal.cramerCertificate 9 9).colDenominator = 4 ∧
    (terminal.cramerCertificate 9 9).rowUtilityNumerator = -12 ∧
    (terminal.cramerCertificate 9 9).colUtilityNumerator = -30 := by
  have hrow : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) (.inl 0) = 0 := by decide
  have hcol : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) (.inr 0) = 1 := by decide
  norm_num [BimatrixBasis.cramerCertificate, complementaryNashCertificate,
    BimatrixCertificate.shiftPayoffs, Fin.sum_univ_one, hrow, hcol,
    weights.1, weights.2, IntegerCramerComputation.denominator_eq, denominator_eq]

example : bimatrixComplementaryPoint
      (fun i => terminal.cramerWeight (toLex (finSumFinEquiv (.inl i), true)))
      (fun j => terminal.cramerWeight (toLex (finSumFinEquiv (.inr j), true)))
      (IntegerCramerEncoding.denominator terminal.integerMatrix)
      (IntegerCramerEncoding.denominator terminal.integerMatrix) = terminal.payoffPoint :=
  terminal.cramerPoint_eq

example : (terminal.cramerCertificate 9 9).Valid originalA originalB ∧
    (terminal.cramerCertificate 9 9).FitsWidth (GameTheory.bimatrixCertificateWidth 1 1 3) := by
  exact shiftedCramerCertificate_valid_fitsWidth originalA originalB 3
    (by intro i j; norm_num [originalA]) (by intro i j; norm_num [originalB]) terminal
    terminal_complementary terminal_not_source

example : ¬((bimatrixSourceBasis shiftedA shiftedB).cramerCertificate 9 9).Valid
    originalA originalB := by decide +kernel

end GameTheory.Tests.BimatrixCramerCertificate
