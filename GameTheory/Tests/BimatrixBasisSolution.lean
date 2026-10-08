import GameTheory.Finite.BimatrixBasisSolution
import Mathlib.Data.Fin.VecNotation

/-! The zero source and a positive complementary terminal basis.
The terminal chooses both payoff columns of the one-action game; its ambient
slack coordinates vanish while both payoff coordinates equal one.
-/

namespace GameTheory.Tests.BimatrixBasisSolution

open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary
open GameTheory.Math.PerturbedDictionary

private def allOnes : Fin 1 → Fin 1 → ℤ := fun _ _ => 1
private def payoffVariables : Finset (BimatrixVariable 1 1) :=
  Finset.univ.image (fun i : Fin 2 => toLex (i, true))

private theorem payoffVariables_card : payoffVariables.card = 2 := by decide

private theorem payoffEnumeration : (fun i : Fin 2 => toLex (i, true)) =
    payoffVariables.orderEmbOfFin payoffVariables_card := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro i j hij
    exact Prod.Lex.left _ _ hij

private def swapMatrix : Matrix (Fin 2) (Fin 2) ℚ := ![![0, 1], ![1, 0]]

private theorem terminalMatrix :
    basisMatrix (bimatrixBasisColumns allOnes allOnes) payoffVariables payoffVariables_card =
      swapMatrix := by
  ext i j
  change bimatrixBasisColumns allOnes allOnes i
    (payoffVariables.orderEmbOfFin payoffVariables_card j) = swapMatrix i j
  rw [← congrFun payoffEnumeration j]
  simp only [bimatrixBasisColumns, ofLex_toLex, ↓reduceIte]
  fin_cases i <;> fin_cases j <;> decide

private theorem swap_inverse : swapMatrix⁻¹ = swapMatrix := by
  apply Matrix.inv_eq_left_inv
  ext i j
  change (∑ k, swapMatrix i k * swapMatrix k j) = (if i = j then 1 else 0)
  fin_cases i <;> fin_cases j <;> norm_num [swapMatrix, Fin.sum_univ_two]

private theorem swap_feasible : IsFeasible (bimatrixBasisColumns allOnes allOnes)
    (fun _ => 1) payoffVariables payoffVariables_card := by
  unfold IsFeasible
  rw [terminalMatrix]
  constructor
  · rw [Matrix.det_fin_two]
    norm_num [swapMatrix]
  · intro i
    refine ⟨0, ?_, ?_⟩
    · intro j hj
      exact (Fin.not_lt_zero j hj).elim
    · change 0 < dictionaryCoefficients swapMatrix (fun _ => 1) i 0
      rw [coefficient_zero, swap_inverse]
      fin_cases i <;> norm_num [swapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def terminal : BimatrixBasis allOnes allOnes :=
  ⟨payoffVariables, payoffVariables_card, swap_feasible⟩

private theorem terminal_complementary : ComplementaryLabels.IsComplementary terminal.nonbasic := by
  intro i
  rw [terminal.mem_nonbasic, terminal.mem_nonbasic]
  change toLex (i, false) ∉ payoffVariables ↔ ¬toLex (i, true) ∉ payoffVariables
  simp [payoffVariables]

example : GameTheory.Math.LinearComplementarity.IsSolution (fun _ => 1)
    (bimatrixComplementaryMatrix allOnes allOnes) terminal.payoffPoint :=
  terminal.payoffPoint_isSolution terminal_complementary

example : terminal.payoffPoint ≠ 0 := by
  intro hz
  have he := congrArg BimatrixBasis.basic (terminal.payoffPoint_eq_zero_iff.mp hz)
  have hm : toLex ((0 : Fin 2), true) ∈ terminal.basic := by
    change toLex ((0 : Fin 2), true) ∈ payoffVariables
    simp [payoffVariables]
  rw [he] at hm
  simp [bimatrixSourceBasis, bimatrixSlackVariables] at hm

example : terminal.coordinates (toLex ((0 : Fin 2), true)) = 1 ∧
    terminal.coordinates (toLex ((1 : Fin 2), true)) = 1 := by
  have he (i : Fin 2) : terminal.coordinates (toLex (i, true)) =
      swapMatrix.mulVec (fun _ => 1) i := by
    change BasisCoordinates.inverseCoordinates _ _ payoffVariables payoffVariables_card
      (toLex (i, true)) = _
    rw [congrFun payoffEnumeration i, BasisCoordinates.inverseCoordinates_on_enumeration,
      terminalMatrix, swap_inverse]
  rw [he 0, he 1]
  norm_num [swapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- The artificial source has zero payoff coordinates, for arbitrary signed payoffs.
example (A B : Fin 1 → Fin 2 → ℤ) : (bimatrixSourceBasis A B).payoffPoint = 0 := by simp

-- The source characterization holds without requiring complementary labels first.
example (basis : BimatrixBasis allOnes allOnes) (hz : basis.payoffPoint = 0) :
    basis = bimatrixSourceBasis allOnes allOnes := basis.payoffPoint_eq_zero_iff.mp hz

private def rectangularOnes : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def degenerateVariables : Finset (BimatrixVariable 1 2) :=
  {toLex (0, true), toLex (1, false), toLex (2, true)}
private theorem degenerate_card : degenerateVariables.card = 3 := by decide
private def degenerateEnumeration : Fin 3 → BimatrixVariable 1 2 :=
  ![toLex (0, true), toLex (1, false), toLex (2, true)]

private theorem degenerateEnumeration_eq : degenerateEnumeration =
    degenerateVariables.orderEmbOfFin degenerate_card := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    fin_cases i <;> decide
  · unfold StrictMono
    decide

private def degenerateMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 0, 1], ![1, 1, 0], ![1, 0, 0]]
private def degenerateInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 0, 1], ![0, 1, -1], ![1, 0, 0]]

private theorem degenerate_basisMatrix : basisMatrix
    (bimatrixBasisColumns rectangularOnes rectangularOnes) degenerateVariables degenerate_card =
      degenerateMatrix := by
  ext i j
  change bimatrixBasisColumns rectangularOnes rectangularOnes i
    (degenerateVariables.orderEmbOfFin degenerate_card j) = degenerateMatrix i j
  rw [← congrFun degenerateEnumeration_eq j]
  fin_cases i <;> fin_cases j <;> decide

private theorem degenerate_inverse : degenerateMatrix⁻¹ = degenerateInverse := by
  apply Matrix.inv_eq_left_inv
  ext i j
  change (∑ k, degenerateInverse i k * degenerateMatrix k j) = (if i = j then 1 else 0)
  fin_cases i <;> fin_cases j <;>
    norm_num [degenerateMatrix, degenerateInverse, Fin.sum_univ_three]

private theorem degenerate_feasible : IsFeasible
    (bimatrixBasisColumns rectangularOnes rectangularOnes) (fun _ => 1)
    degenerateVariables degenerate_card := by
  unfold IsFeasible
  rw [degenerate_basisMatrix]
  constructor
  · rw [Matrix.det_fin_three]
    norm_num [degenerateMatrix]
  · intro i
    fin_cases i
    · refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
      change 0 < dictionaryCoefficients degenerateMatrix (fun _ => 1) 0 0
      rw [coefficient_zero, degenerate_inverse]
      norm_num [degenerateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · refine ⟨2, ?_, ?_⟩
      · intro j hj
        change 0 = dictionaryCoefficients degenerateMatrix (fun _ => 1) 1 j
        fin_cases j
        · change 0 = dictionaryCoefficients degenerateMatrix (fun _ => 1) 1 0
          rw [coefficient_zero, degenerate_inverse]
          norm_num [degenerateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · change 0 = degenerateMatrix⁻¹ 1 0
          rw [degenerate_inverse]
          rfl
        · norm_num at hj
        · norm_num at hj
      · change 0 < degenerateMatrix⁻¹ 1 1
        rw [degenerate_inverse]
        norm_num [degenerateInverse]
    · refine ⟨0, fun j hj => (Fin.not_lt_zero j hj).elim, ?_⟩
      change 0 < dictionaryCoefficients degenerateMatrix (fun _ => 1) 2 0
      rw [coefficient_zero, degenerate_inverse]
      norm_num [degenerateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private def degenerateTerminal : BimatrixBasis rectangularOnes rectangularOnes :=
  ⟨degenerateVariables, degenerate_card, degenerate_feasible⟩

private theorem degenerate_complementary :
    ComplementaryLabels.IsComplementary degenerateTerminal.nonbasic := by
  intro i
  rw [degenerateTerminal.mem_nonbasic, degenerateTerminal.mem_nonbasic]
  change toLex (i, false) ∉ degenerateVariables ↔ ¬toLex (i, true) ∉ degenerateVariables
  fin_cases i <;> decide

-- A fully degenerate rectangular terminal still decodes to a complementary solution.
example : GameTheory.Math.LinearComplementarity.IsSolution (fun _ => 1)
    (bimatrixComplementaryMatrix rectangularOnes rectangularOnes) degenerateTerminal.payoffPoint :=
  degenerateTerminal.payoffPoint_isSolution degenerate_complementary

-- Its basic slack has zero constant coordinate and strictly positive symbolic coefficients.
example : degenerateTerminal.coordinates (toLex ((1 : Fin 3), false)) = 0 := by
  change BasisCoordinates.inverseCoordinates _ _ degenerateVariables degenerate_card
    (degenerateEnumeration 1) = 0
  rw [congrFun degenerateEnumeration_eq 1, BasisCoordinates.inverseCoordinates_on_enumeration,
    degenerate_basisMatrix, degenerate_inverse]
  norm_num [degenerateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

example : degenerateTerminal.payoffPoint ≠ 0 := by
  intro hz
  have he := congrArg BimatrixBasis.basic (degenerateTerminal.payoffPoint_eq_zero_iff.mp hz)
  have hm : toLex ((0 : Fin 3), true) ∈ degenerateTerminal.basic := by
    change toLex ((0 : Fin 3), true) ∈ degenerateVariables
    decide
  rw [he] at hm
  simp [bimatrixSourceBasis, bimatrixSlackVariables] at hm

end GameTheory.Tests.BimatrixBasisSolution
