import GameTheory.Finite.BimatrixPath
import Mathlib.Data.Fin.VecNotation

/-! Source uniqueness, paired pivot operations and terminal extraction controls. -/
namespace GameTheory.Tests.BimatrixPath
open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary
open GameTheory.Math.PerturbedDictionary
private def allOnes : Fin 1 → Fin 1 → ℤ := fun _ _ => 1
private def source : BimatrixPathPort allOnes allOnes (0 : Fin 2) :=
  bimatrixSourcePort allOnes allOnes 0

example (port : BimatrixPathPort allOnes allOnes (0 : Fin 2))
    (h : port.node.basis = bimatrixSourceBasis allOnes allOnes) : port = source :=
  bimatrixSourcePort_unique port h

example : source.switch = source := bimatrixSourcePort_switch _ _ _

example : (source.pivot (by decide) (by decide)
    (by intro _ _; exact Int.zero_lt_one) (by intro _ _; exact Int.zero_lt_one)).pivot
    (by decide) (by decide) (by intro _ _; exact Int.zero_lt_one)
    (by intro _ _; exact Int.zero_lt_one) = source := source.pivot_pivot _ _ _ _

example : source.pivot (by decide) (by decide)
    (by intro _ _; exact Int.zero_lt_one) (by intro _ _; exact Int.zero_lt_one) ≠ source :=
  source.pivot_ne_self _ _ _ _

-- An internal node switches to the other variable at the same duplicated label.
example (port : BimatrixPathPort allOnes allOnes (0 : Fin 2))
    (h : (ofLex port.entering).1 ≠ 0) :
    ofLex port.switch.entering = ((ofLex port.entering).1, !(ofLex port.entering).2) := by
  simp only [BimatrixPathPort.switch, ofLex_toLex, ComplementaryPorts.switch, ite_eq_right h]

example (port : BimatrixPathPort allOnes allOnes (0 : Fin 2))
    (h : ¬ ComplementaryLabels.IsComplementary port.node.basis.nonbasic) :
    port.switch ≠ port := fun he => h (port.switch_eq_self_iff.mp he)

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

private def terminalPort : BimatrixPathPort allOnes allOnes (0 : Fin 2) where
  node := ⟨terminal, fun i _ => Or.inl ((terminal_complementary i).mpr (by
    rw [terminal.mem_nonbasic]
    change ¬ ¬ toLex (i, true) ∈ payoffVariables
    simp [payoffVariables]))⟩
  entering := toLex ((0 : Fin 2), false)
  permitted := ⟨by
    rw [terminal.mem_nonbasic]
    change toLex ((0 : Fin 2), false) ∉ payoffVariables
    simp [payoffVariables], Or.inl rfl⟩

private theorem terminalPort_fixed : terminalPort.switch = terminalPort :=
  terminalPort.switch_eq_self_iff.mpr terminal_complementary

private theorem terminalPort_non_source : terminalPort ≠ source := by
  intro h
  have hb := congrArg (fun p : BimatrixPathPort allOnes allOnes (0 : Fin 2) => p.node.basis.basic) h
  have hm : toLex ((0 : Fin 2), true) ∈ terminalPort.node.basis.basic := by
    change toLex ((0 : Fin 2), true) ∈ payoffVariables
    simp [payoffVariables]
  rw [hb] at hm
  simp [source, bimatrixSourcePort, bimatrixSourceNode, bimatrixSourceBasis,
    bimatrixSlackVariables] at hm

-- A concrete nonsource endpoint yields a nonzero unperturbed rational solution.
example : terminalPort.node.basis.payoffPoint ≠ 0 ∧
    LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix allOnes allOnes)
      terminalPort.node.basis.payoffPoint :=
  terminalPort.non_source_terminal_solution terminalPort_fixed terminalPort_non_source

end GameTheory.Tests.BimatrixPath
