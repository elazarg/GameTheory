import GameTheoryComplexity.Backend.BimatrixRawCircuit
import Mathlib.Tactic.FinCases

/-! An aliased OR gate with opposite inline negation flags is a tautology.
A nonuniform accepted certificate realizes it beside an affine false-input block. -/
namespace GameTheory.Complexity.Tests.BimatrixRawGate
open _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixGateProgram
open GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixBlockGame
open GameTheory.Complexity.Backend.BimatrixRawGate

def tautology : RawGate where
  op := .or
  input₀ := 0
  input₁ := 0
  negated₀ := true
  negated₁ := false

theorem tautology_wellFormed : tautology.WellFormedAt 2 := by decide

def program : Fin 2 → Gate 2 := fun i =>
  if i = 0 then ⟨fun _ => -2, .affine⟩ else gate tautology tautology_wellFormed

def certificate : BimatrixCertificate 4 4 where
  rowDenominator := 1996
  colDenominator := 2
  rowWeights := ![997, 0, 0, 999]
  colWeights := ![0, 1, 1, 0]
  rowUtilityNumerator := 1004
  colUtilityNumerator := -993008

theorem tautology_coefficients : ∀ r, coefficients tautology tautology_wellFormed r = 1 := by
  decide

theorem program_bound : ∀ i r, |(program i).coefficients r| ≤ 2 := by decide

theorem certificate_valid : certificate.Valid (rowPayoff 1000 4) (columnPayoff 1000 4 program) := by
  decide

theorem input_false : |(2 : ℚ) * value (k := 2) certificate 0 - 0| ≤ 0 := by
  norm_num [value, certificate, finProdFinEquiv]

theorem output_positive : 0 < signal certificate 4 program 1 := by
  have h := sign_eval tautology tautology_wellFormed certificate (by decide)
    certificate_valid.1 certificate_valid.2.2.1 program 1 rfl false false 0
    input_false input_false (by norm_num)
  exact h.1.mpr (by decide)

theorem output_full : value (k := 2) certificate 1 =
    blockMass (k := 2) certificate.rowWeights certificate.rowDenominator 1 := by
  have h := gate_value 1000 2 tautology tautology_wellFormed (by decide) program certificate
    certificate_valid (by decide) program_bound (by decide) 1 rfl false false 0
    input_false input_false (by norm_num)
  exact h

theorem output_error : |(2 : ℚ) * value (k := 2) certificate 1 - 1| ≤ 12 / 1000 := by
  have h := gate_output_error 1000 2 tautology tautology_wellFormed (by decide)
    program certificate certificate_valid (by decide) program_bound (by decide)
    1 rfl false false 0 input_false input_false (by norm_num)
  norm_num [tautology, RawGate.eval] at h ⊢
  exact h

theorem output_error_small : (12 / 1000 : ℚ) < 1 / 8 := by norm_num

theorem wholeCircuit_correct :
    RawCircuit.eval? [tautology] [false] = some true ∧
      |(2 : ℚ) * value (k := 2) certificate 1 - 1| ≤ 1 / 8 := by
  have hsize : [false].length + ([tautology] : RawCircuit).length ≤ 2 := by decide
  have hplace : ∀ t : Fin ([tautology] : RawCircuit).length,
      ∀ href : (([tautology] : RawCircuit).get t).WellFormedAt 2,
      program ⟨[false].length + t.val, by have ht := t.isLt; omega⟩ =
        gate (([tautology] : RawCircuit).get t) href := by
    intro t href
    fin_cases t
    rfl
  have hinput : ∀ j : Fin 2, ∀ hj : j.val < [false].length,
      |(2 : ℚ) * value certificate j - (if [false][j.val] then 1 else 0)| ≤ 1 / 8 := by
    intro j hj
    have hj0 : j = 0 := Fin.ext (by
      simp only [List.length_cons, List.length_nil] at hj
      omega)
    subst j
    norm_num [value, certificate, finProdFinEquiv]
  obtain ⟨bit, heval, hlast, herr⟩ :=
    GameTheory.Complexity.Backend.BimatrixRawCircuit.eval_correct 1000 2
      (by decide : 0 < 2) program certificate certificate_valid (by decide) program_bound
      (by decide) (1 / 8) (by norm_num) (by norm_num) [tautology] [false]
      (by decide) hsize hplace hinput
  have he : RawCircuit.eval? [tautology] [false] = some true := by decide
  have hb : bit = true := Option.some.inj (heval.symm.trans he)
  subst bit
  exact ⟨heval, herr⟩

end GameTheory.Complexity.Tests.BimatrixRawGate
