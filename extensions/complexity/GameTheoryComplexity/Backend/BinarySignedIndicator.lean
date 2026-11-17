module

public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.BinarySignedAddition

@[expose] public section

/-! Signed scalar coefficients selected by a unary paired-action index. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

/-- Arguments are row-action ruler, positive input-block ruler and signed scalar coefficient. -/
def binarySignedIndicator (v : Fin 3 → List Bool) : List Bool :=
  if (v 0).length / 2 = (v 1).length ∧ (v 0).length % 2 = 1 then v 2 else []

@[fun_prop] theorem binarySignedIndicator_polyTime :
    ComputableInPolyTime binarySignedIndicator (encPi encBits) encBits := by
  have hrow : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hinput : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hscalar : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hinputLen := ComputableInPolyTime.length_bits_comp hinput
  have hhalf := (ComputableInPolyTime.unary_div_const 2).comp hrowLen
  have heq : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => decide ((v 0).length / 2 = (v 1).length))
      (encPi encBits) encBool :=
    ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
        (hhalf.tidy.prod hinputLen.tidy))
  have hmod := ComputableInPolyTime.unary_mod.comp (hrowLen.prod (.const 2))
  have hodd : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => decide ((v 0).length % 2 = 1))
      (encPi encBits) encBool :=
    ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hmod.tidy.prod (.const 1)))
  have hconditionAnd : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        decide ((v 0).length / 2 = (v 1).length) && decide ((v 0).length % 2 = 1))
      (encPi encBits) encBool :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.bool_and.comp (heq.tidy.prod hodd.tidy))
  have hcondition : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        decide ((v 0).length / 2 = (v 1).length ∧ (v 0).length % 2 = 1))
      (encPi encBits) encBool :=
    hconditionAnd.of_enc_eq (fun v => by simp)
  exact (hcondition.ite hscalar (.const [])).of_enc_eq (fun v => by
    simp [binarySignedIndicator, decide_eq_true_eq])

/-- Arbitrary missing or padded scalar words keep their existing signed interpretation. -/
theorem binarySignedIndicator_value (row input scalar : List Bool) :
    binarySignedValue (binarySignedIndicator ![row, input, scalar]) =
      if row.length / 2 = input.length ∧ row.length % 2 = 1
      then binarySignedValue scalar else 0 := by
  by_cases h : row.length / 2 = input.length ∧ row.length % 2 = 1 <;>
    simp [binarySignedIndicator, h, binarySignedValue, ofBits]

/-- Canonical paired indices select the exact positive-action coefficient. -/
theorem binarySignedIndicator_index {k : ℕ} (row input scalar : List Bool)
    (r : Fin (k * 2)) (a : Fin k) (hr : row.length = r.val) (ha : input.length = a.val) :
    binarySignedValue (binarySignedIndicator ![row, input, scalar]) =
      if r = finProdFinEquiv (a, 1) then binarySignedValue scalar else 0 := by
  rw [binarySignedIndicator_value, hr, ha]
  have he : (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r = finProdFinEquiv (a, 1) := by
    rw [Fin.ext_iff]
    change (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r.val = 1 + 2 * a.val
    omega
  simp only [he]

end GameTheory.Complexity.Backend
