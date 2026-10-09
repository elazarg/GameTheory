import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
import GameTheoryComplexity.Backend.BinarySignedAddition

/-! Signed scalar coefficients selected by a unary paired-action index. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Arguments are row-action ruler, positive input-block ruler and signed scalar coefficient. -/
def binarySignedIndicator (v : Fin 3 → List Bool) : List Bool :=
  caseBit₀ (andBit (binaryLengthParity (v 0))
    (lenEqFlag (binaryHalfRuler (v 0)) (v 1))) (v 2) []

theorem binarySignedIndicator_cobham : Cobham binarySignedIndicator :=
  Cobham.iteFn
    (Cobham.andFn
      (Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 => .proj 0)
      (lenEqFlag_mem
        (Cobham.comp binaryHalfRuler_cobham fun _ : Fin 1 => .proj 0) (.proj 1)))
    (.proj 2) (Cobham.const [])

theorem binarySignedIndicator_mem_FPn : FPn binarySignedIndicator :=
  cobham_iff_FPn.mp binarySignedIndicator_cobham

/-- Arbitrary missing or padded scalar words keep their existing signed interpretation. -/
theorem binarySignedIndicator_value (row input scalar : List Bool) :
    binarySignedValue (binarySignedIndicator ![row, input, scalar]) =
      if row.length / 2 = input.length ∧ row.length % 2 = 1
      then binarySignedValue scalar else 0 := by
  change binarySignedValue (caseBit₀ (andBit (binaryLengthParity row)
    (lenEqFlag (binaryHalfRuler row) input)) scalar []) = _
  rw [binaryLengthParity_value]
  rcases lenEqFlag_flag (binaryHalfRuler row) input with he | he
  · have hlen := (lenEqFlag_eq_true_iff _ _).mp he
    rw [binaryHalfRuler_length] at hlen
    rw [he]
    by_cases hp : row.length % 2 = 1
    · simp [hp, hlen, andBit, caseBit₀]
    · simp [hp, hlen, andBit, caseBit₀]
      rfl
  · have hlen : row.length / 2 ≠ input.length := by
      intro h
      have hx := (lenEqFlag_eq_true_iff (binaryHalfRuler row) input).mpr
        (by simpa only [binaryHalfRuler_length] using h)
      rw [he] at hx
      contradiction
    rw [he]
    by_cases hp : row.length % 2 = 1 <;> simp [hp, hlen, andBit, caseBit₀] <;> rfl

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
