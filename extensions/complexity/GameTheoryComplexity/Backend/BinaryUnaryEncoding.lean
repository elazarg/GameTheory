import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Polynomial-time conversion of length rulers to unsigned binary words. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Encode a ruler length as a little-endian unsigned binary word. -/
def binaryLengthWord (r : List Bool) : List Bool :=
  recNotation (fun _ : Fin 0 → List Bool => [])
    (fun v : Fin 2 → List Bool => binaryCertificateAdd ![v 1, [true]])
    (fun v : Fin 2 → List Bool => binaryCertificateAdd ![v 1, [true]]) r Fin.elim0

theorem binaryLengthWord_value (r : List Bool) :
    Nat.fromBitsLE (binaryLengthWord r) = r.length := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    simp only [binaryLengthWord, recNotation_cons, Bool.cond_self]
    change Nat.fromBitsLE (binaryCertificateAdd ![binaryLengthWord r, [true]]) = _
    rw [binaryCertificateAdd_value, ih]
    simp [Nat.fromBitsLE, Nat.fromBits]

theorem binaryLengthWord_length (r : List Bool) : (binaryLengthWord r).length ≤ r.length + 1 := by
  induction r with
  | nil => simp [binaryLengthWord, recNotation]
  | cons b r ih =>
    simp only [binaryLengthWord, recNotation_cons, Bool.cond_self]
    change (binaryCertificateAdd ![binaryLengthWord r, [true]]).length ≤ _
    have h := binaryCertificateAdd_length (binaryLengthWord r) [true]
    simp only [List.length_cons, List.length_nil] at h ⊢
    omega

theorem binaryLengthWord_cobham : Cobham fun v : Fin 1 → List Bool => binaryLengthWord (v 0) := by
  have hs : Cobham fun v : Fin 2 → List Bool => binaryCertificateAdd ![v 1, [true]] :=
    Cobham.comp₂ binaryCertificateAdd_cobham (.proj 1) (Cobham.const [true])
  exact (Cobham.boundedRec Cobham.empty hs hs (appendFn (.proj 0) (Cobham.const [true]))
    (fun r p => by
      have hp : p = Fin.elim0 := by ext i; exact i.elim0
      rw [hp]
      simp only [Fin.cons_zero, List.length_append, List.length_singleton]
      exact binaryLengthWord_length r)).of_eq fun v => by
        congr 1
        ext i
        exact i.elim0

theorem binaryLengthWord_mem_FPn :
    FPn (fun v : Fin 1 → List Bool => binaryLengthWord (v 0)) :=
  cobham_iff_FPn.mp binaryLengthWord_cobham

end GameTheory.Complexity.Backend
