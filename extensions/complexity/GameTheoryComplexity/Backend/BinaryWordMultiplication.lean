import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Exact unsigned multiplication by recursion on little-endian bit positions.
The output bound and polynomial-time certificate depend on word lengths, including
zero padding, rather than on the represented natural numbers. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

private def binaryMulZeroStep (v : Fin 3 → List Bool) : List Bool := false :: v 1

private def binaryMulOneStep (v : Fin 3 → List Bool) : List Bool :=
  binaryCertificateAdd ![false :: v 1, v 2]

/-- Multiply arbitrary unsigned little-endian words without iterating their values. -/
def binaryWordMul (x y : List Bool) : List Bool :=
  recNotation (fun _ : Fin 1 → List Bool => [])
    binaryMulZeroStep binaryMulOneStep x ![y]

@[simp] theorem binaryWordMul_nil (y : List Bool) : binaryWordMul [] y = [] := rfl

@[simp] theorem binaryWordMul_false (x y : List Bool) :
    binaryWordMul (false :: x) y = false :: binaryWordMul x y := rfl

@[simp] theorem binaryWordMul_true (x y : List Bool) :
    binaryWordMul (true :: x) y =
      binaryCertificateAdd ![false :: binaryWordMul x y, y] := rfl

/-- Multiplication is exact even for noncanonical words and unequal operand widths. -/
theorem binaryWordMul_value (x y : List Bool) :
    Nat.fromBitsLE (binaryWordMul x y) = Nat.fromBitsLE x * Nat.fromBitsLE y := by
  induction x with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons b x ih =>
    cases b <;> simp only [binaryWordMul_false, binaryWordMul_true,
      binaryCertificateAdd_value, Nat.fromBitsLE_cons, ih] <;> simp <;> ring

/-- A linear output bound certifies the bit-recursive multiplication machine. -/
theorem binaryWordMul_length (x y : List Bool) :
    (binaryWordMul x y).length ≤ y.length + 2 * x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    cases b
    · simp only [binaryWordMul_false, List.length_cons]
      omega
    · simp only [binaryWordMul_true, binaryCertificateAdd_length, List.length_cons]
      omega

/-- Multiplication has an actual Cobham certificate, bounded by binary input lengths. -/
theorem binaryWordMul_cobham : Cobham fun v : Fin 2 → List Bool =>
    binaryWordMul (v 0) (v 1) := by
  have hs : Cobham binaryMulZeroStep :=
    (Cobham.comp (.bit false) fun _ => Cobham.proj 1).of_eq fun _ => rfl
  have ha : Cobham binaryMulOneStep :=
    (Cobham.comp₂ binaryCertificateAdd_cobham hs (.proj 2)).of_eq fun _ => rfl
  have hj : Cobham fun v : Fin 2 → List Bool => v 1 ++ v 0 ++ v 0 :=
    Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 0)) (.proj 0)
  refine (Cobham.boundedRec Cobham.empty hs ha hj ?_).of_eq fun v => ?_
  · intro x v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    rw [hv]
    change (binaryWordMul x (v 0)).length ≤ _
    simpa only [Fin.cons_zero, Fin.cons_one, Matrix.cons_val_zero,
      List.length_append, two_mul, Nat.add_assoc] using
      binaryWordMul_length x (v 0)
  · congr 1
    ext i
    fin_cases i
    rfl

/-- The binary multiplication function is polynomial time at arity two. -/
theorem binaryWordMul_mem_FPn :
    FPn (fun v : Fin 2 → List Bool => binaryWordMul (v 0) (v 1)) :=
  cobham_iff_FPn.mp binaryWordMul_cobham

/-- Multiplication composes with any two polynomial-time word producers. -/
theorem binaryWordMulFn_mem_FP {x y : List Bool → List Bool}
    (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => binaryWordMul (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact (Cobham.comp₂ binaryWordMul_cobham
    (FP_subset_CobhamFP hx) (FP_subset_CobhamFP hy)).of_eq fun _ => rfl

end GameTheory.Complexity.Backend
