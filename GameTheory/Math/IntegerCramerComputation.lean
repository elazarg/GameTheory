import GameTheory.Math.TabulatedBirdDeterminant
import GameTheory.Math.IntegerCramerEncoding
import GameTheory.Math.BirdIterationBounds

/-! # Division-free computation of common-denominator Cramer fields

Materialized determinant stages avoid repeated evaluation of earlier entries.
The resulting integer fields agree with the canonical determinant encoding,
so existing decoding and output-size theorems apply unchanged.
-/

namespace GameTheory.Math.IntegerCramerComputation

variable {n : ℕ}

/-- Store a square integer matrix in row-major order. -/
def rowMajor (M : Matrix (Fin n) (Fin n) ℤ) : Array ℤ :=
  Array.ofFn fun k : Fin (n * n) => M k.divNat k.modNat

@[simp] theorem rowMajor_size (M : Matrix (Fin n) (Fin n) ℤ) :
    (rowMajor M).size = n * n := Array.size_ofFn

/-- Evaluate the determinant with materialized division-free stages. -/
def determinant (M : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  TabulatedBirdDeterminant.determinant n (rowMajor M)

theorem determinant_eq (M : Matrix (Fin n) (Fin n) ℤ) : determinant M = M.det := by
  unfold determinant
  rw [TabulatedBirdDeterminant.determinant_eq (rowMajor M) (rowMajor_size M)]
  exact congrArg Matrix.det (Matrix.ofArray_ofFn M)

/-- Every stored intermediate entry retains polynomial binary width. -/
theorem stages_bounds (M : Matrix (Fin n) (Fin n) ℤ) (h t : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (ht : t ≤ n) (i j : Fin n) :
    (BirdDet.get n (TabulatedBirdDeterminant.stages n (rowMajor M) t) i.val j.val).natAbs <
      2 ^ BirdIterationBounds.width n h := by
  rw [TabulatedBirdDeterminant.stages_get_eq_spec (rowMajor M) (rowMajor_size M),
    show Matrix.ofArray (rowMajor M) (rowMajor_size M) = M from Matrix.ofArray_ofFn M]
  exact BirdIterationBounds.stages_natAbs_lt_two_pow M h t hM ht i j

/-- Compute the shared positive scale of a nonsingular integer system. -/
def denominator (M : Matrix (Fin n) (Fin n) ℤ) : ℕ := (determinant M).natAbs

/-- Compute a sign-adjusted natural Cramer numerator. -/
def numerator (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) : ℕ :=
  (Int.sign (determinant M) * determinant (M.updateCol i b)).toNat

theorem denominator_eq (M : Matrix (Fin n) (Fin n) ℤ) :
    denominator M = IntegerCramerEncoding.denominator M := by
  rw [denominator, determinant_eq]
  rfl

theorem numerator_eq (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) :
    numerator M b i = IntegerCramerEncoding.numerator M b i := by
  rw [numerator, determinant_eq, determinant_eq]
  rfl

/-- Computed fields decode to the nonnegative solution of the original system. -/
theorem decode (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (hdet : M.det ≠ 0)
    (hz : ∀ i, 0 ≤ (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i)
    (i : Fin n) :
    (numerator M b i : ℚ) / (denominator M : ℚ) =
      (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (b j : ℚ)) i := by
  rw [numerator_eq, denominator_eq]
  exact IntegerCramerEncoding.decode M b hdet hz i

/-- Computation preserves the canonical output bounds, including the shared scale. -/
theorem fields_bounds (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hb : ∀ i, (b i).natAbs ≤ 2 ^ h)
    (hdet : M.det ≠ 0) (i : Fin n) :
    0 < denominator M ∧ denominator M < 2 ^ IntegerBasisBounds.width n h ∧
      numerator M b i < 2 ^ IntegerBasisBounds.width n h := by
  rw [denominator_eq, numerator_eq]
  exact ⟨IntegerCramerEncoding.denominator_pos M hdet,
    IntegerCramerEncoding.denominator_lt M h hM,
    IntegerCramerEncoding.numerator_lt M b h hM hb hdet i⟩

end GameTheory.Math.IntegerCramerComputation
