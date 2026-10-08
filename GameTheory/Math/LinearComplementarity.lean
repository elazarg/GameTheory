import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Basic

/-! Finite linear complementarity over an ordered field.

A solution has nonnegative coordinates and nonnegative affine slack, with each
coordinate complementary to its slack. This formulation is independent of games
and does not choose a pivot rule or assume a nondegenerate matrix.
-/

namespace GameTheory.Math.LinearComplementarity

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- Affine slack of a finite linear complementarity problem. -/
def slack (q : ι → K) (M : Matrix ι ι K) (z : ι → K) (i : ι) : K :=
  q i + ∑ j, M i j * z j

/-- Nonnegative coordinates and slack with coordinatewise complementarity. -/
def IsSolution (q : ι → K) (M : Matrix ι ι K) (z : ι → K) : Prop :=
  (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ slack q M z i) ∧
    ∀ i, z i * slack q M z i = 0

omit [IsStrictOrderedRing K] in
/-- Coordinatewise checking is equivalent to the global solution predicate. -/
theorem isSolution_iff_pointwise (q : ι → K) (M : Matrix ι ι K) (z : ι → K) :
    IsSolution q M z ↔ ∀ i,
      0 ≤ z i ∧ 0 ≤ slack q M z i ∧ z i * slack q M z i = 0 := by
  simp only [IsSolution, forall_and]

/-- Complementarity can equivalently be expressed by a zero coordinate or slack. -/
theorem isSolution_iff (q : ι → K) (M : Matrix ι ι K) (z : ι → K) :
    IsSolution q M z ↔
      (∀ i, 0 ≤ z i) ∧ (∀ i, 0 ≤ slack q M z i) ∧
        ∀ i, z i = 0 ∨ slack q M z i = 0 := by
  simp only [IsSolution, mul_eq_zero]

namespace IsSolution

variable {q : ι → K} {M : Matrix ι ι K} {z : ι → K}

omit [IsStrictOrderedRing K] in
theorem nonneg (h : IsSolution q M z) (i : ι) : 0 ≤ z i := h.1 i

omit [IsStrictOrderedRing K] in
theorem slack_nonneg (h : IsSolution q M z) (i : ι) : 0 ≤ slack q M z i :=
  h.2.1 i

omit [IsStrictOrderedRing K] in
theorem complementary (h : IsSolution q M z) (i : ι) :
    z i * slack q M z i = 0 := h.2.2 i

/-- Every positive coordinate has zero slack, including in degenerate problems. -/
theorem slack_eq_zero_of_pos (h : IsSolution q M z) {i : ι} (hi : 0 < z i) :
    slack q M z i = 0 :=
  (mul_eq_zero.mp (h.complementary i)).resolve_left (ne_of_gt hi)

/-- Every positive slack forces the corresponding coordinate to vanish. -/
theorem eq_zero_of_slack_pos (h : IsSolution q M z) {i : ι}
    (hi : 0 < slack q M z i) : z i = 0 :=
  (mul_eq_zero.mp (h.complementary i)).resolve_right (ne_of_gt hi)

end IsSolution

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem slack_zero (q : ι → K) (M : Matrix ι ι K) (i : ι) :
    slack q M (fun _ => 0) i = q i := by
  simp [slack]

omit [IsStrictOrderedRing K] in
/-- The zero vector solves precisely the problems with nonnegative constants. -/
@[simp] theorem isSolution_zero_iff (q : ι → K) (M : Matrix ι ι K) :
    IsSolution q M (fun _ => 0) ↔ ∀ i, 0 ≤ q i := by
  simp [IsSolution]

end GameTheory.Math.LinearComplementarity
