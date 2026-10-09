import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-! Scalar support inequalities implement exact saturated affine and comparison gates.
The two gate types use distinct auxiliary support conditions. -/

namespace GameTheory.Math
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Pairwise support comparisons implement a saturated affine target exactly.
Bounds on the auxiliary coordinate are unnecessary for this implication. -/
theorem pairSupport_clamp (X Y x y t : F) (hX : 0 < X) (hY : 0 < Y)
    (hx0 : 0 ≤ x) (hxX : x ≤ X)
    (hr1 : 0 < x → Y - y ≤ y) (hr0 : x < X → y ≤ Y - y)
    (hc0 : 0 < y → x ≤ t) (hc1 : y < Y → t ≤ x) :
    x = max 0 (min X t) := by
  by_cases hzero : x = 0
  · have hylt : y < Y := by
      have hh := hr0 (by rw [hzero]; exact hX)
      linarith
    have ht : t ≤ 0 := by simpa only [hzero] using hc1 hylt
    rw [min_eq_right (ht.trans hX.le), max_eq_left ht]
    exact hzero
  · by_cases hfull : x = X
    · have hypos : 0 < y := by
        have hh := hr1 (by rw [hfull]; exact hX)
        linarith
      have ht : X ≤ t := by simpa only [hfull] using hc0 hypos
      rw [min_eq_left ht, max_eq_right hX.le]
      exact hfull
    · have hxpos : 0 < x := by exact lt_of_le_of_ne hx0 (Ne.symm hzero)
      have hxlt : x < X := lt_of_le_of_ne hxX hfull
      have hypos : 0 < y := by linarith [hr1 hxpos]
      have hylt : y < Y := by linarith [hr0 hxlt]
      have he : t = x := le_antisymm (hc1 hylt) (hc0 hypos)
      rw [he, min_eq_right hxX, max_eq_right hx0]

/-- A full auxiliary mass forces the row pair to its upper endpoint. -/
theorem pairSupport_eq_upper (X Y x y : F) (hY : 0 < Y) (hxX : x ≤ X)
    (hr0 : x < X → y ≤ Y - y) (hy : y = Y) : x = X := by
  by_contra hne
  have hh := hr0 (lt_of_le_of_ne hxX hne)
  rw [hy] at hh
  linarith

/-- A zero auxiliary mass forces the row pair to its lower endpoint. -/
theorem pairSupport_eq_zero (Y x y : F) (hY : 0 < Y) (hx0 : 0 ≤ x)
    (hr1 : 0 < x → Y - y ≤ y) (hy : y = 0) : x = 0 := by
  by_contra hne
  have hh := hr1 (lt_of_le_of_ne hx0 (Ne.symm hne))
  rw [hy] at hh
  linarith

/-- Constant-signal column comparisons select the row endpoint matching its sign. -/
theorem pairSupport_comparator (X Y x y t : F) (hY : 0 < Y)
    (hx0 : 0 ≤ x) (hxX : x ≤ X) (hy0 : 0 ≤ y) (hyY : y ≤ Y)
    (hr1 : 0 < x → Y - y ≤ y) (hr0 : x < X → y ≤ Y - y)
    (hc0 : 0 < y → 0 ≤ t) (hc1 : y < Y → t ≤ 0) :
    (0 < t → y = Y ∧ x = X) ∧ (t < 0 → y = 0 ∧ x = 0) := by
  constructor
  · intro ht
    have hy : y = Y := by
      by_contra hne
      exact (not_le_of_gt ht) (hc1 (lt_of_le_of_ne hyY hne))
    exact ⟨hy, pairSupport_eq_upper X Y x y hY hxX hr0 hy⟩
  · intro ht
    have hy : y = 0 := by
      by_contra hne
      exact (not_le_of_gt ht) (hc0 (lt_of_le_of_ne hy0 (Ne.symm hne)))
    exact ⟨hy, pairSupport_eq_zero Y x y hY hx0 hr1 hy⟩
end GameTheory.Math
