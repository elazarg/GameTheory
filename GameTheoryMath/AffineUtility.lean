/-
# Affine real utilities

Game-independent algebra for utility indices on real monetary outcomes.
Adapted from `Concepts/Foundations/VNM/Basic.lean` in the pinned v1 snapshot
at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GameTheoryMath

/-- A real utility index is affine when it has the form `x ↦ a * x + b`. -/
def IsAffineUtility (u : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, u x = a * x + b

/-- A real utility index is risk neutral when it preserves every binary
convex combination. -/
def IsRiskNeutral (u : ℝ → ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ x y,
    u (t * x + (1 - t) * y) = t * u x + (1 - t) * u y

theorem IsAffineUtility.isRiskNeutral {u : ℝ → ℝ}
    (h : IsAffineUtility u) : IsRiskNeutral u := by
  obtain ⟨a, b, hu⟩ := h
  intro t _ _ x y
  simp [hu]
  ring

theorem IsRiskNeutral.isAffine {u : ℝ → ℝ}
    (h : IsRiskNeutral u) : IsAffineUtility u := by
  refine ⟨u 1 - u 0, u 0, fun x => ?_⟩
  suffices hnonneg : ∀ y : ℝ, 0 ≤ y → u y = (u 1 - u 0) * y + u 0 by
    by_cases hx : 0 ≤ x
    · exact hnonneg x hx
    · have hxlt : x < 0 := lt_of_not_ge hx
      have hmx := hnonneg (-x) (le_of_lt (neg_pos.mpr hxlt))
      have hmid := h (1 / 2) (by norm_num) (by norm_num) x (-x)
      have harg : (1 : ℝ) / 2 * x + (1 - 1 / 2) * -x = 0 := by ring
      rw [harg] at hmid
      linarith
  intro y hy
  rcases hy.eq_or_lt with hy | hy
  · subst y
    ring
  · rcases le_or_gt y 1 with hy1 | hy1
    · have hyFormula := h y hy.le hy1 1 0
      simp at hyFormula
      linarith
    · have hinv := h (1 / y) (le_of_lt (div_pos one_pos hy))
        ((div_le_one hy).mpr hy1.le) y 0
      simp at hinv
      have hyne : y ≠ 0 := ne_of_gt hy
      field_simp [hyne] at hinv ⊢
      linarith

end GameTheoryMath
