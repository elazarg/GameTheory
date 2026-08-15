/-
# Positive-part fixed-point algebra

The finite-dimensional Nash adjustment map has a small algebraic core that is
independent of games and probability: if weighted gains sum to zero and each
weight satisfies the positive-part adjustment identity, every gain is
nonpositive.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace GameTheory.Math

/-- The positive-part adjustment identity and a zero weighted mean force all
gains to be nonpositive. -/
theorem all_nonpos_of_weighted_positivePart_fixedPoint
    {α : Type*} [Fintype α] (weight gain : α → ℝ)
    (hfixed : ∀ action,
      weight action * (1 + ∑ candidate, max (gain candidate) 0) =
        weight action + max (gain action) 0)
    (hmean : ∑ action, weight action * gain action = 0) :
    ∀ action, gain action ≤ 0 := by
  have hadjusted : ∀ action,
      weight action * (∑ candidate, max (gain candidate) 0) =
        max (gain action) 0 := by
    intro action
    linarith [hfixed action]
  have hsum : ∑ action, max (gain action) 0 * gain action = 0 := by
    have hidentity :
        (∑ candidate, max (gain candidate) 0) *
            (∑ action, weight action * gain action) =
          ∑ action, max (gain action) 0 * gain action := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun action _ => ?_
      calc
        (∑ candidate, max (gain candidate) 0) *
              (weight action * gain action) =
            weight action * (∑ candidate, max (gain candidate) 0) *
              gain action := by ring
        _ = max (gain action) 0 * gain action := by
          rw [hadjusted action]
    rw [hmean, mul_zero] at hidentity
    exact hidentity.symm
  have hnonnegative : ∀ action, 0 ≤ max (gain action) 0 * gain action := by
    intro action
    by_cases hgain : gain action ≤ 0
    · simp [max_eq_right hgain]
    · rw [max_eq_left (le_of_not_ge hgain)]
      simpa [pow_two] using sq_nonneg (gain action)
  have hzero : ∀ action, max (gain action) 0 * gain action = 0 := by
    intro action
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun candidate _ => hnonnegative candidate)).1 hsum action
      (Finset.mem_univ action)
  intro action
  by_contra hpositive
  have hgain : 0 < gain action := lt_of_not_ge hpositive
  have := hzero action
  rw [max_eq_left hgain.le] at this
  nlinarith

end GameTheory.Math
