module

/-
# Finite lottery optimality with fixed inferior masses

When an alternative lottery cannot reduce the mass of any strictly suboptimal
action, it cannot raise expected score. Centering scores at their finite maximum
makes the comparison termwise, without introducing utility or game semantics.
-/

public import GameTheory.Math.Probability.Expectation
public import Mathlib.Data.Fintype.Lattice

@[expose] public section

namespace GameTheory.Math.Probability

open scoped BigOperators

/-- Moving mass only out of score-maximizing actions cannot improve a finite
lottery's expected score. No nonemptiness premise is needed beyond the PMFs. -/
theorem expect_le_of_suboptimal_mass_le {A : Type*} [Fintype A]
    (prescribed alternative : PMF A) (score : A → ℝ)
    (locked : ∀ a, (∃ b, score a < score b) →
      (prescribed a).toReal ≤ (alternative a).toReal) :
    expect alternative score ≤ expect prescribed score := by
  obtain ⟨inhabitant, _⟩ := prescribed.support_nonempty
  let : Nonempty A := ⟨inhabitant⟩
  obtain ⟨best, bestScore⟩ := Finite.exists_max score
  have centered :
      ∑ a, (alternative a).toReal * (score a - score best) ≤
        ∑ a, (prescribed a).toReal * (score a - score best) := by
    apply Finset.sum_le_sum
    intro a _
    by_cases inferior : score a < score best
    · exact mul_le_mul_of_nonpos_right (locked a ⟨best, inferior⟩)
        (sub_nonpos.mpr (bestScore a))
    · have equal : score a = score best := le_antisymm (bestScore a) (not_lt.mp inferior)
      rw [equal, sub_self, mul_zero, mul_zero]
  have prescribedSum : ∑ a, (prescribed a).toReal = 1 := by
    simpa only [tsum_fintype] using pmf_weight_tsum_one prescribed
  have alternativeSum : ∑ a, (alternative a).toReal = 1 := by
    simpa only [tsum_fintype] using pmf_weight_tsum_one alternative
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    prescribedSum, alternativeSum, one_mul] at centered
  simpa only [expect_eq_sum] using (sub_le_sub_iff_right (score best)).mp centered

end GameTheory.Math.Probability
