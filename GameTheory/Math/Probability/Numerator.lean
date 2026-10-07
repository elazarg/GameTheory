import GameTheory.Math.Probability.Expectation

/-! Common-denominator natural weights define probability mass functions, with
exact finite weighted-sum expectations. -/

noncomputable section

namespace GameTheory.Math.Probability

open scoped BigOperators

/-- Natural weights summing to a positive denominator define a PMF. -/
def numeratorLaw {α : Type*} [Fintype α] (w : α → ℕ) (d : ℕ)
    (hd : 0 < d) (hs : ∑ i, w i = d) : PMF (α) :=
  PMF.ofFintype (fun i => ENNReal.ofReal ((w i : ℝ) / d)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)), ← Finset.sum_div]
    have hsum : (∑ i, (w i : ℝ)) = d := by exact_mod_cast hs
    rw [hsum, div_self (by exact_mod_cast hd.ne')]
    norm_num)

/-- Expectation under common-denominator weights is the weighted sum divided by
the denominator. -/
theorem expect_numeratorLaw {α : Type*} [Fintype α] (w : α → ℕ) (d : ℕ)
    (hd : 0 < d) (hs : ∑ i, w i = d) (f : α → ℝ) :
    expect (numeratorLaw w d hd hs) f = (∑ i, (w i : ℝ) * f i) / d := by
  rw [expect_eq_sum]
  simp only [numeratorLaw, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A payoff constant on the positive weights has that constant expectation. -/
theorem expect_numeratorLaw_eq {α : Type*} [Fintype α] (w : α → ℕ) (d : ℕ)
    (hd : 0 < d) (hs : ∑ i, w i = d) (f : α → ℝ) (u : ℝ)
    (hu : ∀ i, 0 < w i → f i = u) :
    expect (numeratorLaw w d hd hs) f = u := by
  rw [expect_numeratorLaw]
  have hterms : (∑ i, (w i : ℝ) * f i) = ∑ i, (w i : ℝ) * u := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < w i
    · rw [hu i hi]
    · have hz : w i = 0 := by omega
      simp [hz]
  rw [hterms, ← Finset.sum_mul]
  have hsum : (∑ i, (w i : ℝ)) = d := by exact_mod_cast hs
  rw [hsum]
  exact mul_div_cancel_left₀ u (by exact_mod_cast hd.ne')

end GameTheory.Math.Probability
