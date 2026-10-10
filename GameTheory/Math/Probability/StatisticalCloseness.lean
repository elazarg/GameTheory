/-
# What statistical closeness preserves

Statistical distance bounds every comparison made from polynomially many draws.

* Each mean test with `m` draws moves by at most `m` times the statistical
  distance of the tested law, so replacing either side of a mean comparison
  moves the gap by at most the mean-test advantage, itself at most `2 m` times
  the distance. This is the concrete form of the asymptotic statement that
  negligibly close ensembles are interchangeable under computational mean
  dominance.
* For payoffs in `[-R, R]` the means are at most `2 R` times the distance apart,
  so with polynomially bounded payoffs negligible distance moves means
  negligibly. Without a bound it need not: a jackpot of `4 ^ κ` with
  probability `2 ^ (-κ)` is `2 ^ (-κ)` from nothing.
* Changing a law only on a branch of probability `p` moves it by at most `p`.
-/
import GameTheory.Math.Probability.Indistinguishability
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.StatisticalDistanceStability

noncomputable section

namespace GameTheory.Math.Probability

open Filter GameTheory.Math

universe u

/-! ## Statistical distance -/

/-- Changing the branch taken with probability `p` moves a law by at most `p`. -/
theorem statisticalDistance_mix_le {α : Type u} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (B B' A : PMF α) :
    statisticalDistance (mix p h0 h1 B A) (mix p h0 h1 B' A) ≤ p := by
  unfold statisticalDistance
  have hterm : ∀ x, |(mix p h0 h1 B A x).toReal - (mix p h0 h1 B' A x).toReal| =
      p * |(B x).toReal - (B' x).toReal| := by
    intro x
    rw [mix_apply_toReal, mix_apply_toReal,
      show p * (B x).toReal + (1 - p) * (A x).toReal - (p * (B' x).toReal + (1 - p) * (A x).toReal)
        = p * ((B x).toReal - (B' x).toReal) by ring, abs_mul, abs_of_nonneg h0]
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum : ∑' x, |(B x).toReal - (B' x).toReal| ≤ 2 := by
    calc
      ∑' x, |(B x).toReal - (B' x).toReal| ≤ ∑' x, ((B x).toReal + (B' x).toReal) :=
        (summable_abs_sub_mass B B').tsum_le_tsum (fun x => by
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg])
          ((pmf_weight_summable B).add (pmf_weight_summable B'))
      _ = 2 := by
        rw [(pmf_weight_summable B).tsum_add (pmf_weight_summable B'), pmf_weight_tsum_one,
          pmf_weight_tsum_one]
        norm_num
  have := mul_le_mul_of_nonneg_left hsum h0
  linarith

/-! ## Means -/

/-- Laws with payoffs in `[-R, R]` have means at most `2 R` times their
statistical distance apart. -/
theorem abs_lawMean_sub_le {μ ν : PMF ℝ} {R : ℝ}
    (hμ : ∀ x ∈ μ.support, |x| ≤ R) (hν : ∀ x ∈ ν.support, |x| ≤ R) :
    |lawMean μ - lawMean ν| ≤ 2 * R * statisticalDistance μ ν := by
  calc
    _ ≤ statisticalDistance μ ν * (2 * R) :=
      abs_expect_sub_le_statisticalDistance_mul_range μ ν id (-R) (2 * R) fun x used => by
        have bound := abs_le.mp (used.elim (hμ x) (hν x))
        exact ⟨bound.1, by dsimp; linarith [bound.2]⟩
    _ = 2 * R * statisticalDistance μ ν := by ring

/-- **With polynomially bounded payoffs, negligible statistical distance moves
means negligibly**, so statistical simulation preserves negligible-slack Nash
there; the jackpot shows the bound cannot be dropped. -/
theorem negligible_lawMean_sub_of_statisticalDistance {X X' : ℕ → PMF ℝ} {b : ℕ}
    (hbound : ∀ᶠ κ : ℕ in atTop,
      (∀ x ∈ (X κ).support, |x| ≤ (κ : ℝ) ^ b) ∧ ∀ x ∈ (X' κ).support, |x| ≤ (κ : ℝ) ^ b)
    (h : Negligible fun κ => statisticalDistance (X κ) (X' κ)) :
    Negligible fun κ => lawMean (X κ) - lawMean (X' κ) := by
  have hscaled : Negligible fun κ =>
      2 * ((κ : ℝ) ^ b * statisticalDistance (X κ) (X' κ)) :=
    (h.param_pow_mul b).const_mul 2
  refine hscaled.of_eventually_abs_le ?_
  filter_upwards [hbound] with κ hκ
  have hSD := statisticalDistance_nonneg (X κ) (X' κ)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((κ : ℝ) ^ b *
    statisticalDistance (X κ) (X' κ)))]
  calc
    _ ≤ 2 * (κ : ℝ) ^ b * statisticalDistance (X κ) (X' κ) :=
      abs_lawMean_sub_le hκ.1 hκ.2
    _ = 2 * ((κ : ℝ) ^ b * statisticalDistance (X κ) (X' κ)) := by ring

/-! ## Mean comparisons -/

/-- The advantage, with `m` draws, of the two mean comparisons against `Y`
between `X` and `X'`. -/
def meanTestAdvantage (Y X X' : PMF ℝ) (m : ℕ) : ℝ :=
  |aheadProb X Y m - aheadProb X' Y m| + |aheadProb Y X m - aheadProb Y X' m|

/-- Replacing the dominating side moves the gap by at most the mean-test
advantage against the other side. -/
theorem meanComparisonGap_le_of_left (X X' Y : PMF ℝ) (m : ℕ) :
    meanComparisonGap X' Y m ≤ meanComparisonGap X Y m + meanTestAdvantage Y X X' m := by
  rw [meanComparisonGap_eq_aheadProb_sub, meanComparisonGap_eq_aheadProb_sub, meanTestAdvantage]
  have h1 := le_abs_self (aheadProb X Y m - aheadProb X' Y m)
  have h2 := neg_abs_le (aheadProb Y X m - aheadProb Y X' m)
  linarith

/-- Replacing the dominated side moves the gap by at most the mean-test
advantage against the dominating side. -/
theorem meanComparisonGap_le_of_right (X Y Y' : PMF ℝ) (m : ℕ) :
    meanComparisonGap X Y' m ≤ meanComparisonGap X Y m + meanTestAdvantage X Y Y' m := by
  rw [meanComparisonGap_eq_aheadProb_sub, meanComparisonGap_eq_aheadProb_sub, meanTestAdvantage]
  have h1 := neg_abs_le (aheadProb Y X m - aheadProb Y' X m)
  have h2 := le_abs_self (aheadProb X Y m - aheadProb X Y' m)
  linarith

private theorem mass_mem_Icc (p : PMF Bool) (b : Bool) : 0 ≤ (p b).toReal ∧ (p b).toReal ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, pmf_toReal_apply_le_one p b⟩

/-- Replacing the tested law moves the probability of being ahead by at most
`m` times the statistical distance. -/
theorem abs_aheadProb_sub_left_le (X X' Y : PMF ℝ) (m : ℕ) :
    |aheadProb X Y m - aheadProb X' Y m| ≤ m * statisticalDistance X X' := by
  have h1 := acceptProb_beatsMeanTest (fun _ => Y) (fun _ => X) 1 m
  have h2 := acceptProb_beatsMeanTest (fun _ => Y) (fun _ => X') 1 m
  rw [pow_one] at h1 h2
  rw [← h1, ← h2, SampleTest.acceptProb_eq_expect, SampleTest.acceptProb_eq_expect]
  have := abs_expect_iidLaw_sub_le_of_mem_Icc X X' ((beatsMeanTest (fun _ => Y) 1).samples m)
    (fun z => ((beatsMeanTest (fun _ => Y) 1).accept m z true).toReal)
    fun z => mass_mem_Icc _ true
  simpa [beatsMeanTest] using this

/-- Replacing the reference law moves the probability of the tested law being
ahead by at most `m` times the statistical distance. -/
theorem abs_aheadProb_sub_right_le (X X' Y : PMF ℝ) (m : ℕ) :
    |aheadProb Y X m - aheadProb Y X' m| ≤ m * statisticalDistance X X' := by
  have h1 := acceptProb_beatenByMeanTest (fun _ => Y) (fun _ => X) 1 m
  have h2 := acceptProb_beatenByMeanTest (fun _ => Y) (fun _ => X') 1 m
  rw [pow_one] at h1 h2
  rw [← h1, ← h2, SampleTest.acceptProb_eq_expect, SampleTest.acceptProb_eq_expect]
  have := abs_expect_iidLaw_sub_le_of_mem_Icc X X' ((beatenByMeanTest (fun _ => Y) 1).samples m)
    (fun z => ((beatenByMeanTest (fun _ => Y) 1).accept m z true).toReal)
    fun z => mass_mem_Icc _ true
  simpa [beatenByMeanTest] using this

/-- Each mean-test advantage with `m` draws is at most `2 m` times the
statistical distance. -/
theorem meanTestAdvantage_le (Y X X' : PMF ℝ) (m : ℕ) :
    meanTestAdvantage Y X X' m ≤ 2 * m * statisticalDistance X X' := by
  have h1 := abs_aheadProb_sub_left_le X X' Y m
  have h2 := abs_aheadProb_sub_right_le X X' Y m
  unfold meanTestAdvantage
  linarith

/-- Negligibly modified ensembles are interchangeable on both sides of
computational mean dominance. -/
theorem computationallyMeanDominates_congr_of_negligible {X X' Y : ℕ → PMF ℝ}
    (h : Negligible fun κ => statisticalDistance (X κ) (X' κ)) :
    (ComputationallyMeanDominates X Y ↔ ComputationallyMeanDominates X' Y) ∧
      (ComputationallyMeanDominates Y X ↔ ComputationallyMeanDominates Y X') := by
  have hmean := (indistinguishableBy_polySampleTests_of_statisticalDistance h
    ).meanTestIndistinguishable (containsMeanTests_polySampleTests Y)
  exact ⟨ComputationallyMeanDominates.congr_left hmean,
    ComputationallyMeanDominates.congr_right hmean⟩

end GameTheory.Math.Probability
