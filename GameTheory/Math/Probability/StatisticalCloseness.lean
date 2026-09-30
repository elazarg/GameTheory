/-
# What statistical closeness preserves

Statistical distance bounds every comparison made from polynomially many draws.

* Each mean test with `m` draws moves by at most `2 m` times the statistical
  distance of the tested law, so replacing either side of a mean comparison
  moves the gap by at most the mean-test advantage, itself at most `4 m` times
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

noncomputable section

namespace GameTheory.Math.Probability

open Filter GameTheory.Math

universe u

/-! ## Statistical distance -/

/-- Statistical distance is symmetric. -/
theorem statisticalDistance_comm {α : Type u} (μ ν : PMF α) :
    statisticalDistance μ ν = statisticalDistance ν μ := by
  unfold statisticalDistance
  congr 1
  exact tsum_congr fun a => abs_sub_comm _ _

open Classical in
/-- The statistical distance of a law from a point mass is the mass it puts
elsewhere. -/
theorem statisticalDistance_pure {α : Type u} (μ : PMF α) (a : α) :
    statisticalDistance μ (PMF.pure a) = expect μ fun x => if x = a then 0 else 1 := by
  classical
  have hsplit := (summable_abs_sub_mass μ (PMF.pure a)).tsum_eq_add_tsum_ite a
  have hmass := (pmf_weight_summable μ).tsum_eq_add_tsum_ite a
  rw [pmf_weight_tsum_one] at hmass
  have hrest : (∑' x, if x = a then (0 : ℝ) else |(μ x).toReal - ((PMF.pure a) x).toReal|) =
      ∑' x, if x = a then (0 : ℝ) else (μ x).toReal := by
    apply tsum_congr
    intro x
    by_cases hx : x = a
    · simp [hx]
    · simp [hx, PMF.pure_apply, abs_of_nonneg ENNReal.toReal_nonneg]
  have hexpect : (expect μ fun x => if x = a then (0 : ℝ) else 1) =
      ∑' x, if x = a then (0 : ℝ) else (μ x).toReal := by
    unfold expect
    apply tsum_congr
    intro x
    by_cases hx : x = a <;> simp [hx]
  have ha : |(μ a).toReal - ((PMF.pure a) a).toReal| = 1 - (μ a).toReal := by
    simp only [PMF.pure_apply, ite_true, ENNReal.toReal_one]
    rw [abs_sub_comm, abs_of_nonneg (by linarith [pmf_toReal_apply_le_one μ a])]
  rw [statisticalDistance, hsplit, hrest, ha, hexpect]
  linarith

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
theorem abs_lawMean_sub_le {μ ν : PMF ℝ} {R : ℝ} (hR : 0 < R)
    (hμ : ∀ x ∈ μ.support, |x| ≤ R) (hν : ∀ x ∈ ν.support, |x| ≤ R) :
    |lawMean μ - lawMean ν| ≤ 2 * R * statisticalDistance μ ν := by
  let clip : ℝ → ℝ := fun x => max (-R) (min R x) / R
  have hclip : ∀ x, |clip x| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos hR, div_le_one hR, abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_refl R)) (le_max_left _ _)
    · exact max_le (by linarith) (min_le_left _ _)
  have hscale : ∀ {law : PMF ℝ}, (∀ x ∈ law.support, |x| ≤ R) →
      lawMean law = R * expect law clip := by
    intro law hlaw
    rw [lawMean, ← expect_const_mul]
    apply expect_congr_on_support
    intro x hx
    have hx := abs_le.mp (hlaw x hx)
    simp only [clip, id, min_eq_right hx.2, max_eq_right hx.1]
    field_simp
  rw [hscale hμ, hscale hν, ← mul_sub, abs_mul, abs_of_pos hR]
  have := mul_le_mul_of_nonneg_left
    (abs_expect_sub_le_statisticalDistance (μ := μ) (ν := ν) hclip) hR.le
  linarith

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
  filter_upwards [hbound, eventually_ge_atTop 1] with κ hκ hκ1
  have hpos : (0 : ℝ) < (κ : ℝ) ^ b := pow_pos (by exact_mod_cast hκ1) b
  have hSD := statisticalDistance_nonneg (X κ) (X' κ)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((κ : ℝ) ^ b *
    statisticalDistance (X κ) (X' κ)))]
  calc
    _ ≤ 2 * (κ : ℝ) ^ b * statisticalDistance (X κ) (X' κ) :=
      abs_lawMean_sub_le hpos hκ.1 hκ.2
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

private theorem abs_toReal_le_one (p : PMF Bool) (b : Bool) : |(p b).toReal| ≤ 1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact pmf_toReal_apply_le_one _ _

/-- Replacing the tested law moves the probability of being ahead by at most
`2 m` times the statistical distance. -/
theorem abs_aheadProb_sub_left_le (X X' Y : PMF ℝ) (m : ℕ) :
    |aheadProb X Y m - aheadProb X' Y m| ≤ m * (2 * statisticalDistance X X') := by
  have h1 := acceptProb_beatsMeanTest (fun _ => Y) (fun _ => X) 1 m
  have h2 := acceptProb_beatsMeanTest (fun _ => Y) (fun _ => X') 1 m
  rw [pow_one] at h1 h2
  rw [← h1, ← h2, SampleTest.acceptProb_eq_expect, SampleTest.acceptProb_eq_expect]
  have := abs_expect_iidLaw_sub_le X X' ((beatsMeanTest (fun _ => Y) 1).samples m)
    (fun z => ((beatsMeanTest (fun _ => Y) 1).accept m z true).toReal)
    fun z => abs_toReal_le_one _ true
  simpa [beatsMeanTest] using this

/-- Replacing the reference law moves the probability of the tested law being
ahead by at most `2 m` times the statistical distance. -/
theorem abs_aheadProb_sub_right_le (X X' Y : PMF ℝ) (m : ℕ) :
    |aheadProb Y X m - aheadProb Y X' m| ≤ m * (2 * statisticalDistance X X') := by
  have h1 := acceptProb_beatenByMeanTest (fun _ => Y) (fun _ => X) 1 m
  have h2 := acceptProb_beatenByMeanTest (fun _ => Y) (fun _ => X') 1 m
  rw [pow_one] at h1 h2
  rw [← h1, ← h2, SampleTest.acceptProb_eq_expect, SampleTest.acceptProb_eq_expect]
  have := abs_expect_iidLaw_sub_le X X' ((beatenByMeanTest (fun _ => Y) 1).samples m)
    (fun z => ((beatenByMeanTest (fun _ => Y) 1).accept m z true).toReal)
    fun z => abs_toReal_le_one _ true
  simpa [beatenByMeanTest] using this

/-- Each mean-test advantage with `m` draws is at most `4 m` times the
statistical distance. -/
theorem meanTestAdvantage_le (Y X X' : PMF ℝ) (m : ℕ) :
    meanTestAdvantage Y X X' m ≤ 4 * m * statisticalDistance X X' := by
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
