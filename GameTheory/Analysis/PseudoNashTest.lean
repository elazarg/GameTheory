/-
# Boundaries of pseudo-Nash

Machine-checked witnesses for the hypotheses of the pseudo-Nash library. Each
game is a one-player choice between two payoff ensembles.

* **Per-size Nash does not imply pseudo-Nash.** A payoff of `κ` with probability
  `2 ^ (-κ)` beats half its mean in expectation, strictly at every size and with
  payoffs at most `κ`, yet never in polynomially many draws. So the margin in
  `ParameterizedGame.isPseudoNash_of_isPolynomiallyStrictNash` cannot be
  negligible, and "Nash in the ideal game implies pseudo-Nash in the real
  game" fails for ideal games that depend on the size.
* **Unbounded payoffs.** A jackpot of `4 ^ κ` with probability `2 ^ (-κ)` is
  preferred in expectation and dominated by a fair coin on `{0, 2}`; taking the
  coin is pseudo-Nash but misses a gain of `2 ^ κ - 1`, so the polynomial bound
  in `ParameterizedGame.isNegligibleNash_of_isPseudoNash` is needed.
* **The sample exponent must exceed the tolerance exponent.** If dominance at
  tolerance `κ ^ (-c)` could use any sample exponent `d ≥ 1`, the constant `1`
  would dominate a law of mean `1 + 1 / (κ ^ 3 + 1)` whose `κ` draws are all
  zero with high probability.
* **Negligible sure gains.** A sure `1 - 2 ^ (-κ)` against a sure `1` is Nash up
  to negligible slack and pseudo-Nash with payoff tolerance `2 ^ (-κ)`, but not
  pseudo-Nash.
* **Statistical simulation.** The identity compilation from a game offering a
  sure `1` or nothing to one offering a sure `1` or the jackpot is a
  `SecureImplementation` for tests of polynomially many draws. Taking the sure
  `1` is Nash at every size of the source and pseudo-Nash in the target, where
  it is Nash at no positive size and not Nash up to negligible slack.
-/
import GameTheory.Analysis.PseudoNash
import GameTheory.Examples.PseudoEquilibria

noncomputable section

namespace GameTheory.Tests.PseudoNash

open Filter GameTheory GameTheory.Math GameTheory.Math.Probability
open GameTheory.Examples.PseudoEquilibria

/-! ## A one-player choice between two payoff ensembles -/

/-- One player picks the first ensemble (`true`) or the second; the outcome is
the payoff. -/
@[reducible]
def binaryChoice (A B : ℕ → PMF ℝ) : ParameterizedGame Unit where
  sig := { Strategy := fun _ => Bool, Outcome := ℝ }
  play κ profile := if profile () then A κ else B κ
  utility _ payoff _ := payoff

/-- Picking the first ensemble. -/
def pickFirst (A B : ℕ → PMF ℝ) : Profile (binaryChoice A B).sig := fun _ => true

theorem binaryChoice_utilityLaw (A B : ℕ → PMF ℝ) (profile : Profile (binaryChoice A B).sig) :
    (binaryChoice A B).utilityLaw () profile = fun κ => (binaryChoice A B).play κ profile := by
  funext κ
  exact PMF.map_id _

theorem binaryChoice_utilityLaw_if (A B : ℕ → PMF ℝ) (profile : Profile (binaryChoice A B).sig) :
    (binaryChoice A B).utilityLaw () profile = fun κ => if profile () then A κ else B κ := by
  funext κ
  exact PMF.map_id _

theorem binaryChoice_play_update (A B : ℕ → PMF ℝ) (choice : Bool) (κ : ℕ) :
    (binaryChoice A B).play κ (Profile.update (pickFirst A B) () choice) =
      if choice then A κ else B κ := by
  change (if Profile.update (pickFirst A B) () choice () then A κ else B κ) = _
  rw [Profile.update_same]

theorem binaryChoice_play_pickFirst (A B : ℕ → PMF ℝ) (κ : ℕ) :
    (binaryChoice A B).play κ (pickFirst A B) = A κ := rfl

theorem binaryChoice_isPseudoNash_iff (A B : ℕ → PMF ℝ) :
    (binaryChoice A B).IsPseudoNash (pickFirst A B) ↔ ComputationallyMeanDominates A B := by
  rw [ParameterizedGame.isPseudoNash_iff]
  have hlaw : ∀ choice : Bool,
      (binaryChoice A B).utilityLaw () (Profile.update (pickFirst A B) () choice) =
        fun κ => if choice then A κ else B κ := by
    intro choice
    rw [binaryChoice_utilityLaw]
    funext κ
    exact binaryChoice_play_update A B choice κ
  have hbase : (binaryChoice A B).utilityLaw () (pickFirst A B) = A := by
    rw [binaryChoice_utilityLaw]
    rfl
  constructor
  · intro h
    have := h () false
    rwa [hlaw, hbase] at this
  · intro h who replacement
    cases who
    rw [hlaw, hbase]
    cases replacement
    · exact h
    · exact computationallyMeanDominates_refl A

theorem binaryChoice_isNegligibleNash_iff (A B : ℕ → PMF ℝ) :
    (binaryChoice A B).IsNegligibleNash (pickFirst A B) ↔
      ∀ a : ℕ, ∀ᶠ κ : ℕ in atTop, lawMean (B κ) ≤ lawMean (A κ) + ((κ : ℝ) ^ a)⁻¹ := by
  have hlaw : ∀ (choice : Bool) (κ : ℕ),
      (binaryChoice A B).utilityLaw () (Profile.update (pickFirst A B) () choice) κ =
        if choice then A κ else B κ := by
    intro choice κ
    rw [binaryChoice_utilityLaw]
    exact binaryChoice_play_update A B choice κ
  have hbase : ∀ κ, (binaryChoice A B).utilityLaw () (pickFirst A B) κ = A κ := by
    intro κ
    rw [binaryChoice_utilityLaw]
    rfl
  constructor
  · intro h a
    filter_upwards [h () false a] with κ hκ
    rwa [hlaw, hbase] at hκ
  · intro h who replacement a
    cases who
    filter_upwards [h a, eventually_ge_atTop 1] with κ hκ hκ1
    rw [hlaw, hbase]
    cases replacement
    · exact hκ
    · have : (0 : ℝ) < ((κ : ℝ) ^ a)⁻¹ := by
        have : (0 : ℝ) < κ := by exact_mod_cast hκ1
        positivity
      simp only [ite_true]
      linarith

theorem binaryChoice_polyBoundedPayoffs {A B : ℕ → PMF ℝ} {b : ℕ}
    (hA : ∀ᶠ κ : ℕ in atTop, ∀ x ∈ (A κ).support, |x| ≤ (κ : ℝ) ^ b)
    (hB : ∀ᶠ κ : ℕ in atTop, ∀ x ∈ (B κ).support, |x| ≤ (κ : ℝ) ^ b) :
    (binaryChoice A B).PolyBoundedPayoffs := by
  refine ⟨b, ?_⟩
  filter_upwards [hA, hB] with κ hAκ hBκ who profile x hx
  cases who
  rw [binaryChoice_utilityLaw] at hx
  change x ∈ (if profile () then A κ else B κ).support at hx
  split_ifs at hx
  · exact hAκ x hx
  · exact hBκ x hx

/-- At one size, picking the first ensemble is expected-utility Nash exactly
when its mean is at least that of the second, for laws of bounded support. -/
theorem binaryChoice_isNash_iff (A B : ℕ → PMF ℝ) (κ : ℕ) {R : ℝ}
    (hA : ∀ x ∈ (A κ).support, |x| ≤ R) (hB : ∀ x ∈ (B κ).support, |x| ≤ R) :
    IsNash ((binaryChoice A B).formAt κ) (euPreference ((binaryChoice A B).utility κ))
        (pickFirst A B) ↔ lawMean (B κ) ≤ lawMean (A κ) := by
  have hint : ∀ law : PMF ℝ, (∀ x ∈ law.support, |x| ≤ R) →
      UtilityIntegrable ((binaryChoice A B).utility κ) () law := fun law hlaw =>
    payoffIntegrable_of_bounded_on_support law _ hlaw
  rw [isNash_iff]
  constructor
  · intro h
    have hdev := h () false
    change euPreference ((binaryChoice A B).utility κ) ()
      ((binaryChoice A B).play κ (pickFirst A B))
      ((binaryChoice A B).play κ (Profile.update (pickFirst A B) () false)) at hdev
    rw [binaryChoice_play_pickFirst, binaryChoice_play_update] at hdev
    exact (euPreference_iff _ _ _ _ (hint _ hA) (hint _ hB)).mp hdev
  · intro hle who replacement
    cases who
    change euPreference ((binaryChoice A B).utility κ) ()
      ((binaryChoice A B).play κ (pickFirst A B))
      ((binaryChoice A B).play κ (Profile.update (pickFirst A B) () replacement))
    rw [binaryChoice_play_pickFirst, binaryChoice_play_update]
    cases replacement
    · exact (euPreference_iff _ _ _ _ (hint _ hA) (hint _ hB)).mpr hle
    · exact (euPreference_iff _ _ _ _ (hint _ hA) (hint _ hA)).mpr le_rfl

/-! ## Rare payoffs -/

/-- Pays `v` with probability `1 / n`, and `0` otherwise. -/
def spike (n : ℕ) [NeZero n] (v : ℝ) : PMF ℝ :=
  (PMF.uniformOfFintype (Fin n)).map fun i => if i = 0 then v else 0

theorem lawMean_spike (n : ℕ) [NeZero n] (v : ℝ) : lawMean (spike n v) = v / n := by
  rw [lawMean, spike, expect_map, expect_uniformOfFintype]
  simp only [Function.comp_apply, id, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Fintype.card_fin]

theorem spike_nonneg (n : ℕ) [NeZero n] {v : ℝ} (hv : 0 ≤ v) :
    ∀ x ∈ (spike n v).support, 0 ≤ x := by
  intro x hx
  rw [spike, PMF.mem_support_map_iff] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split_ifs
  · exact hv
  · exact le_rfl

theorem abs_le_of_mem_support_spike (n : ℕ) [NeZero n] (v : ℝ) :
    ∀ x ∈ (spike n v).support, |x| ≤ |v| := by
  intro x hx
  rw [spike, PMF.mem_support_map_iff] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split_ifs <;> simp

theorem probOf_spike_ne_zero_le (n : ℕ) [NeZero n] (v : ℝ) :
    probOf (spike n v) (· ≠ 0) ≤ 1 / n := by
  rw [probOf, spike, expect_map, expect_uniformOfFintype, Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    (∑ i : Fin n, ((fun x : ℝ => if x ≠ 0 then (1 : ℝ) else 0) ∘
        fun i : Fin n => if i = 0 then v else 0) i) ≤
        ∑ i : Fin n, if i = 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i = 0
      · simp only [hi, ite_true]
        split_ifs <;> norm_num
      · simp [hi]
    _ = 1 := by simp

theorem probOf_sampleSum_pure_eq_zero {y : ℝ} (hy : y ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    probOf (sampleSum (PMF.pure y) m) (· = 0) = 0 := by
  rw [sampleSum_pure, probOf, expect_pure]
  have : (m : ℝ) * y ≠ 0 := mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)) hy
  simp [this]

theorem pure_nonneg {y : ℝ} (hy : 0 ≤ y) : ∀ x ∈ (PMF.pure y).support, 0 ≤ x := by
  intro x hx
  rw [PMF.mem_support_pure_iff] at hx
  rw [hx]
  exact hy

/-- Between nonnegative laws, `X` falls behind `Y` about as often as `Y`'s draws
are nonzero and `X`'s draws are all zero. -/
theorem meanComparisonGap_bounds {X Y : PMF ℝ} (hX : ∀ x ∈ X.support, 0 ≤ x)
    (hY : ∀ y ∈ Y.support, 0 ≤ y) (m : ℕ) :
    meanComparisonGap X Y m ≤
        2 * probOf (sampleSum Y m) (· ≠ 0) + probOf (sampleSum X m) (· = 0) - 1 ∧
      1 - 2 * probOf (sampleSum X m) (· ≠ 0) - probOf (sampleSum Y m) (· = 0) ≤
        meanComparisonGap X Y m := by
  rw [meanComparisonGap_eq_aheadProb_sub]
  have h1 := aheadProb_le hX (Y := Y) m
  have h2 := one_sub_le_aheadProb hX hY m
  have h3 := aheadProb_le hY (Y := X) m
  have h4 := one_sub_le_aheadProb hY hX m
  constructor <;> linarith

/-- A nonnegative ensemble whose draws are rarely nonzero does not dominate a
nonnegative ensemble whose sums are rarely zero. -/
theorem not_computationallyMeanDominates_of_rare {A B : ℕ → PMF ℝ}
    (hA : ∀ κ, ∀ x ∈ (A κ).support, 0 ≤ x) (hB : ∀ κ, ∀ x ∈ (B κ).support, 0 ≤ x)
    (hrare : ∀ d : ℕ, ∀ᶠ κ : ℕ in atTop, probOf (sampleSum (A κ) (κ ^ d)) (· ≠ 0) ≤ 1 / 8)
    (hfull : ∀ d : ℕ, 1 ≤ d → ∀ᶠ κ : ℕ in atTop,
      probOf (sampleSum (B κ) (κ ^ d)) (· = 0) ≤ 1 / 8) :
    ¬ ComputationallyMeanDominates A B := by
  intro h
  obtain ⟨d, hd, hev⟩ := h 1 le_rfl
  obtain ⟨κ, hgap, hr, hf, hκ⟩ :=
    (hev.and ((hrare d).and ((hfull d (by omega)).and (eventually_ge_atTop 2)))).exists
  have hbound := (meanComparisonGap_bounds (hA κ) (hB κ) (κ ^ d)).2
  have hκinv : ((κ : ℝ) ^ 1)⁻¹ ≤ 1 / 2 := by
    rw [pow_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hκ)
  linarith

private theorem eventually_pow_div_two_pow_le (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ κ : ℕ in atTop, ((κ ^ d : ℕ) : ℝ) * (1 / 2 ^ κ) ≤ ε := by
  have hlim : Tendsto (fun κ : ℕ => (κ : ℝ) ^ d / 2 ^ κ) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num)
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with κ hκ
  push_cast
  rw [mul_one_div]
  exact hκ.le

private theorem probOf_coin_sum_eq_zero_le {m : ℕ} (hm : 3 ≤ m) :
    probOf (sampleSum coinPayoff m) (· = 0) ≤ 1 / 8 := by
  refine (probOf_sampleSum_eq_zero_le coinPayoff_nonneg m).trans ?_
  rw [probOf_coinPayoff_eq_zero]
  calc
    (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = 1 / 8 := by norm_num

/-! ## Separations -/

/-- **Nash at every size, not pseudo-Nash (unbounded utilities).** Picking the
jackpot over the coin maximizes expected utility at every positive size, yet the
coin dominates it. With the identity implementation this refutes "Nash in a
parameterized ideal game implies pseudo-Nash in the real game". -/
theorem jackpot_isNash_not_isPseudoNash :
    (∀ κ, 1 ≤ κ → IsNash ((binaryChoice jackpot fun _ => coinPayoff).formAt κ)
      (euPreference ((binaryChoice jackpot fun _ => coinPayoff).utility κ))
      (pickFirst jackpot fun _ => coinPayoff)) ∧
    ¬ (binaryChoice jackpot fun _ => coinPayoff).IsPseudoNash
      (pickFirst jackpot fun _ => coinPayoff) := by
  constructor
  · intro κ hκ
    have hcoin : ∀ x ∈ coinPayoff.support, |x| ≤ 4 ^ κ := by
      intro x hx
      have h2 : |x| ≤ 2 := by
        rw [coinPayoff, PMF.mem_support_map_iff] at hx
        obtain ⟨b, _, rfl⟩ := hx
        cases b <;> norm_num
      have : (2 : ℝ) ≤ 4 ^ κ := le_trans (by norm_num) (le_self_pow₀ (by norm_num) (by omega))
      linarith
    have hjack : ∀ x ∈ (jackpot κ).support, |x| ≤ 4 ^ κ := fun x hx =>
      (abs_le_of_mem_support_spike (2 ^ κ) (4 ^ κ) x hx).trans_eq (abs_of_pos (by positivity))
    rw [binaryChoice_isNash_iff _ _ κ hjack hcoin]
    exact (lawMean_coinPayoff_lt_lawMean_jackpot hκ).le
  · rw [binaryChoice_isPseudoNash_iff]
    refine not_computationallyMeanDominates_of_rare (fun κ => jackpot_nonneg κ)
      (fun _ => coinPayoff_nonneg) (fun d => ?_) (fun d hd => ?_)
    · filter_upwards [eventually_pow_div_two_pow_le d (by norm_num : (0 : ℝ) < 1 / 8)]
        with κ hκ
      refine (probOf_sampleSum_ne_zero_le _ _).trans ?_
      rw [← probOf_jackpot_ne_zero] at hκ
      exact hκ
    · filter_upwards [eventually_ge_atTop 3] with κ hκ
      exact probOf_coin_sum_eq_zero_le (le_trans hκ (Nat.le_self_pow (by omega) κ))

/-- **Pseudo-Nash, not negligible-slack Nash (unbounded utilities).** Picking
the coin dominates the jackpot, whose expected gain is `2 ^ κ - 1`. -/
theorem coin_isPseudoNash_not_isNegligibleNash :
    (binaryChoice (fun _ => coinPayoff) jackpot).IsPseudoNash (pickFirst _ _) ∧
      ¬ (binaryChoice (fun _ => coinPayoff) jackpot).IsNegligibleNash (pickFirst _ _) := by
  refine ⟨(binaryChoice_isPseudoNash_iff _ _).mpr
    coinPayoff_computationallyMeanDominates_jackpot, ?_⟩
  rw [binaryChoice_isNegligibleNash_iff]
  intro h
  obtain ⟨κ, hκ, hκ2⟩ := ((h 0).and (eventually_ge_atTop 2)).exists
  rw [lawMean_jackpot, lawMean_coinPayoff, pow_zero, inv_one] at hκ
  have : (4 : ℝ) ≤ 2 ^ κ := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ κ := pow_le_pow_right₀ (by norm_num) hκ2
  linarith

/-- Pays `κ` with probability `2 ^ (-κ)`. -/
def smallSpike (κ : ℕ) : PMF ℝ := spike (2 ^ κ) κ

/-- Half the mean of `smallSpike`, surely. -/
def halfMean (κ : ℕ) : PMF ℝ := PMF.pure ((κ : ℝ) / 2 ^ (κ + 1))

/-- **Strict Nash at every size, not pseudo-Nash, with utilities at most `κ`.**
Polynomially bounded utilities do not make per-size Nash imply pseudo-Nash. -/
theorem smallSpike_isNash_not_isPseudoNash :
    (∀ κ, 1 ≤ κ → lawMean (halfMean κ) < lawMean (smallSpike κ)) ∧
    (∀ κ, 1 ≤ κ → IsNash ((binaryChoice smallSpike halfMean).formAt κ)
      (euPreference ((binaryChoice smallSpike halfMean).utility κ))
      (pickFirst smallSpike halfMean)) ∧
    (binaryChoice smallSpike halfMean).PolyBoundedPayoffs ∧
    ¬ (binaryChoice smallSpike halfMean).IsPseudoNash (pickFirst smallSpike halfMean) := by
  have hmeans : ∀ κ, 1 ≤ κ → lawMean (halfMean κ) < lawMean (smallSpike κ) := by
    intro κ hκ
    rw [smallSpike, lawMean_spike, halfMean, lawMean, expect_pure]
    have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ
    push_cast
    rw [id, pow_succ]
    have h2 : (0 : ℝ) < 2 ^ κ := by positivity
    rw [div_lt_div_iff₀ (by positivity) h2]
    nlinarith
  refine ⟨hmeans, fun κ hκ => ?_, ?_, ?_⟩
  · have hA : ∀ x ∈ (smallSpike κ).support, |x| ≤ κ := fun x hx =>
      (abs_le_of_mem_support_spike (2 ^ κ) κ x hx).trans_eq (abs_of_nonneg (Nat.cast_nonneg κ))
    have hB : ∀ x ∈ (halfMean κ).support, |x| ≤ κ := by
      intro x hx
      rw [halfMean, PMF.mem_support_pure_iff] at hx
      rw [hx, abs_of_nonneg (by positivity)]
      exact div_le_self (Nat.cast_nonneg κ) (one_le_pow₀ (by norm_num))
    rw [binaryChoice_isNash_iff _ _ κ hA hB]
    exact (hmeans κ hκ).le
  · refine binaryChoice_polyBoundedPayoffs (b := 1) ?_ ?_
    · filter_upwards with κ x hx
      rw [pow_one]
      exact (abs_le_of_mem_support_spike (2 ^ κ) κ x hx).trans_eq
        (abs_of_nonneg (Nat.cast_nonneg κ))
    · filter_upwards with κ x hx
      rw [halfMean, PMF.mem_support_pure_iff] at hx
      rw [hx, pow_one, abs_of_nonneg (by positivity)]
      exact div_le_self (Nat.cast_nonneg κ) (one_le_pow₀ (by norm_num))
  · rw [binaryChoice_isPseudoNash_iff]
    refine not_computationallyMeanDominates_of_rare
      (fun κ => spike_nonneg (2 ^ κ) (Nat.cast_nonneg κ))
      (fun κ => pure_nonneg (by positivity)) (fun d => ?_) (fun d hd => ?_)
    · filter_upwards [eventually_pow_div_two_pow_le d (by norm_num : (0 : ℝ) < 1 / 8)]
        with κ hκ
      refine (probOf_sampleSum_ne_zero_le _ _).trans ?_
      refine le_trans ?_ hκ
      have hp := probOf_spike_ne_zero_le (2 ^ κ) (κ : ℝ)
      push_cast at hp
      exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with κ hκ
      rw [halfMean, probOf_sampleSum_pure_eq_zero
        (by have : (0 : ℝ) < κ := by exact_mod_cast hκ
            positivity) (Nat.one_le_pow _ _ (by omega))]
      norm_num

/-! ## The sample-size clause is necessary -/

/-- Mean dominance where the sample exponent need only be positive, instead of
exceeding the tolerance exponent. -/
def WeaklyComputationallyMeanDominates (X Y : ℕ → PMF ℝ) : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∃ d : ℕ, 1 ≤ d ∧
    ∀ᶠ κ : ℕ in atTop, meanComparisonGap (X κ) (Y κ) (κ ^ d) < ((κ : ℝ) ^ c)⁻¹

/-- Pays `κ ^ 3 + 2` with probability `1 / (κ ^ 3 + 1)`: its mean exceeds `1` by
`1 / (κ ^ 3 + 1)`. -/
def bonus (κ : ℕ) : PMF ℝ := spike (κ ^ 3 + 1) ((κ : ℝ) ^ 3 + 2)

theorem lawMean_bonus (κ : ℕ) : lawMean (bonus κ) = 1 + 1 / ((κ : ℝ) ^ 3 + 1) := by
  rw [bonus, lawMean_spike]
  push_cast
  field_simp
  ring

/-- **The clause `d > c` is necessary.** The constant `1` weakly dominates
`bonus`, whose expected gain `1 / (κ ^ 3 + 1)` is not negligible and whose
payoffs are at most `κ ^ 4`; under the paper's dominance it does not dominate. -/
theorem one_weaklyDominates_bonus :
    WeaklyComputationallyMeanDominates (fun _ => PMF.pure 1) bonus ∧
      ¬ ComputationallyMeanDominates (fun _ => PMF.pure 1) bonus := by
  have hone : ∀ x ∈ (PMF.pure (1 : ℝ)).support, 0 ≤ x := pure_nonneg zero_le_one
  have hbonus : ∀ κ, ∀ x ∈ (bonus κ).support, 0 ≤ x := fun κ =>
    spike_nonneg (κ ^ 3 + 1) (by positivity)
  constructor
  · intro c _
    refine ⟨1, le_rfl, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with κ hκ
    have hbound := (meanComparisonGap_bounds hone (hbonus κ) (κ ^ 1)).1
    have hzero : probOf (sampleSum (PMF.pure (1 : ℝ)) (κ ^ 1)) (· = 0) = 0 :=
      probOf_sampleSum_pure_eq_zero one_ne_zero (by rw [pow_one]; omega)
    have hrare : probOf (sampleSum (bonus κ) (κ ^ 1)) (· ≠ 0) ≤
        (κ : ℝ) * (1 / ((κ : ℝ) ^ 3 + 1)) := by
      refine (probOf_sampleSum_ne_zero_le _ _).trans ?_
      rw [pow_one]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg κ)
      have hp := probOf_spike_ne_zero_le (κ ^ 3 + 1) ((κ : ℝ) ^ 3 + 2)
      push_cast at hp
      exact hp
    have hκ2 : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
    have hsmall : (κ : ℝ) * (1 / ((κ : ℝ) ^ 3 + 1)) < 1 / 2 := by
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      have h1 : (4 : ℝ) ≤ κ * κ := by nlinarith
      have h2 : 4 * (κ : ℝ) ≤ κ * κ * κ := by nlinarith
      have h3 : (κ : ℝ) ^ 3 = κ * κ * κ := by ring
      linarith
    have hpos : (0 : ℝ) < ((κ : ℝ) ^ c)⁻¹ := by positivity
    linarith
  · intro h
    have hbd : ∀ᶠ κ : ℕ in atTop,
        (∀ x ∈ (PMF.pure (1 : ℝ)).support, |x| ≤ (κ : ℝ) ^ 4) ∧
          ∀ y ∈ (bonus κ).support, |y| ≤ (κ : ℝ) ^ 4 := by
      filter_upwards [eventually_ge_atTop 2] with κ hκ
      have hκ2 : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
      constructor
      · intro x hx
        rw [PMF.mem_support_pure_iff] at hx
        rw [hx, abs_one]
        exact one_le_pow₀ (by linarith)
      · intro y hy
        refine (abs_le_of_mem_support_spike _ _ y hy).trans ?_
        rw [abs_of_pos (by positivity)]
        have h8 : (8 : ℝ) ≤ (κ : ℝ) ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hκ2 3
          norm_num at this
          exact this
        have h4 : 2 * (κ : ℝ) ^ 3 ≤ (κ : ℝ) ^ 4 := by
          rw [show (κ : ℝ) ^ 4 = (κ : ℝ) ^ 3 * κ by ring]
          nlinarith
        linarith
    obtain ⟨κ, hκ, hκ2⟩ :=
      ((lawMean_le_of_computationallyMeanDominates hbd h 4).and (eventually_ge_atTop 2)).exists
    have hκr : (2 : ℝ) ≤ κ := by exact_mod_cast hκ2
    rw [lawMean_bonus, lawMean, expect_pure] at hκ
    have hlt : ((κ : ℝ) ^ 4)⁻¹ < 1 / ((κ : ℝ) ^ 3 + 1) := by
      rw [inv_eq_one_div, one_div_lt_one_div (by positivity) (by positivity)]
      have h8 : (8 : ℝ) ≤ (κ : ℝ) ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hκr 3
        norm_num at this
        exact this
      have h4 : 2 * (κ : ℝ) ^ 3 ≤ (κ : ℝ) ^ 4 := by
        rw [show (κ : ℝ) ^ 4 = (κ : ℝ) ^ 3 * κ by ring]
        nlinarith
      linarith
    simp only [id] at hκ
    linarith

/-! ## Sure negligible gains -/

/-- Honest play pays `1 - 2 ^ (-κ)` surely. -/
def nearlyOne (κ : ℕ) : PMF ℝ := PMF.pure (1 - 1 / 2 ^ κ)

/-- **Pseudo-Nash is not robust to negligible sure gains; a negligible payoff
tolerance is.** Against a sure `1`, the sure `1 - 2 ^ (-κ)` is negligible-slack
Nash and tolerant pseudo-Nash with tolerance `2 ^ (-κ)`, but not pseudo-Nash. -/
theorem sureGain_separation :
    (binaryChoice nearlyOne fun _ => PMF.pure 1).IsNegligibleNash (pickFirst _ _) ∧
      ¬ (binaryChoice nearlyOne fun _ => PMF.pure 1).IsPseudoNash (pickFirst _ _) ∧
      (binaryChoice nearlyOne fun _ => PMF.pure 1).IsTolerantPseudoNash
        (fun κ => 1 / 2 ^ κ) (pickFirst _ _) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [binaryChoice_isNegligibleNash_iff]
    intro a
    filter_upwards [negligible_inv_two_pow.eventually_abs_lt a] with κ hκ
    simp only [nearlyOne, lawMean, expect_pure, id]
    have := (abs_lt.mp hκ).2
    linarith
  · rw [binaryChoice_isPseudoNash_iff]
    intro h
    obtain ⟨d, hd, hev⟩ := h 1 le_rfl
    obtain ⟨κ, hgap, hκ⟩ := (hev.and (eventually_ge_atTop 2)).exists
    have hsub : (1 : ℝ) - 1 / 2 ^ κ < 1 := by
      have : (0 : ℝ) < 1 / 2 ^ κ := by positivity
      linarith
    rw [nearlyOne, meanComparisonGap_pure_of_lt hsub
      (Nat.one_le_pow _ _ (by omega))] at hgap
    have : ((κ : ℝ) ^ 1)⁻¹ ≤ 1 / 2 := by
      rw [pow_one, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hκ)
    linarith
  · have hshift : shiftEnsemble (fun κ => 1 / 2 ^ κ)
        ((binaryChoice nearlyOne fun _ => PMF.pure 1).utilityLaw () (pickFirst _ _)) =
          fun _ => PMF.pure 1 := by
      funext κ
      rw [binaryChoice_utilityLaw]
      change ((binaryChoice nearlyOne fun _ => PMF.pure 1).play κ (pickFirst _ _)).map
        (· + 1 / 2 ^ κ) = PMF.pure 1
      rw [binaryChoice_play_pickFirst, nearlyOne, PMF.pure_map]
      congr 1
      ring
    intro who replacement
    cases who
    rw [hshift, binaryChoice_utilityLaw]
    have hplay : (fun κ => (binaryChoice nearlyOne fun _ => PMF.pure 1).play κ
        (Profile.update (pickFirst _ _) () replacement)) =
          fun κ => if replacement then nearlyOne κ else PMF.pure 1 := by
      funext κ
      exact binaryChoice_play_update _ _ replacement κ
    rw [hplay]
    cases replacement
    · simpa using computationallyMeanDominates_refl (fun _ : ℕ => (PMF.pure 1 : PMF ℝ))
    · simp only [ite_true]
      intro c _
      refine ⟨c + 1, by omega, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with κ hκ
      have hm : 1 ≤ κ ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      rw [nearlyOne, meanComparisonGap_eq_aheadProb_sub, aheadProb_pure, aheadProb_pure]
      have hmpos : (0 : ℝ) < ((κ ^ (c + 1) : ℕ) : ℝ) := by exact_mod_cast hm
      have hlt : ((κ ^ (c + 1) : ℕ) : ℝ) * (1 - 1 / 2 ^ κ) < ((κ ^ (c + 1) : ℕ) : ℝ) * 1 :=
        mul_lt_mul_of_pos_left (by have : (0 : ℝ) < 1 / 2 ^ κ := by positivity
                                   linarith) hmpos
      simp only [hlt, not_lt.mpr hlt.le, ↓reduceIte]
      have : (0 : ℝ) < ((κ : ℝ) ^ c)⁻¹ := by
        have : (0 : ℝ) < κ := by exact_mod_cast hκ
        positivity
      linarith

/-! ## Statistical simulation -/

theorem statisticalDistance_jackpot (κ : ℕ) :
    statisticalDistance (jackpot κ) (PMF.pure 0) = 1 / 2 ^ κ := by
  rw [statisticalDistance_pure, ← probOf_jackpot_ne_zero]
  apply expect_congr_on_support
  intro x _
  by_cases hx : x = 0 <;> simp [hx]

/-- Take a sure `1` (`true`) or nothing. -/
abbrev safeOrNothing : ParameterizedGame Unit :=
  binaryChoice (fun _ => PMF.pure 1) (fun _ => PMF.pure 0)

/-- Take a sure `1` (`true`) or the jackpot. -/
abbrev safeOrJackpot : ParameterizedGame Unit :=
  binaryChoice (fun _ => PMF.pure 1) jackpot

/-- Taking the sure `1` when the alternative is nothing. -/
abbrev takeSafe : Profile safeOrNothing.sig := pickFirst (fun _ => PMF.pure 1) fun _ => PMF.pure 0

/-- Taking the sure `1` when the alternative is the jackpot. -/
abbrev takeSafeOverJackpot : Profile safeOrJackpot.sig := pickFirst (fun _ => PMF.pure 1) jackpot

private theorem indistinguishable_choice (choice : Bool) :
    IndistinguishableBy (polySampleTests ℝ)
      (fun κ => if choice then (PMF.pure 1 : PMF ℝ) else jackpot κ)
      (fun _ => if choice then (PMF.pure 1 : PMF ℝ) else PMF.pure 0) := by
  cases choice
  · simp only [Bool.false_eq_true, ite_false]
    refine indistinguishableBy_polySampleTests_of_statisticalDistance ?_
    simpa only [statisticalDistance_jackpot] using negligible_inv_two_pow
  · exact IndistinguishableBy.refl _ _

/-- The identity compilation statistically simulates the jackpot game by the
game with nothing in its place. -/
def jackpotSimulation : SecureImplementation (polySampleTests ℝ) safeOrNothing safeOrJackpot where
  compile _ choice := choice
  honest profile who := by
    cases who
    rw [binaryChoice_utilityLaw_if, binaryChoice_utilityLaw_if]
    exact indistinguishable_choice (profile ())
  simulate profile who deviation := by
    cases who
    refine ⟨deviation, ?_⟩
    rw [binaryChoice_utilityLaw_if, binaryChoice_utilityLaw_if]
    change IndistinguishableBy (polySampleTests ℝ)
      (fun κ => if Profile.update (Profile.map (fun _ choice => choice) profile) () deviation ()
        then (PMF.pure 1 : PMF ℝ) else jackpot κ)
      (fun κ => if Profile.update profile () deviation () then (PMF.pure 1 : PMF ℝ)
        else PMF.pure 0)
    rw [Profile.update_same, Profile.update_same]
    exact indistinguishable_choice deviation

theorem safe_isPseudoNash_source :
    safeOrNothing.IsPseudoNash takeSafe := by
  rw [binaryChoice_isPseudoNash_iff]
  have hbound : ∀ y : ℝ, ∀ x ∈ (PMF.pure y).support, |x| ≤ |y| := by
    intro y x hx
    rw [PMF.mem_support_pure_iff] at hx
    rw [hx]
  refine (computationallyMeanDominates_const_iff (R := 1) (fun x hx => ?_) (fun x hx => ?_)).mpr ?_
  · simpa using hbound 1 x hx
  · have := hbound 0 x hx
    rw [abs_zero] at this
    linarith [abs_nonneg x]
  · simp [lawMean, expect_pure]

/-- **Statistical simulation preserves pseudo-Nash but not the per-size
concepts.** Taking the sure `1` is Nash at every size in the source and
pseudo-Nash in the target, where it is Nash at no positive size and not
negligible-slack Nash. -/
theorem jackpotSimulation_preservation :
    (∀ κ, IsNash (safeOrNothing.formAt κ) (euPreference (safeOrNothing.utility κ))
      takeSafe) ∧
    safeOrJackpot.IsPseudoNash (Profile.map jackpotSimulation.compile takeSafe) ∧
    (∀ κ, 1 ≤ κ → ¬ IsNash (safeOrJackpot.formAt κ) (euPreference (safeOrJackpot.utility κ))
      takeSafeOverJackpot) ∧
    ¬ safeOrJackpot.IsNegligibleNash takeSafeOverJackpot := by
  have hpure : ∀ y : ℝ, ∀ x ∈ (PMF.pure y).support, |x| ≤ max |y| 1 := by
    intro y x hx
    rw [PMF.mem_support_pure_iff] at hx
    rw [hx]
    exact le_max_left _ _
  refine ⟨fun κ => ?_, jackpotSimulation.isPseudoNash_of_statistical safe_isPseudoNash_source,
    fun κ hκ => ?_, ?_⟩
  · rw [binaryChoice_isNash_iff _ _ κ (hpure 1) (fun x hx => (hpure 0 x hx).trans
      (by norm_num))]
    simp [lawMean, expect_pure]
  · have hjack : ∀ x ∈ (jackpot κ).support, |x| ≤ 4 ^ κ := fun x hx =>
      (abs_le_of_mem_support_spike (2 ^ κ) (4 ^ κ) x hx).trans_eq (abs_of_pos (by positivity))
    have h4 : (1 : ℝ) ≤ 4 ^ κ := one_le_pow₀ (by norm_num)
    rw [binaryChoice_isNash_iff _ _ κ (fun x hx => (hpure 1 x hx).trans (by simpa using h4))
      hjack, lawMean_jackpot]
    simp only [lawMean, expect_pure, id, not_le]
    exact one_lt_pow₀ (by norm_num) (by omega)
  · rw [binaryChoice_isNegligibleNash_iff]
    intro h
    obtain ⟨κ, hκ, hκ2⟩ := ((h 0).and (eventually_ge_atTop 2)).exists
    rw [lawMean_jackpot, pow_zero, inv_one] at hκ
    simp only [lawMean, expect_pure, id] at hκ
    have : (4 : ℝ) ≤ 2 ^ κ :=
      calc
        (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ κ := pow_le_pow_right₀ (by norm_num) hκ2
    linarith

end GameTheory.Tests.PseudoNash
