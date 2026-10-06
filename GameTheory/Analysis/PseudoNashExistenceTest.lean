/-
# Pseudo-Nash equilibria need not exist

Nash equilibria exist in finite games; pseudo-Nash equilibria of parameterized
games need not, even with one player, two options and payoffs in `[0, 1]`.

* **Strategies fixed across sizes.** Two sure payoffs that swap order with the
  parity of the size leave each option losing surely at infinitely many sizes.
  Strategies of parameterized games should therefore be allowed to depend on
  the size, as machines reading the size do.
* **Size-dependent and mixed strategies.** At size `κ` the rare option pays `1`
  with probability `1 / r`, where `r = 4 κ ^ s + 1` for a scale `s` that takes
  every value at arbitrarily large sizes, and the steady option pays half that
  mean surely. Dominance of the steady option at tolerance `κ ^ (-1)` supplies
  a sample exponent `d₁`, and dominance of the rare option at tolerance
  `κ ^ (-(2 d₁ + 1))` supplies `d₂ > 2 d₁ + 1`. At a size of scale `d₁`, a
  mixture putting probability at least `1/2` on the rare option falls behind
  the steady option at `κ ^ d₁` draws, and any other mixture falls behind the
  rare option at `κ ^ d₂` draws, by Chebyshev. Mixing afresh at every draw is
  the mixed extension of the ensemble form, whose random families are compared
  through their per-size marginals.

Every size's game has a strict pure Nash equilibrium, with a mean margin that is
polynomial at each size but whose exponent grows with the size. So the game has
no profile that is Nash with a polynomial margin, and existence cannot follow
from a per-size fixed-point theorem. Magnitudes play no role:
`ParameterizedGame.isPseudoNash_rescale_iff` makes existence invariant under
per-size rescaling.
-/
import GameTheory.Analysis.PseudoNashTest

noncomputable section

namespace GameTheory.Tests.PseudoNash

open Filter GameTheory GameTheory.Math GameTheory.Math.Probability
open GameTheory.Examples.PseudoEquilibria

/-! ## Strategies fixed across sizes -/

/-- Pays `1` at even sizes and `0` at odd ones, surely. -/
def evenPays (κ : ℕ) : PMF ℝ := PMF.pure (if Even κ then 1 else 0)

/-- Pays `1` at odd sizes and `0` at even ones, surely. -/
def oddPays (κ : ℕ) : PMF ℝ := PMF.pure (if Even κ then 0 else 1)

/-- An ensemble that loses surely at infinitely many sizes does not dominate. -/
private theorem not_dominates_of_frequently_loses {A B : ℕ → PMF ℝ}
    (hlose : ∀ N : ℕ, ∃ κ ≥ N, ∃ x y : ℝ, x < y ∧ A κ = PMF.pure x ∧ B κ = PMF.pure y) :
    ¬ ComputationallyMeanDominates A B := by
  intro h
  obtain ⟨d, _, hev⟩ := h 1 le_rfl
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨κ, hκ, x, y, hxy, hA, hB⟩ := hlose (N + 2)
  have hgap := hN κ (by omega)
  rw [hA, hB, meanComparisonGap_pure_of_lt hxy (Nat.one_le_pow _ _ (by omega))] at hgap
  have : ((κ : ℝ) ^ 1)⁻¹ ≤ 1 / 2 := by
    rw [pow_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 2 ≤ κ by omega))
  linarith

/-- **No pseudo-Nash equilibrium with size-independent strategies.** -/
theorem parity_no_pseudoNash (choice : Bool) :
    ¬ (binaryChoice evenPays oddPays).IsPseudoNash (fun _ => choice) := by
  rw [ParameterizedGame.isPseudoNash_iff]
  intro h
  have hlaw : ∀ (c : Bool), (binaryChoice evenPays oddPays).utilityLaw ()
      (Profile.update (fun _ => choice) () c) = fun κ => if c then evenPays κ else oddPays κ := by
    intro c
    rw [binaryChoice_utilityLaw]
    funext κ
    simp [Profile.update_same]
  have hbase : (binaryChoice evenPays oddPays).utilityLaw () (fun _ => choice) =
      fun κ => if choice then evenPays κ else oddPays κ := by
    rw [binaryChoice_utilityLaw]
  have hdom := h () (!choice)
  rw [hlaw, hbase] at hdom
  refine not_dominates_of_frequently_loses (fun N => ?_) hdom
  cases choice
  · refine ⟨2 * N, by omega, 0, 1, zero_lt_one, ?_, ?_⟩
    · simp [oddPays]
    · simp [evenPays]
  · refine ⟨2 * N + 1, by omega, 0, 1, zero_lt_one, ?_, ?_⟩
    · simp [evenPays]
    · simp [oddPays]

/-! ## Size-dependent strategies -/

/-- A one-player choice between two ensembles, with strategies that may depend on
the size. -/
@[reducible]
def adaptiveChoice (A B : ℕ → PMF ℝ) : ParameterizedGame Unit where
  sig := { Strategy := fun _ => ℕ → Bool, Outcome := ℝ }
  play κ profile := if profile () κ then A κ else B κ
  utility _ payoff _ := payoff

/-- The scale at size `κ`: the first component of its unpairing. -/
def scale (κ : ℕ) : ℕ := (Nat.unpair κ).1

/-- Every scale recurs at arbitrarily large sizes. -/
theorem exists_scale_eq (d N : ℕ) : ∃ κ ≥ N, scale κ = d :=
  ⟨Nat.pair d N, Nat.right_le_pair d N, by simp [scale, Nat.unpair_pair]⟩

/-- The inverse probability of a win of the rare option at size `κ`. -/
def rarity (κ : ℕ) : ℕ := 4 * κ ^ scale κ + 1

instance (κ : ℕ) : NeZero (rarity κ) := ⟨by rw [rarity]; omega⟩

/-- Pays `1` with probability `1 / rarity κ`. -/
def rareWin (κ : ℕ) : PMF ℝ := spike (rarity κ) 1

/-- Pays half the mean of `rareWin`, surely. -/
def steady (κ : ℕ) : PMF ℝ := PMF.pure (1 / (2 * (rarity κ : ℝ)))

theorem rarity_pos (κ : ℕ) : (0 : ℝ) < rarity κ := by
  rw [rarity]
  positivity

theorem one_le_rarity (κ : ℕ) : (1 : ℝ) ≤ rarity κ := by
  rw [rarity]
  push_cast
  have : (0 : ℝ) ≤ (κ : ℝ) ^ scale κ := by positivity
  linarith

theorem rareWin_nonneg (κ : ℕ) : ∀ x ∈ (rareWin κ).support, 0 ≤ x :=
  spike_nonneg (rarity κ) zero_le_one

theorem steady_nonneg (κ : ℕ) : ∀ x ∈ (steady κ).support, 0 ≤ x :=
  pure_nonneg (by have := rarity_pos κ; positivity)

theorem abs_le_one_of_mem_support_rareWin (κ : ℕ) : ∀ x ∈ (rareWin κ).support, |x| ≤ 1 :=
  fun x hx => (abs_le_of_mem_support_spike (rarity κ) 1 x hx).trans_eq abs_one

theorem abs_le_one_of_mem_support_steady (κ : ℕ) : ∀ x ∈ (steady κ).support, |x| ≤ 1 := by
  intro x hx
  rw [steady, PMF.mem_support_pure_iff] at hx
  have hr : (1 : ℝ) ≤ rarity κ := by
    rw [rarity]
    push_cast
    have : (0 : ℝ) ≤ (κ : ℝ) ^ scale κ := by positivity
    linarith
  rw [hx, abs_of_nonneg (by positivity), div_le_one (by positivity)]
  linarith

theorem lawMean_rareWin (κ : ℕ) : lawMean (rareWin κ) = 1 / rarity κ :=
  lawMean_spike (rarity κ) 1

theorem lawMean_steady (κ : ℕ) : lawMean (steady κ) = 1 / (2 * (rarity κ : ℝ)) := by
  rw [steady, lawMean, expect_pure, id]

/-! ## Comparisons against a sure payoff -/

theorem meanComparisonGap_pure_right (X : PMF ℝ) (y : ℝ) (m : ℕ) :
    meanComparisonGap X (PMF.pure y) m =
      1 - probOf (sampleSum X m) (fun s => m * y ≤ s) -
        probOf (sampleSum X m) (fun s => m * y < s) := by
  rw [meanComparisonGap_eq_aheadProb_sub, aheadProb_eq_expect, aheadProb_eq_expect,
    sampleSum_pure, expect_pure]
  have hbehind : expect (sampleSum X m) (fun t => if t < m * y then (1 : ℝ) else 0) =
      1 - probOf (sampleSum X m) (fun s => m * y ≤ s) := by
    rw [← expect_constant (sampleSum X m) 1,
      ← expect_sub (payoffIntegrable_constant _ _) (payoffIntegrable_eventIndicator _ _),
      expect_constant]
    refine expect_congr_on_support fun s _ => ?_
    by_cases h : s < m * y
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  rw [hbehind]
  congr 1
  refine expect_congr_on_support fun s _ => ?_
  rw [expect_pure]

/-! ## Mixed strategies -/

/-- Play the rare option with the probability `q` gives to `true`, afresh at
each draw. -/
def mixture (q : PMF Bool) (κ : ℕ) : PMF ℝ :=
  q.bind fun b => if b then rareWin κ else steady κ

theorem mixture_pure (b : Bool) (κ : ℕ) :
    mixture (PMF.pure b) κ = if b then rareWin κ else steady κ :=
  PMF.pure_bind _ _

theorem abs_le_one_of_mem_support_mixture (q : PMF Bool) (κ : ℕ) :
    ∀ x ∈ (mixture q κ).support, |x| ≤ 1 := by
  intro x hx
  rw [mixture, PMF.mem_support_bind_iff] at hx
  obtain ⟨b, _, hx⟩ := hx
  cases b
  · exact abs_le_one_of_mem_support_steady κ x hx
  · exact abs_le_one_of_mem_support_rareWin κ x hx

theorem mass_true_add_mass_false (q : PMF Bool) : (q true).toReal + (q false).toReal = 1 := by
  have h := expect_constant q 1
  rw [expect_eq_sum, Fintype.sum_bool] at h
  simpa using h

theorem expect_mixture (q : PMF Bool) (κ : ℕ) (f : ℝ → ℝ) {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    expect (mixture q κ) f =
      (q true).toReal * expect (rareWin κ) f + (q false).toReal * expect (steady κ) f := by
  rw [mixture, expect_bind_tower_bounded _ _ _ hf, expect_eq_sum, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]

theorem lawMean_mixture (q : PMF Bool) (κ : ℕ) :
    lawMean (mixture q κ) =
      (q true).toReal * lawMean (rareWin κ) + (q false).toReal * lawMean (steady κ) := by
  have hbound := abs_le_one_of_mem_support_mixture q κ
  rw [lawMean, mixture, expect_bind_tower q (fun b => if b then rareWin κ else steady κ) id
    (payoffIntegrable_of_bounded_on_support _ _ fun x hx => hbound x hx),
    expect_eq_sum, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, lawMean]

/-- The sure payoff of `steady`. -/
abbrev steadyValue (κ : ℕ) : ℝ := 1 / (2 * (rarity κ : ℝ))

theorem steadyValue_pos (κ : ℕ) : 0 < steadyValue κ := by
  have := rarity_pos κ
  positivity

theorem steadyValue_lt_one (κ : ℕ) : steadyValue κ < 1 := by
  have hr : (1 : ℝ) ≤ rarity κ := by
    rw [rarity]
    push_cast
    have : (0 : ℝ) ≤ (κ : ℝ) ^ scale κ := by positivity
    linarith
  rw [steadyValue, div_lt_one (by positivity)]
  linarith

theorem probOf_mixture_gt_le (q : PMF Bool) (κ : ℕ) :
    probOf (mixture q κ) (steadyValue κ < ·) ≤ 1 / rarity κ := by
  rw [probOf, expect_mixture q κ _ fun _ => abs_indicator_le _]
  have hrare : probOf (rareWin κ) (steadyValue κ < ·) ≤ 1 / rarity κ := by
    refine le_trans ?_ (probOf_spike_ne_zero_le (rarity κ) (1 : ℝ))
    refine expect_mono (fun x _ => ?_) (payoffIntegrable_eventIndicator _ _)
      (payoffIntegrable_eventIndicator _ _)
    have := steadyValue_pos κ
    by_cases hx : steadyValue κ < x
    · have : x ≠ 0 := by linarith
      simp only [hx, ↓reduceIte]
      simp [this]
    · simp only [hx, ↓reduceIte]
      exact indicator_nonneg _
  have hsteady : probOf (steady κ) (steadyValue κ < ·) = 0 := by
    rw [probOf, steady, expect_pure]
    simp
  have hmass := mass_true_add_mass_false q
  have ht : 0 ≤ (q true).toReal := ENNReal.toReal_nonneg
  have hf : 0 ≤ (q false).toReal := ENNReal.toReal_nonneg
  have hrare0 : 0 ≤ probOf (rareWin κ) (steadyValue κ < ·) :=
    expect_nonneg _ _ fun _ _ => indicator_nonneg _
  have hr1 : 1 / (rarity κ : ℝ) ≤ 1 := by
    rw [div_le_one (rarity_pos κ)]
    exact one_le_rarity κ
  change (q true).toReal * probOf (rareWin κ) (steadyValue κ < ·) +
    (q false).toReal * probOf (steady κ) (steadyValue κ < ·) ≤ _
  rw [hsteady]
  nlinarith

theorem probOf_mixture_eq (q : PMF Bool) (κ : ℕ) :
    probOf (mixture q κ) (· = steadyValue κ) = (q false).toReal := by
  rw [probOf, expect_mixture q κ _ fun _ => abs_indicator_le _]
  have hrare : probOf (rareWin κ) (· = steadyValue κ) = 0 := by
    rw [probOf]
    refine (expect_congr_on_support (g := fun _ => (0 : ℝ)) fun x hx => ?_).trans
      (expect_constant _ 0)
    rw [rareWin, spike, PMF.mem_support_map_iff] at hx
    obtain ⟨i, _, rfl⟩ := hx
    have h0 := steadyValue_pos κ
    have h1 := steadyValue_lt_one κ
    split_ifs with hi hv hv <;> first | (exfalso; linarith) | norm_num
  have hsteady : probOf (steady κ) (· = steadyValue κ) = 1 := by
    rw [probOf, steady, expect_pure]
    simp
  change (q true).toReal * probOf (rareWin κ) (· = steadyValue κ) +
    (q false).toReal * probOf (steady κ) (· = steadyValue κ) = _
  rw [hrare, hsteady]
  ring

/-- **Mostly rare falls behind steady** at `κ ^ scale κ` samples: when the rare
option has probability at least `1/2`, the draws usually neither pay `1` nor
all equal the steady payoff. -/
theorem quarter_le_meanComparisonGap_mixture_steady (q : PMF Bool) {κ : ℕ} (hκ : 2 ≤ κ)
    (hscale : 1 ≤ scale κ) (hq : (q false).toReal ≤ 1 / 2) :
    1 / 4 ≤ meanComparisonGap (mixture q κ) (steady κ) (κ ^ scale κ) := by
  set m := κ ^ scale κ
  rw [steady, meanComparisonGap_pure_right]
  have hge := probOf_sampleSum_ge_le (mixture q κ) (steadyValue κ) m
  have hgt := probOf_sampleSum_gt_le (mixture q κ) (steadyValue κ) m
  rw [probOf_mixture_eq] at hge
  have hp := probOf_mixture_gt_le q κ
  have hp0 : 0 ≤ probOf (mixture q κ) (steadyValue κ < ·) :=
    expect_nonneg _ _ fun _ _ => indicator_nonneg _
  have hm2 : 2 ≤ m := le_trans hκ (by
    calc κ = κ ^ 1 := (pow_one κ).symm
      _ ≤ κ ^ scale κ := Nat.pow_le_pow_right (by omega) hscale)
  have hmr : (m : ℝ) * (1 / rarity κ) ≤ 1 / 4 := by
    rw [rarity, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    simp only [m]
    push_cast
    linarith
  have hmp : (m : ℝ) * probOf (mixture q κ) (steadyValue κ < ·) ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hmr
  have hpow : (q false).toReal ^ m ≤ 1 / 4 :=
    calc
      (q false).toReal ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ ENNReal.toReal_nonneg hq m
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm2
      _ = 1 / 4 := by norm_num
  change 1 / 4 ≤ 1 - probOf (sampleSum (mixture q κ) m) (fun s => m * steadyValue κ ≤ s) -
    probOf (sampleSum (mixture q κ) m) (fun s => m * steadyValue κ < s)
  linarith

/-- **A law of mean at most `3 / (4 r)` falls behind the rare option** at
`κ ^ d` samples with `d ≥ 2 scale κ + 2`, for `κ ≥ 160`, by Chebyshev. -/
theorem half_le_meanComparisonGap_rareWin {X : PMF ℝ} (hX : ∀ x ∈ X.support, |x| ≤ 1)
    {κ d : ℕ} (hmean : lawMean X ≤ 3 / (4 * (rarity κ : ℝ))) (hκ : 160 ≤ κ)
    (hd : 2 * scale κ + 2 ≤ d) :
    1 / 2 ≤ meanComparisonGap X (rareWin κ) (κ ^ d) := by
  have hr0 := rarity_pos κ
  have hlt : lawMean X < lawMean (rareWin κ) := by
    rw [lawMean_rareWin]
    have : 3 / (4 * (rarity κ : ℝ)) < 1 / rarity κ := by
      rw [div_lt_div_iff₀ (by positivity) hr0]
      linarith
    linarith
  have hlower := one_sub_le_meanComparisonGap_of_lt hX
    (abs_le_one_of_mem_support_rareWin κ) hlt (m := κ ^ d) (Nat.one_le_pow _ _ (by omega))
  set V := lawVariance (differenceLaw X (rareWin κ))
  have hV : V ≤ 16 := by
    have := lawVariance_le (abs_le_of_mem_support_differenceLaw hX
      (abs_le_one_of_mem_support_rareWin κ))
    norm_num at this
    exact this
  set Δ := lawMean (rareWin κ) - lawMean X
  have hK : (160 : ℝ) ≤ κ := by exact_mod_cast hκ
  set K : ℝ := (κ : ℝ)
  set P : ℝ := K ^ scale κ
  have hP : 1 ≤ P := one_le_pow₀ (by linarith)
  have hr : (rarity κ : ℝ) = 4 * P + 1 := by
    rw [rarity]
    push_cast
    rfl
  have hΔ : 1 / (4 * (4 * P + 1)) ≤ Δ := by
    simp only [Δ, lawMean_rareWin]
    rw [hr] at hmean ⊢
    have : 1 / (4 * P + 1) - 3 / (4 * (4 * P + 1)) = 1 / (4 * (4 * P + 1)) := by
      field_simp
      ring
    linarith
  have hm : P ^ 2 * K ^ 2 ≤ ((κ ^ d : ℕ) : ℝ) := by
    push_cast
    calc
      P ^ 2 * K ^ 2 = K ^ (2 * scale κ + 2) := by simp only [P]; ring
      _ ≤ K ^ d := pow_le_pow_right₀ (by linarith) hd
  have hden : K ^ 2 / 400 ≤ ((κ ^ d : ℕ) : ℝ) * Δ ^ 2 := by
    have hsq : 1 / (400 * P ^ 2) ≤ Δ ^ 2 := by
      have hpos : 0 < 1 / (4 * (4 * P + 1)) := by positivity
      refine le_trans ?_ (pow_le_pow_left₀ hpos.le hΔ 2)
      rw [div_pow, one_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc
      K ^ 2 / 400 = P ^ 2 * K ^ 2 * (1 / (400 * P ^ 2)) := by
        field_simp
      _ ≤ ((κ ^ d : ℕ) : ℝ) * Δ ^ 2 := mul_le_mul hm hsq (by positivity) (by positivity)
  have hdenpos : 0 < ((κ ^ d : ℕ) : ℝ) * Δ ^ 2 := by
    have : 0 < K ^ 2 / 400 := by positivity
    linarith
  have hratio : V / (((κ ^ d : ℕ) : ℝ) * Δ ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  have hlower' : 1 - 2 * (V / (((κ ^ d : ℕ) : ℝ) * Δ ^ 2)) ≤
      meanComparisonGap X (rareWin κ) (κ ^ d) := hlower
  linarith

/-- **No mixed choice dominates both pure options.** At the sizes of a scale
`d₁` supplied by dominance of the steady option at tolerance `κ ^ (-1)`, a
mixture that is mostly rare loses to the steady option at `κ ^ d₁` samples, and
one that is mostly steady loses to the rare option at the sample exponent
supplied for tolerance `κ ^ (-(2 d₁ + 1))`. -/
theorem not_dominates_both (q : ℕ → PMF Bool) :
    ¬ (ComputationallyMeanDominates (fun κ => mixture (q κ) κ) steady ∧
      ComputationallyMeanDominates (fun κ => mixture (q κ) κ) rareWin) := by
  rintro ⟨hsteady, hrare⟩
  obtain ⟨d₁, hd₁, hev₁⟩ := hsteady 1 le_rfl
  obtain ⟨d₂, hd₂, hev₂⟩ := hrare (2 * d₁ + 1) (by omega)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev₁.and hev₂)
  obtain ⟨κ, hκN, hscale⟩ := exists_scale_eq d₁ (N + 160)
  obtain ⟨h1, h2⟩ := hN κ (by omega)
  have hK : (160 : ℝ) ≤ κ := by exact_mod_cast (show 160 ≤ κ by omega)
  have hsmall : ∀ c : ℕ, 1 ≤ c → ((κ : ℝ) ^ c)⁻¹ ≤ 1 / 4 := by
    intro c hc
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    calc
      (4 : ℝ) ≤ κ := by linarith
      _ = (κ : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (κ : ℝ) ^ c := pow_le_pow_right₀ (by linarith) hc
  by_cases hq : ((q κ) false).toReal ≤ 1 / 2
  · have := quarter_le_meanComparisonGap_mixture_steady (q κ) (κ := κ) (by omega)
      (by omega) hq
    rw [hscale] at this
    have := hsmall 1 le_rfl
    linarith
  · have hmean : lawMean (mixture (q κ) κ) ≤ 3 / (4 * (rarity κ : ℝ)) := by
      rw [lawMean_mixture, lawMean_rareWin, lawMean_steady]
      have hmass := mass_true_add_mass_false (q κ)
      have hr0 := rarity_pos κ
      rw [not_le] at hq
      rw [show (q κ true).toReal = 1 - (q κ false).toReal by linarith]
      rw [show (1 - (q κ false).toReal) * (1 / (rarity κ : ℝ)) +
          (q κ false).toReal * (1 / (2 * (rarity κ : ℝ))) =
          (2 - (q κ false).toReal) / (2 * rarity κ) by field_simp; ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := half_le_meanComparisonGap_rareWin (abs_le_one_of_mem_support_mixture (q κ) κ)
      (d := d₂) hmean (by omega) (by omega)
    have := hsmall (2 * d₁ + 1) (by omega)
    linarith

/-! ## The games -/

theorem adaptiveChoice_utilityLaw (A B : ℕ → PMF ℝ)
    (profile : Profile (adaptiveChoice A B).sig) :
    (adaptiveChoice A B).utilityLaw () profile =
      fun κ => if profile () κ then A κ else B κ := by
  funext κ
  exact PMF.map_id _

/-- **No pseudo-Nash equilibrium, with size-dependent strategies and payoffs in
`[0, 1]`.** -/
theorem multiScale_no_pseudoNash (profile : Profile (adaptiveChoice rareWin steady).sig) :
    ¬ (adaptiveChoice rareWin steady).IsPseudoNash profile := by
  rw [ParameterizedGame.isPseudoNash_iff]
  intro h
  have hlaw : ∀ σ : ℕ → Bool,
      (fun κ => if σ κ then rareWin κ else steady κ) = fun κ => mixture (PMF.pure (σ κ)) κ :=
    fun σ => funext fun κ => (mixture_pure _ _).symm
  have hsteady := h () fun _ => false
  have hrare := h () fun _ => true
  rw [adaptiveChoice_utilityLaw, adaptiveChoice_utilityLaw, Profile.update_same, hlaw] at hsteady
  rw [adaptiveChoice_utilityLaw, adaptiveChoice_utilityLaw, Profile.update_same, hlaw] at hrare
  simp only [mixture_pure, Bool.false_eq_true, ↓reduceIte] at hsteady hrare
  exact not_dominates_both (fun κ => PMF.pure (profile () κ))
    ⟨by simpa only [mixture_pure] using hsteady, by simpa only [mixture_pure] using hrare⟩

/-- The payoffs are bounded by `1 = κ ^ 0`. -/
theorem multiScale_polyBoundedPayoffs : (adaptiveChoice rareWin steady).PolyBoundedPayoffs := by
  refine ⟨0, Eventually.of_forall fun κ who profile x hx => ?_⟩
  rw [adaptiveChoice_utilityLaw] at hx
  rw [pow_zero]
  dsimp only at hx
  split_ifs at hx
  · exact abs_le_one_of_mem_support_rareWin κ x hx
  · exact abs_le_one_of_mem_support_steady κ x hx

/-- The same choice with mixed strategies: at each size a strategy is a law on
the two options, and each draw of the outcome draws the option afresh. -/
@[reducible]
def mixedChoice (A B : ℕ → PMF ℝ) : ParameterizedGame Unit where
  sig := { Strategy := fun _ => ℕ → PMF Bool, Outcome := ℝ }
  play κ profile := (profile () κ).bind fun b => if b then A κ else B κ
  utility _ payoff _ := payoff

theorem mixedChoice_utilityLaw (profile : Profile (mixedChoice rareWin steady).sig) :
    (mixedChoice rareWin steady).utilityLaw () profile =
      fun κ => mixture (profile () κ) κ := by
  funext κ
  exact PMF.map_id _

/-- **Mixing does not restore existence.** -/
theorem multiScale_no_mixed_pseudoNash (profile : Profile (mixedChoice rareWin steady).sig) :
    ¬ (mixedChoice rareWin steady).IsPseudoNash profile := by
  rw [ParameterizedGame.isPseudoNash_iff]
  intro h
  have hsteady := h () fun _ => PMF.pure false
  have hrare := h () fun _ => PMF.pure true
  rw [mixedChoice_utilityLaw, mixedChoice_utilityLaw, Profile.update_same] at hsteady hrare
  simp only [mixture_pure, Bool.false_eq_true, ↓reduceIte] at hsteady hrare
  exact not_dominates_both (profile ()) ⟨hsteady, hrare⟩

/-- The multi-scale choice has no polynomially strict profile,
although picking the rare option is strict Nash at every size with margin
`1 / (2 (4 κ ^ s + 1))`. -/
theorem multiScale_not_isPolyStrictNash
    (profile : Profile (adaptiveChoice rareWin steady).sig) :
    ¬ (adaptiveChoice rareWin steady).IsPolynomiallyStrictNash profile := fun h =>
  multiScale_no_pseudoNash profile
    (ParameterizedGame.isPseudoNash_of_isPolynomiallyStrictNash multiScale_polyBoundedPayoffs h)

end GameTheory.Tests.PseudoNash
