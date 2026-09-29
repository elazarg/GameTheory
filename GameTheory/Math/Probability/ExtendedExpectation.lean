/-
# Extended-real expectation

The real `expect` vanishes on a non-integrable payoff, so it cannot compare
laws whose expectation is infinite. A payoff whose losses have infinite
expectation has the definite value `−∞`, and such a law should lose every
comparison rather than be incomparable. This file splits a payoff into its
positive and negative parts, takes each part's expectation in `ℝ≥0∞`, and
defines the expectation in `EReal` as their difference. The expectation exists
unless both parts are infinite; only then is the value genuinely undefined.
-/

import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationMap
import Mathlib.Data.EReal.Operations

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

variable {α β : Type*}

/-- Expectation of the positive part of a payoff. -/
def positiveExpect (μ : PMF α) (f : α → ℝ) : ℝ≥0∞ :=
  ∑' a, μ a * ENNReal.ofReal (f a)

/-- Expectation of the negative part of a payoff. -/
def negativeExpect (μ : PMF α) (f : α → ℝ) : ℝ≥0∞ :=
  ∑' a, μ a * ENNReal.ofReal (-f a)

/-- The expectation exists in `EReal`: the positive and negative parts are not
both infinite. -/
def HasExpectation (μ : PMF α) (f : α → ℝ) : Prop :=
  positiveExpect μ f ≠ ⊤ ∨ negativeExpect μ f ≠ ⊤

/-- The expectation in `EReal`. It is meaningful when `HasExpectation μ f`
holds; for a payoff whose two parts are both infinite it is the junk value
`⊥`, and comparisons state `HasExpectation` explicitly. -/
def extendedExpect (μ : PMF α) (f : α → ℝ) : EReal :=
  (positiveExpect μ f : EReal) - negativeExpect μ f

theorem negativeExpect_eq_positiveExpect_neg (μ : PMF α) (f : α → ℝ) :
    negativeExpect μ f = positiveExpect μ (fun a => -f a) := rfl

private theorem weighted_ofReal (μ : PMF α) (a : α) (x : ℝ) :
    μ a * ENNReal.ofReal x = ENNReal.ofReal ((μ a).toReal * x) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top μ a)]

private theorem tsum_ofReal_ne_top_iff {g : α → ℝ} (hg : ∀ a, 0 ≤ g a) :
    ∑' a, ENNReal.ofReal (g a) ≠ ⊤ ↔ Summable g := by
  constructor
  · intro h
    have := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal (hg _)] using this
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg hg h]
    exact ENNReal.ofReal_ne_top

private theorem positiveExpect_eq (μ : PMF α) (f : α → ℝ) :
    positiveExpect μ f = ∑' a, ENNReal.ofReal (max ((μ a).toReal * f a) 0) := by
  unfold positiveExpect
  refine tsum_congr fun a => ?_
  rw [weighted_ofReal, ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)]

private theorem negativeExpect_eq (μ : PMF α) (f : α → ℝ) :
    negativeExpect μ f = ∑' a, ENNReal.ofReal (max (-((μ a).toReal * f a)) 0) := by
  unfold negativeExpect
  refine tsum_congr fun a => ?_
  rw [weighted_ofReal, ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _), mul_neg]

/-- A payoff is integrable exactly when both of its parts have finite
expectation. -/
theorem payoffIntegrable_iff_parts (μ : PMF α) (f : α → ℝ) :
    PayoffIntegrable μ f ↔ positiveExpect μ f ≠ ⊤ ∧ negativeExpect μ f ≠ ⊤ := by
  rw [positiveExpect_eq, negativeExpect_eq,
    tsum_ofReal_ne_top_iff (fun _ => le_max_right _ _),
    tsum_ofReal_ne_top_iff (fun _ => le_max_right _ _)]
  have habs (a : α) : (μ a).toReal * |f a| =
      max ((μ a).toReal * f a) 0 + max (-((μ a).toReal * f a)) 0 := by
    rw [← abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ (μ a).toReal), ← abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg]
    rcases le_total 0 ((μ a).toReal * f a) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  constructor
  · intro h
    refine ⟨h.of_nonneg_of_le (fun _ => le_max_right _ _) fun a => ?_,
      h.of_nonneg_of_le (fun _ => le_max_right _ _) fun a => ?_⟩ <;>
      · rw [habs]; linarith [le_max_right ((μ a).toReal * f a) 0,
          le_max_right (-((μ a).toReal * f a)) 0]
  · rintro ⟨hpos, hneg⟩
    unfold PayoffIntegrable
    simp_rw [habs]
    exact hpos.add hneg

theorem hasExpectation_of_payoffIntegrable {μ : PMF α} {f : α → ℝ}
    (h : PayoffIntegrable μ f) : HasExpectation μ f :=
  Or.inl ((payoffIntegrable_iff_parts μ f).1 h).1

/-- On an integrable payoff the extended expectation is the real one. -/
theorem extendedExpect_eq_expect {μ : PMF α} {f : α → ℝ}
    (h : PayoffIntegrable μ f) : extendedExpect μ f = (expect μ f : EReal) := by
  have hpos : Summable (fun a => max ((μ a).toReal * f a) 0) := by
    have := ((payoffIntegrable_iff_parts μ f).1 h).1
    rwa [positiveExpect_eq, tsum_ofReal_ne_top_iff (fun _ => le_max_right _ _)] at this
  have hneg : Summable (fun a => max (-((μ a).toReal * f a)) 0) := by
    have := ((payoffIntegrable_iff_parts μ f).1 h).2
    rwa [negativeExpect_eq, tsum_ofReal_ne_top_iff (fun _ => le_max_right _ _)] at this
  unfold extendedExpect
  rw [positiveExpect_eq, negativeExpect_eq,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) hpos,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) hneg,
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (tsum_nonneg fun _ => le_max_right _ _),
    max_eq_left (tsum_nonneg fun _ => le_max_right _ _), ← EReal.coe_sub,
    ← hpos.tsum_sub hneg]
  congr 1
  unfold expect
  refine tsum_congr fun a => ?_
  rcases le_total 0 ((μ a).toReal * f a) with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
  · rw [max_eq_right hx, max_eq_left (by linarith)]; ring

/-- Pointwise domination on the support orders extended expectations. No
existence hypothesis is needed: the junk value `⊥` is the least element. -/
theorem extendedExpect_mono {μ : PMF α} {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a ≤ g a) : extendedExpect μ f ≤ extendedExpect μ g := by
  have hterm (u v : α → ℝ) (huv : ∀ a ∈ μ.support, u a ≤ v a) :
      ∑' a, μ a * ENNReal.ofReal (u a) ≤ ∑' a, μ a * ENNReal.ofReal (v a) := by
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ μ.support
    · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (huv a ha))
    · rw [(PMF.apply_eq_zero_iff μ a).2 ha, zero_mul, zero_mul]
  have hpos := hterm f g h
  have hneg := hterm (fun a => -g a) (fun a => -f a) fun a ha => neg_le_neg (h a ha)
  exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hpos)
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 hneg)

theorem extendedExpect_congr_on_support {μ : PMF α} {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a = g a) : extendedExpect μ f = extendedExpect μ g :=
  le_antisymm (extendedExpect_mono fun a ha => (h a ha).le)
    (extendedExpect_mono fun a ha => (h a ha).ge)

@[simp]
theorem extendedExpect_constant (μ : PMF α) (c : ℝ) :
    extendedExpect μ (fun _ => c) = c := by
  rw [extendedExpect_eq_expect (payoffIntegrable_constant μ c), expect_constant]

@[simp]
theorem extendedExpect_pure (a : α) (f : α → ℝ) :
    extendedExpect (PMF.pure a) f = f a := by
  rw [extendedExpect_eq_expect (payoffIntegrable_pure a f), expect_pure]

theorem extendedExpect_map (g : α → β) (μ : PMF α) (f : β → ℝ) :
    extendedExpect (μ.map g) f = extendedExpect μ (f ∘ g) := by
  unfold extendedExpect positiveExpect negativeExpect
  rw [tsum_map_mul g μ (fun b => ENNReal.ofReal (f b)),
    tsum_map_mul g μ (fun b => ENNReal.ofReal (-f b))]
  rfl

theorem hasExpectation_map_iff (g : α → β) (μ : PMF α) (f : β → ℝ) :
    HasExpectation (μ.map g) f ↔ HasExpectation μ (f ∘ g) := by
  unfold HasExpectation positiveExpect negativeExpect
  rw [tsum_map_mul g μ (fun b => ENNReal.ofReal (f b)),
    tsum_map_mul g μ (fun b => ENNReal.ofReal (-f b))]
  rfl

/-- Two laws with the same observed law have the same extended expectation of
any payoff of the observation. -/
theorem extendedExpect_observed_law_eq {Observation : Type*} (μ : PMF α) (ν : PMF β)
    (f : α → Observation) (g : β → Observation) (value : Observation → ℝ)
    (hlaw : μ.map f = ν.map g) :
    extendedExpect μ (value ∘ f) = extendedExpect ν (value ∘ g) := by
  rw [← extendedExpect_map f μ value, ← extendedExpect_map g ν value, hlaw]

theorem hasExpectation_observed_law_iff {Observation : Type*} (μ : PMF α) (ν : PMF β)
    (f : α → Observation) (g : β → Observation) (value : Observation → ℝ)
    (hlaw : μ.map f = ν.map g) :
    HasExpectation μ (value ∘ f) ↔ HasExpectation ν (value ∘ g) := by
  rw [← hasExpectation_map_iff f μ value, ← hasExpectation_map_iff g ν value, hlaw]

/-! ## Infinite values -/

/-- Infinite expected losses give the value `⊥`, whatever the gains. -/
theorem extendedExpect_eq_bot_of_negativeExpect_eq_top {μ : PMF α} {f : α → ℝ}
    (hneg : negativeExpect μ f = ⊤) : extendedExpect μ f = ⊥ := by
  unfold extendedExpect
  rw [hneg, EReal.coe_ennreal_top, EReal.sub_top]

/-- Infinite expected gains and finite expected losses give the value `⊤`. -/
theorem extendedExpect_eq_top {μ : PMF α} {f : α → ℝ}
    (hpos : positiveExpect μ f = ⊤) (hneg : negativeExpect μ f ≠ ⊤) :
    extendedExpect μ f = ⊤ := by
  unfold extendedExpect
  rw [hpos, EReal.coe_ennreal_top, ← ENNReal.ofReal_toReal hneg,
    EReal.coe_ennreal_ofReal, EReal.top_sub_coe]

/-! ## Positive affine transformations -/

private theorem tsum_weighted_const (μ : PMF α) (x : ℝ≥0∞) :
    ∑' a, μ a * x = x := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem positiveExpect_affine_le {μ : PMF α} {f : α → ℝ} {c : ℝ} (b : ℝ)
    (hc : 0 ≤ c) :
    positiveExpect μ (fun a => c * f a + b) ≤
      ENNReal.ofReal c * positiveExpect μ f + ENNReal.ofReal b := by
  unfold positiveExpect
  calc
    ∑' a, μ a * ENNReal.ofReal (c * f a + b) ≤
        ∑' a, (ENNReal.ofReal c * (μ a * ENNReal.ofReal (f a)) +
          μ a * ENNReal.ofReal b) := by
      refine ENNReal.tsum_le_tsum fun a => ?_
      calc
        μ a * ENNReal.ofReal (c * f a + b) ≤
            μ a * (ENNReal.ofReal (c * f a) + ENNReal.ofReal b) :=
          mul_le_mul' le_rfl ENNReal.ofReal_add_le
        _ = _ := by rw [ENNReal.ofReal_mul hc]; ring
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_weighted_const]

private theorem positiveExpect_le_affine {μ : PMF α} {f : α → ℝ} {c : ℝ} (b : ℝ)
    (hc : 0 ≤ c) :
    ENNReal.ofReal c * positiveExpect μ f ≤
      positiveExpect μ (fun a => c * f a + b) + ENNReal.ofReal (-b) := by
  unfold positiveExpect
  rw [← tsum_weighted_const μ (ENNReal.ofReal (-b)), ← ENNReal.tsum_add,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  calc
    ENNReal.ofReal c * (μ a * ENNReal.ofReal (f a)) =
        μ a * ENNReal.ofReal (c * f a + b + -b) := by
      rw [add_neg_cancel_right, ENNReal.ofReal_mul hc]; ring
    _ ≤ μ a * (ENNReal.ofReal (c * f a + b) + ENNReal.ofReal (-b)) :=
      mul_le_mul' le_rfl ENNReal.ofReal_add_le
    _ = _ := by ring

theorem positiveExpect_affine_eq_top_iff {μ : PMF α} {f : α → ℝ} {c : ℝ} (b : ℝ)
    (hc : 0 < c) :
    positiveExpect μ (fun a => c * f a + b) = ⊤ ↔ positiveExpect μ f = ⊤ := by
  constructor
  · intro h
    by_contra hf
    have hup := positiveExpect_affine_le (μ := μ) (f := f) b hc.le
    rw [h, top_le_iff] at hup
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf,
      ENNReal.ofReal_ne_top⟩ hup
  · intro h
    have hdown := positiveExpect_le_affine (μ := μ) (f := f) b hc.le
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne', top_le_iff,
      ENNReal.add_eq_top] at hdown
    exact hdown.resolve_right ENNReal.ofReal_ne_top

theorem negativeExpect_affine_eq_top_iff {μ : PMF α} {f : α → ℝ} {c : ℝ} (b : ℝ)
    (hc : 0 < c) :
    negativeExpect μ (fun a => c * f a + b) = ⊤ ↔ negativeExpect μ f = ⊤ := by
  have hrewrite : negativeExpect μ (fun a => c * f a + b) =
      positiveExpect μ (fun a => c * (-f a) + -b) := by
    unfold negativeExpect positiveExpect
    refine tsum_congr fun a => ?_
    ring_nf
  rw [hrewrite, positiveExpect_affine_eq_top_iff (-b) hc]
  rfl

theorem hasExpectation_affine_iff {μ : PMF α} {f : α → ℝ} {c : ℝ} (b : ℝ)
    (hc : 0 < c) :
    HasExpectation μ (fun a => c * f a + b) ↔ HasExpectation μ f := by
  unfold HasExpectation
  rw [Ne, Ne, Ne, Ne, positiveExpect_affine_eq_top_iff b hc,
    negativeExpect_affine_eq_top_iff b hc]

/-- A positive affine transformation of the payoff transforms the extended
expectation in the same way, in every case. -/
theorem extendedExpect_affine (μ : PMF α) (f : α → ℝ) {c : ℝ} (b : ℝ)
    (hc : 0 < c) :
    extendedExpect μ (fun a => c * f a + b) = c * extendedExpect μ f + b := by
  by_cases hneg : negativeExpect μ f = ⊤
  · rw [extendedExpect_eq_bot_of_negativeExpect_eq_top hneg,
      extendedExpect_eq_bot_of_negativeExpect_eq_top
        ((negativeExpect_affine_eq_top_iff b hc).2 hneg),
      EReal.coe_mul_bot_of_pos hc, EReal.bot_add]
  by_cases hpos : positiveExpect μ f = ⊤
  · rw [extendedExpect_eq_top hpos hneg,
      extendedExpect_eq_top ((positiveExpect_affine_eq_top_iff b hc).2 hpos)
        (mt (negativeExpect_affine_eq_top_iff b hc).1 hneg),
      EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]
  have hf : PayoffIntegrable μ f := (payoffIntegrable_iff_parts μ f).2 ⟨hpos, hneg⟩
  have hscaled : PayoffIntegrable μ (fun a => c * f a) := payoffIntegrable_const_mul hf
  rw [extendedExpect_eq_expect (payoffIntegrable_add hscaled (payoffIntegrable_constant μ b)),
    extendedExpect_eq_expect hf, expect_add hscaled (payoffIntegrable_constant μ b),
    expect_const_mul, expect_constant]
  norm_cast

/-- An integrable payoff has a finite extended expectation. -/
theorem extendedExpect_ne_top_of_payoffIntegrable {μ : PMF α} {f : α → ℝ}
    (h : PayoffIntegrable μ f) : extendedExpect μ f ≠ ⊤ := by
  rw [extendedExpect_eq_expect h]; exact EReal.coe_ne_top _

theorem extendedExpect_ne_bot_of_payoffIntegrable {μ : PMF α} {f : α → ℝ}
    (h : PayoffIntegrable μ f) : extendedExpect μ f ≠ ⊥ := by
  rw [extendedExpect_eq_expect h]; exact EReal.coe_ne_bot _

/-- A payoff that is not integrable is worth `⊤` or `⊥`. -/
theorem extendedExpect_eq_top_or_bot {μ : PMF α} {f : α → ℝ}
    (hnot : ¬ PayoffIntegrable μ f) :
    extendedExpect μ f = ⊤ ∨ extendedExpect μ f = ⊥ := by
  rw [payoffIntegrable_iff_parts, not_and_or, not_not, not_not] at hnot
  by_cases hneg : negativeExpect μ f = ⊤
  · exact Or.inr (extendedExpect_eq_bot_of_negativeExpect_eq_top hneg)
  · exact Or.inl (extendedExpect_eq_top (hnot.resolve_right hneg) hneg)

/-- A payoff is integrable unless it is worth `⊤` or `⊥`. -/
theorem payoffIntegrable_of_ne_top_of_ne_bot {μ : PMF α} {f : α → ℝ}
    (htop : extendedExpect μ f ≠ ⊤) (hbot : extendedExpect μ f ≠ ⊥) :
    PayoffIntegrable μ f := by
  by_contra hnot
  rcases extendedExpect_eq_top_or_bot hnot with h | h
  · exact htop h
  · exact hbot h

/-! ## Negation -/

theorem positiveExpect_neg (μ : PMF α) (f : α → ℝ) :
    positiveExpect μ (fun a => -f a) = negativeExpect μ f := rfl

theorem negativeExpect_neg (μ : PMF α) (f : α → ℝ) :
    negativeExpect μ (fun a => -f a) = positiveExpect μ f := by
  unfold negativeExpect positiveExpect
  simp only [neg_neg]

theorem hasExpectation_neg_iff (μ : PMF α) (f : α → ℝ) :
    HasExpectation μ (fun a => -f a) ↔ HasExpectation μ f := by
  unfold HasExpectation
  rw [positiveExpect_neg, negativeExpect_neg, or_comm]

/-- Negation negates the extended expectation whenever it exists. -/
theorem extendedExpect_neg {μ : PMF α} {f : α → ℝ} (h : HasExpectation μ f) :
    extendedExpect μ (fun a => -f a) = -extendedExpect μ f := by
  unfold extendedExpect
  rw [positiveExpect_neg, negativeExpect_neg,
    EReal.neg_sub (Or.inl (EReal.coe_ennreal_ne_bot _))
      (h.imp (fun hpos => mt EReal.coe_ennreal_eq_top_iff.1 hpos)
        (fun hneg => mt EReal.coe_ennreal_eq_top_iff.1 hneg)),
    sub_eq_add_neg, add_comm]

/-! ## Congruence on the support -/

theorem positiveExpect_congr_on_support {μ : PMF α} {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a = g a) : positiveExpect μ f = positiveExpect μ g := by
  unfold positiveExpect
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff μ a).2 ha, zero_mul, zero_mul]

theorem negativeExpect_congr_on_support {μ : PMF α} {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a = g a) : negativeExpect μ f = negativeExpect μ g :=
  positiveExpect_congr_on_support fun a ha => by rw [h a ha]

theorem hasExpectation_congr_on_support {μ : PMF α} {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a = g a) : HasExpectation μ f ↔ HasExpectation μ g := by
  unfold HasExpectation
  rw [positiveExpect_congr_on_support h, negativeExpect_congr_on_support h]

/-! ## Weight domination -/

private theorem tsum_scaled_weight_le {source target : PMF α} {scale : ℝ}
    (hscale : 0 < scale) (hle : ∀ a, scale * (source a).toReal ≤ (target a).toReal)
    (g : α → ℝ≥0∞) :
    ENNReal.ofReal scale * ∑' a, source a * g a ≤ ∑' a, target a * g a := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  calc
    ENNReal.ofReal scale * source a =
        ENNReal.ofReal (scale * (source a).toReal) := by
      rw [ENNReal.ofReal_mul hscale.le, ENNReal.ofReal_toReal (source.apply_ne_top a)]
    _ ≤ ENNReal.ofReal (target a).toReal := ENNReal.ofReal_le_ofReal (hle a)
    _ = target a := ENNReal.ofReal_toReal (target.apply_ne_top a)

/-- A law dominated by a positive multiple of another has at most a matching
multiple of its expected gains. -/
theorem positiveExpect_le_of_scaled_weight_le {source target : PMF α} {scale : ℝ}
    (hscale : 0 < scale) (hle : ∀ a, scale * (source a).toReal ≤ (target a).toReal)
    (f : α → ℝ) :
    ENNReal.ofReal scale * positiveExpect source f ≤ positiveExpect target f :=
  tsum_scaled_weight_le hscale hle _

theorem negativeExpect_le_of_scaled_weight_le {source target : PMF α} {scale : ℝ}
    (hscale : 0 < scale) (hle : ∀ a, scale * (source a).toReal ≤ (target a).toReal)
    (f : α → ℝ) :
    ENNReal.ofReal scale * negativeExpect source f ≤ negativeExpect target f :=
  tsum_scaled_weight_le hscale hle _

private theorem ne_top_of_scaled_le {scale : ℝ} (hscale : 0 < scale) {x y : ℝ≥0∞}
    (hle : ENNReal.ofReal scale * x ≤ y) (hy : y ≠ ⊤) : x ≠ ⊤ := by
  rintro rfl
  rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hscale).ne', top_le_iff] at hle
  exact hy hle

/-- An expectation passes to any law dominated by a positive multiple of the
original law. -/
theorem hasExpectation_of_scaled_weight_le {source target : PMF α} {f : α → ℝ} {scale : ℝ}
    (hscale : 0 < scale) (hle : ∀ a, scale * (source a).toReal ≤ (target a).toReal)
    (htarget : HasExpectation target f) : HasExpectation source f := by
  rcases htarget with hpos | hneg
  · exact Or.inl (ne_top_of_scaled_le hscale
      (positiveExpect_le_of_scaled_weight_le hscale hle f) hpos)
  · exact Or.inr (ne_top_of_scaled_le hscale
      (negativeExpect_le_of_scaled_weight_le hscale hle f) hneg)

/-! ## Sign -/

/-- The extended expectation is nonpositive exactly when the expected gains do
not exceed the expected losses. This holds in every case, including the junk
value `⊥` when both are infinite. -/
theorem extendedExpect_nonpos_iff (μ : PMF α) (f : α → ℝ) :
    extendedExpect μ f ≤ 0 ↔ positiveExpect μ f ≤ negativeExpect μ f := by
  rw [extendedExpect, EReal.sub_nonpos, EReal.coe_ennreal_le_coe_ennreal_iff]

/-- A payoff that is nonnegative on the support has no expected losses, so its
expectation exists. -/
theorem negativeExpect_eq_zero_of_nonneg {μ : PMF α} {f : α → ℝ}
    (h : ∀ a ∈ μ.support, 0 ≤ f a) : negativeExpect μ f = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (h a ha)), mul_zero]
  · rw [(PMF.apply_eq_zero_iff μ a).2 ha, zero_mul]

theorem hasExpectation_of_nonneg {μ : PMF α} {f : α → ℝ}
    (h : ∀ a ∈ μ.support, 0 ≤ f a) : HasExpectation μ f :=
  Or.inr (ne_of_eq_of_ne (negativeExpect_eq_zero_of_nonneg h) ENNReal.zero_ne_top)

/-- A nonnegative payoff that is not integrable has expectation `⊤`. -/
theorem extendedExpect_eq_top_of_nonneg {μ : PMF α} {f : α → ℝ}
    (h : ∀ a ∈ μ.support, 0 ≤ f a) (hnot : ¬ PayoffIntegrable μ f) :
    extendedExpect μ f = ⊤ := by
  have hneg : negativeExpect μ f ≠ ⊤ :=
    ne_of_eq_of_ne (negativeExpect_eq_zero_of_nonneg h) ENNReal.zero_ne_top
  refine extendedExpect_eq_top ?_ hneg
  by_contra hpos
  exact hnot ((payoffIntegrable_iff_parts μ f).2 ⟨hpos, hneg⟩)

/-- Only infinite expected losses make the extended expectation `⊥`. -/
theorem negativeExpect_eq_top_of_extendedExpect_eq_bot {μ : PMF α} {f : α → ℝ}
    (h : extendedExpect μ f = ⊥) : negativeExpect μ f = ⊤ := by
  by_contra hne
  have hlower : -(negativeExpect μ f : EReal) ≤ extendedExpect μ f := by
    rw [extendedExpect, sub_eq_add_neg]
    exact le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _)
  rw [h, le_bot_iff, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff] at hlower
  exact hne hlower

/-- Comparing with a real threshold is comparing the shifted payoff with zero. -/
private theorem extendedExpect_le_coe_iff (μ : PMF α) (f : α → ℝ) (r : ℝ) :
    extendedExpect μ f ≤ r ↔ extendedExpect μ (fun a => 1 * f a + -r) ≤ 0 := by
  rw [extendedExpect_affine μ f (-r) one_pos, EReal.coe_one, one_mul,
    ← (EReal.addLECancellable_coe (-r)).add_le_add_iff_right, ← EReal.coe_add,
    add_neg_cancel, EReal.coe_zero]

/-! ## Mixtures -/

private theorem tsum_bind_mul (μ : PMF α) (q : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' b, μ.bind q b * g b = ∑' a, μ a * ∑' b, q a b * g b := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

/-- The expected gains of a mixture are the mixture of the expected gains. -/
theorem positiveExpect_bind (μ : PMF α) (q : α → PMF β) (f : β → ℝ) :
    positiveExpect (μ.bind q) f = ∑' a, μ a * positiveExpect (q a) f :=
  tsum_bind_mul μ q _

/-- The expected losses of a mixture are the mixture of the expected losses. -/
theorem negativeExpect_bind (μ : PMF α) (q : α → PMF β) (f : β → ℝ) :
    negativeExpect (μ.bind q) f = ∑' a, μ a * negativeExpect (q a) f :=
  tsum_bind_mul μ q _

private theorem tsum_weighted_eq_top {μ : PMF α} {x : α → ℝ≥0∞} {a : α}
    (ha : a ∈ μ.support) (hx : x a = ⊤) : ∑' b, μ b * x b = ⊤ := by
  rw [← top_le_iff]
  calc
    (⊤ : ℝ≥0∞) = μ a * x a := by rw [hx, ENNReal.mul_top ha]
    _ ≤ ∑' b, μ b * x b := ENNReal.le_tsum (f := fun b => μ b * x b) a

private theorem tsum_weighted_le {μ : PMF α} {x y : α → ℝ≥0∞}
    (h : ∀ a ∈ μ.support, x a ≤ y a) : ∑' a, μ a * x a ≤ ∑' a, μ a * y a := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [(PMF.apply_eq_zero_iff μ a).2 ha, zero_mul, zero_mul]

/-- Each law of a mixture that has an expectation has one on its support. -/
theorem HasExpectation.of_bind {μ : PMF α} {q : α → PMF β} {f : β → ℝ}
    (h : HasExpectation (μ.bind q) f) {a : α} (ha : a ∈ μ.support) :
    HasExpectation (q a) f := by
  by_contra hnot
  rw [HasExpectation, not_or, not_not, not_not] at hnot
  rw [HasExpectation, positiveExpect_bind, negativeExpect_bind] at h
  rcases h with h | h
  · exact h (tsum_weighted_eq_top ha hnot.1)
  · exact h (tsum_weighted_eq_top ha hnot.2)

/-- **A mixture of laws each worth at most `v` is worth at most `v`.** No
existence hypothesis is needed: a mixture without an expectation has the junk
value `⊥`. -/
theorem extendedExpect_bind_le {μ : PMF α} {q : α → PMF β} {f : β → ℝ} {v : EReal}
    (hall : ∀ a ∈ μ.support, extendedExpect (q a) f ≤ v) :
    extendedExpect (μ.bind q) f ≤ v := by
  induction v using EReal.rec with
  | bot =>
    obtain ⟨a, ha⟩ := μ.support_nonempty
    have hloss := negativeExpect_eq_top_of_extendedExpect_eq_bot (le_bot_iff.1 (hall a ha))
    refine (extendedExpect_eq_bot_of_negativeExpect_eq_top ?_).le
    rw [negativeExpect_bind]
    exact tsum_weighted_eq_top ha hloss
  | top => exact le_top
  | coe r =>
    rw [extendedExpect_le_coe_iff, extendedExpect_nonpos_iff, positiveExpect_bind,
      negativeExpect_bind]
    exact tsum_weighted_le fun a ha =>
      (extendedExpect_nonpos_iff _ _).1 ((extendedExpect_le_coe_iff _ _ r).1 (hall a ha))

/-- **A mixture of laws each worth at least `v` is worth at least `v`,** when
the mixture has an expectation. -/
theorem le_extendedExpect_bind {μ : PMF α} {q : α → PMF β} {f : β → ℝ} {v : EReal}
    (hall : ∀ a ∈ μ.support, v ≤ extendedExpect (q a) f)
    (hbind : HasExpectation (μ.bind q) f) :
    v ≤ extendedExpect (μ.bind q) f := by
  rw [← EReal.neg_le_neg_iff, ← extendedExpect_neg hbind]
  refine extendedExpect_bind_le fun a ha => ?_
  rw [extendedExpect_neg (hbind.of_bind ha), EReal.neg_le_neg_iff]
  exact hall a ha

/-! ## Comparison bounds -/

/-- The extended expectation never exceeds the expected gains. -/
theorem extendedExpect_le_positiveExpect (μ : PMF α) (f : α → ℝ) :
    extendedExpect μ f ≤ positiveExpect μ f := by
  rw [extendedExpect, sub_eq_add_neg]
  refine add_le_of_nonpos_right (EReal.neg_le.2 ?_)
  rw [neg_zero]
  exact EReal.coe_ennreal_nonneg _

/-- Only infinite expected gains make the extended expectation `⊤`. -/
theorem positiveExpect_eq_top_of_extendedExpect_eq_top {μ : PMF α} {f : α → ℝ}
    (h : extendedExpect μ f = ⊤) : positiveExpect μ f = ⊤ := by
  have hle := extendedExpect_le_positiveExpect μ f
  rwa [h, top_le_iff, EReal.coe_ennreal_eq_top_iff] at hle

/-- A payoff worth at most another has expected gains bounded by the other's
expected gains plus its own expected losses. -/
theorem positiveExpect_le_of_extendedExpect_le {μ : PMF α} {ν : PMF β} {f : α → ℝ}
    {g : β → ℝ} (h : extendedExpect μ f ≤ extendedExpect ν g) :
    positiveExpect μ f ≤ positiveExpect ν g + negativeExpect μ f := by
  by_cases hloss : negativeExpect μ f = ⊤
  · rw [hloss, add_top]
    exact le_top
  have hle := h.trans (extendedExpect_le_positiveExpect ν g)
  rw [extendedExpect, EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inl (mt EReal.coe_ennreal_eq_top_iff.1 hloss)), ← EReal.coe_ennreal_add] at hle
  exact EReal.coe_ennreal_le_coe_ennreal_iff.1 hle

/-- A mixture whose components are each worth at most the matching components
of an integrable mixture, and which is not worth `⊥`, is integrable. -/
theorem payoffIntegrable_bind_of_extendedExpect_le {μ : PMF α} {p q : α → PMF β}
    {f : β → ℝ}
    (h : ∀ a ∈ μ.support, extendedExpect (p a) f ≤ extendedExpect (q a) f)
    (hq : PayoffIntegrable (μ.bind q) f) (hp : extendedExpect (μ.bind p) f ≠ ⊥) :
    PayoffIntegrable (μ.bind p) f := by
  have hloss : negativeExpect (μ.bind p) f ≠ ⊤ :=
    fun htop => hp (extendedExpect_eq_bot_of_negativeExpect_eq_top htop)
  have hbound : positiveExpect (μ.bind p) f ≤
      positiveExpect (μ.bind q) f + negativeExpect (μ.bind p) f := by
    rw [positiveExpect_bind, positiveExpect_bind, negativeExpect_bind, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    by_cases ha : a ∈ μ.support
    · exact mul_le_mul' le_rfl (positiveExpect_le_of_extendedExpect_le (h a ha))
    · rw [(PMF.apply_eq_zero_iff μ a).2 ha, zero_mul, zero_mul]
  refine (payoffIntegrable_iff_parts _ _).2 ⟨ne_top_of_le_ne_top ?_ hbound, hloss⟩
  exact ENNReal.add_ne_top.2 ⟨((payoffIntegrable_iff_parts _ _).1 hq).1, hloss⟩

/-! ## Monotone mixtures -/

private theorem coe_sub_le_coe_sub_iff {a b c d : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    (a : EReal) - b ≤ (c : EReal) - d ↔ a + d ≤ c + b := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  lift c to NNReal using hc
  lift d to NNReal using hd
  rw [EReal.coe_nnreal_eq_coe_real, EReal.coe_nnreal_eq_coe_real, EReal.coe_nnreal_eq_coe_real,
    EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff,
    ← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
    NNReal.coe_add, NNReal.coe_add]
  constructor <;> intro h <;> linarith

/-- The cross inequality of gains and losses orders extended expectations,
when the larger side has an expectation. -/
theorem extendedExpect_le_of_cross {μ : PMF α} {ν : PMF β} {f : α → ℝ} {g : β → ℝ}
    (hcross : positiveExpect μ f + negativeExpect ν g ≤
      positiveExpect ν g + negativeExpect μ f)
    (hν : HasExpectation ν g) :
    extendedExpect μ f ≤ extendedExpect ν g := by
  by_cases hloss : negativeExpect μ f = ⊤
  · rw [extendedExpect_eq_bot_of_negativeExpect_eq_top hloss]
    exact bot_le
  by_cases hgain : positiveExpect ν g = ⊤
  · rw [extendedExpect_eq_top hgain (hν.resolve_left (not_not.2 hgain))]
    exact le_top
  have hsum : positiveExpect ν g + negativeExpect μ f ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hgain, hloss⟩
  have hgainμ : positiveExpect μ f ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (le_self_add.trans hcross)
  have hlossν : negativeExpect ν g ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (le_add_self.trans hcross)
  exact (coe_sub_le_coe_sub_iff hgainμ hloss hgain hlossν).2 hcross

/-- Ordered extended expectations satisfy the cross inequality of gains and
losses. -/
theorem positiveExpect_add_negativeExpect_le {μ : PMF α} {ν : PMF β} {f : α → ℝ}
    {g : β → ℝ} (h : extendedExpect μ f ≤ extendedExpect ν g) :
    positiveExpect μ f + negativeExpect ν g ≤ positiveExpect ν g + negativeExpect μ f := by
  by_cases hloss : negativeExpect μ f = ⊤
  · rw [hloss, add_top]
    exact le_top
  by_cases hgain : positiveExpect ν g = ⊤
  · rw [hgain, top_add]
    exact le_top
  have hgainμ : positiveExpect μ f ≠ ⊤ := fun htop => by
    rw [extendedExpect_eq_top htop hloss, top_le_iff] at h
    exact hgain (positiveExpect_eq_top_of_extendedExpect_eq_top h)
  have hlossν : negativeExpect ν g ≠ ⊤ := fun htop => by
    rw [extendedExpect_eq_bot_of_negativeExpect_eq_top htop, le_bot_iff] at h
    exact hloss (negativeExpect_eq_top_of_extendedExpect_eq_bot h)
  exact (coe_sub_le_coe_sub_iff hgainμ hloss hgain hlossν).1 h

private theorem tsum_bindOnSupport_mul (μ : PMF α) (k : ∀ a ∈ μ.support, PMF β)
    (g : β → ℝ≥0∞) :
    ∑' b, μ.bindOnSupport k b * g b =
      ∑' a, μ a * (if h : μ a = 0 then 0 else ∑' b, k a h b * g b) := by
  simp_rw [PMF.bindOnSupport_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  by_cases h : μ a = 0
  · simp [h]
  · simp only [h, dite_false, ← ENNReal.tsum_mul_left, mul_assoc]

theorem positiveExpect_bindOnSupport (μ : PMF α) (k : ∀ a ∈ μ.support, PMF β)
    (f : β → ℝ) :
    positiveExpect (μ.bindOnSupport k) f =
      ∑' a, μ a * (if h : μ a = 0 then 0 else positiveExpect (k a h) f) :=
  tsum_bindOnSupport_mul μ k _

theorem negativeExpect_bindOnSupport (μ : PMF α) (k : ∀ a ∈ μ.support, PMF β)
    (f : β → ℝ) :
    negativeExpect (μ.bindOnSupport k) f =
      ∑' a, μ a * (if h : μ a = 0 then 0 else negativeExpect (k a h) f) :=
  tsum_bindOnSupport_mul μ k _

/-- A mixture of laws, each worth at most the matching law of another mixture,
is worth at most that mixture, when the larger mixture has an expectation. -/
theorem extendedExpect_bindOnSupport_mono {μ : PMF α} {p q : ∀ a ∈ μ.support, PMF β}
    {f : β → ℝ}
    (h : ∀ a (ha : a ∈ μ.support), extendedExpect (p a ha) f ≤ extendedExpect (q a ha) f)
    (hq : HasExpectation (μ.bindOnSupport q) f) :
    extendedExpect (μ.bindOnSupport p) f ≤ extendedExpect (μ.bindOnSupport q) f := by
  refine extendedExpect_le_of_cross ?_ hq
  rw [positiveExpect_bindOnSupport, positiveExpect_bindOnSupport, negativeExpect_bindOnSupport,
    negativeExpect_bindOnSupport, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add, ← mul_add]
  by_cases ha : μ a = 0
  · simp [ha]
  · simp only [ha, dite_false]
    exact mul_le_mul' le_rfl (positiveExpect_add_negativeExpect_le (h a ha))

/-- The mixture form of `extendedExpect_bindOnSupport_mono`. -/
theorem extendedExpect_bind_mono {μ : PMF α} {p q : α → PMF β} {f : β → ℝ}
    (h : ∀ a ∈ μ.support, extendedExpect (p a) f ≤ extendedExpect (q a) f)
    (hq : HasExpectation (μ.bind q) f) :
    extendedExpect (μ.bind p) f ≤ extendedExpect (μ.bind q) f := by
  rw [← PMF.bindOnSupport_eq_bind] at hq ⊢
  rw [← PMF.bindOnSupport_eq_bind]
  exact extendedExpect_bindOnSupport_mono (fun a ha => h a ha) hq

/-- Two extended reals have a defined sum unless they are opposite infinities.
`EReal` addition sends that case to `⊥` only by convention, so a sum of two
separately taken expectations is meaningful exactly when this holds. -/
def HasDefinedSum (a b : EReal) : Prop :=
  ¬ (a = ⊤ ∧ b = ⊥) ∧ ¬ (a = ⊥ ∧ b = ⊤)

theorem hasDefinedSum_coe_right (a : EReal) (r : ℝ) : HasDefinedSum a r := by
  simp [HasDefinedSum]

/-- A positive affine map is an order embedding of the extended reals. -/
theorem coe_mul_add_coe_le_iff {c : ℝ} (hc : 0 < c) (k : ℝ) {a b : EReal} :
    (c : EReal) * a + k ≤ c * b + k ↔ a ≤ b := by
  induction a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top =>
    induction b using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_top_of_pos hc]
    | top => simp
    | coe b =>
      rw [EReal.coe_mul_top_of_pos hc, EReal.top_add_coe, ← EReal.coe_mul, ← EReal.coe_add]
      exact iff_of_false (fun h => EReal.coe_ne_top _ (top_le_iff.1 h))
        (fun h => EReal.coe_ne_top _ (top_le_iff.1 h))
  | coe a =>
    induction b using EReal.rec with
    | bot =>
      rw [EReal.coe_mul_bot_of_pos hc, EReal.bot_add, ← EReal.coe_mul, ← EReal.coe_add]
      exact iff_of_false (fun h => EReal.coe_ne_bot _ (le_bot_iff.1 h))
        (fun h => EReal.coe_ne_bot _ (le_bot_iff.1 h))
    | top =>
      rw [EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]
      simp
    | coe b =>
      rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, add_le_add_iff_right,
        mul_le_mul_iff_right₀ hc]

end GameTheory.Math.Probability
