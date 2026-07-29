/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# The stochastic account update for uniform zero-sum strategies

This file isolates the three-point account update used by published
Mertens–Neyman-style uniform-value constructions. Given a multiplicative
step `γ > 1`, current account `s`, floor `M`, and payoff/value gap `y`, the
next account is `γs`, `s`, or `γ⁻¹s`.

The upward and downward probabilities are calibrated so that the expected
account increment is exactly `y` away from the floor. At the floor,
downward motion is suppressed; the resulting error is bounded by one when
`-1 ≤ y`. The scale conditions make explicit a prerequisite that informal
descriptions can hide: the account must be large enough for these formulas
to define probabilities.

This is the algebraic kernel behind the account telescope. It proves the
logarithmic corrector estimate for the concrete discount schedule, and
isolates the probability-weighted discounted-value switch estimate that
remains to be supplied by a game-induced value process. Together with a
bounded-potential drift, these bounds control floor occupation.

The formulation follows Section 4 of Hansen, Ibsen-Jensen, and Neyman,
*Stochastic Games with Limited Public Memory*.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Filter Math.Probability Topology

/-- The slow discount schedule used by the stochastic account
construction. -/
def discountRate (s : ℝ) : ℝ :=
  1 / (s * (Real.log s) ^ 2)

/-- The logarithmic corrector paired with `discountRate`. Its derivative is
the negative discount rate. -/
def logCorrector (s : ℝ) : ℝ :=
  (Real.log s)⁻¹

theorem discountRate_pos {s : ℝ} (hs : 1 < s) :
    0 < discountRate s := by
  unfold discountRate
  apply one_div_pos.mpr
  exact mul_pos (lt_trans zero_lt_one hs)
    (sq_pos_of_pos (Real.log_pos hs))

theorem hasDerivAt_logCorrector
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsm1 : s ≠ -1) :
    HasDerivAt logCorrector (-discountRate s) s := by
  unfold logCorrector
  simpa [discountRate, div_eq_mul_inv, mul_comm] using
    Real.hasDerivAt_inv_log hs0 hs1 hsm1

/-- Mean-value form of the identity that the logarithmic corrector is an
antiderivative of the negative discount rate. -/
theorem exists_logCorrector_secant
    {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    ∃ c ∈ Set.Ioo a b,
      logCorrector a - logCorrector b =
        discountRate c * (b - a) := by
  have hdiffIoi :
      DifferentiableOn ℝ logCorrector (Set.Ioi 1) := by
    unfold logCorrector
    exact Real.differentiableOn_inv_log
  have hcont :
      ContinuousOn logCorrector (Set.Icc a b) :=
    (hdiffIoi.mono (fun x hx => lt_of_lt_of_le ha hx.1)).continuousOn
  have hderiv :
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt logCorrector (-discountRate x) x := by
    intro x hx
    apply hasDerivAt_logCorrector
    · linarith [hx.1]
    · linarith [hx.1]
    · linarith [hx.1]
  obtain ⟨c, hc, heq⟩ :=
    exists_hasDerivAt_eq_slope logCorrector
      (fun x => -discountRate x) hab hcont hderiv
  refine ⟨c, hc, ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [eq_div_iff hba] at heq
  linarith

/-- A local relative-variation bound on `discountRate` yields the corrector
inequality used by the account-potential drift argument. This is valid in
both directions of an account move. -/
theorem discountRate_secant_le_logCorrector_sub
    {ε s s' : ℝ} (hs : 1 < s) (hs' : 1 < s')
    (hlocal : ∀ u,
      min s s' ≤ u → u ≤ max s s' →
        |discountRate u - discountRate s| ≤
          ε * discountRate s / 8) :
    discountRate s *
        (s' - s - ε * |s' - s| / 8) ≤
      logCorrector s - logCorrector s' := by
  rcases lt_trichotomy s s' with hlt | rfl | hgt
  · obtain ⟨c, hc, heq⟩ :=
      exists_logCorrector_secant hs hlt
    have hvariation := hlocal c
      (by simpa [min_eq_left hlt.le] using hc.1.le)
      (by simpa [max_eq_right hlt.le] using hc.2.le)
    have hlower :
        -(ε * discountRate s / 8) ≤
          discountRate c - discountRate s :=
      neg_le_of_abs_le hvariation
    have hscaled := mul_le_mul_of_nonneg_right hlower
      (sub_nonneg.mpr hlt.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    nlinarith
  · simp
  · obtain ⟨c, hc, heq⟩ :=
      exists_logCorrector_secant hs' hgt
    have hvariation := hlocal c
      (by simpa [min_eq_right hgt.le] using hc.1.le)
      (by simpa [max_eq_left hgt.le] using hc.2.le)
    have hupper :
        discountRate c - discountRate s ≤
          ε * discountRate s / 8 :=
      le_of_abs_le hvariation
    have hscaled := mul_le_mul_of_nonpos_right hupper
      (sub_nonpos.mpr hgt.le)
    rw [abs_of_nonpos (sub_nonpos.mpr hgt.le)]
    nlinarith

/-- Multiplying the account by a fixed positive constant changes its
logarithm by an asymptotically negligible relative amount. -/
theorem tendsto_log_div_log_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun s : ℝ => Real.log s / Real.log (c * s))
      atTop (𝓝 1) := by
  have hden :
      Tendsto (fun s : ℝ => Real.log c + Real.log s) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hzero :
      Tendsto (fun s : ℝ =>
        Real.log c / (Real.log c + Real.log s)) atTop (𝓝 0) :=
    hden.const_div_atTop (Real.log c)
  have hone :
      Tendsto (fun s : ℝ =>
        1 - Real.log c / (Real.log c + Real.log s))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hzero
  have hsimple :
      Tendsto (fun s : ℝ =>
        Real.log s / (Real.log c + Real.log s))
        atTop (𝓝 1) := by
    apply hone.congr'
    filter_upwards
      [hden.eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    field_simp [ne_of_gt hs]
    ring
  apply hsimple.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hs)]

/-- `discountRate` is regularly varying with index `-1`. -/
theorem tendsto_discountRate_mul_div (c : ℝ) (hc : 0 < c) :
    Tendsto (fun s : ℝ => discountRate (c * s) / discountRate s)
      atTop (𝓝 c⁻¹) := by
  have hlog := tendsto_log_div_log_mul c hc
  have hsimple :
      Tendsto (fun s : ℝ =>
        c⁻¹ * (Real.log s / Real.log (c * s)) ^ 2)
        atTop (𝓝 c⁻¹) := by
    simpa using tendsto_const_nhds.mul (hlog.pow 2)
  apply hsimple.congr'
  filter_upwards
    [eventually_gt_atTop (max 1 (1 / c))] with s hs
  have hs1 : 1 < s := lt_of_le_of_lt (le_max_left _ _) hs
  have hcs1 : 1 < c * s := by
    have hdiv : 1 / c < s :=
      lt_of_le_of_lt (le_max_right _ _) hs
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hdiv
  unfold discountRate
  field_simp [ne_of_gt hc, ne_of_gt (lt_trans zero_lt_one hs1),
    ne_of_gt (Real.log_pos hs1), ne_of_gt (Real.log_pos hcs1)]

theorem discountRate_antitoneOn :
    AntitoneOn discountRate (Set.Ioi 1) := by
  intro a ha b hb hab
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogab : Real.log a ≤ Real.log b :=
    Real.log_le_log ha0 hab
  have hlogsq :
      (Real.log a) ^ 2 ≤ (Real.log b) ^ 2 := by
    nlinarith [Real.log_nonneg hb.le]
  have hden :
      a * (Real.log a) ^ 2 ≤ b * (Real.log b) ^ 2 :=
    mul_le_mul hab hlogsq (sq_nonneg _)
      (lt_trans zero_lt_one hb).le
  unfold discountRate
  exact one_div_le_one_div_of_le
    (mul_pos ha0 (sq_pos_of_pos hloga)) hden

/-- For `γ = 1 + ε/9`, the relative variation of `discountRate` across
the whole account interval `[γ⁻¹s, γs]` is eventually at most `ε/8`.
The strict slack between `ε/9` and `ε/8` absorbs the logarithmic factor. -/
theorem eventually_discountRate_local_variation
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ u : ℝ,
      (1 + ε / 9)⁻¹ * s ≤ u →
      u ≤ (1 + ε / 9) * s →
      |discountRate u - discountRate s| ≤
        ε * discountRate s / 8 := by
  let γ : ℝ := 1 + ε / 9
  have hγ : 1 < γ := by
    dsimp [γ]
    linarith
  have hγ0 : 0 < γ := lt_trans zero_lt_one hγ
  have hlowerLimit : 1 - ε / 8 < γ⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hγ0]
    dsimp [γ]
    nlinarith [sq_nonneg ε]
  have hupperLimit : γ < 1 + ε / 8 := by
    dsimp [γ]
    linarith
  have hupRatio :
      Tendsto (fun s : ℝ =>
        discountRate (γ * s) / discountRate s)
        atTop (𝓝 γ⁻¹) :=
    tendsto_discountRate_mul_div γ hγ0
  have hdownRatio :
      Tendsto (fun s : ℝ =>
        discountRate (γ⁻¹ * s) / discountRate s)
        atTop (𝓝 γ) := by
    simpa [hγ0.ne'] using
      tendsto_discountRate_mul_div γ⁻¹ (inv_pos.mpr hγ0)
  filter_upwards
    [(tendsto_order.1 hupRatio).1 _ hlowerLimit,
      (tendsto_order.1 hdownRatio).2 _ hupperLimit,
      eventually_gt_atTop γ] with s hup hdown hsγ
  intro u hsu hus
  change γ⁻¹ * s ≤ u at hsu
  change u ≤ γ * s at hus
  have hs1 : 1 < s := lt_trans hγ hsγ
  have hinvγs1 : 1 < γ⁻¹ * s := by
    have hscaled :=
      mul_lt_mul_of_pos_left hsγ (inv_pos.mpr hγ0)
    simpa [hγ0.ne'] using hscaled
  have hu1 : 1 < u := lt_of_lt_of_le hinvγs1 hsu
  have hγs1 : 1 < γ * s := by
    nlinarith [mul_pos (sub_pos.mpr hγ) (sub_pos.mpr hs1)]
  have hratePos : 0 < discountRate s := discountRate_pos hs1
  have hlowerEndpoint :
      discountRate s * (1 - ε / 8) ≤ discountRate (γ * s) := by
    have := (lt_div_iff₀ hratePos).mp hup
    nlinarith
  have hupperEndpoint :
      discountRate (γ⁻¹ * s) ≤
        discountRate s * (1 + ε / 8) := by
    have := (div_lt_iff₀ hratePos).mp hdown
    nlinarith
  have hlowerRate :
      discountRate (γ * s) ≤ discountRate u :=
    discountRate_antitoneOn hu1 hγs1 hus
  have hupperRate :
      discountRate u ≤ discountRate (γ⁻¹ * s) :=
    discountRate_antitoneOn hinvγs1 hu1 hsu
  rw [abs_le]
  constructor <;> nlinarith

/-- The logarithmic corrector inequality holds eventually, simultaneously
for every possible next account in the multiplicative update interval. -/
theorem eventually_discountRate_secant_le_logCorrector_sub
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ s' : ℝ,
      (1 + ε / 9)⁻¹ * s ≤ s' →
      s' ≤ (1 + ε / 9) * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s' := by
  let γ : ℝ := 1 + ε / 9
  have hγ : 1 < γ := by
    dsimp [γ]
    linarith
  have hγ0 : 0 < γ := lt_trans zero_lt_one hγ
  filter_upwards
    [eventually_discountRate_local_variation hε,
      eventually_gt_atTop γ] with s hvariation hsγ
  intro s' hs'Lower hs'Upper
  change γ⁻¹ * s ≤ s' at hs'Lower
  change s' ≤ γ * s at hs'Upper
  have hs1 : 1 < s := lt_trans hγ hsγ
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hinvγs1 : 1 < γ⁻¹ * s := by
    have hscaled :=
      mul_lt_mul_of_pos_left hsγ (inv_pos.mpr hγ0)
    simpa [hγ0.ne'] using hscaled
  have hs'1 : 1 < s' := lt_of_lt_of_le hinvγs1 hs'Lower
  have hinvγ_le_one : γ⁻¹ ≤ 1 :=
    (inv_le_one₀ hγ0).2 hγ.le
  have hinvγs_le_s : γ⁻¹ * s ≤ s := by
    simpa using mul_le_mul_of_nonneg_right hinvγ_le_one hs0.le
  have hs_le_γs : s ≤ γ * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγ.le) hs0.le]
  apply discountRate_secant_le_logCorrector_sub hs1 hs'1
  intro u hmin hmax
  apply hvariation u
  · change γ⁻¹ * s ≤ u
    exact (le_min hinvγs_le_s hs'Lower).trans hmin
  · change u ≤ γ * s
    exact hmax.trans (max_le hs_le_γs hs'Upper)

/-- Floor-threshold form of the eventual corrector estimate. A single
account floor works simultaneously for all later accounts and all three
possible multiplicative updates. -/
theorem exists_floor_discountRate_secant_le_logCorrector_sub
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ s : ℝ, M ≤ s → ∀ s' : ℝ,
      (1 + ε / 9)⁻¹ * s ≤ s' →
      s' ≤ (1 + ε / 9) * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s' := by
  rcases (eventually_atTop.1
      (eventually_discountRate_secant_le_logCorrector_sub hε)) with
    ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-- The three possible multiplicative account moves. -/
inductive AccountMove
  | up
  | stay
  | down
  deriving DecidableEq, Fintype

/-- Probability of moving from `s` to `γs`. -/
def upProbability (γ s y : ℝ) : ℝ :=
  max y 0 / (s * (γ - 1))

/-- Probability of moving from `s` to `γ⁻¹s`. Downward motion is suppressed
at the account floor. -/
def downProbability (γ M s y : ℝ) : ℝ :=
  if M < s then min y 0 / (s * (γ⁻¹ - 1)) else 0

/-- Probability of leaving the account unchanged. -/
def stayProbability (γ M s y : ℝ) : ℝ :=
  1 - upProbability γ s y - downProbability γ M s y

/-- Expected one-step account increment under the up/stay/down weights. -/
def expectedChange (γ M s y : ℝ) : ℝ :=
  upProbability γ s y * (γ * s - s) +
    downProbability γ M s y * (γ⁻¹ * s - s)

/-- Sufficient scale conditions for the three account-update weights to be
probabilities for every gap in `[-1, 2]`. -/
def IsValidScale (γ s : ℝ) : Prop :=
  1 < γ ∧ 0 < s ∧
    2 ≤ s * (γ - 1) ∧
    1 ≤ s * (1 - γ⁻¹)

/-- For `γ = 1 + ε/9`, the explicit floor condition `18/ε ≤ s`
implies both probability-normalization scale bounds. -/
theorem isValidScale_one_add_epsilon_div_nine
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 18 / ε ≤ s) :
    IsValidScale (1 + ε / 9) s := by
  have hse : 18 ≤ s * ε := (div_le_iff₀ hε).mp hs
  have hs0 : 0 < s := by nlinarith
  have hden : 0 < 9 + ε := by linarith
  refine ⟨by linarith, hs0, ?_, ?_⟩
  · norm_num
    nlinarith
  · have hinv :
        1 - (1 + ε / 9)⁻¹ = ε / (9 + ε) := by
      field_simp
      ring
    rw [hinv]
    rw [← mul_div_assoc]
    rw [le_div_iff₀ hden]
    nlinarith

theorem IsValidScale.gamma_ne_one {γ s : ℝ} (h : IsValidScale γ s) :
    γ ≠ 1 :=
  ne_of_gt h.1

theorem IsValidScale.s_ne_zero {γ s : ℝ} (h : IsValidScale γ s) :
    s ≠ 0 :=
  ne_of_gt h.2.1

theorem IsValidScale.upDenom_pos {γ s : ℝ} (h : IsValidScale γ s) :
    0 < s * (γ - 1) :=
  mul_pos h.2.1 (sub_pos.mpr h.1)

theorem IsValidScale.inv_sub_one_neg {γ s : ℝ} (h : IsValidScale γ s) :
    γ⁻¹ - 1 < 0 := by
  have hγ0 : 0 < γ := lt_trans zero_lt_one h.1
  exact sub_neg.mpr ((inv_lt_one₀ hγ0).2 h.1)

theorem IsValidScale.downDenom_neg {γ s : ℝ} (h : IsValidScale γ s) :
    s * (γ⁻¹ - 1) < 0 :=
  mul_neg_of_pos_of_neg h.2.1 h.inv_sub_one_neg

theorem upProbability_nonneg {γ s y : ℝ} (h : IsValidScale γ s) :
    0 ≤ upProbability γ s y := by
  exact div_nonneg (le_max_right _ _) h.upDenom_pos.le

theorem downProbability_nonneg {γ M s y : ℝ} (h : IsValidScale γ s) :
    0 ≤ downProbability γ M s y := by
  unfold downProbability
  split_ifs
  · exact div_nonneg_of_nonpos (min_le_right _ _) h.downDenom_neg.le
  · exact le_rfl

theorem up_add_down_le_one
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    upProbability γ s y + downProbability γ M s y ≤ 1 := by
  by_cases hy : 0 ≤ y
  · have hup : upProbability γ s y ≤ 1 := by
      unfold upProbability
      rw [max_eq_left hy, div_le_one h.upDenom_pos]
      exact hyUpper.trans h.2.2.1
    simpa [downProbability, min_eq_right hy] using hup
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hup : upProbability γ s y = 0 := by
      simp [upProbability, max_eq_right hy']
    rw [hup, zero_add]
    unfold downProbability
    split_ifs
    · rw [min_eq_left hy', div_le_one_of_neg h.downDenom_neg]
      have hdenom :
          s * (γ⁻¹ - 1) = -(s * (1 - γ⁻¹)) := by ring
      rw [hdenom]
      linarith [h.2.2.2]
    · exact zero_le_one

theorem stayProbability_nonneg
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    0 ≤ stayProbability γ M s y := by
  unfold stayProbability
  linarith [up_add_down_le_one (M := M) h hyLower hyUpper]

theorem probabilities_sum (γ M s y : ℝ) :
    upProbability γ s y + stayProbability γ M s y +
      downProbability γ M s y = 1 := by
  unfold stayProbability
  ring

/-- Real weight assigned to an account move. -/
def moveProbability (γ M s y : ℝ) : AccountMove → ℝ
  | .up => upProbability γ s y
  | .stay => stayProbability γ M s y
  | .down => downProbability γ M s y

theorem moveProbability_nonneg
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) (move : AccountMove) :
    0 ≤ moveProbability γ M s y move := by
  cases move with
  | up => exact upProbability_nonneg h
  | stay => exact stayProbability_nonneg h hyLower hyUpper
  | down => exact downProbability_nonneg h

@[simp] theorem sum_moveProbability (γ M s y : ℝ) :
    ∑ move, moveProbability γ M s y move = 1 := by
  classical
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simpa [moveProbability, add_assoc] using probabilities_sum γ M s y

/-- The account update as an actual probability mass function. -/
def updatePMF
    (γ M s y : ℝ) (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) : PMF AccountMove :=
  PMF.ofFintype
    (fun move => ENNReal.ofReal (moveProbability γ M s y move))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun move _ => moveProbability_nonneg h hyLower hyUpper move)]
      simp)

@[simp] theorem updatePMF_apply_toReal
    (γ M s y : ℝ) (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) (move : AccountMove) :
    ((updatePMF γ M s y h hyLower hyUpper) move).toReal =
      moveProbability γ M s y move := by
  rw [updatePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (moveProbability_nonneg h hyLower hyUpper move)]

/-- Account level after a three-point move. -/
def nextAccount (γ s : ℝ) : AccountMove → ℝ
  | .up => γ * s
  | .stay => s
  | .down => γ⁻¹ * s

/-- Every possible next account lies in the multiplicative interval
`[γ⁻¹s, γs]`. -/
theorem nextAccount_mem_interval
    {γ s : ℝ} (h : IsValidScale γ s) (move : AccountMove) :
    γ⁻¹ * s ≤ nextAccount γ s move ∧
      nextAccount γ s move ≤ γ * s := by
  have hγ0 : 0 < γ := lt_trans zero_lt_one h.1
  have hinvγ_le_one : γ⁻¹ ≤ 1 :=
    (inv_le_one₀ hγ0).2 h.1.le
  have hinvγs_le_s : γ⁻¹ * s ≤ s := by
    simpa using
      mul_le_mul_of_nonneg_right hinvγ_le_one h.2.1.le
  have hs_le_γs : s ≤ γ * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h.1.le) h.2.1.le]
  have hinvγs_le_γs : γ⁻¹ * s ≤ γ * s :=
    hinvγs_le_s.trans hs_le_γs
  cases move <;>
    simp [nextAccount, hinvγs_le_s, hs_le_γs, hinvγs_le_γs]

/-- The expectation of the PMF update agrees with `expectedChange`. -/
theorem expect_nextAccount_sub
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => nextAccount γ s move - s) =
      expectedChange γ M s y := by
  classical
  rw [expect_eq_sum]
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simp [moveProbability, nextAccount, expectedChange]

/-- The expected absolute account jump is at most the magnitude of the
payoff/value gap. Away from the floor the inequality is an equality:
the positive and negative parts of `y` pay exactly for the corresponding
upward and downward account increments. At the floor the negative part is
suppressed. -/
theorem expect_abs_nextAccount_sub_le_abs
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => |nextAccount γ s move - s|) ≤ |y| := by
  classical
  rw [expect_eq_sum]
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simp only [updatePMF_apply_toReal, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, moveProbability, nextAccount, sub_self, abs_zero,
    mul_zero, zero_add]
  have hupInc : γ * s - s = s * (γ - 1) := by ring
  have hdownInc : γ⁻¹ * s - s = s * (γ⁻¹ - 1) := by ring
  rw [hupInc, hdownInc, abs_of_pos h.upDenom_pos,
    abs_of_neg h.downDenom_neg]
  unfold upProbability downProbability
  by_cases hMs : M < s
  · rw [if_pos hMs, mul_neg,
      div_mul_cancel₀ _ h.upDenom_pos.ne',
      div_mul_cancel₀ _ h.downDenom_neg.ne]
    by_cases hy : 0 ≤ y
    · simp [max_eq_left hy, min_eq_right hy, abs_of_nonneg hy]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      simp [max_eq_right hy', min_eq_left hy', abs_of_nonpos hy']
  · rw [if_neg hMs, zero_mul, add_zero,
      div_mul_cancel₀ _ h.upDenom_pos.ne']
    exact max_le (le_abs_self y) (abs_nonneg y)

/-- For gaps in `[-1, 2]`, the expected absolute account jump is at most
`2`. This is the uniform movement bound used to charge corrector errors in
the account-potential drift estimate. -/
theorem expect_abs_nextAccount_sub_le_two
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => |nextAccount γ s move - s|) ≤ 2 := by
  refine (expect_abs_nextAccount_sub_le_abs h hyLower hyUpper).trans ?_
  rw [abs_le]
  constructor <;> linarith

/-- A pointwise logarithmic-corrector estimate on the multiplicative
account interval passes through the actual stochastic account update.
Linearity converts the expected corrector gain into the expected account
change minus its absolute-movement error. -/
theorem discountRate_mul_expect_sub_le_expect_logCorrector_sub
    {γ M s y ε : ℝ} (h : IsValidScale γ s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s') :
    discountRate s *
        (expect (updatePMF γ M s y h hyLower hyUpper)
            (fun move => nextAccount γ s move - s) -
          ε *
            expect (updatePMF γ M s y h hyLower hyUpper)
              (fun move => |nextAccount γ s move - s|) / 8) ≤
      expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move =>
          logCorrector s - logCorrector (nextAccount γ s move)) := by
  let d := updatePMF γ M s y h hyLower hyUpper
  have hpoint : ∀ move,
      discountRate s *
          (nextAccount γ s move - s -
            ε * |nextAccount γ s move - s| / 8) ≤
        logCorrector s - logCorrector (nextAccount γ s move) := by
    intro move
    exact hsecant _ (nextAccount_mem_interval h move).1
      (nextAccount_mem_interval h move).2
  change
    discountRate s *
        (expect d (fun move => nextAccount γ s move - s) -
          ε * expect d (fun move => |nextAccount γ s move - s|) / 8) ≤
      expect d (fun move =>
        logCorrector s - logCorrector (nextAccount γ s move))
  have hlinear :
      expect d (fun move =>
          discountRate s *
            ((nextAccount γ s move - s) -
              (ε / 8) * |nextAccount γ s move - s|)) =
        discountRate s *
          (expect d (fun move => nextAccount γ s move - s) -
            (ε / 8) *
              expect d (fun move => |nextAccount γ s move - s|)) := by
    rw [expect_const_mul, expect_sub, expect_const_mul]
  calc
    _ = expect d (fun move =>
        discountRate s *
          ((nextAccount γ s move - s) -
            (ε / 8) * |nextAccount γ s move - s|)) := by
      rw [hlinear]
      ring
    _ ≤ expect d (fun move =>
        logCorrector s - logCorrector (nextAccount γ s move)) :=
      expect_mono d _ _ fun move => by
        have hrewrite :
            discountRate s *
                (nextAccount γ s move - s -
                  (ε / 8) * |nextAccount γ s move - s|) =
              discountRate s *
                (nextAccount γ s move - s -
                  ε * |nextAccount γ s move - s| / 8) := by
          ring
        rw [hrewrite]
        exact hpoint move

/-- Closed form for the expected value of a scalar account potential after
one stochastic account update. -/
theorem expect_nextAccount_value
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) (V : ℝ → ℝ) :
    expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => V (nextAccount γ s move)) =
      upProbability γ s y * V (γ * s) +
        stayProbability γ M s y * V s +
        downProbability γ M s y * V (γ⁻¹ * s) := by
  classical
  rw [expect_eq_sum]
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simp [moveProbability, nextAccount, add_assoc]

/-- The probability-weighted variation bill for changing the account
potential by one multiplicative step. -/
def switchBudget (γ M s y : ℝ) (V : ℝ → ℝ) : ℝ :=
  upProbability γ s y * |V (γ * s) - V s| +
    downProbability γ M s y * |V (γ⁻¹ * s) - V s|

/-- The upward account-move probability is at most the largest positive gap
`2` divided by the upward account increment. -/
theorem upProbability_le_two_div
    {γ s y : ℝ} (h : IsValidScale γ s) (hyUpper : y ≤ 2) :
    upProbability γ s y ≤ 2 / (s * (γ - 1)) := by
  unfold upProbability
  apply div_le_div_of_nonneg_right
  · exact max_le hyUpper (by norm_num)
  · exact h.upDenom_pos.le

/-- The downward account-move probability is at most the largest negative
gap magnitude `1` divided by the downward account decrement. -/
theorem downProbability_le_one_div
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y) :
    downProbability γ M s y ≤ 1 / (s * (1 - γ⁻¹)) := by
  have hdenPos : 0 < s * (1 - γ⁻¹) :=
    lt_of_lt_of_le zero_lt_one h.2.2.2
  by_cases hMs : M < s
  · rw [downProbability, if_pos hMs]
    have hrewrite :
        min y 0 / (s * (γ⁻¹ - 1)) =
          (-min y 0) / (s * (1 - γ⁻¹)) := by
      have hden :
          s * (γ⁻¹ - 1) = -(s * (1 - γ⁻¹)) := by ring
      rw [hden, div_neg, neg_div]
    rw [hrewrite]
    apply div_le_div_of_nonneg_right
    · have hmin : -1 ≤ min y 0 :=
        le_min hyLower (by norm_num)
      linarith
    · exact hdenPos.le
  · rw [downProbability, if_neg hMs]
    exact div_nonneg zero_le_one hdenPos.le

/-- A sufficient adjacent-variation criterion for the weighted switch
budget. The permitted pointwise changes are proportional to the sizes of
the corresponding account moves. After multiplication by the rare-move
probabilities, each direction costs at most `ε * lam / 32`. -/
theorem switchBudget_le_of_adjacent_variation
    {γ M s y ε lam : ℝ} {V : ℝ → ℝ}
    (h : IsValidScale γ s) (hyLower : -1 ≤ y) (hyUpper : y ≤ 2)
    (hε : 0 ≤ ε) (hlam : 0 ≤ lam)
    (hupVariation :
      |V (γ * s) - V s| ≤
        ε * lam * (s * (γ - 1)) / 64)
    (hdownVariation :
      |V (γ⁻¹ * s) - V s| ≤
        ε * lam * (s * (1 - γ⁻¹)) / 32) :
    switchBudget γ M s y V ≤ ε * lam / 16 := by
  have hup0 : 0 ≤ upProbability γ s y := upProbability_nonneg h
  have hdown0 : 0 ≤ downProbability γ M s y :=
    downProbability_nonneg h
  have h_eps_lam : 0 ≤ ε * lam := mul_nonneg hε hlam
  have hupScale : 0 < s * (γ - 1) := h.upDenom_pos
  have hdownScale : 0 < s * (1 - γ⁻¹) :=
    lt_of_lt_of_le zero_lt_one h.2.2.2
  have hupTerm :
      upProbability γ s y * |V (γ * s) - V s| ≤
        ε * lam / 32 := by
    calc
      _ ≤ upProbability γ s y *
          (ε * lam * (s * (γ - 1)) / 64) :=
        mul_le_mul_of_nonneg_left hupVariation hup0
      _ ≤ (2 / (s * (γ - 1))) *
          (ε * lam * (s * (γ - 1)) / 64) := by
        apply mul_le_mul_of_nonneg_right
          (upProbability_le_two_div h hyUpper)
        positivity
      _ = ε * lam / 32 := by
        have hcancel (D a : ℝ) (hD : D ≠ 0) :
            (2 / D) * (a * D / 64) = a / 32 := by
          field_simp [hD]
          ring
        exact hcancel _ _ hupScale.ne'
  have hdownTerm :
      downProbability γ M s y * |V (γ⁻¹ * s) - V s| ≤
        ε * lam / 32 := by
    calc
      _ ≤ downProbability γ M s y *
          (ε * lam * (s * (1 - γ⁻¹)) / 32) :=
        mul_le_mul_of_nonneg_left hdownVariation hdown0
      _ ≤ (1 / (s * (1 - γ⁻¹))) *
          (ε * lam * (s * (1 - γ⁻¹)) / 32) := by
        apply mul_le_mul_of_nonneg_right
          (downProbability_le_one_div h hyLower)
        positivity
      _ = ε * lam / 32 := by
        have hcancel (D a : ℝ) (hD : D ≠ 0) :
            (1 / D) * (a * D / 32) = a / 32 := by
          field_simp [hD]
        exact hcancel _ _ hdownScale.ne'
  unfold switchBudget
  linarith

/-- Expected switching, rather than pointwise switching, is controlled by
the probability-weighted adjacent variation. This is the cancellation that
allows rare account moves to avoid a pointwise relative-rate requirement.
-/
theorem value_sub_expect_nextAccount_value_ge_neg_switchBudget
    {γ M s y : ℝ} (h : IsValidScale γ s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2) (V : ℝ → ℝ) :
    -switchBudget γ M s y V ≤
      V s -
        expect (updatePMF γ M s y h hyLower hyUpper)
          (fun move => V (nextAccount γ s move)) := by
  have hup0 : 0 ≤ upProbability γ s y := upProbability_nonneg h
  have hdown0 : 0 ≤ downProbability γ M s y :=
    downProbability_nonneg h
  have hupDiff :
      -upProbability γ s y * |V (γ * s) - V s| ≤
        upProbability γ s y * (V s - V (γ * s)) := by
    have hdiff : -|V (γ * s) - V s| ≤ V s - V (γ * s) := by
      rw [abs_sub_comm]
      exact neg_abs_le _
    nlinarith [mul_le_mul_of_nonneg_left hdiff hup0]
  have hdownDiff :
      -downProbability γ M s y * |V (γ⁻¹ * s) - V s| ≤
        downProbability γ M s y * (V s - V (γ⁻¹ * s)) := by
    have hdiff : -|V (γ⁻¹ * s) - V s| ≤
        V s - V (γ⁻¹ * s) := by
      rw [abs_sub_comm]
      exact neg_abs_le _
    nlinarith [mul_le_mul_of_nonneg_left hdiff hdown0]
  rw [expect_nextAccount_value h hyLower hyUpper]
  have hsum := probabilities_sum γ M s y
  have hidentity :
      V s -
          (upProbability γ s y * V (γ * s) +
            stayProbability γ M s y * V s +
            downProbability γ M s y * V (γ⁻¹ * s)) =
        upProbability γ s y * (V s - V (γ * s)) +
          downProbability γ M s y * (V s - V (γ⁻¹ * s)) := by
    calc
      _ = (upProbability γ s y + stayProbability γ M s y +
            downProbability γ M s y) * V s -
          (upProbability γ s y * V (γ * s) +
            stayProbability γ M s y * V s +
            downProbability γ M s y * V (γ⁻¹ * s)) := by
              rw [hsum]
              ring
      _ = _ := by ring
  rw [hidentity]
  unfold switchBudget
  linarith

/-- Away from the floor, the expected account increment equals the
payoff/value gap exactly. -/
theorem expectedChange_eq_of_floor_lt
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M < s) :
    expectedChange γ M s y = y := by
  have hup :
      γ * s - s = s * (γ - 1) := by ring
  have hdown :
      γ⁻¹ * s - s = s * (γ⁻¹ - 1) := by ring
  unfold expectedChange upProbability downProbability
  rw [if_pos hMs, hup, hdown,
    div_mul_cancel₀ _ h.upDenom_pos.ne',
    div_mul_cancel₀ _ h.downDenom_neg.ne]
  linarith [max_add_min y 0]

/-- At the floor, the expected account increment is the positive part of
the payoff/value gap. -/
theorem expectedChange_eq_of_le_floor
    {γ M s y : ℝ} (h : IsValidScale γ s) (hsM : s ≤ M) :
    expectedChange γ M s y = max y 0 := by
  have hup :
      γ * s - s = s * (γ - 1) := by ring
  unfold expectedChange upProbability downProbability
  rw [if_neg (not_lt.mpr hsM), hup, zero_mul, add_zero,
    div_mul_cancel₀ _ h.upDenom_pos.ne']

/-- The account update never has less expected growth than its input gap.
Away from the floor this is equality; at the floor, suppressing a requested
downward move can only increase the expected change. -/
theorem le_expectedChange
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s) :
    y ≤ expectedChange γ M s y := by
  by_cases hstrict : M < s
  · rw [expectedChange_eq_of_floor_lt h hstrict]
  · have hsM : s = M := le_antisymm (not_lt.mp hstrict) hMs
    rw [expectedChange_eq_of_le_floor h hsM.le]
    exact le_max_left y 0

/-- PMF form of the lower expected-growth inequality. -/
theorem le_expect_nextAccount_sub
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2) :
    y ≤
      expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => nextAccount γ s move - s) := by
  rw [expect_nextAccount_sub h hyLower hyUpper]
  exact le_expectedChange h hMs

/-- The update law's floor correction. With `M ≤ s`, expected account
growth minus the floor indicator is bounded above by the gap `y`. This is
the one-step inequality that telescopes in the uniform-payoff proof. -/
theorem expectedChange_sub_floorIndicator_le
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s)
    (hyLower : -1 ≤ y) :
    expectedChange γ M s y - (if s = M then 1 else 0) ≤ y := by
  by_cases hstrict : M < s
  · rw [expectedChange_eq_of_floor_lt h hstrict, if_neg (ne_of_gt hstrict)]
    linarith
  · have hsM : s = M := le_antisymm (not_lt.mp hstrict) hMs
    rw [expectedChange_eq_of_le_floor h (not_lt.mp hstrict), if_pos hsM]
    by_cases hy : 0 ≤ y
    · rw [max_eq_left hy]
      linarith
    · rw [max_eq_right (le_of_not_ge hy)]
      simpa using hyLower

/-- PMF form of the floor-corrected account inequality. -/
theorem expect_nextAccount_sub_floorIndicator_le
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
          (fun move => nextAccount γ s move - s) -
        (if s = M then 1 else 0) ≤ y := by
  rw [expect_nextAccount_sub h hyLower hyUpper]
  exact expectedChange_sub_floorIndicator_le h hMs hyLower

/-- The conditional-expectation algebra behind the positive drift of the
corrected value potential. The five premises are respectively the
probability-weighted value-switch estimate, the logarithmic-corrector
estimate, the absolute account-movement bound, the account update's lower
drift, and the discounted Bellman inequality. Their constants yield the
published margin `ε * lam / 8`. -/
theorem correctedValuePotential_drift_ge
    {ε lam oldCurrent oldNext newNext correctorGain
      expectedAccountChange expectedAbsChange expectedGap : ℝ}
    (hε : 0 ≤ ε) (hlam : 0 ≤ lam)
    (hswitch : -ε * lam / 16 ≤ newNext - oldNext)
    (hcorrector :
      lam * (expectedAccountChange - ε * expectedAbsChange / 8) ≤
        correctorGain)
    (habs : expectedAbsChange ≤ 2)
    (haccount : expectedGap + ε / 2 ≤ expectedAccountChange)
    (hbellman : 0 ≤ oldNext - oldCurrent + lam * expectedGap) :
    ε * lam / 8 ≤ newNext - oldCurrent + correctorGain := by
  have habsScaled :=
    mul_le_mul_of_nonneg_left habs (mul_nonneg hε hlam)
  have haccountScaled :=
    mul_le_mul_of_nonneg_left haccount hlam
  nlinarith

/-- One-step positive drift for the corrected value potential, with the
account-movement and logarithmic-corrector premises discharged by the
stochastic update kernel. The remaining two premises are game-facing: the
discounted-value switch estimate and the discounted Bellman inequality. -/
theorem correctedValuePotential_drift_ge_of_accountUpdate
    {γ M s y ε oldCurrent oldNext newNext : ℝ}
    (h : IsValidScale γ s) (hMs : M ≤ s) (hs1 : 1 < s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2)
    (hε : 0 ≤ ε)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hswitch :
      -ε * discountRate s / 16 ≤ newNext - oldNext)
    (hbellman :
      0 ≤ oldNext - oldCurrent + discountRate s * (y - ε / 2)) :
    ε * discountRate s / 8 ≤
      newNext - oldCurrent +
        expect (updatePMF γ M s y h hyLower hyUpper)
          (fun move =>
            logCorrector s - logCorrector (nextAccount γ s move)) := by
  let d := updatePMF γ M s y h hyLower hyUpper
  have hcorrector :
      discountRate s *
          (expect d (fun move => nextAccount γ s move - s) -
            ε *
              expect d (fun move => |nextAccount γ s move - s|) / 8) ≤
        expect d (fun move =>
          logCorrector s - logCorrector (nextAccount γ s move)) := by
    exact discountRate_mul_expect_sub_le_expect_logCorrector_sub
      h hyLower hyUpper hsecant
  have habs :
      expect d (fun move => |nextAccount γ s move - s|) ≤ 2 :=
    expect_abs_nextAccount_sub_le_two h hyLower hyUpper
  have haccountBase :
      y ≤ expect d (fun move => nextAccount γ s move - s) :=
    le_expect_nextAccount_sub h hMs hyLower hyUpper
  have haccount :
      y - ε / 2 + ε / 2 ≤
        expect d (fun move => nextAccount γ s move - s) := by
    linarith
  exact correctedValuePotential_drift_ge hε
    (discountRate_pos hs1).le hswitch hcorrector habs haccount hbellman

/-- The published one-step payoff estimate. The account gap is formed using
the old discounted value. If switching to the next discounted value loses
at most `ε * lam / 16`, with `lam ≤ 1`, the stage payoff minus the switched
value covers the account drift, the floor correction, and a `9ε/16` error.
-/
theorem payoff_sub_switchedValue_ge
    {γ M s ε lam payoff oldValue newValue : ℝ}
    (h : IsValidScale γ s) (hMs : M ≤ s)
    (hε : 0 ≤ ε) (hlam1 : lam ≤ 1)
    (hyLower : -1 ≤ payoff - oldValue + ε / 2)
    (hyUpper : payoff - oldValue + ε / 2 ≤ 2)
    (hswitch : -ε * lam / 16 ≤ oldValue - newValue) :
    -9 * ε / 16 +
          expect
            (updatePMF γ M s (payoff - oldValue + ε / 2) h
              hyLower hyUpper)
            (fun move => nextAccount γ s move - s) -
          (if s = M then 1 else 0) ≤
        payoff - newValue := by
  have haccount :=
    expect_nextAccount_sub_floorIndicator_le h hMs hyLower hyUpper
  have h_eps_lam : ε * lam ≤ ε := by
    exact mul_le_of_le_one_right hε hlam1
  nlinarith

/-- Account-step payoff estimate with the switched value expressed as an
actual expectation over the same account-update PMF. The analytic obligation
is exactly the weighted `switchBudget ≤ ε * lam / 16`; no pointwise
`O(lam)` bound on adjacent values is assumed. -/
theorem payoff_sub_expectedNextValue_ge
    {γ M s ε lam payoff : ℝ} {V : ℝ → ℝ}
    (h : IsValidScale γ s) (hMs : M ≤ s)
    (hε : 0 ≤ ε) (hlam1 : lam ≤ 1)
    (hyLower : -1 ≤ payoff - V s + ε / 2)
    (hyUpper : payoff - V s + ε / 2 ≤ 2)
    (hbudget :
      switchBudget γ M s (payoff - V s + ε / 2) V ≤ ε * lam / 16) :
    -9 * ε / 16 +
          expect
            (updatePMF γ M s (payoff - V s + ε / 2) h
              hyLower hyUpper)
            (fun move => nextAccount γ s move - s) -
          (if s = M then 1 else 0) ≤
        payoff -
          expect
            (updatePMF γ M s (payoff - V s + ε / 2) h
              hyLower hyUpper)
            (fun move => V (nextAccount γ s move)) := by
  have hswitchBase :=
    value_sub_expect_nextAccount_value_ge_neg_switchBudget
      (M := M) h hyLower hyUpper V
  have hswitch :
      -ε * lam / 16 ≤
        V s -
          expect
            (updatePMF γ M s (payoff - V s + ε / 2) h
              hyLower hyUpper)
            (fun move => V (nextAccount γ s move)) := by
    have := (neg_le_neg hbudget).trans hswitchBase
    nlinarith
  exact payoff_sub_switchedValue_ge h hMs hε hlam1
    hyLower hyUpper hswitch

/-- One-step payoff estimate discharged by the two explicit adjacent-value
variation bounds. This is the proof-facing interface for the analytic
discounted-value germ estimate. -/
theorem payoff_sub_expectedNextValue_ge_of_adjacent_variation
    {γ M s ε lam payoff : ℝ} {V : ℝ → ℝ}
    (h : IsValidScale γ s) (hMs : M ≤ s)
    (hε : 0 ≤ ε) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hyLower : -1 ≤ payoff - V s + ε / 2)
    (hyUpper : payoff - V s + ε / 2 ≤ 2)
    (hupVariation :
      |V (γ * s) - V s| ≤
        ε * lam * (s * (γ - 1)) / 64)
    (hdownVariation :
      |V (γ⁻¹ * s) - V s| ≤
        ε * lam * (s * (1 - γ⁻¹)) / 32) :
    -9 * ε / 16 +
          expect
            (updatePMF γ M s (payoff - V s + ε / 2) h
              hyLower hyUpper)
            (fun move => nextAccount γ s move - s) -
          (if s = M then 1 else 0) ≤
        payoff -
          expect
            (updatePMF γ M s (payoff - V s + ε / 2) h
              hyLower hyUpper)
            (fun move => V (nextAccount γ s move)) := by
  apply payoff_sub_expectedNextValue_ge h hMs hε hlam1
    hyLower hyUpper
  exact switchBudget_le_of_adjacent_variation h hyLower hyUpper
    hε hlam0 hupVariation hdownVariation

/-- Finite-horizon telescope for the account-process payoff inequality.
This is the deterministic expectation-level form of the summation step: a
one-step `9ε/16` loss accumulates linearly, account increments telescope,
and floor corrections remain as an occupation sum. -/
theorem sum_payoff_ge_of_account_steps
    (ε : ℝ) (payoff nextValue account floorLoss : ℕ → ℝ)
    (hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) - floorLoss t ≤
        payoff t - nextValue t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, nextValue t) -
          (T : ℝ) * (9 * ε / 16) +
          (account T - account 0) -
          ∑ t ∈ Finset.range T, floorLoss t ≤
        ∑ t ∈ Finset.range T, payoff t := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      push_cast
      linarith [hstep T]

/-- Cesàro conclusion of the account telescope. If the average switched
value loses at most `ε/8`, floor occupation costs at most `ε/8`, and the
expected account has not fallen below its initial level, then the average
payoff is at least the target minus `ε`. -/
theorem average_payoff_ge_target_sub_epsilon_of_account_bounds
    {ε target : ℝ} (hε : 0 ≤ ε)
    (payoff nextValue account floorLoss : ℕ → ℝ)
    (hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) - floorLoss t ≤
        payoff t - nextValue t)
    {T : ℕ} (hT : 0 < T)
    (haccount : account 0 ≤ account T)
    (hvalue :
      target - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t)
    (hfloor :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8) :
    target - ε ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, payoff t := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum :=
    sum_payoff_ge_of_account_steps ε payoff nextValue account floorLoss
      hstep T
  have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
  have hscaled' :
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, nextValue t) -
            9 * ε / 16 +
            (T : ℝ)⁻¹ * (account T - account 0) -
            (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, floorLoss t) ≤
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, payoff t := by
    calc
      _ = (T : ℝ)⁻¹ *
          ((∑ t ∈ Finset.range T, nextValue t) -
            (T : ℝ) * (9 * ε / 16) +
            (account T - account 0) -
            ∑ t ∈ Finset.range T, floorLoss t) := by
              rw [inv_eq_one_div]
              field_simp
      _ ≤ _ := hscaled
  have haccountScaled :
      0 ≤ (T : ℝ)⁻¹ * (account T - account 0) :=
    mul_nonneg (inv_nonneg.mpr hTreal.le) (sub_nonneg.mpr haccount)
  nlinarith

/-- Total floor occupation is bounded by a bounded potential with positive
drift proportional to the local discount. This is the abstract form of the
published floor-occupation estimate `∑ 1{sₜ=M} ≤ 9 / (ε λ(M))`. -/
theorem sum_floorLoss_le_of_potential_drift
    {ε lamFloor : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlamFloor : 0 < lamFloor)
    (lam potential floorLoss : ℕ → ℝ)
    (hfloor : ∀ t, lamFloor * floorLoss t ≤ lam t)
    (hdrift : ∀ t,
      ε * lam t / 8 ≤ potential (t + 1) - potential t)
    {T : ℕ} (hpotential0 : -ε / 8 ≤ potential 0)
    (hpotentialT : potential T ≤ 1) :
    ∑ t ∈ Finset.range T, floorLoss t ≤ 9 / (ε * lamFloor) := by
  have hdriftSumAll : ∀ n : ℕ,
      ε / 8 * (∑ t ∈ Finset.range n, lam t) ≤
        potential n - potential 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        nlinarith [hdrift n]
  have hdriftSum := hdriftSumAll T
  have hlamSum :
      ε * (∑ t ∈ Finset.range T, lam t) ≤ 9 := by
    have hpotentialRange : potential T - potential 0 ≤ 9 / 8 := by
      nlinarith
    nlinarith
  have hfloorSum :
      lamFloor * (∑ t ∈ Finset.range T, floorLoss t) ≤
        ∑ t ∈ Finset.range T, lam t := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => hfloor t
  have hcombined :
      ε * lamFloor * (∑ t ∈ Finset.range T, floorLoss t) ≤ 9 := by
    have := mul_le_mul_of_nonneg_left hfloorSum hε.le
    nlinarith
  rw [le_div_iff₀ (mul_pos hε hlamFloor)]
  nlinarith

/-- Cesàro form of the floor-occupation estimate. The explicit horizon
condition is the cross-multiplied form of
`T ≥ 72 / (ε² * lamFloor)`. -/
theorem average_floorLoss_le_of_potential_drift
    {ε lamFloor : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlamFloor : 0 < lamFloor)
    (lam potential floorLoss : ℕ → ℝ)
    (hfloor : ∀ t, lamFloor * floorLoss t ≤ lam t)
    (hdrift : ∀ t,
      ε * lam t / 8 ≤ potential (t + 1) - potential t)
    {T : ℕ} (hT : 0 < T)
    (hpotential0 : -ε / 8 ≤ potential 0)
    (hpotentialT : potential T ≤ 1)
    (hhorizon : 72 ≤ (T : ℝ) * ε ^ 2 * lamFloor) :
    (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, floorLoss t) ≤ ε / 8 := by
  have hsum := sum_floorLoss_le_of_potential_drift
    hε hε1 hlamFloor lam potential floorLoss hfloor hdrift
    hpotential0 hpotentialT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, floorLoss t) ≤
        (T : ℝ)⁻¹ * (9 / (ε * lamFloor)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    _ = 9 / ((T : ℝ) * ε * lamFloor) := by
      field_simp
    _ ≤ ε / 8 := by
      rw [div_le_div_iff₀
        (mul_pos (mul_pos hTreal hε) hlamFloor) (by norm_num)]
      nlinarith [sq_nonneg ε]

end MertensNeymanAccount
end StochasticGame
end GameTheory
