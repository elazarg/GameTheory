module

/-
# Integrating supporting slopes

A function with supporting slopes on a closed interval is the integral of
those slopes, up to an additive constant. Slopes may be signed, globally
unbounded, or discontinuous. Supporting inequalities imply monotonicity and
local Lipschitz continuity of the function. The exceptional set of slopes is
countable, so the fundamental theorem applies.

The differentiation argument adapts MathEconLib's single-parameter envelope
proof, Copyright (c) 2026 Bo Cowgill, under Apache-2.0.
-/

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

noncomputable section

namespace GameTheory.Math

open Set MeasureTheory Filter Topology Asymptotics

/-- Supporting slopes are monotone on their common interval. -/
theorem monotoneOn_of_supporting_slopes {U q : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (x - y) * q y ≤ U x - U y) :
    MonotoneOn q (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra! hq
    have hxy := h x hx y hy
    have hyx := h y hy x hx
    nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hq)]
  · rfl

private theorem continuousOn_of_supporting_slopesOn {U q : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (x - y) * q y ≤ U x - U y) :
    ContinuousOn U (Icc a b) := by
  have hmono := monotoneOn_of_supporting_slopes h
  let C := |q a| + |q b|
  have hbound : ∀ x ∈ Icc a b, |q x| ≤ C := by
    intro x hx
    have hlo := hmono ⟨le_rfl, hab⟩ hx hx.1
    have hhi := hmono hx ⟨hab, le_rfl⟩ hx.2
    exact abs_le.mpr ⟨by dsimp [C]; linarith [neg_abs_le (q a), abs_nonneg (q b)],
      by dsimp [C]; linarith [le_abs_self (q b), abs_nonneg (q a)]⟩
  have hupper : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      U x - U y ≤ C * |x - y| := by
    intro x hx y hy
    calc
      U x - U y ≤ (x - y) * q x := by linarith [h y hy x hx]
      _ ≤ |(x - y) * q x| := le_abs_self _
      _ = |x - y| * |q x| := abs_mul _ _
      _ ≤ |x - y| * C := mul_le_mul_of_nonneg_left (hbound x hx) (abs_nonneg _)
      _ = C * |x - y| := mul_comm _ _
  have hlip : LipschitzOnWith ⟨C, by dsimp [C]; positivity⟩ U (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |U x - U y| ≤ C * |x - y|
    have hlo := hupper y hy x hx
    rw [abs_sub_comm y x] at hlo
    exact abs_le.mpr ⟨by linarith, hupper x hx y hy⟩
  exact hlip.continuousOn

private theorem hasDerivAt_of_supporting_slopes {U q : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (x - y) * q y ≤ U x - U y) {x : ℝ}
    (hx : x ∈ Ioo a b)
    (hq : ContinuousAt q x) : HasDerivAt U (q x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hmaps : Tendsto (x + ·) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : ℝ => x + t) 0 from
      continuousAt_const.add continuousAt_id).tendsto
  have hin : ∀ᶠ t in 𝓝 0, x + t ∈ Icc a b := hmaps (Icc_mem_nhds hx.1 hx.2)
  have hsmall : ∀ᶠ t in 𝓝 0, ‖q (x + t) - q x‖ < c := by
    have ht : Tendsto (fun t => q (x + t) - q x) (𝓝 0) (𝓝 0) := by
      simpa using (hq.tendsto.comp hmaps).sub_const (q x)
    filter_upwards [ht (Metric.ball_mem_nhds 0 hc)] with t hh
    rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hh
  filter_upwards [hin, hsmall] with t hxt ht
  have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hlo := h (x + t) hxt x hx'
  have hhi := h x hx' (x + t) hxt
  have he : 0 ≤ U (x + t) - U x - t * q x := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg he]
  calc
    U (x + t) - U x - t * q x ≤ t * (q (x + t) - q x) := by nlinarith
    _ ≤ |t * (q (x + t) - q x)| := le_abs_self _
    _ = |t| * |q (x + t) - q x| := abs_mul _ _
    _ ≤ |t| * c := mul_le_mul_of_nonneg_left (by simpa using ht.le) (abs_nonneg t)
    _ = c * |t| := mul_comm _ _

/-- Interval-local supporting slopes recover the endpoint difference by
integration. No continuity or sign assumption on the slopes is required. -/
theorem integral_eq_sub_of_supporting_slopesOn {U q : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (x - y) * q y ≤ U x - U y) :
    (∫ x in a..b, q x) = U b - U a := by
  have hmono := monotoneOn_of_supporting_slopes h
  have hcont : ContinuousOn U (uIcc a b) := by
    simpa only [uIcc_of_le hab] using continuousOn_of_supporting_slopesOn hab h
  have hm : MonotoneOn q (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hmono
  apply integral_eq_of_hasDerivAt_off_countable U q
    hmono.countable_not_continuousWithinAt hcont _ hm.intervalIntegrable
  intro x hx
  have hxi : x ∈ Ioo a b := by
    simpa only [min_eq_left hab, max_eq_right hab] using hx.1
  have hxc : x ∈ Icc a b := ⟨hxi.1.le, hxi.2.le⟩
  have hq : ContinuousWithinAt q (Icc a b) x := by
    by_contra hn
    exact hx.2 ⟨hxc, hn⟩
  exact hasDerivAt_of_supporting_slopes h hxi (hq.continuousAt (Icc_mem_nhds hxi.1 hxi.2))

/-- Global supporting slopes recover the function by integration on every
oriented interval. Monotonicity follows from the supporting inequalities. -/
theorem integral_eq_sub_of_supporting_slopes {U q : ℝ → ℝ}
    (h : ∀ x y, (x - y) * q y ≤ U x - U y) (a b : ℝ) :
    (∫ x in a..b, q x) = U b - U a := by
  rcases le_total a b with hab | hba
  · exact integral_eq_sub_of_supporting_slopesOn hab (fun x _ y _ => h x y)
  · rw [intervalIntegral.integral_symm]
    have hi := integral_eq_sub_of_supporting_slopesOn hba (fun x _ y _ => h x y)
    linarith

end GameTheory.Math
