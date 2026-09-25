/-
# Pointwise convergence of discrete probability laws

Pointwise convergence is stated on the canonical PMF weights. Normalization
controls escaping tails, so bounded expectations converge on arbitrary carriers.
-/

import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Mixture
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section

namespace GameTheory.Math.Probability

open Filter

/-- Pointwise convergence of ordinary PMFs in their native `ENNReal` weights. -/
def PMFConvergesPointwise {α : Type*}
    (sequence : ℕ → PMF α) (target : PMF α) : Prop :=
  ∀ value : α, Tendsto (fun n => sequence n value) atTop (nhds (target value))

theorem pmfConvergesPointwise_const {α : Type*} (law : PMF α) :
    PMFConvergesPointwise (fun _ => law) law :=
  fun _ => tendsto_const_nhds

/-- Pointwise PMF convergence implies convergence of the corresponding real
weights, because each target atom has finite mass. -/
theorem PMFConvergesPointwise.toReal {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target) (value : α) :
    Tendsto (fun n => (sequence n value).toReal) atTop
      (nhds ((target value).toReal)) :=
  (ENNReal.continuousAt_toReal (target.apply_ne_top value)).tendsto.comp (h value)

/-- Native and real pointwise mass convergence agree for PMFs. -/
theorem pmfConvergesPointwise_iff_toReal {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α} :
    PMFConvergesPointwise sequence target ↔
      ∀ value : α, Tendsto (fun n => (sequence n value).toReal) atTop
        (nhds ((target value).toReal)) := by
  constructor
  · intro h value
    exact h.toReal value
  · intro h value
    have hcoe : Tendsto (fun n => ENNReal.ofReal ((sequence n value).toReal)) atTop
        (nhds (ENNReal.ofReal ((target value).toReal))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (h value)
    simpa only [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)] using hcoe

/-- The overlap of a pointwise-convergent PMF with its limit approaches one,
even when the underlying carrier is uncountable. -/
theorem pmf_overlap_tendsto {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target) :
    Tendsto (fun n => ∑' value : α,
      min ((sequence n value).toReal) ((target value).toReal)) atTop (nhds 1) := by
  have hsum : Summable (fun value : α => (target value).toReal) :=
    pmf_weight_summable target
  have ht := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun n value => min ((sequence n value).toReal) ((target value).toReal))
    (g := fun value => (target value).toReal)
    (bound := fun value => (target value).toReal)
    hsum
    (fun value => by
      have hconst : Tendsto (fun _ : ℕ => (target value).toReal) atTop
          (nhds ((target value).toReal)) := tendsto_const_nhds
      simpa using (h.toReal value).min hconst)
    (Eventually.of_forall (fun n value => by
      have hnonneg : 0 ≤ min ((sequence n value).toReal) ((target value).toReal) :=
        le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hle := min_le_right ((sequence n value).toReal) ((target value).toReal)
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]))
  simpa [pmf_weight_tsum_one target] using ht

/-- A bounded payoff's expectation changes by at most twice its bound times
the two laws' non-overlap mass. -/
theorem abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap {α : Type*}
    (μ ν : PMF α) (f : α → ℝ) {C : ℝ} (hbd : ∀ value, |f value| ≤ C) :
    |expect μ f (payoffIntegrable_of_bounded μ f hbd) -
      expect ν f (payoffIntegrable_of_bounded ν f hbd)| ≤
      2 * C * (1 - ∑' value : α,
        min ((μ value).toReal) ((ν value).toReal)) := by
  let r : α → ℝ := fun value => min ((μ value).toReal) ((ν value).toReal)
  have hr_nonneg : ∀ value, 0 ≤ r value :=
    fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hr_le_μ : ∀ value, r value ≤ (μ value).toReal := fun _ => min_le_left _ _
  have hr_le_ν : ∀ value, r value ≤ (ν value).toReal := fun _ => min_le_right _ _
  have hμ_sum : Summable (fun value : α => (μ value).toReal) := pmf_weight_summable μ
  have hν_sum : Summable (fun value : α => (ν value).toReal) := pmf_weight_summable ν
  have hr_sum_μ : Summable r := by
    refine Summable.of_norm_bounded hμ_sum ?_
    intro value
    simp [r, Real.norm_eq_abs, abs_of_nonneg (hr_nonneg value), hr_le_μ value]
  have hr_sum_ν : Summable r := by
    refine Summable.of_norm_bounded hν_sum ?_
    intro value
    simp [r, Real.norm_eq_abs, abs_of_nonneg (hr_nonneg value), hr_le_ν value]
  have hrf_sum : Summable (fun value : α => r value * f value) := by
    refine Summable.of_norm_bounded (hr_sum_μ.mul_left C) ?_
    intro value
    calc
      ‖r value * f value‖ = |r value * f value| := Real.norm_eq_abs _
      _ = r value * |f value| := by rw [abs_mul, abs_of_nonneg (hr_nonneg value)]
      _ ≤ r value * C := mul_le_mul_of_nonneg_left (hbd value) (hr_nonneg value)
      _ = C * r value := by ring
  have hμf_sum : Summable (fun value : α => (μ value).toReal * f value) := by
    have h := payoffIntegrable_of_bounded μ f hbd
    have hnorm : Summable (fun value : α => ‖(μ value).toReal * f value‖) := by
      simpa [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg] using h
    exact hnorm.of_norm
  have hνf_sum : Summable (fun value : α => (ν value).toReal * f value) := by
    have h := payoffIntegrable_of_bounded ν f hbd
    have hnorm : Summable (fun value : α => ‖(ν value).toReal * f value‖) := by
      simpa [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg] using h
    exact hnorm.of_norm
  have hμ_tail_hasSum : HasSum (fun value : α => ((μ value).toReal - r value) * f value)
      (expect μ f (payoffIntegrable_of_bounded μ f hbd) -
        ∑' value : α, r value * f value) := by
    have h := hμf_sum.hasSum.sub hrf_sum.hasSum
    have hfun : (fun value : α => (μ value).toReal * f value - r value * f value) =
        (fun value : α => ((μ value).toReal - r value) * f value) := by
      funext value
      ring
    rw [hfun] at h
    simpa [expect] using h
  have hν_tail_hasSum : HasSum (fun value : α => ((ν value).toReal - r value) * f value)
      (expect ν f (payoffIntegrable_of_bounded ν f hbd) -
        ∑' value : α, r value * f value) := by
    have h := hνf_sum.hasSum.sub hrf_sum.hasSum
    have hfun : (fun value : α => (ν value).toReal * f value - r value * f value) =
        (fun value : α => ((ν value).toReal - r value) * f value) := by
      funext value
      ring
    rw [hfun] at h
    simpa [expect] using h
  have hμ_tail_mass : HasSum (fun value : α => C * ((μ value).toReal - r value))
      (C * (1 - ∑' value : α, r value)) := by
    have hbase := hμ_sum.hasSum.sub hr_sum_μ.hasSum
    have hbase' : HasSum (fun value : α => (μ value).toReal - r value)
        (1 - ∑' value : α, r value) := by
      simpa [pmf_weight_tsum_one μ] using hbase
    simpa [mul_sub] using hbase'.mul_left C
  have hν_tail_mass : HasSum (fun value : α => C * ((ν value).toReal - r value))
      (C * (1 - ∑' value : α, r value)) := by
    have hbase := hν_sum.hasSum.sub hr_sum_ν.hasSum
    have hbase' : HasSum (fun value : α => (ν value).toReal - r value)
        (1 - ∑' value : α, r value) := by
      simpa [pmf_weight_tsum_one ν] using hbase
    simpa [mul_sub] using hbase'.mul_left C
  have hμ_tail_bound :
      |expect μ f (payoffIntegrable_of_bounded μ f hbd) -
        ∑' value : α, r value * f value| ≤
        C * (1 - ∑' value : α, r value) := by
    have hle := hμ_tail_hasSum.norm_le_of_bounded hμ_tail_mass ?_
    · simpa [Real.norm_eq_abs] using hle
    intro value
    have htail_nonneg : 0 ≤ (μ value).toReal - r value :=
      sub_nonneg.2 (hr_le_μ value)
    calc
      ‖((μ value).toReal - r value) * f value‖ =
          |((μ value).toReal - r value) * f value| := Real.norm_eq_abs _
      _ = ((μ value).toReal - r value) * |f value| := by
        rw [abs_mul, abs_of_nonneg htail_nonneg]
      _ ≤ ((μ value).toReal - r value) * C :=
        mul_le_mul_of_nonneg_left (hbd value) htail_nonneg
      _ = C * ((μ value).toReal - r value) := by ring
  have hν_tail_bound :
      |expect ν f (payoffIntegrable_of_bounded ν f hbd) -
        ∑' value : α, r value * f value| ≤
        C * (1 - ∑' value : α, r value) := by
    have hle := hν_tail_hasSum.norm_le_of_bounded hν_tail_mass ?_
    · simpa [Real.norm_eq_abs] using hle
    intro value
    have htail_nonneg : 0 ≤ (ν value).toReal - r value :=
      sub_nonneg.2 (hr_le_ν value)
    calc
      ‖((ν value).toReal - r value) * f value‖ =
          |((ν value).toReal - r value) * f value| := Real.norm_eq_abs _
      _ = ((ν value).toReal - r value) * |f value| := by
        rw [abs_mul, abs_of_nonneg htail_nonneg]
      _ ≤ ((ν value).toReal - r value) * C :=
        mul_le_mul_of_nonneg_left (hbd value) htail_nonneg
      _ = C * ((ν value).toReal - r value) := by ring
  calc
    _ = |(expect μ f (payoffIntegrable_of_bounded μ f hbd) -
          ∑' value : α, r value * f value) -
          (expect ν f (payoffIntegrable_of_bounded ν f hbd) -
            ∑' value : α, r value * f value)| := by ring_nf
    _ ≤ |expect μ f (payoffIntegrable_of_bounded μ f hbd) -
          ∑' value : α, r value * f value| +
          |expect ν f (payoffIntegrable_of_bounded ν f hbd) -
            ∑' value : α, r value * f value| := abs_sub _ _
    _ ≤ C * (1 - ∑' value : α, r value) +
          C * (1 - ∑' value : α, r value) :=
      add_le_add hμ_tail_bound hν_tail_bound
    _ = 2 * C * (1 - ∑' value : α, r value) := by ring

/-- Bounded expectations converge under pointwise PMF convergence on any
carrier. No finite or countable typeclass is needed. -/
theorem PMFConvergesPointwise.expect_of_bounded {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    (f : α → ℝ) {C : ℝ} (hbd : ∀ value, |f value| ≤ C) :
    Tendsto (fun n => expect (sequence n) f
      (payoffIntegrable_of_bounded (sequence n) f hbd)) atTop
      (nhds (expect target f (payoffIntegrable_of_bounded target f hbd))) := by
  have hoverlap := pmf_overlap_tendsto h
  have hgap : Tendsto (fun n => 2 * C *
      (1 - ∑' value : α,
        min ((sequence n value).toReal) ((target value).toReal))) atTop (nhds 0) := by
    have hsub : Tendsto (fun n => 1 - ∑' value : α,
        min ((sequence n value).toReal) ((target value).toReal)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.sub hoverlap :
        Tendsto (fun n : ℕ => (1 : ℝ) - ∑' value : α,
          min ((sequence n value).toReal) ((target value).toReal)) atTop (nhds (1 - 1)))
    simpa [mul_assoc] using hsub.const_mul (2 * C)
  have habs : Tendsto (fun n =>
      |expect (sequence n) f (payoffIntegrable_of_bounded (sequence n) f hbd) -
        expect target f (payoffIntegrable_of_bounded target f hbd)|) atTop (nhds 0) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hgap
    intro n
    exact abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap (sequence n) target f hbd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- On a finite carrier every real observable is bounded, so pointwise mass
convergence gives expectation convergence without a caller-supplied bound. -/
theorem PMFConvergesPointwise.expect_finite {α : Type*} [Fintype α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target) (f : α → ℝ) :
    Tendsto (fun n => expect (sequence n) f (payoffIntegrable_of_finite (sequence n) f))
      atTop (nhds (expect target f (payoffIntegrable_of_finite target f))) := by
  have hfinite : (Set.range fun value : α => |f value|).Finite := Set.finite_range _
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  have hbd : ∀ value, |f value| ≤ C := fun value => hC ⟨value, rfl⟩
  exact h.expect_of_bounded f hbd

/-- For a fixed kernel, integrable bind expectations converge when the outer
PMFs converge on a finite carrier. Conditional integration is needed only at
atoms supported by the actual outer laws. -/
theorem PMFConvergesPointwise.expect_bind_finite {α β : Type*} [Fintype α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    (q : α → PMF β) (f : β → ℝ)
    (hsequence : ∀ n, PayoffIntegrable ((sequence n).bind q) f)
    (htarget : PayoffIntegrable (target.bind q) f) :
    Tendsto (fun n => expect ((sequence n).bind q) f (hsequence n)) atTop
      (nhds (expect (target.bind q) f htarget)) := by
  classical
  let g : α → ℝ := fun a =>
    if ha : PayoffIntegrable (q a) f then expect (q a) f ha else 0
  have hrow (p : PMF α) (hp : PayoffIntegrable (p.bind q) f)
      (a : α) (ha : a ∈ p.support) :
      g a = expect (q a) f
        (payoffIntegrable_bind_conditional_on_support p q f hp a ha) := by
    have hc := payoffIntegrable_bind_conditional_on_support p q f hp a ha
    simp [g, hc]
  have hseq (n : ℕ) :
      expect ((sequence n).bind q) f (hsequence n) =
        expect (sequence n) g (payoffIntegrable_of_finite _ _) := by
    exact expect_bind_tower_on_support (sequence n) q f (hsequence n)
      g (hrow (sequence n) (hsequence n))
  have ht : expect (target.bind q) f htarget =
      expect target g (payoffIntegrable_of_finite _ _) := by
    exact expect_bind_tower_on_support target q f htarget g (hrow target htarget)
  simpa only [hseq, ht] using h.expect_finite g

/-- On a finite outer carrier, sequence bind integration plus pointwise PMF
convergence also forces integration of the limiting bind. -/
theorem PMFConvergesPointwise.payoffIntegrable_bind_finite
    {α β : Type*} [Fintype α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    (q : α → PMF β) (f : β → ℝ)
    (hsequence : ∀ n, PayoffIntegrable ((sequence n).bind q) f) :
    PayoffIntegrable (target.bind q) f := by
  apply payoffIntegrable_bind_of_finite_support target q f
    (Set.finite_univ.subset (Set.subset_univ _))
  intro a ha
  have hpos : 0 < (target a).toReal :=
    ENNReal.toReal_pos ((target.mem_support_iff a).mp ha)
      (target.apply_ne_top a)
  have hevent : ∀ᶠ n in atTop, 0 < (sequence n a).toReal :=
    (h.toReal a).eventually (eventually_gt_nhds hpos)
  obtain ⟨n, hn⟩ := hevent.exists
  have ha' : a ∈ (sequence n).support := by
    rw [PMF.mem_support_iff]
    intro hzero
    simp [hzero] at hn
  exact payoffIntegrable_bind_conditional_on_support
    (sequence n) q f (hsequence n) a ha'

/-- The limiting bind guard is derived from sequence integration, so the
caller need only certify the actual sequence laws. -/
theorem PMFConvergesPointwise.expect_bind_finite_of_sequence_integrable
    {α β : Type*} [Fintype α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    (q : α → PMF β) (f : β → ℝ)
    (hsequence : ∀ n, PayoffIntegrable ((sequence n).bind q) f) :
    Tendsto (fun n => expect ((sequence n).bind q) f (hsequence n)) atTop
      (nhds (expect (target.bind q) f
        (h.payoffIntegrable_bind_finite q f hsequence))) :=
  h.expect_bind_finite q f hsequence
    (h.payoffIntegrable_bind_finite q f hsequence)

/-- On a finite carrier, jointly pointwise-convergent masses and observables
have convergent expectations without a separate uniform bound. -/
theorem PMFConvergesPointwise.expect_varying_finite {α : Type*} [Fintype α]
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    {observable : ℕ → α → ℝ} {limit : α → ℝ}
    (hobservable : ∀ value,
      Tendsto (fun n => observable n value) atTop (nhds (limit value))) :
    Tendsto (fun n => expect (sequence n) (observable n)
      (payoffIntegrable_of_finite (sequence n) (observable n))) atTop
      (nhds (expect target limit (payoffIntegrable_of_finite target limit))) := by
  simp_rw [expect_eq_sum]
  exact tendsto_finsetSum Finset.univ fun value _ =>
    (h.toReal value).mul (hobservable value)

/-- Expectations converge when both the PMF and observable vary pointwise,
provided all observables share one absolute bound. -/
theorem PMFConvergesPointwise.expect_varying_of_bounded {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    (observable : ℕ → α → ℝ) (limit : α → ℝ) {C : ℝ}
    (hbd : ∀ n value, |observable n value| ≤ C)
    (hobservable : ∀ value,
      Tendsto (fun n => observable n value) atTop (nhds (limit value))) :
    Tendsto (fun n => expect (sequence n) (observable n)
      (payoffIntegrable_of_bounded (sequence n) (observable n) (hbd n))) atTop
      (nhds (expect target limit (payoffIntegrable_of_bounded target limit (by
        intro value
        exact le_of_tendsto ((hobservable value).abs)
          (Eventually.of_forall fun n => hbd n value))))) := by
  have hlimitBound : ∀ value, |limit value| ≤ C := by
    intro value
    exact le_of_tendsto ((hobservable value).abs)
      (Eventually.of_forall fun n => hbd n value)
  have hfixed : Tendsto (fun n => expect target (observable n)
      (payoffIntegrable_of_bounded target (observable n) (hbd n))) atTop
      (nhds (expect target limit
        (payoffIntegrable_of_bounded target limit hlimitBound))) := by
    have hsum : Summable (fun value : α => (target value).toReal * C) :=
      (pmf_weight_summable target).mul_right C
    have ht := tendsto_tsum_of_dominated_convergence
      (𝓕 := atTop)
      (f := fun n value => (target value).toReal * observable n value)
      (g := fun value => (target value).toReal * limit value)
      (bound := fun value => (target value).toReal * C)
      hsum
      (fun value =>
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (target value).toReal)
          atTop (nhds ((target value).toReal))).mul (hobservable value))
      (Eventually.of_forall (fun n value => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (hbd n value) ENNReal.toReal_nonneg))
    simpa only [expect] using ht
  have hoverlap := pmf_overlap_tendsto h
  have hgap : Tendsto (fun n => 2 * C *
      (1 - ∑' value : α,
        min ((sequence n value).toReal) ((target value).toReal))) atTop (nhds 0) := by
    have hsub : Tendsto (fun n => 1 - ∑' value : α,
        min ((sequence n value).toReal) ((target value).toReal)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.sub hoverlap :
        Tendsto (fun n : ℕ => (1 : ℝ) - ∑' value : α,
          min ((sequence n value).toReal) ((target value).toReal)) atTop (nhds (1 - 1)))
    simpa [mul_assoc] using hsub.const_mul (2 * C)
  have hdelta : Tendsto (fun n =>
      expect (sequence n) (observable n)
          (payoffIntegrable_of_bounded (sequence n) (observable n) (hbd n)) -
        expect target (observable n)
          (payoffIntegrable_of_bounded target (observable n) (hbd n))) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have habs : Tendsto (fun n =>
        |expect (sequence n) (observable n)
            (payoffIntegrable_of_bounded (sequence n) (observable n) (hbd n)) -
          expect target (observable n)
            (payoffIntegrable_of_bounded target (observable n) (hbd n))|)
        atTop (nhds 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) ?_ hgap
      intro n
      exact abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap
        (sequence n) target (observable n) (hbd n)
    simpa [Real.norm_eq_abs] using habs
  have htotal := hdelta.add hfixed
  simpa only [sub_add_cancel, zero_add] using htotal

private theorem pmf_bind_apply_toReal_eq_expect {α β : Type*}
    (μ : PMF α) (kernel : α → PMF β) (value : β)
    (h : PayoffIntegrable μ (fun source => (kernel source value).toReal)) :
    (μ.bind kernel value).toReal =
      expect μ (fun source => (kernel source value).toReal) h := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun source => ENNReal.mul_ne_top (μ.apply_ne_top source)
      ((kernel source).apply_ne_top value))]
  simp only [expect, ENNReal.toReal_mul]

/-- Pointwise PMF convergence is preserved by bind even when the source and
target carriers are infinite and the kernel varies with the sequence. -/
theorem PMFConvergesPointwise.bind {α β : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    {kernel : ℕ → α → PMF β} {targetKernel : α → PMF β}
    (hkernel : ∀ source,
      PMFConvergesPointwise (fun n => kernel n source) (targetKernel source)) :
    PMFConvergesPointwise (fun n => (sequence n).bind (kernel n))
      (target.bind targetKernel) := by
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro value
  have hbd : ∀ n source, |(kernel n source value).toReal| ≤ (1 : ℝ) := by
    intro n source
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      ((kernel n source).coe_le_one value)
  have houter := h.expect_varying_of_bounded
    (fun n source => (kernel n source value).toReal)
    (fun source => (targetKernel source value).toReal)
    hbd (fun source => (hkernel source).toReal value)
  simpa only [← pmf_bind_apply_toReal_eq_expect] using houter

/-- Pushforward preserves pointwise convergence on arbitrary carriers. -/
theorem PMFConvergesPointwise.map {α β : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target) (f : α → β) :
    PMFConvergesPointwise (fun n => (sequence n).map f) (target.map f) := by
  have hkernel : ∀ source : α,
      PMFConvergesPointwise (fun _ : ℕ => (PMF.pure (f source) : PMF β))
        (PMF.pure (f source)) := fun source => pmfConvergesPointwise_const _
  simpa [PMF.map, Function.comp_def] using
    h.bind (kernel := fun _ source => PMF.pure (f source))
      (targetKernel := fun source => PMF.pure (f source)) hkernel

/-- A finite independent product preserves pointwise convergence without
finite coordinate carriers. -/
theorem PMFConvergesPointwise.independentProduct {ι : Type*} [Fintype ι]
    {A : ι → Type*}
    {sequence : ℕ → ∀ i, PMF (A i)} {target : ∀ i, PMF (A i)}
    (h : ∀ i, PMFConvergesPointwise (fun n => sequence n i) (target i)) :
    PMFConvergesPointwise
      (fun n => independentProduct (sequence n)) (independentProduct target) := by
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro assignment
  simp only [independentProduct_apply, ENNReal.toReal_prod]
  exact tendsto_finsetProd Finset.univ fun i _ => (h i).toReal (assignment i)

/-- A vanishing mixture with a fixed PMF converges pointwise to its other
branch on any carrier. -/
theorem pmfConvergesPointwise_mix_zero {α : Type*}
    (weight : ℕ → ℝ) (h0 : ∀ n, 0 ≤ weight n) (h1 : ∀ n, weight n ≤ 1)
    (hweight : Tendsto weight atTop (nhds 0)) (first second : PMF α) :
    PMFConvergesPointwise
      (fun n => mix (weight n) (h0 n) (h1 n) first second) second := by
  intro value
  have hfirst : Tendsto (fun n => ENNReal.ofReal (weight n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hweight
  have hcomplement : Tendsto (fun n => ENNReal.ofReal (1 - weight n))
      atTop (nhds 1) := by
    have hsub : Tendsto (fun n => (1 : ℝ) - weight n) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hweight :
        Tendsto (fun n : ℕ => (1 : ℝ) - weight n) atTop (nhds (1 - 0)))
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hsub
  have hfirstTerm : Tendsto (fun n => ENNReal.ofReal (weight n) * first value)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((ENNReal.continuous_mul_const (first.apply_ne_top value)).tendsto 0).comp hfirst
  have hsecondTerm : Tendsto (fun n => ENNReal.ofReal (1 - weight n) * second value)
      atTop (nhds (second value)) := by
    simpa only [Function.comp_def, one_mul] using
      ((ENNReal.continuous_mul_const (second.apply_ne_top value)).tendsto 1).comp
        hcomplement
  have hsum := hfirstTerm.add hsecondTerm
  simpa only [mix_apply, zero_mul, one_mul, zero_add] using hsum

/-- Passing to a strictly increasing subsequence preserves pointwise mass
convergence. -/
theorem PMFConvergesPointwise.subseq {α : Type*}
    {sequence : ℕ → PMF α} {target : PMF α}
    (h : PMFConvergesPointwise sequence target)
    {subseq : ℕ → ℕ} (hsubseq : StrictMono subseq) :
    PMFConvergesPointwise (fun n => sequence (subseq n)) target :=
  fun value => (h value).comp hsubseq.tendsto_atTop

end GameTheory.Math.Probability
