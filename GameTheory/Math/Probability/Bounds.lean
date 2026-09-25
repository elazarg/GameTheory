/-
# Probability bounds for ordinary PMFs

Real-valued expectations carry integrability certificates. Event mass is the
canonical PMF outer-measure value, converted to a real only when compared with
an expected payoff.
-/

import GameTheory.Math.Probability.ExpectationAlgebra

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

open Classical in
/-- The expectation of an event indicator is its real probability mass. -/
theorem expect_indicator {α : Type*} (μ : PMF α) (event : Set α)
    (h : PayoffIntegrable μ (fun value => if value ∈ event then (1 : ℝ) else 0)) :
    expect μ (fun value => if value ∈ event then (1 : ℝ) else 0) h =
      (μ.toOuterMeasure event).toReal := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq (fun value => by
    by_cases hevent : value ∈ event
    · simpa [Set.indicator, hevent] using μ.apply_ne_top value
    · simp [Set.indicator, hevent])]
  unfold expect
  apply tsum_congr
  intro value
  by_cases hevent : value ∈ event <;> simp [Set.indicator, hevent]

/-- A pointwise discrepancy confined to an event costs at most its size times
the event probability. -/
theorem expect_le_add_event_gap {α : Type*}
    (μ : PMF α) (event : Set α)
    (source target : α → ℝ) (gap : ℝ)
    (hsource : PayoffIntegrable μ source)
    (htarget : PayoffIntegrable μ target)
    (houtside : ∀ value ∈ μ.support, value ∉ event → target value ≤ source value)
    (hinside : ∀ value ∈ μ.support, value ∈ event →
      target value ≤ source value + gap) :
    expect μ target htarget ≤ expect μ source hsource +
      gap * (μ.toOuterMeasure event).toReal := by
  classical
  let indicator : α → ℝ := fun value => if value ∈ event then 1 else 0
  have hindBound : ∀ value, |indicator value| ≤ 1 := by
    intro value
    by_cases hevent : value ∈ event <;> simp [indicator, hevent]
  have hind : PayoffIntegrable μ indicator :=
    payoffIntegrable_of_bounded μ indicator hindBound
  have hgap : PayoffIntegrable μ (fun value => gap * indicator value) :=
    payoffIntegrable_const_mul hind
  have hsum : PayoffIntegrable μ (fun value => source value + gap * indicator value) :=
    payoffIntegrable_add hsource hgap
  have hpointwise : expect μ target htarget ≤
      expect μ (fun value => source value + gap * indicator value) hsum := by
    apply expect_mono
    intro value hsupport
    by_cases hevent : value ∈ event
    · simpa [indicator, hevent] using hinside value hsupport hevent
    · simpa [indicator, hevent] using houtside value hsupport hevent
  rw [expect_add hsource hgap, expect_const_mul hind] at hpointwise
  have hindvalue : expect μ indicator hind = (μ.toOuterMeasure event).toReal :=
    expect_indicator μ event hind
  rw [hindvalue] at hpointwise
  exact hpointwise

open Classical in
/-- Partition an integrable expectation into the (possibly infinite) fibers
of an observation map. -/
theorem expect_eq_tsum_fibers {α β : Type*}
    (μ : PMF α) (information : α → β) (u : α → ℝ)
    (h : PayoffIntegrable μ u) :
    expect μ u h = ∑' observed : β,
      expect μ (fun value => if value ∈ information ⁻¹' {observed} then u value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) h) := by
  classical
  have hsigned : Summable (fun value : α => (μ value).toReal * u value) := by
    have hnorm : Summable (fun value : α => ‖(μ value).toReal * u value‖) := by
      simpa [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg] using h
    exact hnorm.of_norm
  have hpartition := hsigned.hasSum.tsum_fiberwise information
  rw [expect]
  refine (hpartition.tsum_eq).symm.trans ?_
  apply tsum_congr
  intro observed
  rw [tsum_subtype (information ⁻¹' {observed})
    (fun value => (μ value).toReal * u value)]
  unfold expect
  apply tsum_congr
  intro value
  by_cases hvalue : information value = observed <;>
    simp [Set.indicator, hvalue]

open Classical in
/-- Comparison on each supported information fiber implies comparison of
global expectations. The observation carrier may be infinite. -/
theorem expect_le_of_fiber_expect_le {α β : Type*}
    (μ : PMF α) (information : α → β) (source target : α → ℝ)
    (hsource : PayoffIntegrable μ source)
    (htarget : PayoffIntegrable μ target)
    (hfiber : ∀ observed ∈ (μ.map information).support,
      expect μ (fun value =>
        if value ∈ information ⁻¹' {observed} then target value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) htarget) ≤
      expect μ (fun value =>
        if value ∈ information ⁻¹' {observed} then source value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) hsource)) :
    expect μ target htarget ≤ expect μ source hsource := by
  rw [expect_eq_tsum_fibers μ information target htarget,
    expect_eq_tsum_fibers μ information source hsource]
  have hzero (u : α → ℝ) (hu : PayoffIntegrable μ u)
      (observed : β) (hnotsupport : observed ∉ (μ.map information).support) :
      expect μ (fun value => if value ∈ information ⁻¹' {observed} then u value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) hu) = 0 := by
    classical
    have heq : ∀ value ∈ μ.support,
        (if value ∈ information ⁻¹' {observed} then u value else 0) = 0 := by
      intro value hvalue
      have hne : information value ≠ observed := by
        intro hequal
        apply hnotsupport
        exact (PMF.mem_support_map_iff information μ observed).2
          ⟨value, hvalue, hequal⟩
      simp [Set.mem_preimage, Set.mem_singleton_iff, hne]
    have hcongr := expect_congr_on_support heq
      (payoffIntegrable_indicator (information ⁻¹' {observed}) hu)
      (payoffIntegrable_zero μ)
    simpa only [expect_zero] using hcongr
  have htargetSum : Summable (fun observed : β =>
      expect μ (fun value => if value ∈ information ⁻¹' {observed} then target value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) htarget)) := by
    have hsigned : Summable (fun value : α => (μ value).toReal * target value) := by
      have hnorm : Summable (fun value : α => ‖(μ value).toReal * target value‖) := by
        simpa [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg] using htarget
      exact hnorm.of_norm
    have hpart := hsigned.hasSum.tsum_fiberwise information
    convert hpart.summable using 1
    funext observed
    rw [tsum_subtype (information ⁻¹' {observed})
      (fun value => (μ value).toReal * target value)]
    simp only [expect]
    apply tsum_congr
    intro value
    by_cases hv : information value = observed <;> simp [Set.indicator, hv]
  have hsourceSum : Summable (fun observed : β =>
      expect μ (fun value => if value ∈ information ⁻¹' {observed} then source value else 0)
        (payoffIntegrable_indicator (information ⁻¹' {observed}) hsource)) := by
    have hsigned : Summable (fun value : α => (μ value).toReal * source value) := by
      have hnorm : Summable (fun value : α => ‖(μ value).toReal * source value‖) := by
        simpa [PayoffIntegrable, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ENNReal.toReal_nonneg] using hsource
      exact hnorm.of_norm
    have hpart := hsigned.hasSum.tsum_fiberwise information
    convert hpart.summable using 1
    funext observed
    rw [tsum_subtype (information ⁻¹' {observed})
      (fun value => (μ value).toReal * source value)]
    simp only [expect]
    apply tsum_congr
    intro value
    by_cases hv : information value = observed <;> simp [Set.indicator, hv]
  exact htargetSum.tsum_le_tsum (fun observed => by
    by_cases hs : observed ∈ (μ.map information).support
    · exact hfiber observed hs
    · rw [hzero target htarget observed hs, hzero source hsource observed hs])
    hsourceSum

/-- A nonnegative observable that exceeds a positive threshold on an event
bounds that event's probability by its expectation divided by the threshold. -/
theorem eventMass_toReal_le_expect_div {α : Type*}
    (μ : PMF α) (event : Set α) (observable : α → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hobs : PayoffIntegrable μ observable)
    (hnonnegative : ∀ value ∈ μ.support, 0 ≤ observable value)
    (hlower : ∀ value ∈ μ.support, value ∈ event → threshold ≤ observable value) :
    (μ.toOuterMeasure event).toReal ≤ expect μ observable hobs / threshold := by
  classical
  let indicator : α → ℝ := fun value => if value ∈ event then 1 else 0
  have hindBound : ∀ value, |indicator value| ≤ 1 := by
    intro value
    by_cases hevent : value ∈ event <;> simp [indicator, hevent]
  have hind : PayoffIntegrable μ indicator :=
    payoffIntegrable_of_bounded μ indicator hindBound
  have hscaled : PayoffIntegrable μ (fun value => threshold * indicator value) :=
    payoffIntegrable_const_mul hind
  have hpointwise : expect μ (fun value => threshold * indicator value) hscaled ≤
      expect μ observable hobs := by
    apply expect_mono
    intro value hsupport
    by_cases hevent : value ∈ event
    · simpa [indicator, hevent] using hlower value hsupport hevent
    · simpa [indicator, hevent] using hnonnegative value hsupport
  rw [expect_const_mul hind] at hpointwise
  have hmass : expect μ indicator hind = (μ.toOuterMeasure event).toReal :=
    expect_indicator μ event hind
  rw [hmass] at hpointwise
  exact (le_div_iff₀ hthreshold).2 (by simpa [mul_comm] using hpointwise)

/-- Markov's inequality for a supported nonnegative observable. -/
theorem markov_inequality {α : Type*} (μ : PMF α) (observable : α → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hobs : PayoffIntegrable μ observable)
    (hnonnegative : ∀ value ∈ μ.support, 0 ≤ observable value) :
    (μ.toOuterMeasure {value | threshold ≤ observable value}).toReal ≤
      expect μ observable hobs / threshold :=
  eventMass_toReal_le_expect_div μ _ observable hthreshold hobs hnonnegative
    (fun _ _ hlower => hlower)

end GameTheory.Math.Probability
