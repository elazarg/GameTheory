/-
# PMFs and probability measures

Mathlib provides `PMF.toMeasure` and the inverse `Measure.toPMF` on countable
measurable carriers. This file relates guarded real expectations and PMF
composition to those canonical measure constructions.
-/

import GameTheory.Math.Probability.Expectation
import GameTheory.Math.Probability.Product
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure

noncomputable section

namespace GameTheory.Math.Probability

open MeasureTheory ProbabilityTheory

universe u v

/-- A PMF measure is the countable sum of its positive singleton masses. -/
private theorem toMeasure_eq_sum_support {α : Type u}
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : PMF α) :
    μ.toMeasure =
      Measure.sum (fun a : μ.support => μ a • Measure.dirac a.val) := by
  let : Countable μ.support := μ.support_countable.to_subtype
  ext event hevent
  rw [Measure.sum_apply _ hevent, μ.toMeasure_apply_eq_tsum event]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hevent, smul_eq_mul]
  calc
    (∑' a, event.indicator μ a) =
        ∑' a, μ.support.indicator (event.indicator μ) a := by
      apply tsum_congr
      intro a
      by_cases ha : a ∈ μ.support
      · simp [ha]
      · have hzero : μ a = 0 := not_ne_iff.mp ha
        simp [hzero, ha]
    _ = ∑' a : μ.support, event.indicator μ a := by
      rw [tsum_subtype μ.support (fun a => event.indicator μ a)]
    _ = ∑' a : μ.support, μ a * event.indicator 1 a := by
      apply tsum_congr
      intro a
      by_cases ha : (a : α) ∈ event <;> simp [ha]

/-- The weighted absolute sum is precisely Bochner integrability for the
PMF's canonical measure; only its support must be countable. -/
theorem payoffIntegrable_iff_integrable {α : Type u}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (f : α → ℝ) :
    PayoffIntegrable μ f ↔ Integrable f μ.toMeasure := by
  let : Countable μ.support := μ.support_countable.to_subtype
  rw [toMeasure_eq_sum_support, integrable_sum_dirac_iff (f := f)
    (fun a : μ.support => μ.apply_ne_top a)]
  simp only [PayoffIntegrable, Real.norm_eq_abs]
  let weighted : α → ℝ := fun a => (μ a).toReal * |f a|
  have hsame : μ.support.indicator weighted = weighted := by
    funext a
    by_cases ha : a ∈ μ.support
    · simp [ha]
    · have hzero : μ a = 0 := not_ne_iff.mp ha
      simp [weighted, ha, hzero]
  exact (show Summable weighted ↔ Summable (weighted ∘ Subtype.val) from by
    rw [summable_subtype_iff_indicator, hsame]
  )

/-- A guarded expectation equals integration against the canonical PMF
measure. -/
theorem expect_eq_integral {α : Type u}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : PMF α) (f : α → ℝ) (h : PayoffIntegrable μ f) :
    expect μ f h = ∫ a, f a ∂μ.toMeasure := by
  rw [PMF.integral_eq_tsum μ f ((payoffIntegrable_iff_integrable μ f).1 h)]
  simp only [expect, smul_eq_mul]

/-- Reading a countable discrete probability measure as a PMF preserves the
mass of each measurable event. -/
theorem toPMF_event_mass {α : Type u}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {event : Set α} (hevent : MeasurableSet event) :
    μ.toPMF.toOuterMeasure event = μ event := by
  rw [← μ.toPMF.toMeasure_apply_eq_toOuterMeasure_apply hevent]
  simp

/-- An arbitrary function is almost everywhere measurable when the source
measure is concentrated on a countable set of measurable atoms. -/
theorem aemeasurable_of_countable_full_set {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [Nonempty β]
    (μ : Measure α) (f : α → β) (s : Set α)
    (hs : s.Countable) (hfull : μ sᶜ = 0) : AEMeasurable f μ := by
  classical
  let fallback : β := Classical.choice inferInstance
  let g : α → β := fun a => if a ∈ s then f a else fallback
  have hconst : Measurable (fun _ : α => fallback) := measurable_const
  have hsubset : {a | (fun _ : α => fallback) a ≠ g a} ⊆ s := by
    intro a ha
    by_contra hnot
    simp [g, hnot] at ha
  have hg : Measurable g :=
    hconst.measurable_of_countable_ne (hs.mono hsubset)
  have hmem : ∀ᵐ a ∂μ, a ∈ s := by
    filter_upwards [(compl_mem_ae_iff.mpr hfull)] with a ha
    simpa using ha
  apply hg.aemeasurable.congr
  filter_upwards [hmem] with a ha
  simp [g, ha]

/-- Two measures concentrated on one countable measurable set agree when
their singleton masses agree there. The ambient carrier need not be countable. -/
theorem measure_ext_of_countable_full_set {α : Type u}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) (s : Set α) (hs : s.Countable)
    (hμ : μ sᶜ = 0) (hν : ν sᶜ = 0)
    (hatom : ∀ a ∈ s, μ {a} = ν {a}) : μ = ν := by
  have hμae : s ∈ ae μ := (mem_ae_iff).2 hμ
  have hνae : s ∈ ae ν := (mem_ae_iff).2 hν
  ext event hevent
  let relevant := s ∩ event
  have hcount : relevant.Countable := hs.mono Set.inter_subset_left
  have hμsum : (∑' a : relevant, μ {a.1}) = μ relevant := by
    simpa using
      (tsum_measure_preimage_singleton (μ := μ) (f := id) hcount
        (fun a _ => measurableSet_singleton a))
  have hνsum : (∑' a : relevant, ν {a.1}) = ν relevant := by
    simpa using
      (tsum_measure_preimage_singleton (μ := ν) (f := id) hcount
        (fun a _ => measurableSet_singleton a))
  calc
    μ event = μ relevant := (μ.measure_inter_eq_of_ae hμae).symm
    _ = ∑' a : relevant, μ {a.1} := hμsum.symm
    _ = ∑' a : relevant, ν {a.1} := by
      apply tsum_congr
      intro a
      exact hatom a.1 a.2.1
    _ = ν relevant := hνsum
    _ = ν event := ν.measure_inter_eq_of_ae hνae

/-- A PMF supported in a selected set is the weighted sum of its Dirac
measures over that set. -/
private theorem toMeasure_eq_sum_of_support_subset {β : Type v}
    [MeasurableSpace β]
    (p : PMF β) (s : Set β) (hsupport : p.support ⊆ s) :
    p.toMeasure = Measure.sum (fun b : s => p b.1 • Measure.dirac b.1) := by
  ext event hevent
  rw [Measure.sum_apply _ hevent, p.toMeasure_apply hevent]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hevent, smul_eq_mul]
  calc
    (∑' b, event.indicator p b) =
        ∑' b, s.indicator (event.indicator p) b := by
      apply tsum_congr
      intro b
      by_cases hb : b ∈ s
      · simp [hb]
      · have hzero : p b = 0 := by
          by_contra hne
          exact hb (hsupport ((p.mem_support_iff b).mpr hne))
        simp [hb, hzero]
    _ = ∑' b : s, event.indicator p b := by
      rw [tsum_subtype s (fun b => event.indicator p b)]
    _ = ∑' b : s, p b.1 * event.indicator 1 b.1 := by
      apply tsum_congr
      intro b
      by_cases hb : (b : β) ∈ event <;> simp [hb]

/-- A PMF kernel with a common countable support is almost everywhere
measurable when each supported atom mass is almost everywhere measurable. -/
theorem aemeasurable_toMeasure_of_countable_support {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (source : Measure α) (next : α → PMF β) (s : Set β)
    (hcount : s.Countable)
    (hfull : ∀ᵐ a ∂source, (next a).support ⊆ s)
    (hpoint : ∀ b ∈ s, AEMeasurable (fun a => next a b) source) :
    AEMeasurable (fun a => (next a).toMeasure) source := by
  classical
  let : Countable s := hcount.to_subtype
  let mass (b : s) : α → ENNReal :=
    (hpoint b.1 b.2).mk (fun a => next a b.1)
  let kernel (a : α) : Measure β :=
    Measure.sum (fun b : s => mass b a • Measure.dirac b.1)
  have hmass (b : s) : Measurable (mass b) :=
    (hpoint b.1 b.2).measurable_mk
  have hkernel : Measurable kernel := by
    apply Measure.measurable_measure.mpr
    intro event hevent
    have hsum : ∀ a, kernel a event =
        ∑' b : s, mass b a * (Measure.dirac b.1) event := by
      intro a
      simp only [kernel, Measure.sum_apply _ hevent, Measure.smul_apply,
        smul_eq_mul]
    simp_rw [hsum]
    exact Measurable.tsum fun b => (hmass b).mul measurable_const
  have heq : ∀ᵐ a ∂source, ∀ b : s, mass b a = next a b.1 := by
    apply ae_all_iff.mpr
    intro b
    exact (hpoint b.1 b.2).ae_eq_mk.symm
  apply hkernel.aemeasurable.congr
  filter_upwards [hfull, heq] with a ha hb
  simp only [kernel]
  rw [toMeasure_eq_sum_of_support_subset (next a) s ha]
  congr 1
  funext b
  rw [hb b]

/-- Any measure-valued kernel is almost everywhere measurable under a PMF
measure: only the countably many supported source atoms matter. -/
theorem aemeasurable_toMeasure_kernel {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (μ : PMF α) (next : α → PMF β) :
    AEMeasurable (fun a => (next a).toMeasure) μ.toMeasure := by
  let : Countable μ.support := μ.support_countable.to_subtype
  rw [toMeasure_eq_sum_support, aemeasurable_sum_measure_iff]
  intro a
  exact (aemeasurable_smul_measure_iff a.2).2 aemeasurable_dirac

/-- Measure bind agrees with PMF bind for any kernel on a PMF source. -/
theorem toMeasure_bind {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (μ : PMF α) (next : α → PMF β) :
    Measure.bind μ.toMeasure (fun a => (next a).toMeasure) =
      (μ.bind next).toMeasure := by
  ext event hevent
  rw [Measure.bind_apply hevent (aemeasurable_toMeasure_kernel μ next)]
  rw [PMF.toMeasure_bind_apply (p := μ) (f := next) (s := event) hevent]
  conv_lhs => rw [← μ.restrict_toMeasure_support]
  rw [lintegral_countable _ μ.support_countable]
  rw [tsum_subtype μ.support
    (fun a => (next a).toMeasure event * μ.toMeasure {a})]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · simp [ha, PMF.toMeasure_apply_singleton μ a
      (measurableSet_singleton a), mul_comm]
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [ha, hzero]

/-- Filtering a PMF on a measurable positive-mass event is conditioning its
canonical measure on that event. -/
theorem toMeasure_filter {α : Type u}
    [MeasurableSpace α]
    (μ : PMF α) (event : Set α) (hevent : MeasurableSet event)
    (hmeet : ∃ a ∈ event, a ∈ μ.support) :
    (μ.filter event hmeet).toMeasure = cond μ.toMeasure event := by
  classical
  ext target htarget
  rw [PMF.toMeasure_apply (p := μ.filter event hmeet) htarget,
    cond_apply hevent, μ.toMeasure_apply (hevent.inter htarget),
    μ.toMeasure_apply hevent]
  simp only [Set.indicator_apply, PMF.filter_apply]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ event <;> by_cases ht : a ∈ target <;>
    simp [ha, ht, mul_comm]

/-- A measurable event meeting the PMF support has nonzero measure. -/
theorem toMeasure_event_ne_zero_of_meet {α : Type u}
    [MeasurableSpace α] (μ : PMF α) (event : Set α)
    (hevent : MeasurableSet event)
    (hmeet : ∃ a ∈ event, a ∈ μ.support) :
    μ.toMeasure event ≠ 0 := by
  intro hzero
  obtain ⟨a, ha, hsupport⟩ := hmeet
  exact (Set.disjoint_left.mp
    ((μ.toMeasure_apply_eq_zero_iff hevent).1 hzero)) hsupport ha

/-- Conditioning and then pushing forward through Mathlib's measure API
agrees with filtering and mapping the original PMF. Only the output carrier
must be countable to read an arbitrary probability measure back as a PMF. -/
theorem toPMF_map_cond_toMeasure {α : Type u} {β : Type v}
    [MeasurableSpace α]
    [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : PMF α) (event : Set α) (hevent : MeasurableSet event)
    (hmeet : ∃ a ∈ event, a ∈ μ.support)
    (f : α → β) (hf : Measurable f) :
    let conditioned := cond μ.toMeasure event
    letI : IsProbabilityMeasure conditioned :=
      cond_isProbabilityMeasure
        (toMeasure_event_ne_zero_of_meet μ event hevent hmeet)
    let pushed := conditioned.map f
    letI : IsProbabilityMeasure pushed := inferInstance
    pushed.toPMF = (μ.filter event hmeet).map f := by
  let conditioned := cond μ.toMeasure event
  let : IsProbabilityMeasure conditioned :=
    cond_isProbabilityMeasure
      (toMeasure_event_ne_zero_of_meet μ event hevent hmeet)
  let pushed := conditioned.map f
  let : IsProbabilityMeasure pushed := inferInstance
  have hmap : pushed = ((μ.filter event hmeet).map f).toMeasure := by
    dsimp [pushed, conditioned]
    rw [← toMeasure_filter μ event hevent hmeet]
    exact PMF.toMeasure_map (p := μ.filter event hmeet) (f := f) hf
  exact (show pushed.toPMF = (μ.filter event hmeet).map f from by
    apply PMF.ext
    intro b
    rw [Measure.toPMF_apply, hmap]
    exact PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b)
  )

/-- A finite independent PMF product has Mathlib's product measure. The
coordinate carriers may themselves be infinite. -/
theorem toMeasure_independentProduct {ι : Type u} [Fintype ι]
    {A : ι → Type v} [∀ i, MeasurableSpace (A i)]
    (μ : ∀ i, PMF (A i)) :
    (independentProduct μ).toMeasure = Measure.pi (fun i => (μ i).toMeasure) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (μ i).toMeasure) fun rectangle hrectangle => ?_).symm
  rw [PMF.toMeasure_apply (p := independentProduct μ)
    (MeasurableSet.univ_pi hrectangle)]
  have hfactor (assignment : ∀ i, A i) :
      (Set.pi Set.univ rectangle).indicator (independentProduct μ) assignment =
        ∏ i, (rectangle i).indicator (μ i) (assignment i) := by
    by_cases hall : ∀ i, assignment i ∈ rectangle i
    · have hmem : assignment ∈ Set.pi Set.univ rectangle :=
        fun i _ => hall i
      simp [hmem, hall, independentProduct_apply]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hnot : assignment ∉ Set.pi Set.univ rectangle := by
        intro hmem
        exact hi (hmem i (Set.mem_univ i))
      simp only [Set.indicator_of_notMem hnot]
      symm
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, Finset.mem_univ i,
        Set.indicator_of_notMem hi (μ i)⟩
  simp_rw [hfactor]
  rw [ENNReal_tsum_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact ((μ i).toMeasure_apply (hrectangle i)).symm

end GameTheory.Math.Probability
