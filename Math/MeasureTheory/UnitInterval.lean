/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# Unit-Interval Measure Helpers

Reusable measure-continuity facts for cuts of the unit interval.
-/

open MeasureTheory Set
open scoped unitInterval

namespace Math
namespace MeasureTheory

/-- Non-atomicity is preserved when a measure on the unit interval is pushed
forward along the subtype inclusion into `ℝ`. -/
instance noAtomsMapSubtypeVal (μ : Measure I) [NoAtoms μ] :
    NoAtoms (μ.map Subtype.val) where
  measure_singleton x := by
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
    exact Set.Subsingleton.measure_zero
      (by
        intro y hy z hz
        exact Subtype.ext (by simpa using hy.trans hz.symm))
      μ

/-- A non-atomic measure on the unit interval, pushed forward to `ℝ`, is
supported on `[0,1)`. The right endpoint can be removed because it is a
singleton. -/
theorem mapSubtypeVal_eq_restrict_Ico (μ : Measure I) [NoAtoms μ] :
    μ.map Subtype.val = (μ.map Subtype.val).restrict (Set.Ico 0 1) := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  rw [Measure.map_apply measurable_subtype_coe hs]
  rw [Measure.map_apply measurable_subtype_coe (hs.inter measurableSet_Ico)]
  exact (measure_eq_measure_of_null_sdiff Set.inter_subset_left <|
    measure_mono_null (μ := μ) (t := {(1 : I)}) (by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff]
        at hx ⊢
      apply Subtype.ext
      have hxnot_lt : ¬ (x : ℝ) < 1 := by
        intro hxlt
        exact hx.2 ⟨hx.1, unitInterval.nonneg x, hxlt⟩
      exact le_antisymm (unitInterval.le_one x) (le_of_not_gt hxnot_lt))
    (measure_singleton (1 : I))).symm

/-- The CDF `t ↦ (ν (Iic t)).toReal` is continuous for a non-atomic finite
measure on `ℝ`. -/
theorem cdfRealContinuous (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] :
    Continuous (fun t : ℝ => (ν (Set.Iic t)).toReal) := by
  have hf_mono : Monotone (fun t : ℝ => (ν (Set.Iic t)).toReal) := fun a b hab =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (measure_mono (Set.Iic_subset_Iic.mpr hab))
  have hf_right :
      ∀ a : ℝ,
        ContinuousWithinAt (fun t => (ν (Set.Iic t)).toReal) (Set.Ioi a) a := by
    intro a
    have htendsto : Filter.Tendsto (ν ∘ Set.Iic) (nhdsWithin a (Set.Ioi a))
        (nhds (ν (Set.Iic a))) := by
      have key := tendsto_measure_biInter_gt (μ := ν) (s := Set.Iic) (a := a)
        (fun _ _ => measurableSet_Iic.nullMeasurableSet)
        (fun _ _ _ h => Set.Iic_subset_Iic.mpr h)
        ⟨a + 1, by linarith, measure_ne_top _ _⟩
      have h_eq : (⋂ r > a, Set.Iic r) = Set.Iic a := by
        ext x
        simp only [mem_iInter, mem_Iic, gt_iff_lt]
        constructor
        · intro h
          by_contra hxa
          push Not at hxa
          linarith [h ((a + x) / 2) (by linarith)]
        · intro h r hr
          exact le_trans h hr.le
      rwa [h_eq] at key
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp htendsto
  have hf_left :
      ∀ a : ℝ,
        ContinuousWithinAt (fun t => (ν (Set.Iic t)).toReal) (Set.Iio a) a := by
    intro a
    rw [hf_mono.continuousWithinAt_Iio_iff_leftLim_eq]
    obtain ⟨u, hu_mono, hu_lt, hu_nhds⟩ := exists_seq_strictMono_tendsto_nhdsWithin a
    have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds a) :=
      hu_nhds.mono_right nhdsWithin_le_nhds
    have h_union : ⋃ n : ℕ, Set.Iic (u n) = Set.Iio a :=
      iUnion_Iic_eq_Iio_of_lt_of_tendsto hu_lt hu_tendsto
    have h_meas : Filter.Tendsto (fun n => ν (Set.Iic (u n))) Filter.atTop
        (nhds (ν (Set.Iio a))) := by
      have := tendsto_measure_iUnion_atTop (μ := ν)
        (fun m n hmn => Set.Iic_subset_Iic.mpr (hu_mono.monotone hmn))
      rwa [h_union] at this
    have h_leftLim :
        Function.leftLim (fun t => (ν (Set.Iic t)).toReal) a =
          (ν (Set.Iio a)).toReal :=
      tendsto_nhds_unique
        ((hf_mono.tendsto_leftLim a).comp hu_nhds)
        ((ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp h_meas)
    rw [h_leftLim, measure_congr Iio_ae_eq_Iic]
  exact continuous_iff_continuousAt.mpr fun a =>
    continuousAt_iff_continuous_left'_right'.mpr ⟨hf_left a, hf_right a⟩

/-- For a finite non-atomic measure on `ℝ`, the real value of `Ico l r` is
the positive part of the CDF difference. -/
theorem measure_Ico_toReal (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] (l r : ℝ) :
    (ν (Set.Ico l r)).toReal =
      max ((ν (Set.Iic r)).toReal - (ν (Set.Iic l)).toReal) 0 := by
  by_cases hlr : l ≤ r
  · have h_Ico_eq_Ioc : ν (Set.Ico l r) = ν (Set.Ioc l r) := by
      have h : ν.restrict (Set.Ico l r) = ν.restrict (Set.Ioc l r) :=
        restrict_Ico_eq_restrict_Ioc
      calc
        ν (Set.Ico l r) = ν.restrict (Set.Ico l r) Set.univ := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        _ = ν.restrict (Set.Ioc l r) Set.univ := by rw [h]
        _ = ν (Set.Ioc l r) := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hd : Disjoint (Set.Iic l) (Set.Ioc l r) :=
      Set.disjoint_left.mpr fun _ hxl hxr => absurd hxl (not_le.mpr hxr.1)
    have hu : Set.Iic l ∪ Set.Ioc l r = Set.Iic r := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact le_trans h hlr
        · exact h
      · intro h
        by_cases h' : x ≤ l
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.mp h', h⟩
    have h_sum : ν (Set.Iic r) = ν (Set.Iic l) + ν (Set.Ioc l r) := by
      rw [← hu]
      exact measure_union hd measurableSet_Ioc
    have h_sum_real : (ν (Set.Iic r)).toReal =
        (ν (Set.Iic l)).toReal + (ν (Set.Ioc l r)).toReal := by
      rw [h_sum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have hnn : 0 ≤ (ν (Set.Ioc l r)).toReal := ENNReal.toReal_nonneg
    rw [h_Ico_eq_Ioc, max_eq_left (by linarith)]
    linarith
  · push Not at hlr
    have hempty : Set.Ico l r = ∅ := Set.Ico_eq_empty (not_lt.mpr (le_of_lt hlr))
    have hle : (ν (Set.Iic r)).toReal ≤ (ν (Set.Iic l)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        (measure_mono (Set.Iic_subset_Iic.mpr (le_of_lt hlr)))
    simp only [hempty, measure_empty, ENNReal.toReal_zero]
    exact (max_eq_right (by linarith)).symm

private theorem map_Iic_eq (μ : Measure I) (t : I) :
    (μ.map Subtype.val) (Set.Iic (t : ℝ)) = μ (Set.Iic t) := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  rfl

private theorem map_univ_eq (μ : Measure I) :
    (μ.map Subtype.val) Set.univ = μ Set.univ := by
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp

private theorem cut_exists_real (μ : Measure ℝ) [IsFiniteMeasure μ] [NoAtoms μ]
    (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < (μ Set.univ).toReal) :
    ∃ t : ℝ, (μ (Set.Iic t)).toReal = c := by
  let f : ℝ → ℝ := fun t => (μ (Set.Iic t)).toReal
  set M := (μ Set.univ).toReal with hM_def
  have hf_top : Filter.Tendsto f Filter.atTop (nhds M) :=
    (ENNReal.continuousAt_toReal (measure_ne_top μ Set.univ)).tendsto.comp
      (tendsto_measure_Iic_atTop μ)
  have hf_bot : Filter.Tendsto f Filter.atBot (nhds 0) := by
    have h_conv : Filter.Tendsto (μ ∘ Set.Iic) Filter.atBot (nhds 0) := by
      have h0 : Filter.Tendsto (μ ∘ Set.Iic) Filter.atBot
          (nhds (μ (⋂ t : ℝ, Set.Iic t))) :=
        tendsto_measure_iInter_atBot
          (fun _ => measurableSet_Iic.nullMeasurableSet)
          (fun _ _ h => Set.Iic_subset_Iic.mpr h)
          ⟨0, measure_ne_top _ _⟩
      have h_empty : ⋂ t : ℝ, Set.Iic t = (∅ : Set ℝ) := by
        ext x
        simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
        exact fun h => absurd (h (x - 1)) (by linarith)
      simp only [h_empty, measure_empty] at h0
      exact h0
    simpa [f, Function.comp_def] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h_conv
  have hf_cont : Continuous f := cdfRealContinuous μ
  have h_low : ∃ a, f a ≤ c :=
    (hf_bot.eventually (Iio_mem_nhds hc_pos)).exists.imp fun _ ha => le_of_lt ha
  have h_high : ∃ b, c ≤ f b :=
    (hf_top.eventually (Ioi_mem_nhds hc_lt)).exists.imp fun _ hb => le_of_lt hb
  exact mem_range_of_exists_le_of_exists_ge hf_cont h_low h_high

/-- Intermediate value theorem for finite non-atomic measures on `[0,1]`: every
target strictly between `0` and the total mass is attained by an initial segment. -/
theorem unitInterval_cut_exists (μ : Measure I) [IsFiniteMeasure μ] [NoAtoms μ]
    (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < (μ Set.univ).toReal) :
    ∃ t : I, (μ (Set.Iic t)).toReal = c := by
  let ν : Measure ℝ := μ.map Subtype.val
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  haveI : NoAtoms ν := noAtomsMapSubtypeVal μ
  have hc_lt' : c < (ν Set.univ).toReal := by
    simpa [ν, map_univ_eq] using hc_lt
  obtain ⟨t, ht⟩ := cut_exists_real ν c hc_pos hc_lt'
  have ht_nonneg : 0 ≤ t := by
    by_contra ht_neg
    push Not at ht_neg
    have h_zero : ν (Set.Iic t) = 0 := by
      rw [show ν = μ.map Subtype.val by rfl, Measure.map_apply measurable_subtype_coe
        measurableSet_Iic]
      have hpre : Subtype.val ⁻¹' Set.Iic t = (∅ : Set I) := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_preimage, Set.mem_Iic] at hx
          linarith [unitInterval.nonneg x]
        · intro hx
          simp at hx
      rw [hpre, measure_empty]
    have : c = 0 := by
      rw [← ht, h_zero]
      simp
    linarith
  have ht_le_one : t ≤ 1 := by
    by_contra ht_gt
    push Not at ht_gt
    have h_full : ν (Set.Iic t) = ν Set.univ := by
      rw [show ν = μ.map Subtype.val by rfl, Measure.map_apply measurable_subtype_coe
        measurableSet_Iic]
      have hpre : Subtype.val ⁻¹' Set.Iic t = (Set.univ : Set I) := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          simp only [Set.mem_preimage, Set.mem_Iic]
          linarith [unitInterval.le_one x, ht_gt]
      rw [hpre]
      simpa [ν] using (map_univ_eq μ).symm
    have h_eq : c = (ν Set.univ).toReal := by
      rw [← ht, h_full]
    have : ¬ c < (ν Set.univ).toReal := by
      rw [h_eq]
      exact lt_irrefl ((ν Set.univ).toReal)
    exact this hc_lt'
  let tI : I := ⟨t, ⟨ht_nonneg, ht_le_one⟩⟩
  refine ⟨tI, ?_⟩
  rw [← map_Iic_eq μ tI]
  simpa [ν, tI] using ht

end MeasureTheory
end Math
