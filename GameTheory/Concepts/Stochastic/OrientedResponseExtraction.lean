/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkObstruction
import Math.AlgebraicSelection

/-!
# Oriented extraction from analytic stochastic responses

After a common ramification, the Laurent--Puiseux data of a finite signed
response family are ordinary real-analytic germs. A positive total charge
then has one fixed edge carrying at least its average share. The signs of
the two factors on that edge stabilize together, and each oriented factor
has a power-law lower bound.

The orientation changes only the public coordinate score. The transition
used in the visible branch is always the given forward PMF. If the forward
and baseline PMFs coincide, the extracted charge is transition-invisible
and must be accounted for as a stage-payoff charge.

The signed flow-balance equation is deliberately absent: analytic extraction
uses only the positive total charge. Implementable circulation is a separate
question about the actual occupation cone.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability Set Topology

/-- The real sign encoded by the Boolean orientation used by the public
coordinate-monitor family. -/
def responseOrientation (positive : Bool) : ℝ :=
  if positive then 1 else -1

@[simp]
theorem responseOrientation_true : responseOrientation true = 1 := by
  rfl

@[simp]
theorem responseOrientation_false : responseOrientation false = -1 := by
  rfl

theorem responseOrientation_eq_one_or_neg_one (positive : Bool) :
    responseOrientation positive = 1 ∨
      responseOrientation positive = -1 := by
  cases positive <;> simp

/-- A fixed analytic member carries at least the average of any finite
analytic family, even when the other members have arbitrary signs. -/
theorem exists_fixed_analytic_average_charge
    {E : Type*} [Fintype E] [Nonempty E]
    (f : E → ℝ → ℝ)
    (hf : ∀ e, AnalyticAt ℝ (f e) 0) :
    ∃ e,
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (Fintype.card E : ℝ)⁻¹ * (∑ j, f j t) ≤ f e t := by
  obtain ⟨e, hmax⟩ :=
    finite_analytic_family_eventually_fixed_maximizer f hf
  refine ⟨e, ?_⟩
  have hcard : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast Fintype.card_pos
  filter_upwards [hmax] with t ht
  rw [inv_mul_le_iff₀ hcard]
  calc
    ∑ j, f j t ≤ ∑ _j : E, f e t :=
      Finset.sum_le_sum fun j _ => ht j
    _ = (Fintype.card E : ℝ) * f e t := by simp

/-- Analytic extraction of one fixed oriented response.

The exponent `L` and constant `kappa` work simultaneously for the absolute
weight and the oriented stage charge. The first inequality records the
stronger average-share conclusion for their product. -/
theorem exists_fixed_oriented_analytic_response
    {E : Type*} [Fintype E] [Nonempty E]
    (weight charge : E → ℝ → ℝ)
    (hweight : ∀ e, AnalyticAt ℝ (weight e) 0)
    (hcharge : ∀ e, AnalyticAt ℝ (charge e) 0)
    {C : ℝ} {K : ℕ} (hC : 0 < C)
    (htotal :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        C * t ^ K ≤ ∑ e, weight e t * charge e t) :
    ∃ e positive L kappa, 0 < kappa ∧
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) ≤
            weight e t * charge e t ∧
          kappa * t ^ L ≤ |weight e t| ∧
          kappa * t ^ L ≤
            responseOrientation positive * charge e t := by
  let term : E → ℝ → ℝ := fun e t => weight e t * charge e t
  have hterm : ∀ e, AnalyticAt ℝ (term e) 0 := by
    intro e
    exact (hweight e).mul (hcharge e)
  obtain ⟨e, havg⟩ :=
    exists_fixed_analytic_average_charge term hterm
  have hcard : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast Fintype.card_pos
  have hproduct :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) ≤
            weight e t * charge e t ∧
          0 < weight e t * charge e t := by
    filter_upwards [havg, htotal, self_mem_nhdsWithin] with t havg_t htotal_t ht
    have ht_pos : 0 < t := ht
    have hpow_pos : 0 < t ^ K := pow_pos ht_pos K
    have hscaled_pos :
        0 < (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) :=
      mul_pos (inv_pos.mpr hcard) (mul_pos hC hpow_pos)
    have hscaled :
        (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) ≤
          (Fintype.card E : ℝ)⁻¹ *
            (∑ j, weight j t * charge j t) :=
      mul_le_mul_of_nonneg_left htotal_t (inv_nonneg.mpr hcard.le)
    have hshare :
        (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) ≤
          weight e t * charge e t :=
      hscaled.trans havg_t
    exact ⟨hshare, hscaled_pos.trans_le hshare⟩
  rcases analyticAt_eventually_eq_or_lt_or_gt
      (hweight e) analyticAt_const with hzero | hnegative | hpositive
  · obtain ⟨t, htzero, htproduct⟩ := (hzero.and hproduct).exists
    rw [htzero, zero_mul] at htproduct
    exact False.elim (lt_irrefl 0 htproduct.2)
  · have hcharge_negative :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), charge e t < 0 := by
      filter_upwards [hnegative, hproduct] with t hw_t hp_t
      rcases (mul_pos_iff.mp hp_t.2) with hboth_pos | hboth_neg
      · exact False.elim ((not_lt_of_ge hboth_pos.1.le) hw_t)
      · exact hboth_neg.2
    have hweight_oriented :
        AnalyticAt ℝ (fun t => -weight e t) 0 :=
      (hweight e).neg
    have hcharge_oriented :
        AnalyticAt ℝ (fun t => -charge e t) 0 :=
      (hcharge e).neg
    have hweight_pos :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < -weight e t :=
      hnegative.mono fun _ ht => neg_pos.mpr ht
    have hcharge_pos :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < -charge e t :=
      hcharge_negative.mono fun _ ht => neg_pos.mpr ht
    obtain ⟨nw, cw, hcw, hw_power⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        hweight_oriented hweight_pos
    obtain ⟨nc, cc, hcc, hc_power⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        hcharge_oriented hcharge_pos
    let L := nw + nc
    let kappa := min cw cc
    have hkappa : 0 < kappa := lt_min hcw hcc
    refine ⟨e, false, L, kappa, hkappa, ?_⟩
    have hlt_one_nhds :
        ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 :=
      Iio_mem_nhds (by norm_num)
    have hlt_one :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < 1 := by
      exact hlt_one_nhds.filter_mono nhdsWithin_le_nhds
    filter_upwards [hproduct, hnegative, hw_power, hc_power,
      hlt_one, self_mem_nhdsWithin] with t hp_t hw_t hwp_t hcp_t ht_one ht
    have ht_nonneg : 0 ≤ t := ht.le
    have hLw : t ^ L ≤ t ^ nw := by
      exact pow_le_pow_of_le_one ht_nonneg ht_one.le
        (Nat.le_add_right nw nc)
    have hLc : t ^ L ≤ t ^ nc := by
      exact pow_le_pow_of_le_one ht_nonneg ht_one.le
        (Nat.le_add_left nc nw)
    have hkw : kappa * t ^ L ≤ cw * t ^ nw := by
      exact mul_le_mul (min_le_left _ _) hLw
        (pow_nonneg ht_nonneg _) hcw.le
    have hkc : kappa * t ^ L ≤ cc * t ^ nc := by
      exact mul_le_mul (min_le_right _ _) hLc
        (pow_nonneg ht_nonneg _) hcc.le
    have hwp_t' : cw * t ^ nw ≤ -weight e t := by
      simpa only [sub_zero] using hwp_t
    have hcp_t' : cc * t ^ nc ≤ -charge e t := by
      simpa only [sub_zero] using hcp_t
    refine ⟨hp_t.1, ?_, ?_⟩
    · rw [abs_of_neg hw_t]
      exact hkw.trans hwp_t'
    · simpa [responseOrientation] using hkc.trans hcp_t'
  · have hcharge_positive :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < charge e t := by
      filter_upwards [hpositive, hproduct] with t hw_t hp_t
      rcases (mul_pos_iff.mp hp_t.2) with hboth_pos | hboth_neg
      · exact hboth_pos.2
      · exact False.elim ((not_lt_of_ge hw_t.le) hboth_neg.1)
    obtain ⟨nw, cw, hcw, hw_power⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        (hweight e) hpositive
    obtain ⟨nc, cc, hcc, hc_power⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        (hcharge e) hcharge_positive
    let L := nw + nc
    let kappa := min cw cc
    have hkappa : 0 < kappa := lt_min hcw hcc
    refine ⟨e, true, L, kappa, hkappa, ?_⟩
    have hlt_one_nhds :
        ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 :=
      Iio_mem_nhds (by norm_num)
    have hlt_one :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < 1 := by
      exact hlt_one_nhds.filter_mono nhdsWithin_le_nhds
    filter_upwards [hproduct, hpositive, hw_power, hc_power,
      hlt_one, self_mem_nhdsWithin] with t hp_t hw_t hwp_t hcp_t ht_one ht
    have ht_nonneg : 0 ≤ t := ht.le
    have hLw : t ^ L ≤ t ^ nw := by
      exact pow_le_pow_of_le_one ht_nonneg ht_one.le
        (Nat.le_add_right nw nc)
    have hLc : t ^ L ≤ t ^ nc := by
      exact pow_le_pow_of_le_one ht_nonneg ht_one.le
        (Nat.le_add_left nc nw)
    have hkw : kappa * t ^ L ≤ cw * t ^ nw := by
      exact mul_le_mul (min_le_left _ _) hLw
        (pow_nonneg ht_nonneg _) hcw.le
    have hkc : kappa * t ^ L ≤ cc * t ^ nc := by
      exact mul_le_mul (min_le_right _ _) hLc
        (pow_nonneg ht_nonneg _) hcc.le
    have hwp_t' : cw * t ^ nw ≤ weight e t := by
      simpa only [sub_zero] using hwp_t
    have hcp_t' : cc * t ^ nc ≤ charge e t := by
      simpa only [sub_zero] using hcp_t
    refine ⟨hp_t.1, ?_, ?_⟩
    · rw [abs_of_pos hw_t]
      exact hkw.trans hwp_t'
    · simpa [responseOrientation] using hkc.trans hcp_t'

/-- A prescribed orientation detects some coordinate of any two distinct
finite PMFs. Both orientations work because the coordinate differences sum
to zero. -/
theorem exists_pmfCoordinateTestScore_pos_for_orientation
    {S : Type} [Fintype S] [DecidableEq S]
    (baseline comparison : PMF S) (positive : Bool)
    (hne : comparison ≠ baseline) :
    ∃ x,
      0 < expect comparison
        (pmfCoordinateTestScore baseline x positive) := by
  let difference : S → ℝ := fun x =>
    (comparison x).toReal - (baseline x).toReal
  have hsum : ∑ x, difference x = 0 := by
    simp [difference, Finset.sum_sub_distrib, pmf_toReal_sum_one]
  cases positive
  · have hex : ∃ x, difference x < 0 := by
      by_contra h
      have hnonnegative : ∀ x, 0 ≤ difference x := by
        intro x
        exact le_of_not_gt fun hx => h ⟨x, hx⟩
      have hzeroFun : difference = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg hnonnegative).mp hsum
      have hzero : ∀ x, difference x = 0 :=
        fun x => congrFun hzeroFun x
      apply hne
      apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
      intro x
      exact sub_eq_zero.mp (hzero x)
    obtain ⟨x, hx⟩ := hex
    refine ⟨x, ?_⟩
    rw [expect_pmfCoordinateTestScore]
    change 0 < (-1 : ℝ) * difference x
    linarith
  · have hex : ∃ x, 0 < difference x := by
      by_contra h
      have hnonpositive : ∀ x, difference x ≤ 0 := by
        intro x
        exact le_of_not_gt fun hx => h ⟨x, hx⟩
      have hzeroFun : difference = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonpos hnonpositive).mp hsum
      have hzero : ∀ x, difference x = 0 :=
        fun x => congrFun hzeroFun x
      apply hne
      apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
      intro x
      exact sub_eq_zero.mp (hzero x)
    obtain ⟨x, hx⟩ := hex
    refine ⟨x, ?_⟩
    rw [expect_pmfCoordinateTestScore]
    change 0 < (1 : ℝ) * difference x
    simpa using hx

/-- For a selected orientation and actual forward transition, either the
transition is invisible or one existing public coordinate score is centered
under the baseline and has positive drift under the forward transition. -/
theorem pmf_orientedResponse_visible_or_invisible
    {S : Type} [Fintype S] [DecidableEq S]
    (baseline forward : PMF S) (positive : Bool) :
    forward = baseline ∨
      ∃ x,
        expect baseline
            (pmfCoordinateTestScore baseline x positive) = 0 ∧
          0 < expect forward
            (pmfCoordinateTestScore baseline x positive) ∧
          ∀ y,
            |pmfCoordinateTestScore baseline x positive y| ≤ 1 := by
  by_cases hsame : forward = baseline
  · exact Or.inl hsame
  · right
    obtain ⟨x, hx⟩ :=
      exists_pmfCoordinateTestScore_pos_for_orientation
        baseline forward positive hsame
    exact ⟨x, expect_pmfCoordinateTestScore_baseline _ _ _, hx,
      abs_pmfCoordinateTestScore_le_one baseline x positive⟩

/-- Game-facing analytic extraction. The selected edge uses only its actual
forward transition; `positive` orients the monitor and never constructs a
reverse transition. -/
theorem exists_fixed_oriented_analytic_stochastic_response
    {S : Type} {E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [Nonempty E]
    (baseline : S → PMF S) (source : E → S) (forward : E → PMF S)
    (weight charge : E → ℝ → ℝ)
    (hweight : ∀ e, AnalyticAt ℝ (weight e) 0)
    (hcharge : ∀ e, AnalyticAt ℝ (charge e) 0)
    {C : ℝ} {K : ℕ} (hC : 0 < C)
    (htotal :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        C * t ^ K ≤ ∑ e, weight e t * charge e t) :
    ∃ e positive L kappa, 0 < kappa ∧
      (∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (Fintype.card E : ℝ)⁻¹ * (C * t ^ K) ≤
            weight e t * charge e t ∧
          kappa * t ^ L ≤ |weight e t| ∧
          kappa * t ^ L ≤
            responseOrientation positive * charge e t) ∧
      (forward e = baseline (source e) ∨
        ∃ x,
          expect (baseline (source e))
              (pmfCoordinateTestScore
                (baseline (source e)) x positive) = 0 ∧
            0 < expect (forward e)
              (pmfCoordinateTestScore
                (baseline (source e)) x positive) ∧
            ∀ y,
              |pmfCoordinateTestScore
                (baseline (source e)) x positive y| ≤ 1) := by
  obtain ⟨e, positive, L, kappa, hkappa, hextract⟩ :=
    exists_fixed_oriented_analytic_response
      weight charge hweight hcharge hC htotal
  exact ⟨e, positive, L, kappa, hkappa, hextract,
    pmf_orientedResponse_visible_or_invisible
      (baseline (source e)) (forward e) positive⟩

end StochasticGame
end GameTheory
