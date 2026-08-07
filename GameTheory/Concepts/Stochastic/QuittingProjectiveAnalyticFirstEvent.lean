/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAnalyticGerm
import Math.ProjectiveBellmanPacket

/-!
# Matching-order analytic first-event masses

This module extracts the projective *mass packet* of a matching-order analytic
quitting germ. Suppose the quit family has the same leading order as the
discount complement `t ^ g.ramification`, with nonnegative leading vector `a`
and `L = ∑ i, a i > 0`. Then the exact first-event denominator

`D(t) = t^q + (1 - t^q) * quittingGermAbsorption g t`

has leading coefficient `1 + L`. The normalized cemetery and singleton masses
therefore converge, without taking a subsequence, to

`z₀ = 1 / (1 + L)`,

`z_i = a i / (1 + L)`.

The residual normalized real-absorption mass after removing all singleton
packets tends to zero. This is the analytic mass-extraction part of the
projective singleton packet. It does not yet identify the limiting value as
the singleton reward mixture or pass endpoint complementarity to the limit;
those are separate game-facing steps needed to construct
`QuittingProjectiveSingletonPacket`.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact denominator of the discount/cemetery versus real-absorption first
event race along a quitting germ. -/
def quittingGermFirstEventDenominator
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) : ℝ :=
  t ^ g.ramification +
    (1 - t ^ g.ramification) * quittingGermAbsorption g t

/-- Normalized cemetery mass along a quitting germ. -/
def quittingGermCemeteryFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) : ℝ :=
  t ^ g.ramification / quittingGermFirstEventDenominator g t

/-- One-stage probability that exactly player `owner` quits, written directly
in the germ's real quit-rate coordinates. -/
def quittingGermSingletonProbability
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (owner : ι) (t : ℝ) : ℝ :=
  quittingGermQuitRate g owner t *
    ∏ other ∈ Finset.univ.erase owner,
      (1 - quittingGermQuitRate g other t)

/-- Normalized first-event weight of singleton quitter `owner`. -/
def quittingGermSingletonFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (owner : ι) (t : ℝ) : ℝ :=
  (1 - t ^ g.ramification) * quittingGermSingletonProbability g owner t /
    quittingGermFirstEventDenominator g t

/-- Normalized weight of all real absorption events. -/
def quittingGermRealAbsorptionFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) : ℝ :=
  (1 - t ^ g.ramification) * quittingGermAbsorption g t /
    quittingGermFirstEventDenominator g t

/-- Normalized real-absorption mass left after removing singleton packets. -/
def quittingGermNonsingletonFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) : ℝ :=
  quittingGermRealAbsorptionFirstEventWeight g t -
    ∑ owner, quittingGermSingletonFirstEventWeight g owner t

/-- Canonical data supplied by the existing leading-order normalization in the
matching regime. -/
structure QuittingGermMatchingLeadingData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm) where
  leading : ι → ℝ
  leading_nonneg : ∀ owner, 0 ≤ leading owner
  leading_sum_pos : 0 < ∑ owner, leading owner
  order_eq_ramification :
    Math.familyAnalyticOrder (quittingGermQuitRate g) = g.ramification
  eventually_total_pos :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ owner, quittingGermQuitRate g owner t
  share_tendsto : ∀ owner,
    Tendsto
      (fun t => quittingGermQuitRate g owner t /
        ∑ other, quittingGermQuitRate g other t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (leading owner / ∑ other, leading other))
  discount_div_total_tendsto :
    Tendsto
      (fun t : ℝ => t ^ g.ramification /
        ∑ owner, quittingGermQuitRate g owner t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / ∑ owner, leading owner))
  absorption_div_discount_tendsto :
    Tendsto
      (fun t : ℝ => quittingGermAbsorption g t / t ^ g.ramification)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ owner, leading owner))

/-- Existing analytic normalization constructs the canonical matching data
whenever the quit family's leading order equals the germ ramification. -/
theorem exists_quittingGermMatchingLeadingData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hne : ∃ owner,
      ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0)
    (hmatching :
      Math.familyAnalyticOrder (quittingGermQuitRate g) = g.ramification) :
    Nonempty (QuittingGermMatchingLeadingData reward g) := by
  obtain ⟨m, a, horder, hnonneg, hapos, -, htotal, hshare, -, hmatch, -⟩ :=
    exists_quittingGermQuitRate_leadingOrder_normalization g hne
  have hqm : g.ramification = m := by
    exact_mod_cast hmatching.symm.trans horder
  have hm : 1 ≤ m := by
    rw [← hqm]
    exact g.ramification_pos
  have hmatch' := hmatch hqm
  have habs :=
    (analyticOrderAt_quittingGermAbsorption_eq
      g hm horder htotal hapos (by simpa [hqm] using hmatch')).2.1
  refine ⟨{
    leading := a
    leading_nonneg := hnonneg
    leading_sum_pos := hapos
    order_eq_ramification := hmatching
    eventually_total_pos := htotal
    share_tendsto := hshare
    discount_div_total_tendsto := hmatch'
    absorption_div_discount_tendsto := ?_ }⟩
  simpa [hqm] using habs

namespace QuittingGermMatchingLeadingData

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {g : (quittingGame reward).AnalyticBellmanGerm}

/-- The discount-complement power tends to zero on the matching branch. -/
theorem discountComplement_tendsto_zero
    (_data : QuittingGermMatchingLeadingData reward g) :
    Tendsto (fun t : ℝ => t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hfull :
      Tendsto (fun t : ℝ => t ^ g.ramification)
        (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ g.ramification)) :=
    (continuousAt_id.pow g.ramification).tendsto
  have hright := hfull.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [zero_pow g.ramification_pos.ne'] using hright

/-- The total quit mass divided by the matching discount scale converges to
the total leading coefficient. -/
theorem total_div_discount_tendsto
    (data : QuittingGermMatchingLeadingData reward g) :
    Tendsto
      (fun t : ℝ => (∑ owner, quittingGermQuitRate g owner t) /
        t ^ g.ramification)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ owner, data.leading owner)) := by
  have h := data.discount_div_total_tendsto.inv₀
    (one_div_ne_zero data.leading_sum_pos.ne')
  simpa [inv_div] using h

/-- Every individual quit rate has the expected leading coefficient on the
matching discount scale. -/
theorem quitRate_div_discount_tendsto
    (data : QuittingGermMatchingLeadingData reward g) (owner : ι) :
    Tendsto
      (fun t : ℝ => quittingGermQuitRate g owner t /
        t ^ g.ramification)
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.leading owner)) := by
  have hmul := (data.share_tendsto owner).mul data.total_div_discount_tendsto
  have hlimit :
      (data.leading owner / ∑ other, data.leading other) *
          (∑ other, data.leading other) = data.leading owner := by
    field_simp [data.leading_sum_pos.ne']
  rw [hlimit] at hmul
  refine hmul.congr' ?_
  filter_upwards [data.eventually_total_pos, self_mem_nhdsWithin] with t htotal ht
  change 0 < t at ht
  have htne : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  have hsumne : (∑ other, quittingGermQuitRate g other t) ≠ 0 :=
    ne_of_gt htotal
  field_simp

/-- Every quit rate itself vanishes in the matching regime. -/
theorem quitRate_tendsto_zero
    (data : QuittingGermMatchingLeadingData reward g) (owner : ι) :
    Tendsto (quittingGermQuitRate g owner)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont := (analyticAt_quittingGermQuitRate g owner).continuousAt.tendsto
    |>.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [quittingGermQuitRate_zero_eq_zero g g.ramification_pos
    data.order_eq_ramification owner] using hcont

/-- The probability that all players other than `owner` continue tends to one. -/
theorem excludedContinueProduct_tendsto_one
    (data : QuittingGermMatchingLeadingData reward g) (owner : ι) :
    Tendsto
      (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
        (1 - quittingGermQuitRate g other t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hprod :
      Tendsto
        (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
          (1 - quittingGermQuitRate g other t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∏ _other ∈ Finset.univ.erase owner, (1 : ℝ))) :=
    tendsto_finsetProd (Finset.univ.erase owner)
      (fun other _ => by
        simpa using hone.sub (data.quitRate_tendsto_zero other))
  simpa using hprod

/-- A singleton quitting event has leading coefficient `a_owner`. -/
theorem singletonProbability_div_discount_tendsto
    (data : QuittingGermMatchingLeadingData reward g) (owner : ι) :
    Tendsto
      (fun t : ℝ => quittingGermSingletonProbability g owner t /
        t ^ g.ramification)
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.leading owner)) := by
  have hmul := (data.quitRate_div_discount_tendsto owner).mul
    (data.excludedContinueProduct_tendsto_one owner)
  have hmul' :
      Tendsto
        (fun t : ℝ =>
          (quittingGermQuitRate g owner t / t ^ g.ramification) *
            ∏ other ∈ Finset.univ.erase owner,
              (1 - quittingGermQuitRate g other t))
        (𝓝[>] (0 : ℝ)) (𝓝 (data.leading owner)) := by
    simpa using hmul
  refine hmul'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htne : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  unfold quittingGermSingletonProbability
  field_simp

/-- The first-event denominator has leading coefficient `1 + ∑ a`. -/
theorem firstEventDenominator_div_discount_tendsto
    (data : QuittingGermMatchingLeadingData reward g) :
    Tendsto
      (fun t : ℝ => quittingGermFirstEventDenominator g t /
        t ^ g.ramification)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 + ∑ owner, data.leading owner)) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hfactor := hone.sub data.discountComplement_tendsto_zero
  have hraw := hone.add
    (hfactor.mul data.absorption_div_discount_tendsto)
  have hraw' :
      Tendsto
        (fun t : ℝ =>
          1 + (1 - t ^ g.ramification) *
            (quittingGermAbsorption g t / t ^ g.ramification))
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 + ∑ owner, data.leading owner)) := by
    simpa using hraw
  refine hraw'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htne : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  unfold quittingGermFirstEventDenominator
  field_simp
  ring

/-- The normalized cemetery mass converges to `1 / (1 + ∑ a)`. -/
theorem cemeteryFirstEventWeight_tendsto
    (data : QuittingGermMatchingLeadingData reward g) :
    Tendsto (quittingGermCemeteryFirstEventWeight g)
      (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (1 + ∑ owner, data.leading owner))) := by
  have hdenomPos : 0 < 1 + ∑ owner, data.leading owner := by
    linarith [data.leading_sum_pos]
  have h := data.firstEventDenominator_div_discount_tendsto.inv₀
    hdenomPos.ne'
  change Tendsto
    (fun t : ℝ => t ^ g.ramification /
      quittingGermFirstEventDenominator g t)
    (𝓝[>] (0 : ℝ))
    (𝓝 (1 / (1 + ∑ owner, data.leading owner)))
  simpa [inv_div] using h

/-- The normalized singleton first-event mass converges to
`a_owner / (1 + ∑ a)`. -/
theorem singletonFirstEventWeight_tendsto
    (data : QuittingGermMatchingLeadingData reward g) (owner : ι) :
    Tendsto (quittingGermSingletonFirstEventWeight g owner)
      (𝓝[>] (0 : ℝ))
      (𝓝 (data.leading owner /
        (1 + ∑ other, data.leading other))) := by
  have hdenomPos : 0 < 1 + ∑ other, data.leading other := by
    linarith [data.leading_sum_pos]
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hnum := (hone.sub data.discountComplement_tendsto_zero).mul
    (data.singletonProbability_div_discount_tendsto owner)
  have hnum' :
      Tendsto
        (fun t : ℝ =>
          (1 - t ^ g.ramification) *
            (quittingGermSingletonProbability g owner t /
              t ^ g.ramification))
        (𝓝[>] (0 : ℝ)) (𝓝 (data.leading owner)) := by
    simpa using hnum
  have hinv := data.firstEventDenominator_div_discount_tendsto.inv₀
    hdenomPos.ne'
  have h := hnum'.mul hinv
  have hlimit :
      data.leading owner *
          (1 + ∑ other, data.leading other)⁻¹ =
        data.leading owner / (1 + ∑ other, data.leading other) := by
    rw [div_eq_mul_inv]
  rw [hlimit] at h
  change Tendsto
    (fun t : ℝ =>
      (1 - t ^ g.ramification) * quittingGermSingletonProbability g owner t /
        quittingGermFirstEventDenominator g t)
    (𝓝[>] (0 : ℝ))
    (𝓝 (data.leading owner /
      (1 + ∑ other, data.leading other)))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htne : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  field_simp

/-- The total normalized real-absorption mass converges to
`L / (1 + L)`. -/
theorem realAbsorptionFirstEventWeight_tendsto
    (data : QuittingGermMatchingLeadingData reward g) :
    Tendsto (quittingGermRealAbsorptionFirstEventWeight g)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ owner, data.leading owner) /
        (1 + ∑ owner, data.leading owner))) := by
  have hdenomPos : 0 < 1 + ∑ owner, data.leading owner := by
    linarith [data.leading_sum_pos]
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hnum := (hone.sub data.discountComplement_tendsto_zero).mul
    data.absorption_div_discount_tendsto
  have hnum' :
      Tendsto
        (fun t : ℝ =>
          (1 - t ^ g.ramification) *
            (quittingGermAbsorption g t / t ^ g.ramification))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ owner, data.leading owner)) := by
    simpa using hnum
  have hinv := data.firstEventDenominator_div_discount_tendsto.inv₀
    hdenomPos.ne'
  have h := hnum'.mul hinv
  have hlimit :
      (∑ owner, data.leading owner) *
          (1 + ∑ owner, data.leading owner)⁻¹ =
        (∑ owner, data.leading owner) /
          (1 + ∑ owner, data.leading owner) := by
    rw [div_eq_mul_inv]
  rw [hlimit] at h
  change Tendsto
    (fun t : ℝ =>
      (1 - t ^ g.ramification) * quittingGermAbsorption g t /
        quittingGermFirstEventDenominator g t)
    (𝓝[>] (0 : ℝ))
    (𝓝 ((∑ owner, data.leading owner) /
      (1 + ∑ owner, data.leading owner)))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have htne : t ^ g.ramification ≠ 0 :=
    pow_ne_zero _ (ne_of_gt ht)
  field_simp

/-- After removing all singleton packets, normalized real-absorption mass tends
to zero. -/
theorem nonsingletonFirstEventWeight_tendsto_zero
    (data : QuittingGermMatchingLeadingData reward g) :
    Tendsto (quittingGermNonsingletonFirstEventWeight g)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsingle :
      Tendsto
        (fun t : ℝ => ∑ owner,
          quittingGermSingletonFirstEventWeight g owner t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ owner,
          data.leading owner /
            (1 + ∑ other, data.leading other))) :=
    tendsto_finsetSum Finset.univ
      (fun owner _ => data.singletonFirstEventWeight_tendsto owner)
  have h := data.realAbsorptionFirstEventWeight_tendsto.sub hsingle
  have hsum :
      (∑ owner, data.leading owner /
        (1 + ∑ other, data.leading other)) =
      (∑ owner, data.leading owner) /
        (1 + ∑ other, data.leading other) := by
    rw [Finset.sum_div]
  rw [hsum, sub_self] at h
  change Tendsto
    (fun t : ℝ => quittingGermRealAbsorptionFirstEventWeight g t -
      ∑ owner, quittingGermSingletonFirstEventWeight g owner t)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  exact h

end QuittingGermMatchingLeadingData

end GameTheory
