/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkPublicResponse
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.OccupationAlternative

/-!
# Public responses extracted from player-owned analytic circulations

A positive charged circulation on the full operational family of one player
already contains an actual forward response.  The circulation masses are
nonnegative and the baseline columns have zero charge.  Hence one fixed pure
action carries a positive mass-charge product on a punctured neighborhood.
Its mass is nonnegative there, so the action's moving Bellman charge itself is
positive.

Analyticity gives a power-law charge margin.  The existing stage-or-transition
extraction then turns the same fixed action into an
`AnalyticForwardFinkPublicResponse`.

This is an operational one-step response theorem.  It does not assert that
the response is a credible punishment or that it transports a recurrent
continuation target.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A player-owned pure action whose circulation mass and moving
stage-plus-`B` continuation charge are both eventually positive. -/
structure EventuallyPositiveOwnedActionCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) where
  source : G.State
  action : G.Act who
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      0 < C.mass t (.inr (source, action)) ∧
        0 <
          germ.rawPlayerOwnedOccupationCharge B who t
            (.inr (source, action))

namespace EventuallyPositiveOwnedActionCharge

/-- The selected action has eventually positive circulation mass. -/
theorem eventual_mass_pos
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (selected :
      EventuallyPositiveOwnedActionCharge germ B who C) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      0 < C.mass t (.inr (selected.source, selected.action)) :=
  selected.eventual.mono fun _ ht => ht.1

/-- The selected action has eventually positive moving Bellman charge. -/
theorem eventual_charge_pos
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (selected :
      EventuallyPositiveOwnedActionCharge germ B who C) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      0 <
        germ.rawPlayerOwnedOccupationCharge B who t
          (.inr (selected.source, selected.action)) :=
  selected.eventual.mono fun _ ht => ht.2

/-- The selected owned action as the response index used by the public
response API. -/
def forwardResponse
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)}
    (selected :
      EventuallyPositiveOwnedActionCharge germ B who C) :
    Σ owner : ι, G.State × G.Act owner :=
  ⟨who, selected.source, selected.action⟩

end EventuallyPositiveOwnedActionCharge

/-- A public response tied to the positively occupied circulation action
from which it was constructed. -/
structure CirculationTiedAnalyticForwardFinkPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) where
  selected : EventuallyPositiveOwnedActionCharge germ B who C
  response : AnalyticForwardFinkPublicResponse germ B 0
  response_eq : response.response = selected.forwardResponse

/-- A positive analytic circulation freezes one actual action of the same
player whose moving Bellman charge is eventually positive. -/
theorem
    exists_eventuallyPositiveOwnedActionCharge_of_analyticCirculation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    Nonempty (EventuallyPositiveOwnedActionCharge germ B who C) := by
  classical
  cases isEmpty_or_nonempty (OwnerOccupationIndex G who) with
  | inl empty =>
      obtain ⟨t, hcirculation, ht⟩ :=
        (C.eventual.and self_mem_nhdsWithin).exists
      have positive : 0 < t ^ C.poleOrder :=
        pow_pos (mem_Ioi.mp ht) C.poleOrder
      have zero :
          (∑ index : OwnerOccupationIndex G who,
            C.mass t index *
              germ.rawPlayerOwnedOccupationCharge B who t index) = 0 := by
        simp
      rw [zero] at hcirculation
      exact False.elim ((ne_of_gt positive) hcirculation.2.2.symm)
  | inr nonempty =>
    letI : Nonempty (OwnerOccupationIndex G who) := nonempty
    let term : OwnerOccupationIndex G who → ℝ → ℝ := fun index t =>
      C.mass t index *
        germ.rawPlayerOwnedOccupationCharge B who t index
    have term_analytic :
        ∀ index, AnalyticAt ℝ (term index) 0 := by
      intro index
      exact
        (analyticAt_pi_iff.mp C.analytic_mass index).mul
          (germ.analytic_rawPlayerOwnedOccupationCharge B who index)
    obtain ⟨index, maximal⟩ :=
      exists_fixed_analytic_average_charge term term_analytic
    have card_pos :
        (0 : ℝ) < Fintype.card (OwnerOccupationIndex G who) := by
      exact_mod_cast Fintype.card_pos
    have term_pos :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < term index t := by
      filter_upwards [C.eventual, maximal, self_mem_nhdsWithin] with
          t hcirculation hmax ht
      have average_pos :
          0 <
            (Fintype.card (OwnerOccupationIndex G who) : ℝ)⁻¹ *
              ∑ other, term other t := by
        have weighted_charge :
            (∑ other, term other t) = t ^ C.poleOrder := by
          simpa only [term] using hcirculation.2.2
        rw [weighted_charge]
        exact mul_pos (inv_pos.mpr card_pos)
          (pow_pos (mem_Ioi.mp ht) C.poleOrder)
      exact average_pos.trans_le hmax
    cases index with
    | inl source =>
        obtain ⟨t, positive⟩ := term_pos.exists
        simp only [term, rawPlayerOwnedOccupationCharge, mul_zero] at positive
        exact False.elim ((lt_irrefl 0) positive)
    | inr response =>
        have mass_charge_pos :
            ∀ᶠ t in nhdsWithin 0 (Ioi 0),
              0 < C.mass t (.inr response) ∧
                0 <
                  germ.rawPlayerOwnedOccupationCharge B who t
                    (.inr response) := by
          filter_upwards [C.eventual, term_pos] with
              t hcirculation hterm
          have mass_nonneg : 0 ≤ C.mass t (.inr response) :=
            hcirculation.1 (.inr response)
          rcases mul_pos_iff.mp hterm with positive | negative
          · exact positive
          · exact False.elim ((not_lt_of_ge mass_nonneg) negative.1)
        exact ⟨{
          source := response.1
          action := response.2
          eventual := mass_charge_pos }⟩

/-- Any fixed owned action with eventually positive moving Bellman charge
defines one fixed analytic forward public response tied to the same
positively occupied circulation coordinate. -/
theorem
    EventuallyPositiveOwnedActionCharge.toCirculationTiedPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (circulation : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (selected :
      EventuallyPositiveOwnedActionCharge
        germ B who circulation) :
    Nonempty
      (CirculationTiedAnalyticForwardFinkPublicResponse
        germ B who circulation) := by
  classical
  let forward := selected.forwardResponse
  let supported :
      (Σ owner : ι, G.State × G.Act owner) → Bool :=
    fun _ => true
  let charge : ℝ → ℝ := fun t =>
    germ.rawFinkObstructionMass supported B 0 t (Sum.inr forward)
  have charge_eq :
      ∀ t,
        charge t =
          germ.rawPlayerOwnedOccupationCharge B who t
            (.inr (selected.source, selected.action)) := by
    intro t
    simp only [charge, AnalyticBellmanGerm.rawFinkObstructionMass,
      supported, if_true, forward,
      EventuallyPositiveOwnedActionCharge.forwardResponse,
      rawPlayerOwnedOccupationCharge, sub_zero]
  have charge_analytic : AnalyticAt ℝ charge 0 := by
    exact germ.analytic_rawFinkObstructionMass
      supported B 0 (Sum.inr forward)
  have charge_pos :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < charge t := by
    filter_upwards [selected.eventual_charge_pos] with t ht
    rw [charge_eq]
    exact ht
  obtain ⟨chargeOrder, chargeMargin, chargeMargin_pos, charge_power⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      charge_analytic charge_pos
  have eventual_charge :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          supported forward = true ∧
          chargeMargin * t ^ chargeOrder ≤
            germ.rawFinkObstructionMass supported B 0 t
              (Sum.inr forward) ∧
          0 <
            germ.rawFinkObstructionMass supported B 0 t
              (Sum.inr forward) := by
    filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
      charge_power, charge_pos] with t ht hpower hpos
    refine ⟨ht, ?_⟩
    refine ⟨show supported forward = true by rfl, ?_⟩
    refine ⟨?_, hpos⟩
    change chargeMargin * t ^ chargeOrder ≤ charge t
    simpa only [sub_zero] using hpower
  let stage : ℝ → ℝ := fun t =>
    germ.rawPureDeviationStageGainCurve
      t selected.source who selected.action
  let continuation : ℝ → ℝ := fun t =>
    germ.rawPureDeviationContinuationGainCurve
      B t selected.source who selected.action
  have stage_analytic : AnalyticAt ℝ stage 0 := by
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve
            selected.source) who) selected.action)
  have continuation_analytic : AnalyticAt ℝ continuation 0 := by
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (germ.analytic_rawPureDeviationContinuationGainCurve B)
            selected.source) who) selected.action)
  have total_power :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        chargeMargin * t ^ chargeOrder ≤
          stage t + continuation t := by
    filter_upwards [charge_power] with t ht
    rw [charge_eq] at ht
    simpa only [sub_zero, stage, continuation,
      rawPlayerOwnedOccupationCharge] using ht
  rcases analytic_sum_powerCharge_left_or_right
      stage_analytic continuation_analytic total_power with
    stage_power | continuation_power
  · have stage_eventual :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (chargeMargin / 2) * t ^ chargeOrder ≤ stage t ∧
            0 < stage t := by
      filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
        stage_power, self_mem_nhdsWithin] with t ht hpower htpos
      have lower_pos :
          0 < (chargeMargin / 2) * t ^ chargeOrder :=
        mul_pos (div_pos chargeMargin_pos (by norm_num))
          (pow_pos (mem_Ioi.mp htpos) chargeOrder)
      exact ⟨ht, hpower, lower_pos.trans_le hpower⟩
    exact ⟨{
      selected := selected
      response := {
        supported := supported
        response := forward
        chargeOrder := chargeOrder
        chargeMargin := chargeMargin
        chargeMargin_pos := chargeMargin_pos
        eventual_charge := eventual_charge
        branch := Sum.inl {
          order := chargeOrder
          margin := chargeMargin / 2
          margin_pos := div_pos chargeMargin_pos (by norm_num)
          eventual := by
            simpa only [stage, forward,
              EventuallyPositiveOwnedActionCharge.forwardResponse] using
              stage_eventual } }
      response_eq := rfl }⟩
  · have continuation_pos :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          0 < continuation t := by
      filter_upwards [continuation_power,
        self_mem_nhdsWithin] with t hpower htpos
      have lower_pos :
          0 < (chargeMargin / 2) * t ^ chargeOrder :=
        mul_pos (div_pos chargeMargin_pos (by norm_num))
          (pow_pos (mem_Ioi.mp htpos) chargeOrder)
      exact lower_pos.trans_le hpower
    let difference : G.State → ℝ → ℝ := fun destination t =>
      germ.rawPureDeviationStateKernelCurve
          t selected.source who selected.action destination -
        germ.rawStateKernelCurve t selected.source destination
    have difference_analytic :
        ∀ destination, AnalyticAt ℝ (difference destination) 0 := by
      intro destination
      exact
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStateKernelCurve
                selected.source) who) selected.action)
          destination).sub
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve selected.source)
          destination)
    have difference_sum :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∑ destination, difference destination t = 0 := by
      filter_upwards [Ioo_mem_nhdsGT germ.radius_pos] with t ht
      have pure_sum :=
        pmf_toReal_sum_one
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            selected.source who selected.action)
      have baseline_sum :=
        pmf_toReal_sum_one
          (G.finkStateKernel
            (germ.finkPointAt ht) selected.source)
      simp_rw [difference, Finset.sum_sub_distrib]
      rw [show
          (∑ destination,
            germ.rawPureDeviationStateKernelCurve
              t selected.source who selected.action destination) = 1 by
            simpa only [
              germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
                ht selected.source who selected.action] using pure_sum]
      rw [show
          (∑ destination,
            germ.rawStateKernelCurve
              t selected.source destination) = 1 by
            simpa only [
              germ.rawStateKernelCurve_eq_finkStateKernel
                ht selected.source] using baseline_sum]
      exact sub_self 1
    have difference_nonzero :
        ¬∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∀ destination, difference destination t = 0 := by
      intro zero
      obtain ⟨t, positive, zero_t⟩ :=
        (continuation_pos.and zero).exists
      have vanish : continuation t = 0 := by
        simp only [continuation,
          AnalyticBellmanGerm.rawPureDeviationContinuationGainCurve]
        apply Finset.sum_eq_zero
        intro destination _
        change difference destination t * (B destination who) = 0
        rw [zero_t destination, zero_mul]
      rw [vanish] at positive
      exact (lt_irrefl 0) positive
    obtain ⟨destination, monitorOrder, monitorMargin,
        monitorMargin_pos, monitor_power⟩ :=
      exists_coordinate_powerCharge_of_analytic_zeroSum
        difference difference_analytic difference_sum difference_nonzero
    let monitor : PMFCoordinateMonitor G.State := (destination, true)
    have monitor_eventual :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            monitorMargin * t ^ monitorOrder ≤
              analyticFinkMonitorDrift germ forward monitor t ∧
            0 <
              analyticFinkMonitorDrift germ forward monitor t := by
      filter_upwards [Ioo_mem_nhdsGT germ.radius_pos,
        monitor_power] with t ht hpower
      simpa only [analyticFinkMonitorDrift, monitor,
        responseOrientation_true, one_mul, difference, forward,
        EventuallyPositiveOwnedActionCharge.forwardResponse] using
          And.intro ht hpower
    exact ⟨{
      selected := selected
      response := {
        supported := supported
        response := forward
        chargeOrder := chargeOrder
        chargeMargin := chargeMargin
        chargeMargin_pos := chargeMargin_pos
        eventual_charge := eventual_charge
        branch := Sum.inr {
          monitor := monitor
          order := monitorOrder
          margin := monitorMargin
          margin_pos := monitorMargin_pos
          eventual := monitor_eventual } }
      response_eq := rfl }⟩

/-- Forgetting circulation provenance recovers the response-only API. -/
theorem
    EventuallyPositiveOwnedActionCharge.toAnalyticForwardFinkPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (circulation : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who))
    (selected :
      EventuallyPositiveOwnedActionCharge
        germ B who circulation) :
    Nonempty (AnalyticForwardFinkPublicResponse germ B 0) := by
  obtain ⟨tied⟩ :=
    EventuallyPositiveOwnedActionCharge.toCirculationTiedPublicResponse
      germ B who circulation selected
  exact ⟨tied.response⟩

/-- Every positive analytic circulation yields a fixed forward response
tied to an action with eventually positive circulation mass and charge. -/
theorem
    exists_circulationTiedAnalyticForwardFinkPublicResponse
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    Nonempty
      (CirculationTiedAnalyticForwardFinkPublicResponse
        germ B who C) := by
  obtain ⟨selected⟩ :=
    exists_eventuallyPositiveOwnedActionCharge_of_analyticCirculation
      germ B who C
  exact
    EventuallyPositiveOwnedActionCharge.toCirculationTiedPublicResponse
      germ B who C selected

/-- Every positive analytic circulation on a player's full operational family
produces one fixed actual forward public response owned by that player. -/
theorem
    exists_playerOwnedAnalyticForwardFinkPublicResponse_of_analyticCirculation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (C : AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge B who)) :
    Nonempty (AnalyticForwardFinkPublicResponse germ B 0) := by
  obtain ⟨tied⟩ :=
    exists_circulationTiedAnalyticForwardFinkPublicResponse
      germ B who C
  exact ⟨tied.response⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
