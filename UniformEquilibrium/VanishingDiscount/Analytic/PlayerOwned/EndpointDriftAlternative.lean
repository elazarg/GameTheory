/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkPublicResponse
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedTargetTransportBoundary

/-!
# Analytic alternative for moving endpoint-value drift

For every player, source, and actual pure action, pair the moving transition
row with that player's endpoint value.  Finiteness and analyticity give one
common punctured neighborhood on which either all these drifts are
nonpositive, or one fixed owned action has positive drift with a power-law
margin.

The nonpositive branch is converted to one common calendar burn-in and feeds
`IsMovingPlayerOwnedEndpointSuperharmonic`.

A positive drift does not automatically give a public transition monitor.
The action row may have exactly the same analytic transition germ as the
prescribed baseline row.  The final theorem therefore records the exact
three-way alternative:

* moving endpoint superharmonicity after one common burn-in;
* one fixed actual owned action with positive endpoint drift and a fixed
  centered transition-coordinate monitor;
* one fixed actual owned action with positive endpoint drift whose transition
  germ is prescribed-indistinguishable.

The monitored branch orients only the public score, never the action.  No
branch is called a credible punishment.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.OnlineLearning Math.Probability Set Topology

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- One actual player-owned pure action, retaining its owner and source. -/
abbrev PlayerOwnedPureResponse (G : StochasticGame ι) :=
  Σ who : ι, G.State × G.Act who

/-- Raw moving drift of the selected owner's endpoint value under one actual
pure-action transition row. -/
def rawPlayerOwnedEndpointValueDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (response : PlayerOwnedPureResponse G) (t : ℝ) : ℝ :=
  (∑ destination,
      germ.rawPureDeviationStateKernelCurve
          t response.2.1 response.1 response.2.2 destination *
        germ.endpointValue destination response.1) -
    germ.endpointValue response.2.1 response.1

omit [DecidableEq G.State] in
/-- Every player-owned endpoint-value drift coordinate is analytic. -/
theorem analytic_rawPlayerOwnedEndpointValueDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (response : PlayerOwnedPureResponse G) :
    AnalyticAt ℝ
      (germ.rawPlayerOwnedEndpointValueDriftCurve response) 0 := by
  unfold rawPlayerOwnedEndpointValueDriftCurve
  exact
    (Finset.univ.analyticAt_fun_sum fun destination _ =>
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStateKernelCurve)
                response.2.1)) response.1)) response.2.2))
          destination).mul analyticAt_const).sub
      analyticAt_const

omit [DecidableEq G.State] in
/-- At a valid positive parameter, the raw drift is the semantic expected
endpoint-value increment of the same actual forward action. -/
theorem rawPlayerOwnedEndpointValueDriftCurve_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (response : PlayerOwnedPureResponse G)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.rawPlayerOwnedEndpointValueDriftCurve response t =
      expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.2.1 response.1 response.2.2)
          (fun destination =>
            germ.endpointValue destination response.1) -
        germ.endpointValue response.2.1 response.1 := by
  unfold rawPlayerOwnedEndpointValueDriftCurve
  rw [expect_eq_sum]
  apply sub_left_inj.mpr
  apply Finset.sum_congr rfl
  intro destination _
  rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht]

/-- A fixed actual owned action with positive moving endpoint-value drift and
a quantitative analytic margin. -/
structure AnalyticPositivePlayerOwnedEndpointDrift
    (germ : G.AnalyticBellmanGerm) where
  response : PlayerOwnedPureResponse G
  order : ℕ
  margin : ℝ
  margin_pos : 0 < margin
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        margin * t ^ order ≤
          germ.rawPlayerOwnedEndpointValueDriftCurve response t ∧
        0 <
          germ.rawPlayerOwnedEndpointValueDriftCurve response t

/-- One shared calendar burn-in on which every actual player-owned row is
superharmonic for its owner's endpoint value. -/
structure MovingPlayerOwnedEndpointSuperharmonicBurnIn
    (germ : G.AnalyticBellmanGerm) where
  startEpoch : ℕ
  valid :
    ∀ k : ℕ,
      shiftedUniversalEpochScale startEpoch k ∈
        Ioo (0 : ℝ) germ.radius
  superharmonic :
    FiniteBiasSeed.IsMovingPlayerOwnedEndpointSuperharmonic
      germ startEpoch valid

namespace MovingPlayerOwnedEndpointSuperharmonicBurnIn

/-- The superharmonic branch is not merely a label: it supplies the exact
zero-budget target-transport account consumed by the finite-bias payoff
bound, at every selected entry state. -/
def targetTransportAccount
    {germ : G.AnalyticBellmanGerm}
    (burnIn : MovingPlayerOwnedEndpointSuperharmonicBurnIn germ)
    (entry : G.State) :
    FiniteBiasSeed.PlayerOwnedCalendarEndpointTargetTransportAccount
      germ entry burnIn.startEpoch burnIn.valid :=
  FiniteBiasSeed.targetTransportAccountOfMovingSuperharmonic
    burnIn.superharmonic entry

end MovingPlayerOwnedEndpointSuperharmonicBurnIn

omit [DecidableEq G.State] in
private theorem eventually_nonpos_or_pos_playerOwnedEndpointDrift
    (germ : G.AnalyticBellmanGerm)
    (response : PlayerOwnedPureResponse G) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
        germ.rawPlayerOwnedEndpointValueDriftCurve response t ≤ 0) ∨
      (∀ᶠ t in nhdsWithin 0 (Ioi 0),
        0 < germ.rawPlayerOwnedEndpointValueDriftCurve response t) := by
  rcases
      analyticAt_eventually_eq_or_lt_or_gt
        (germ.analytic_rawPlayerOwnedEndpointValueDriftCurve response)
        analyticAt_const with
    zero | negative | positive
  · left
    filter_upwards [zero] with t ht
    rw [ht]
  · left
    exact negative.mono fun _ ht => ht.le
  · exact Or.inr positive

omit [DecidableEq G.State] in
/-- Finite analytic sign stabilization: either all actual endpoint-value
drifts are nonpositive on one punctured neighborhood, or one fixed actual
owned action has a positive power-law drift. -/
theorem
    eventually_allPlayerOwnedEndpointDrift_nonpos_or_positivePowerDrift
    (germ : G.AnalyticBellmanGerm) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ response : PlayerOwnedPureResponse G,
          germ.rawPlayerOwnedEndpointValueDriftCurve response t ≤ 0) ∨
      Nonempty (AnalyticPositivePlayerOwnedEndpointDrift germ) := by
  classical
  by_cases hpositive :
      ∃ response : PlayerOwnedPureResponse G,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          0 < germ.rawPlayerOwnedEndpointValueDriftCurve response t
  · right
    obtain ⟨response, response_pos⟩ := hpositive
    obtain ⟨order, margin, margin_pos, power⟩ :=
      analyticAt_eventually_const_mul_pow_le_of_eventually_pos
        (germ.analytic_rawPlayerOwnedEndpointValueDriftCurve response)
        response_pos
    exact ⟨{
      response := response
      order := order
      margin := margin
      margin_pos := margin_pos
      eventual := by
        filter_upwards
            [Ioo_mem_nhdsGT germ.radius_pos, power, response_pos] with
            t ht hpower hpos
        simpa only [sub_zero] using
          And.intro ht (And.intro hpower hpos) }⟩
  · left
    have nonpositive :
        ∀ response : PlayerOwnedPureResponse G,
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            germ.rawPlayerOwnedEndpointValueDriftCurve response t ≤ 0 := by
      intro response
      rcases
          eventually_nonpos_or_pos_playerOwnedEndpointDrift
            germ response with
        hnonpos | hpos
      · exact hnonpos
      · exact False.elim (hpositive ⟨response, hpos⟩)
    filter_upwards
        [Ioo_mem_nhdsGT germ.radius_pos,
          Filter.eventually_all.mpr nonpositive] with t ht hnonpos
    exact ⟨ht, hnonpos⟩

omit [DecidableEq G.State] in
/-- The nonpositive punctured-neighborhood branch supplies one common
calendar burn-in for `IsMovingPlayerOwnedEndpointSuperharmonic`. -/
theorem
    exists_movingPlayerOwnedEndpointSuperharmonicBurnIn_or_positivePowerDrift
    (germ : G.AnalyticBellmanGerm) :
    Nonempty (MovingPlayerOwnedEndpointSuperharmonicBurnIn germ) ∨
      Nonempty (AnalyticPositivePlayerOwnedEndpointDrift germ) := by
  classical
  rcases
      germ.eventually_allPlayerOwnedEndpointDrift_nonpos_or_positivePowerDrift
      with hnonpositive | hpositive
  · left
    have hscale :
        Tendsto universalEpochScale atTop
          (nhdsWithin 0 (Ioi (0 : ℝ))) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact
        ⟨tendsto_universalEpochScale,
          Filter.Eventually.of_forall universalEpochScale_pos⟩
    have hcalendar :
        ∀ᶠ k : ℕ in atTop,
          universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius ∧
            ∀ response : PlayerOwnedPureResponse G,
              germ.rawPlayerOwnedEndpointValueDriftCurve response
                  (universalEpochScale k) ≤ 0 :=
      hscale.eventually hnonpositive
    obtain ⟨startEpoch, hstart⟩ := eventually_atTop.1 hcalendar
    let valid :
        ∀ k : ℕ,
          shiftedUniversalEpochScale startEpoch k ∈
            Ioo (0 : ℝ) germ.radius :=
      fun k => (hstart (startEpoch + k) (by omega)).1
    refine ⟨{
      startEpoch := startEpoch
      valid := valid
      superharmonic := ?_ }⟩
    intro who k source action
    let response : PlayerOwnedPureResponse G :=
      ⟨who, source, action⟩
    have hrow_raw :=
      (hstart (startEpoch + k) (by omega)).2 response
    have hrow :
        germ.rawPlayerOwnedEndpointValueDriftCurve response
            (shiftedUniversalEpochScale startEpoch k) ≤ 0 := by
      simpa only [shiftedUniversalEpochScale] using hrow_raw
    have hsemantic :=
      germ.rawPlayerOwnedEndpointValueDriftCurve_eq_finkPointAt
        response (valid k)
    rw [hsemantic] at hrow
    have hle := sub_nonpos.mp hrow
    simpa only [
      finkOwnerActualOccupationKernelAt,
      ownerOccupationIndexEmbedding,
      finkActualOccupationKernelAt,
      Math.Probability.occupationKernel, response] using hle
  · exact Or.inr hpositive

/-- Positive endpoint drift carried by an actual owned action together with
a centered, fixed transition-coordinate monitor for that same action. -/
structure AnalyticPlayerOwnedEndpointDriftTransitionResponse
    (germ : G.AnalyticBellmanGerm) where
  positiveDrift : AnalyticPositivePlayerOwnedEndpointDrift germ
  transition :
    AnalyticFinkTransitionPublicResponse
      germ positiveDrift.response

/-- Exact obstruction to turning a positive endpoint drift into a centered
transition monitor: the same actual action row is analytically
indistinguishable from its prescribed baseline row. -/
structure AnalyticInvisiblePositivePlayerOwnedEndpointDrift
    (germ : G.AnalyticBellmanGerm) where
  positiveDrift : AnalyticPositivePlayerOwnedEndpointDrift germ
  same_kernel :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ destination,
        germ.rawPureDeviationStateKernelCurve
            t positiveDrift.response.2.1
              positiveDrift.response.1
              positiveDrift.response.2.2 destination =
          germ.rawStateKernelCurve
            t positiveDrift.response.2.1 destination

/-- Raw moving drift of the owner's endpoint value under the prescribed
baseline row at the selected source. -/
def rawPlayerOwnedEndpointBaselineDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (response : PlayerOwnedPureResponse G) (t : ℝ) : ℝ :=
  (∑ destination,
      germ.rawStateKernelCurve t response.2.1 destination *
        germ.endpointValue destination response.1) -
    germ.endpointValue response.2.1 response.1

namespace AnalyticInvisiblePositivePlayerOwnedEndpointDrift

omit [DecidableEq G.State] in
/-- In the invisible branch the positive actual drift is exactly the moving
prescribed baseline drift.  Hence no centered response-versus-baseline score
can witness it. -/
theorem eventual_drift_eq_baseline
    {germ : G.AnalyticBellmanGerm}
    (data : AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      germ.rawPlayerOwnedEndpointValueDriftCurve
          data.positiveDrift.response t =
        germ.rawPlayerOwnedEndpointBaselineDriftCurve
          data.positiveDrift.response t := by
  filter_upwards [data.same_kernel] with t ht
  unfold rawPlayerOwnedEndpointValueDriftCurve
    rawPlayerOwnedEndpointBaselineDriftCurve
  apply sub_left_inj.mpr
  apply Finset.sum_congr rfl
  intro destination _
  rw [ht destination]

end AnalyticInvisiblePositivePlayerOwnedEndpointDrift

omit [DecidableEq G.State] in
/-- A fixed positive endpoint-drift action either has an honest centered
transition monitor, or is prescribed-indistinguishable as an analytic
transition germ. -/
theorem
    AnalyticPositivePlayerOwnedEndpointDrift.toTransitionResponse_or_invisible
    {germ : G.AnalyticBellmanGerm}
    (positiveDrift : AnalyticPositivePlayerOwnedEndpointDrift germ) :
    Nonempty (AnalyticPlayerOwnedEndpointDriftTransitionResponse germ) ∨
      Nonempty (AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ) := by
  classical
  let response := positiveDrift.response
  let difference : G.State → ℝ → ℝ := fun destination t =>
    germ.rawPureDeviationStateKernelCurve
        t response.2.1 response.1 response.2.2 destination -
      germ.rawStateKernelCurve t response.2.1 destination
  have difference_analytic :
      ∀ destination, AnalyticAt ℝ (difference destination) 0 := by
    intro destination
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStateKernelCurve
              response.2.1) response.1) response.2.2)
        destination).sub
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelCurve response.2.1)
        destination)
  have difference_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∑ destination, difference destination t = 0 := by
    filter_upwards [Ioo_mem_nhdsGT germ.radius_pos] with t ht
    have pure_sum :=
      pmf_toReal_sum_one
        (G.finkPureDeviationStateKernel
          (germ.finkPointAt ht)
          response.2.1 response.1 response.2.2)
    have baseline_sum :=
      pmf_toReal_sum_one
        (G.finkStateKernel
          (germ.finkPointAt ht) response.2.1)
    simp_rw [difference, Finset.sum_sub_distrib]
    rw [show
        (∑ destination,
          germ.rawPureDeviationStateKernelCurve
            t response.2.1 response.1 response.2.2 destination) = 1 by
          simpa only [
            germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
              ht response.2.1 response.1 response.2.2] using pure_sum]
    rw [show
        (∑ destination,
          germ.rawStateKernelCurve
            t response.2.1 destination) = 1 by
          simpa only [
            germ.rawStateKernelCurve_eq_finkStateKernel
              ht response.2.1] using baseline_sum]
    exact sub_self 1
  by_cases same :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ destination, difference destination t = 0
  · right
    refine ⟨{
      positiveDrift := positiveDrift
      same_kernel := ?_ }⟩
    filter_upwards [same] with t ht
    intro destination
    have := ht destination
    simpa only [difference, sub_eq_zero] using this
  · left
    obtain ⟨destination, order, margin, margin_pos, signal⟩ :=
      exists_coordinate_powerCharge_of_analytic_zeroSum
        difference difference_analytic difference_sum same
    let monitor : PMFCoordinateMonitor G.State := (destination, true)
    refine ⟨{
      positiveDrift := positiveDrift
      transition := {
        monitor := monitor
        order := order
        margin := margin
        margin_pos := margin_pos
        eventual := ?_ } }⟩
    filter_upwards
        [Ioo_mem_nhdsGT germ.radius_pos, signal] with t ht hsignal
    simpa only [analyticFinkMonitorDrift, monitor,
      responseOrientation_true, one_mul, difference, response] using
        And.intro ht hsignal

omit [DecidableEq G.State] in
/-- Complete honest target-transport classification.  The third branch is
the exact reason the tempting two-way
`superharmonic ∨ centered public monitor` statement is false without an
additional baseline-drift hypothesis. -/
theorem
    exists_movingSuperharmonicBurnIn_or_endpointDriftResponse_or_invisible
    (germ : G.AnalyticBellmanGerm) :
    Nonempty (MovingPlayerOwnedEndpointSuperharmonicBurnIn germ) ∨
      Nonempty (AnalyticPlayerOwnedEndpointDriftTransitionResponse germ) ∨
        Nonempty
          (AnalyticInvisiblePositivePlayerOwnedEndpointDrift germ) := by
  rcases
      germ.exists_movingPlayerOwnedEndpointSuperharmonicBurnIn_or_positivePowerDrift
      with hsuper | hpositive
  · exact Or.inl hsuper
  · obtain ⟨positiveDrift⟩ := hpositive
    rcases positiveDrift.toTransitionResponse_or_invisible with
      hresponse | hinvisible
    · exact Or.inr (Or.inl hresponse)
    · exact Or.inr (Or.inr hinvisible)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
