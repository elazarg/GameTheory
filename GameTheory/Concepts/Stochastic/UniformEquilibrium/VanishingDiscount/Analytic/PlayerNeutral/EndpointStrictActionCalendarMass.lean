/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BehaviorCalendarDeviationAccount

/-!
# Endpoint-strict action mass on the analytic Fink calendar

Fix a player and let `W` be the endpoint continuation value.  Endpoint
excessiveness splits the player's finite pure-action family into neutral
actions and actions with a uniform strict negative gap.  Along the analytic
Fink germ, the errors in these continuation gains and the prescribed
`W`-residual both vanish uniformly over the finite state/action family.

For an arbitrary unilateral behavior strategy against the shifted universal
Fink schedule, the actual one-step `W` drift is the prescribed residual plus
the strategy's average moving continuation gain.  Telescoping this identity
under the strategy's own full public-history law bounds cumulative expected
endpoint-strict action mass by a bounded endpoint bill plus the sums of the
two vanishing envelopes.  The resulting bound is sublinear at every horizon.

This is an action-mass account only.  It does not replace strict actions by a
shadow transition and makes no payoff-cap or punishment claim.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.PMFProduct Math.Probability Set Topology
open Math.OnlineLearning

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Finite set of strictly negative endpoint continuation gains of one
player. -/
def endpointStrictGainValues
    (germ : G.AnalyticBellmanGerm) (who : ι) : Finset ℝ :=
  ((Finset.univ : Finset (G.State × G.Act who)).image
      (fun pair =>
        G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint pair.1 who pair.2)).filter
    (fun gain => gain < 0)

omit [DecidableEq G.State] in
/-- Finiteness supplies a positive gap below zero, with the assertion
vacuous when the player has no endpoint-strict action. -/
theorem exists_endpointStrictGap
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ source action,
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action < 0 →
          G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ≤ -gap := by
  classical
  by_cases empty : germ.endpointStrictGainValues who = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro source action strict
    exfalso
    have member :
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action ∈
          germ.endpointStrictGainValues who := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, strict⟩
      exact Finset.mem_image.mpr
        ⟨(source, action), Finset.mem_univ _, rfl⟩
    rw [empty] at member
    simp at member
  · have nonempty :
        (germ.endpointStrictGainValues who).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr empty
    let largest := (germ.endpointStrictGainValues who).max' nonempty
    refine ⟨-largest, ?_, ?_⟩
    · have largest_mem :
          largest ∈ germ.endpointStrictGainValues who :=
        Finset.max'_mem _ _
      have largest_neg : largest < 0 :=
        (Finset.mem_filter.mp largest_mem).2
      linarith
    · intro source action strict
      have member :
          G.finkContinuationGain germ.endpointValue
              germ.endpointFinkPoint source who action ∈
            germ.endpointStrictGainValues who := by
        apply Finset.mem_filter.mpr
        refine ⟨?_, strict⟩
        exact Finset.mem_image.mpr
          ⟨(source, action), Finset.mem_univ _, rfl⟩
      have below :=
        Finset.le_max' (germ.endpointStrictGainValues who) _ member
      simpa only [neg_neg, largest] using below

/-- A canonical positive endpoint-strict gap. -/
def endpointStrictGap
    (germ : G.AnalyticBellmanGerm) (who : ι) : ℝ :=
  Classical.choose (germ.exists_endpointStrictGap who)

omit [DecidableEq G.State] in
theorem endpointStrictGap_pos
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    0 < germ.endpointStrictGap who :=
  (Classical.choose_spec (germ.exists_endpointStrictGap who)).1

omit [DecidableEq G.State] in
theorem endpointContinuationGain_le_neg_strictGap
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (source : G.State) (action : G.Act who)
    (strict :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action < 0) :
    G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action ≤
      -germ.endpointStrictGap who :=
  (Classical.choose_spec
    (germ.exists_endpointStrictGap who)).2 source action strict

/-- Uniform absolute error between moving and endpoint pure-deviation
continuation gains. -/
def endpointMovingGainErrorEnvelope
    (germ : G.AnalyticBellmanGerm) (who : ι) (t : ℝ) : ℝ :=
  ∑ pair : G.State × G.Act who,
    |germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t pair.1 who pair.2 -
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint pair.1 who pair.2|

/-- Raw prescribed-kernel residual of the endpoint value. -/
def rawEndpointValueBaselineResidual
    (germ : G.AnalyticBellmanGerm)
    (t : ℝ) (source : G.State) (who : ι) : ℝ :=
  (∑ destination,
      germ.rawStateKernelCurve t source destination *
        germ.endpointValue destination who) -
    germ.endpointValue source who

/-- Uniform absolute prescribed-kernel residual envelope. -/
def endpointBaselineResidualEnvelope
    (germ : G.AnalyticBellmanGerm) (who : ι) (t : ℝ) : ℝ :=
  ∑ source : G.State,
    |germ.rawEndpointValueBaselineResidual t source who|

omit [DecidableEq G.State] in
theorem analytic_rawEndpointValueBaselineResidual
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι) :
    AnalyticAt ℝ
      (fun t =>
        germ.rawEndpointValueBaselineResidual t source who) 0 := by
  unfold rawEndpointValueBaselineResidual
  exact
    (Finset.univ.analyticAt_fun_sum fun destination _ =>
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelCurve) source)) destination).mul
        analyticAt_const).sub analyticAt_const

omit [DecidableEq G.State] in
@[simp]
theorem rawEndpointValueBaselineResidual_zero
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι) :
    germ.rawEndpointValueBaselineResidual 0 source who = 0 := by
  have harmonic :=
    congrFun
      (congrFun
        germ.finkContinuationResidualVector_endpointValue_eq_zero
        source) who
  simp only [Pi.zero_apply] at harmonic
  unfold finkContinuationResidualVector finkContinuationResidual
    finkContinuationEU at harmonic
  unfold rawEndpointValueBaselineResidual
  rw [expect_eq_sum] at harmonic
  have kernel :
      (∑ destination,
          germ.rawStateKernelCurve 0 source destination *
            germ.endpointValue destination who) =
        expect
          (G.finkStateKernel germ.endpointFinkPoint source)
          (fun destination => germ.endpointValue destination who) := by
    rw [expect_eq_sum]
    apply Finset.sum_congr rfl
    intro destination _
    rw [germ.rawStateKernelCurve_zero_eq_finkStateKernel]
  rw [kernel, G.expect_finkStateKernel_eq]
  rw [expect_eq_sum]
  exact harmonic

omit [DecidableEq G.State] in
theorem tendsto_endpointMovingGainErrorEnvelope
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    Tendsto (germ.endpointMovingGainErrorEnvelope who)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  unfold endpointMovingGainErrorEnvelope
  have total :=
    tendsto_finsetSum (s := Finset.univ)
      (fun pair : G.State × G.Act who => fun _ => by
        have analytic :=
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (analyticAt_pi_iff.mp
                (germ.analytic_rawPureDeviationContinuationGainCurve
                  germ.endpointValue)
                pair.1) who) pair.2).continuousAt
        have endpoint :
            germ.rawPureDeviationContinuationGainCurve
                germ.endpointValue 0 pair.1 who pair.2 =
              G.finkContinuationGain germ.endpointValue
                germ.endpointFinkPoint pair.1 who pair.2 :=
          germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint
            germ.endpointValue pair.1 who pair.2
        have raw :
            Tendsto
              (fun t =>
                germ.rawPureDeviationContinuationGainCurve
                  germ.endpointValue t pair.1 who pair.2)
              (𝓝 (0 : ℝ))
              (𝓝
                (germ.rawPureDeviationContinuationGainCurve
                  germ.endpointValue 0 pair.1 who pair.2)) :=
          analytic
        have difference :
            Tendsto
              (fun t =>
                germ.rawPureDeviationContinuationGainCurve
                    germ.endpointValue t pair.1 who pair.2 -
                  G.finkContinuationGain germ.endpointValue
                    germ.endpointFinkPoint pair.1 who pair.2)
              (𝓝 (0 : ℝ)) (𝓝 0) := by
          simpa only [endpoint, sub_self] using
            raw.sub_const
              (G.finkContinuationGain germ.endpointValue
                germ.endpointFinkPoint pair.1 who pair.2)
        simpa only [abs_zero] using difference.abs)
  simpa using total

omit [DecidableEq G.State] in
theorem tendsto_endpointBaselineResidualEnvelope
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    Tendsto (germ.endpointBaselineResidualEnvelope who)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  unfold endpointBaselineResidualEnvelope
  have total :=
    tendsto_finsetSum (s := Finset.univ)
      (fun source : G.State => fun _ => by
        have residual :
            Tendsto
              (fun t =>
                germ.rawEndpointValueBaselineResidual
                  t source who)
              (𝓝 (0 : ℝ))
              (𝓝
                (germ.rawEndpointValueBaselineResidual
                  0 source who)) :=
          (germ.analytic_rawEndpointValueBaselineResidual
            source who).continuousAt
        simpa only [
          germ.rawEndpointValueBaselineResidual_zero source who,
          abs_zero] using residual.abs)
  simpa using total

omit [DecidableEq G.State] in
theorem rawMovingGain_error_le_envelope
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (source : G.State) (action : G.Act who) :
    |germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t source who action -
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action| ≤
      germ.endpointMovingGainErrorEnvelope who t := by
  unfold endpointMovingGainErrorEnvelope
  exact Finset.single_le_sum
    (fun pair _ => abs_nonneg
      (germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t pair.1 who pair.2 -
        G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint pair.1 who pair.2))
    (Finset.mem_univ (source, action))

omit [DecidableEq G.State] in
theorem rawBaselineResidual_abs_le_envelope
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (source : G.State) :
    |germ.rawEndpointValueBaselineResidual t source who| ≤
      germ.endpointBaselineResidualEnvelope who t := by
  unfold endpointBaselineResidualEnvelope
  exact Finset.single_le_sum
    (fun other _ => abs_nonneg
      (germ.rawEndpointValueBaselineResidual t other who))
    (Finset.mem_univ source)

/-- Endpoint-strict probability of one mixed action. -/
def endpointStrictActionMass
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι)
    (deviation : PMF (G.Act who)) : ℝ :=
  expect deviation fun action =>
    if G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action < 0 then
      1
    else
      0

omit [DecidableEq G.State] in
theorem endpointStrictActionMass_nonneg
    (germ : G.AnalyticBellmanGerm)
    (source : G.State) (who : ι)
    (deviation : PMF (G.Act who)) :
    0 ≤ germ.endpointStrictActionMass source who deviation := by
  unfold endpointStrictActionMass
  apply expect_nonneg
  intro action
  split_ifs <;> norm_num

omit [DecidableEq G.State] in
/-- Every action's moving continuation gain is bounded by the uniform
analytic error minus the strict gap on strict actions. -/
theorem rawMovingGain_le_error_sub_strictGap
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (source : G.State) (action : G.Act who) :
    germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t source who action ≤
      germ.endpointMovingGainErrorEnvelope who t -
        germ.endpointStrictGap who *
          (if G.finkContinuationGain germ.endpointValue
              germ.endpointFinkPoint source who action < 0 then
            1
          else
            0) := by
  have error :=
    germ.rawMovingGain_error_le_envelope
      who t source action
  rw [abs_le] at error
  by_cases strict :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action < 0
  · rw [if_pos strict, mul_one]
    have gap :=
      germ.endpointContinuationGain_le_neg_strictGap
        who source action strict
    linarith
  · rw [if_neg strict, mul_zero, sub_zero]
    have endpoint_nonpos :=
      germ.finkContinuationGain_endpointValue_nonpos
        source who action
    have endpoint_zero :
        G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint source who action = 0 := by
      exact le_antisymm endpoint_nonpos (not_lt.mp strict)
    linarith

omit [DecidableEq G.State] in
/-- Uniform finite-family stabilization: sufficiently near the endpoint,
every endpoint-strict action retains at least half of the canonical strict
gap. -/
theorem eventually_rawMovingGain_le_neg_half_strictGap
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ source action,
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint source who action < 0 →
          germ.rawPureDeviationContinuationGainCurve
              germ.endpointValue t source who action ≤
            -(germ.endpointStrictGap who / 2) := by
  have half_pos :
      0 < germ.endpointStrictGap who / 2 := by
    exact div_pos (germ.endpointStrictGap_pos who) (by norm_num)
  have envelope_small :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        germ.endpointMovingGainErrorEnvelope who t <
          germ.endpointStrictGap who / 2 :=
    (germ.tendsto_endpointMovingGainErrorEnvelope who).eventually
      (Iio_mem_nhds half_pos)
  filter_upwards [envelope_small] with t ht
  intro source action strict
  have bound :=
    germ.rawMovingGain_le_error_sub_strictGap
      who t source action
  rw [if_pos strict, mul_one] at bound
  linarith

omit [DecidableEq G.State] in
/-- Endpoint-neutral actions have moving gain bounded above by the common
vanishing finite-family envelope. -/
theorem rawMovingGain_le_envelope_of_endpointNeutral
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (source : G.State) (action : G.Act who)
    (neutral :
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint source who action = 0) :
    germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t source who action ≤
      germ.endpointMovingGainErrorEnvelope who t := by
  have error :=
    germ.rawMovingGain_error_le_envelope who t source action
  rw [neutral, sub_zero, abs_le] at error
  exact error.2

omit [DecidableEq G.State] in
/-- Mixed moving continuation gain is controlled by the gain-error envelope
minus the strict gap times endpoint-strict action mass. -/
theorem expect_rawMovingGain_le_error_sub_strictMass
    (germ : G.AnalyticBellmanGerm) (who : ι)
    (t : ℝ) (source : G.State)
    (deviation : PMF (G.Act who)) :
    expect deviation
        (germ.rawPureDeviationContinuationGainCurve
          germ.endpointValue t source who) ≤
      germ.endpointMovingGainErrorEnvelope who t -
        germ.endpointStrictGap who *
          germ.endpointStrictActionMass source who deviation := by
  calc
    expect deviation
          (germ.rawPureDeviationContinuationGainCurve
            germ.endpointValue t source who) ≤
        expect deviation (fun action =>
          germ.endpointMovingGainErrorEnvelope who t -
            germ.endpointStrictGap who *
              (if G.finkContinuationGain germ.endpointValue
                  germ.endpointFinkPoint source who action < 0 then
                1
              else
                0)) :=
      expect_mono deviation _ _
        (germ.rawMovingGain_le_error_sub_strictGap who t source)
    _ =
        germ.endpointMovingGainErrorEnvelope who t -
          germ.endpointStrictGap who *
            germ.endpointStrictActionMass source who deviation := by
      unfold endpointStrictActionMass
      rw [expect_sub, expect_const, expect_const_mul]

omit [DecidableEq G.State] in
/-- At a valid analytic parameter, the raw baseline residual is the
semantic prescribed Fink residual. -/
theorem rawEndpointValueBaselineResidual_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (source : G.State) (who : ι) :
    germ.rawEndpointValueBaselineResidual t source who =
      G.finkContinuationEU germ.endpointValue
          (germ.finkPointAt ht) source who -
        germ.endpointValue source who := by
  unfold rawEndpointValueBaselineResidual finkContinuationEU
  have kernel :
      (∑ destination,
          germ.rawStateKernelCurve t source destination *
            germ.endpointValue destination who) =
        expect
          (G.finkStateKernel (germ.finkPointAt ht) source)
          (fun destination => germ.endpointValue destination who) := by
    rw [expect_eq_sum]
    apply Finset.sum_congr rfl
    intro destination _
    rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
  rw [kernel, G.expect_finkStateKernel_eq]

/-- State-only endpoint-value history potential for one player. -/
def endpointValueHistoryPotential
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    G.HistoryPotential :=
  fun _ history => germ.endpointValue history.2 who

omit [DecidableEq G.State] in
/-- Exact full-history one-step decomposition: actual endpoint-value drift
equals the prescribed residual plus the unilateral action mixture's moving
continuation gain. -/
theorem scheduledFinkDeviation_endpointValueDrift_eq
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    G.historyContinuationEU
          (scheduledFinkDeviationProfile
            germ who startEpoch valid dev)
          (germ.endpointValueHistoryPotential who)
          history -
        germ.endpointValue history.2 who =
      germ.rawEndpointValueBaselineResidual
          (playerNeutralCalendarScale startEpoch stage)
          history.2 who +
        expect (dev stage history)
          (germ.rawPureDeviationContinuationGainCurve
            germ.endpointValue
            (playerNeutralCalendarScale startEpoch stage)
            history.2 who) := by
  let ht := valid (anytimeEpochIndex stage)
  have baseline :=
    germ.rawEndpointValueBaselineResidual_eq_finkPointAt
      ht history.2 who
  have gain (action : G.Act who) :=
    germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt
      germ.endpointValue ht history.2 who action
  unfold endpointValueHistoryPotential
  unfold scheduledFinkDeviationProfile
  unfold historyContinuationEU
  rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
  rw [pmfPi_update_bind, expect_bind]
  dsimp only [playerNeutralCalendarScale, calendarScale]
  rw [baseline]
  have gainExpectation :
      expect (dev stage history)
          (germ.rawPureDeviationContinuationGainCurve
            germ.endpointValue
            (shiftedUniversalEpochScale startEpoch
              (anytimeEpochIndex stage))
            history.2 who) =
        expect (dev stage history)
          (fun action =>
            G.finkContinuationGain germ.endpointValue
              (germ.finkPointAt ht) history.2 who action) := by
    apply congrArg (expect (dev stage history))
    funext action
    exact gain action
  rw [gainExpectation]
  unfold finkContinuationEU finkContinuationGain
  rw [expect_sub, expect_const]
  ring

/-- Expected cumulative endpoint-strict mass under the arbitrary deviating
strategy's own public-history law. -/
def expectedEndpointStrictActionMass
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    G.expectedHistoryValue
      (scheduledFinkDeviationProfile
        germ who startEpoch valid dev)
      initial
      (fun stage history =>
        germ.endpointStrictActionMass
          history.2 who (dev stage history))
      stage

/-- Explicit finite-horizon strict-mass budget. -/
def endpointStrictActionMassBudget
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch T : ℕ) : ℝ :=
  (germ.endpointStrictGap who)⁻¹ *
    (2 * finiteStatePotentialBound
        (fun source => germ.endpointValue source who) +
      ∑ stage ∈ Finset.range T,
        (germ.endpointMovingGainErrorEnvelope who
            (playerNeutralCalendarScale startEpoch stage) +
          germ.endpointBaselineResidualEnvelope who
            (playerNeutralCalendarScale startEpoch stage)))

private theorem tendsto_endpointStrict_anytimeEpochIndex :
    Tendsto anytimeEpochIndex atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards
    [eventually_ge_atTop
      (epochStart anytimeEpochLength K)] with stage hstage
  exact anytimeEpochIndex_ge_of_start_le hstage

theorem tendsto_playerNeutralCalendarScale
    (startEpoch : ℕ) :
    Tendsto (playerNeutralCalendarScale startEpoch)
      atTop (𝓝 0) :=
  (tendsto_shiftedUniversalEpochScale startEpoch).comp
    tendsto_endpointStrict_anytimeEpochIndex

omit [DecidableEq G.State] in
/-- The explicit strict-mass budget is sublinear. -/
theorem endpointStrictActionMassBudget_sublinear
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ) :
    IsAsymptoticallySublinear
      (germ.endpointStrictActionMassBudget who startEpoch) := by
  let stageError : ℕ → ℝ := fun stage =>
    germ.endpointMovingGainErrorEnvelope who
        (playerNeutralCalendarScale startEpoch stage) +
      germ.endpointBaselineResidualEnvelope who
        (playerNeutralCalendarScale startEpoch stage)
  have stageError_zero :
      Tendsto stageError atTop (𝓝 0) := by
    simpa only [stageError, Function.comp_apply, zero_add] using
      (germ.tendsto_endpointMovingGainErrorEnvelope who).comp
          (tendsto_playerNeutralCalendarScale startEpoch) |>.add
        ((germ.tendsto_endpointBaselineResidualEnvelope who).comp
          (tendsto_playerNeutralCalendarScale startEpoch))
  have cumulative :
      IsAsymptoticallySublinear
        (fun T => ∑ stage ∈ Finset.range T, stageError stage) :=
    isAsymptoticallySublinear_iff_tendsto.mpr stageError_zero.cesaro
  unfold endpointStrictActionMassBudget
  apply IsAsymptoticallySublinear.const_mul
  exact
    (IsAsymptoticallySublinear.const
      (2 * finiteStatePotentialBound
        (fun source => germ.endpointValue source who))).add cumulative

omit [DecidableEq G.State] in
/-- Full-public-history finite-horizon bound on endpoint-strict action mass
for every unilateral behavior strategy. -/
theorem expectedEndpointStrictActionMass_le_budget
    (germ : G.AnalyticBellmanGerm)
    (who : ι) (startEpoch : ℕ)
    (valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius)
    (dev : G.BehaviorStrategy who)
    (initial : G.State) (T : ℕ) :
    germ.expectedEndpointStrictActionMass
        who startEpoch valid dev initial T ≤
      germ.endpointStrictActionMassBudget who startEpoch T := by
  let profile :=
    scheduledFinkDeviationProfile germ who startEpoch valid dev
  let potential := germ.endpointValueHistoryPotential who
  let mass : G.HistoryPotential := fun stage history =>
    germ.endpointStrictActionMass history.2 who (dev stage history)
  let error : ℕ → ℝ := fun stage =>
    germ.endpointMovingGainErrorEnvelope who
        (playerNeutralCalendarScale startEpoch stage) +
      germ.endpointBaselineResidualEnvelope who
        (playerNeutralCalendarScale startEpoch stage)
  have step :
      ∀ stage (history : G.Hist stage),
        germ.endpointStrictGap who * mass stage history ≤
          error stage -
            (G.historyContinuationEU profile potential history -
              potential stage history) := by
    intro stage history
    have drift :=
      germ.scheduledFinkDeviation_endpointValueDrift_eq
        who startEpoch valid dev history
    have gain :=
      germ.expect_rawMovingGain_le_error_sub_strictMass
        who (playerNeutralCalendarScale startEpoch stage)
        history.2 (dev stage history)
    have baseline :=
      germ.rawBaselineResidual_abs_le_envelope
        who (playerNeutralCalendarScale startEpoch stage)
        history.2
    rw [abs_le] at baseline
    change
      germ.endpointStrictGap who *
          germ.endpointStrictActionMass
            history.2 who (dev stage history) ≤
        (germ.endpointMovingGainErrorEnvelope who
            (playerNeutralCalendarScale startEpoch stage) +
          germ.endpointBaselineResidualEnvelope who
            (playerNeutralCalendarScale startEpoch stage)) -
          (G.historyContinuationEU
              (scheduledFinkDeviationProfile
                germ who startEpoch valid dev)
              (germ.endpointValueHistoryPotential who)
              history -
            germ.endpointValue history.2 who)
    rw [drift]
    linarith [baseline.2]
  have expected_step (stage : ℕ) :
      germ.endpointStrictGap who *
          G.expectedHistoryValue profile initial mass stage ≤
        error stage +
          G.expectedHistoryValue profile initial potential stage -
          G.expectedHistoryValue profile initial potential (stage + 1) := by
    have successor :=
      G.expectedHistoryValue_succ
        profile initial potential stage
    have averaged :=
      expect_mono
        (G.histDist profile initial stage)
        (fun history =>
          germ.endpointStrictGap who * mass stage history)
        (fun history =>
          error stage -
            (G.historyContinuationEU profile potential history -
              potential stage history))
        (step stage)
    rw [expect_const_mul, expect_sub, expect_const, expect_sub]
      at averaged
    rw [successor]
    change
      germ.endpointStrictGap who *
          expect (G.histDist profile initial stage) (mass stage) ≤
        error stage +
          expect (G.histDist profile initial stage) (potential stage) -
          expect (G.histDist profile initial stage)
            (G.historyContinuationEU profile potential)
    linarith
  have telescope :
      germ.endpointStrictGap who *
          germ.expectedEndpointStrictActionMass
            who startEpoch valid dev initial T ≤
        (∑ stage ∈ Finset.range T, error stage) +
          G.expectedHistoryValue profile initial potential 0 -
          G.expectedHistoryValue profile initial potential T := by
    unfold expectedEndpointStrictActionMass
    change
      germ.endpointStrictGap who *
          (∑ stage ∈ Finset.range T,
            G.expectedHistoryValue profile initial mass stage) ≤ _
    rw [Finset.mul_sum]
    induction T with
    | zero => simp
    | succ T inductionHypothesis =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith [expected_step T]
  have potential_bound (stage : ℕ) :
      |G.expectedHistoryValue profile initial potential stage| ≤
        finiteStatePotentialBound
          (fun source => germ.endpointValue source who) := by
    apply abs_expect_le_of_abs_le
    intro history
    simpa only [potential, endpointValueHistoryPotential,
      statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        (fun source => germ.endpointValue source who)
        (fun _ => history.2) 0
  have initial_bound := potential_bound 0
  have final_bound := potential_bound T
  rw [abs_le] at initial_bound final_bound
  have raw :
      germ.endpointStrictGap who *
          germ.expectedEndpointStrictActionMass
            who startEpoch valid dev initial T ≤
        2 * finiteStatePotentialBound
            (fun source => germ.endpointValue source who) +
          ∑ stage ∈ Finset.range T, error stage := by
    linarith
  have gap_pos := germ.endpointStrictGap_pos who
  unfold endpointStrictActionMassBudget
  rw [show
      (∑ stage ∈ Finset.range T,
        (germ.endpointMovingGainErrorEnvelope who
            (playerNeutralCalendarScale startEpoch stage) +
          germ.endpointBaselineResidualEnvelope who
            (playerNeutralCalendarScale startEpoch stage))) =
      ∑ stage ∈ Finset.range T, error stage by rfl]
  exact (le_inv_mul_iff₀' gap_pos).2 (by
    simpa only [mul_comm] using raw)

omit [DecidableEq G.State] in
/-- A finite burn-in makes every shifted calendar parameter valid.  The same
calendar then controls endpoint-strict action mass for every unilateral
behavior strategy and every horizon by one explicit sublinear budget. -/
theorem exists_endpointStrictActionMassCalendarAccount
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      (∀ (dev : G.BehaviorStrategy who) initial T,
        germ.expectedEndpointStrictActionMass
            who startEpoch valid dev initial T ≤
          germ.endpointStrictActionMassBudget
            who startEpoch T) ∧
      IsAsymptoticallySublinear
        (germ.endpointStrictActionMassBudget who startEpoch) := by
  have hscale :
      Tendsto universalEpochScale atTop
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact
      ⟨tendsto_universalEpochScale,
        Filter.Eventually.of_forall universalEpochScale_pos⟩
  have hvalid :
      ∀ᶠ k : ℕ in atTop,
        universalEpochScale k ∈ Ioo (0 : ℝ) germ.radius :=
    hscale.eventually (Ioo_mem_nhdsGT germ.radius_pos)
  obtain ⟨startEpoch, hstart⟩ := eventually_atTop.1 hvalid
  let valid :
      ∀ k : ℕ,
        shiftedUniversalEpochScale startEpoch k ∈
          Ioo (0 : ℝ) germ.radius :=
    fun k => hstart (startEpoch + k) (by omega)
  refine ⟨startEpoch, valid, ?_, ?_⟩
  · intro dev initial T
    exact germ.expectedEndpointStrictActionMass_le_budget
      who startEpoch valid dev initial T
  · exact germ.endpointStrictActionMassBudget_sublinear
      who startEpoch

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
