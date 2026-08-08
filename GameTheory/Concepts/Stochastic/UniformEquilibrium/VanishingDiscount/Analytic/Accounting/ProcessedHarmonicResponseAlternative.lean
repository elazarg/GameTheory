/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkPublicResponse
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicResponseGainCalendar

/-!
# Public-response or sublinear-gain closure of the processed harmonic branch

The complete moving response-gain identity leaves one endpoint term outside
the harmonic continuation account: the endpoint stage gain.  Finiteness of
the invisible-response family gives the exact operational alternative.

* If one endpoint stage gain is positive, analyticity turns the same action,
  owned by the same player, into a fixed `AnalyticFinkStagePublicResponse`.
* Otherwise every endpoint stage gain is nonpositive.  The correction slack
  is nonnegative, so the full moving corrected gain is bounded above by the
  absolute moving analytic remainder.  Its positive part therefore has a
  sublinear cumulative expectation along the universal calendar, uniformly
  over arbitrary history laws and predictable behavioral mixtures.

This closes the analytic/accounting part of the processed harmonic response
branch.  It does not construct the phase strategy that realizes a supplied
behavioral selector.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Filter Math Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- The actual player-owned response index attached to an invisible action.
The owner is fixed rather than selected from an unoriented obstruction. -/
def ownedInvisibleForwardResponse
    {who : ι} (response : germ.InvisibleNeutralAction who) :
    Σ owner : ι, G.State × G.Act owner :=
  ⟨who, response.source, response.1.2⟩

omit [DecidableEq G.State] in
/-- A positive endpoint stage gain persists as one fixed player-owned
analytic stage response with a power-law margin. -/
theorem exists_analyticFinkStagePublicResponse_of_invisible_endpoint_pos
    {who : ι} (response : germ.InvisibleNeutralAction who)
    (positive :
      0 <
        G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2) :
    Nonempty
      (AnalyticFinkStagePublicResponse germ
        (ownedInvisibleForwardResponse response)) := by
  let stage : ℝ → ℝ := fun t =>
    germ.rawPureDeviationStageGainCurve
      t response.source who response.1.2
  have stage_analytic : AnalyticAt ℝ stage 0 := by
    exact
      analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve
            response.source)
          who)
        response.1.2
  have stage_zero :
      stage 0 =
        G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 := by
    exact
      germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint
        response.source who response.1.2
  have stage_positive :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 < stage t := by
    have near : ∀ᶠ t in nhds 0, 0 < stage t :=
      stage_analytic.continuousAt.tendsto.eventually_const_lt
        (stage_zero ▸ positive)
    exact near.filter_mono nhdsWithin_le_nhds
  obtain ⟨order, margin, margin_pos, power⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      stage_analytic stage_positive
  refine ⟨{
    order := order
    margin := margin
    margin_pos := margin_pos
    eventual := ?_ }⟩
  filter_upwards
      [Ioo_mem_nhdsGT germ.radius_pos, power, stage_positive] with
      t ht hpower hpositive
  simpa only [sub_zero, stage, ownedInvisibleForwardResponse] using
    And.intro ht (And.intro hpower hpositive)

omit [DecidableEq G.State] in
/-- Finite endpoint dichotomy for invisible responses of a fixed player. -/
theorem
    exists_ownedStagePublicResponse_or_endpointStageGain_nonpos
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    (∃ response : germ.InvisibleNeutralAction who,
        Nonempty
          (AnalyticFinkStagePublicResponse germ
            (ownedInvisibleForwardResponse response))) ∨
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0 := by
  classical
  by_cases exists_positive :
      ∃ response : germ.InvisibleNeutralAction who,
        0 <
          G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2
  · left
    obtain ⟨response, positive⟩ := exists_positive
    exact
      ⟨response,
        exists_analyticFinkStagePublicResponse_of_invisible_endpoint_pos
          response positive⟩
  · right
    intro response
    exact le_of_not_gt fun positive =>
      exists_positive ⟨response, positive⟩

omit [DecidableEq G.State] in
/-- If the endpoint stage gain is nonpositive, every moving corrected gain
is bounded above by the absolute complete analytic remainder. -/
theorem
    HarmonicInvisibleQuotientCorrection.rawMovingCorrectedResponseGain_le_abs_remainder
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) :
    correction.rawMovingCorrectedResponseGain t response ≤
      |correction.rawMovingResponseGainRemainder t response| := by
  have identity :=
    correction.rawMovingCorrectedResponseGain_add_slack t response
  have slack_nonneg := correction.slack_nonneg response
  have remainder_le_abs :
      correction.rawMovingResponseGainRemainder t response ≤
        |correction.rawMovingResponseGainRemainder t response| :=
    le_abs_self _
  linarith [stage_nonpos response]

omit [DecidableEq G.State] in
/-- The positive part of every moving corrected response gain is bounded by
the same absolute remainder. -/
theorem
    HarmonicInvisibleQuotientCorrection.max_zero_rawMovingCorrectedResponseGain_le_abs_remainder
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (t : ℝ) (response : germ.InvisibleNeutralAction who) :
    max 0 (correction.rawMovingCorrectedResponseGain t response) ≤
      |correction.rawMovingResponseGainRemainder t response| := by
  apply max_le
  · exact abs_nonneg _
  · exact
      correction.rawMovingCorrectedResponseGain_le_abs_remainder
        stage_nonpos t response

/-- Expected positive moving corrected response gain at one calendar stage.
The history law and predictable behavioral response mixture are arbitrary. -/
def
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGainStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) : ℝ :=
  expect (historyLaw stage) fun history =>
    expect (selection stage history) fun response =>
      max 0
        (correction.rawMovingCorrectedResponseGain
          (residualCalendarScale stage) response)

omit [DecidableEq G.State] in
/-- Expected positive moving gain is nonnegative. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGainStage_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    0 ≤ correction.calendarPositiveResponseGainStage
      historyLaw selection stage := by
  unfold calendarPositiveResponseGainStage
  apply expect_nonneg
  intro history
  exact expect_nonneg _ _ fun response => le_max_left _ _

omit [DecidableEq G.State] in
/-- Under the nonpositive endpoint-stage branch, expected positive moving
gain is bounded by the complete analytic remainder budget stage by stage. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGainStage_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (stage : ℕ) :
    correction.calendarPositiveResponseGainStage
        historyLaw selection stage ≤
      correction.calendarResponseGainStageBudget
        historyLaw selection stage := by
  unfold calendarPositiveResponseGainStage
    calendarResponseGainStageBudget
  apply expect_mono
  intro history
  apply expect_mono
  intro response
  exact
    correction.max_zero_rawMovingCorrectedResponseGain_le_abs_remainder
      stage_nonpos (residualCalendarScale stage) response

/-- Cumulative expected positive moving corrected response gain. -/
def
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T,
    correction.calendarPositiveResponseGainStage
      historyLaw selection stage

omit [DecidableEq G.State] in
/-- The cumulative expected positive moving gain is nonnegative. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGain_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) :
    0 ≤ correction.calendarPositiveResponseGain
      historyLaw selection T := by
  unfold calendarPositiveResponseGain
  exact Finset.sum_nonneg fun stage _ =>
    correction.calendarPositiveResponseGainStage_nonneg
      historyLaw selection stage

omit [DecidableEq G.State] in
/-- Exact finite-horizon upper budget in the nonpositive endpoint-stage
branch. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGain_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) :
    correction.calendarPositiveResponseGain historyLaw selection T ≤
      correction.calendarResponseGainCumulativeBudget
        historyLaw selection T := by
  unfold calendarPositiveResponseGain
    calendarResponseGainCumulativeBudget
  apply Finset.sum_le_sum
  intro stage _
  exact
    correction.calendarPositiveResponseGainStage_le
      stage_nonpos historyLaw selection stage

omit [DecidableEq G.State] in
/-- If no invisible response has positive endpoint stage gain, cumulative
expected positive moving corrected gain is sublinear on the universal
calendar under every supplied law and behavioral mixture. -/
theorem
    HarmonicInvisibleQuotientCorrection.calendarPositiveResponseGain_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (stage_nonpos :
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 ≤
          0)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    IsAsymptoticallySublinear
      (correction.calendarPositiveResponseGain
        historyLaw selection) := by
  apply IsAsymptoticallySublinear.of_nonneg_le
  · exact
      correction.calendarPositiveResponseGain_nonneg
        historyLaw selection
  · exact
      correction.calendarPositiveResponseGain_le
        stage_nonpos historyLaw selection
  · exact
      correction.calendarResponseGainCumulativeBudget_sublinear
        historyLaw selection

omit [DecidableEq G.State] in
/-- Capstone processed-harmonic response alternative: either one fixed
owned stage response exists, or every supplied behavioral implementation
has only sublinear expected cumulative positive corrected gain. -/
theorem
    HarmonicInvisibleQuotientCorrection.ownedStagePublicResponse_or_sublinearPositiveGain
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (historyLaw : ∀ stage, PMF (Fin (stage + 1) → G.State))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who)) :
    (∃ response : germ.InvisibleNeutralAction who,
        Nonempty
          (AnalyticFinkStagePublicResponse germ
            (ownedInvisibleForwardResponse response))) ∨
      IsAsymptoticallySublinear
        (correction.calendarPositiveResponseGain
          historyLaw selection) := by
  rcases
      exists_ownedStagePublicResponse_or_endpointStageGain_nonpos
        germ who with response | stage_nonpos
  · exact Or.inl response
  · exact Or.inr
      (correction.calendarPositiveResponseGain_sublinear
        stage_nonpos historyLaw selection)

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
