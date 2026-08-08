/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicInvisibleResponseAlternative
import Math.Probability.AdaptiveTransitionAccount
import Math.Probability.IntegratedResponseLedger

/-!
# Adaptive accounts for harmonic invisible-response corrections

A harmonic invisible-response correction is stronger than a static finite
compatibility witness.  Its quotient is the drift of one bounded state
account under the actual endpoint deviation kernel.  Adding that potential
to the processed leading coordinate also turns every corrected continuation
gain into the drift of one bounded combined account.

Consequently, under an arbitrary history-dependent, source-compatible
selection of invisible responses:

* quotient drift plus its centered observation telescopes exactly;
* the nonnegative slack in the corrected continuation inequality has
  uniformly bounded expectation;
* both expected cumulative quantities are asymptotically sublinear.

These are endpoint-kernel accounting statements.  They do not construct a
punishment, and endpoint harmonicity does not make the same potential
harmonic for the positive-parameter moving baseline kernels.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Math Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- The scalar account potential obtained by adding the processed leading
coordinate to a harmonic quotient correction. -/
def HarmonicInvisibleQuotientCorrection.combinedPotential
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family) :
    G.State → ℝ :=
  fun state =>
    jet.endpointCoordinatePotential who state +
      correction.potential state

/-- The nonnegative slack in the corrected leading continuation
inequality. -/
def HarmonicInvisibleQuotientCorrection.slack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) : ℝ :=
  -G.finkContinuationGain
      (jet.factor 0 +
        G.finkPlayerPotential who correction.potential)
      germ.endpointFinkPoint
      response.source who response.1.2

/-- Residual of the endpoint-harmonic correction potential under the
positive-parameter prescribed kernel.  Endpoint harmonicity controls this
at `t = 0`, not at a general positive parameter. -/
def HarmonicInvisibleQuotientCorrection.movingBaselineResidualAt
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (source : G.State) : ℝ :=
  expect
      (G.finkStateKernel (germ.finkPointAt ht) source)
      correction.potential -
    correction.potential source

omit [DecidableEq G.State] in
/-- The quotient is exactly the transition drift of the correction
potential under the actual endpoint response kernel. -/
theorem
    HarmonicInvisibleQuotientCorrection.quotient_eq_transitionPotentialDrift
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    family.quotient response 0 =
      transitionPotentialDrift
        (fun action : germ.InvisibleNeutralAction who =>
          action.kernel)
        (fun action : germ.InvisibleNeutralAction who =>
          action.source)
        correction.potential response := by
  rw [correction.quotient_eq_expectedAccountIncrement response]
  unfold transitionPotentialDrift
  rw [expect_sub, expect_const]

omit [DecidableEq G.State] in
/-- Exact positive-parameter boundary: actual correction-account drift is
the continuation gain plus the moving-baseline residual.  The endpoint
construction controls the first term only after passing to the endpoint;
a moving-bias argument must separately budget the residual. -/
theorem
    HarmonicInvisibleQuotientCorrection.movingDrift_eq_gain_add_residual
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (response : germ.InvisibleNeutralAction who) :
    expect
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht)
            response.source who response.1.2)
          correction.potential -
        correction.potential response.source =
      G.finkContinuationGain
          (G.finkPlayerPotential who correction.potential)
          (germ.finkPointAt ht)
          response.source who response.1.2 +
        correction.movingBaselineResidualAt
          ht response.source := by
  rw [G.finkContinuationGain_playerPotential_self]
  unfold movingBaselineResidualAt
  ring

omit [DecidableEq G.State] in
/-- At the endpoint the residual vanishes exactly. -/
theorem HarmonicInvisibleQuotientCorrection.endpointBaselineResidual_eq_zero
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (source : G.State) :
    expect
          (G.finkStateKernel germ.endpointFinkPoint source)
          correction.potential -
        correction.potential source =
      0 := by
  rw [correction.harmonic source, sub_self]

omit [DecidableEq G.State] in
/-- The sum of the processed coordinate and correction potential is
harmonic for every endpoint prescribed transition. -/
theorem HarmonicInvisibleQuotientCorrection.combinedPotential_harmonic
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (source : G.State) :
    expect
        (G.finkStateKernel germ.endpointFinkPoint source)
        correction.combinedPotential =
      correction.combinedPotential source := by
  unfold combinedPotential
  rw [expect_add,
    jet.endpointCoordinatePotential_harmonic_of_processed
      span processed who source,
    correction.harmonic source]

omit [DecidableEq G.State] in
/-- Every corrected leading gain is the actual expected increment of the
combined bounded state account. -/
theorem
    HarmonicInvisibleQuotientCorrection.correctedGain_eq_expectedIncrement
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    G.finkContinuationGain
        (jet.factor 0 +
          G.finkPlayerPotential who correction.potential)
        germ.endpointFinkPoint
        response.source who response.1.2 =
      expect response.kernel
        (fun successor =>
          correction.combinedPotential successor -
            correction.combinedPotential response.source) := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  rw [expect_sub, expect_const]
  simp only [Pi.add_apply, G.finkPlayerPotential_apply_self]
  unfold combinedPotential endpointCoordinatePotential
  change
    expect response.kernel correction.combinedPotential -
        expect
          (G.finkStateKernel
            germ.endpointFinkPoint response.source)
          correction.combinedPotential =
      expect response.kernel correction.combinedPotential -
        correction.combinedPotential response.source
  rw [correction.combinedPotential_harmonic
    span processed response.source]

omit [DecidableEq G.State] in
/-- The correction slack is nonnegative. -/
theorem HarmonicInvisibleQuotientCorrection.slack_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    0 ≤ correction.slack response := by
  unfold slack
  exact neg_nonneg.mpr (correction.corrected_gain_nonpos response)

omit [DecidableEq G.State] in
/-- The correction slack is the negative transition drift of the combined
account under the actual endpoint response kernel. -/
theorem HarmonicInvisibleQuotientCorrection.slack_eq_neg_transitionDrift
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (response : germ.InvisibleNeutralAction who) :
    correction.slack response =
      -transitionPotentialDrift
        (fun action : germ.InvisibleNeutralAction who =>
          action.kernel)
        (fun action : germ.InvisibleNeutralAction who =>
          action.source)
        correction.combinedPotential response := by
  unfold slack transitionPotentialDrift
  rw [correction.correctedGain_eq_expectedIncrement
    span processed response]
  rw [expect_sub, expect_const]

/-- Expected cumulative quotient selected from finite public state histories.
The law uses the actual endpoint response kernel at every selected index. -/
def HarmonicInvisibleQuotientCorrection.expectedSelectedQuotient
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (_correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (selectedTransitionComparison
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          choice))
      (T + 1))
    (fun history =>
      selectedTransitionCostSum choice
        (fun response => family.quotient response 0)
        T history)

/-- Expected cumulative nonnegative slack in the corrected leading
continuation inequality. -/
def HarmonicInvisibleQuotientCorrection.expectedSelectedSlack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (selectedTransitionComparison
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          choice))
      (T + 1))
    (fun history =>
      selectedTransitionCostSum choice correction.slack T history)

omit [DecidableEq G.State] in
/-- Exact pathwise quotient-account identity for an arbitrary
history-dependent source-compatible selection of invisible responses. -/
theorem
    HarmonicInvisibleQuotientCorrection.selectedQuotient_add_centered_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (source_compatible :
      ∀ n history,
        (choice n history).source = history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → G.State) :
    predictableScoreSum
          (adaptiveSelectedTransitionCenteredScore
            (fun response : germ.InvisibleNeutralAction who =>
              response.kernel)
            correction.potential choice)
          (T + 1) history +
        selectedTransitionCostSum choice
          (fun response => family.quotient response 0)
          T history =
      correction.potential (history (Fin.last T)) -
        correction.potential (history 0) := by
  have account :=
    selectedTransitionCenteredScore_add_drift_eq_accountIncrement
      (fun response : germ.InvisibleNeutralAction who =>
        response.kernel)
      (fun response : germ.InvisibleNeutralAction who =>
        response.source)
      correction.potential choice source_compatible T history
  have cost_eq :
      (fun response : germ.InvisibleNeutralAction who =>
        family.quotient response 0) =
        transitionPotentialDrift
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          (fun response : germ.InvisibleNeutralAction who =>
            response.source)
          correction.potential := by
    funext response
    exact
      correction.quotient_eq_transitionPotentialDrift response
  rw [cost_eq]
  exact account

omit [DecidableEq G.State] in
/-- The expected cumulative quotient is the expected endpoint motion of
the bounded correction account.  The centered observation has expectation
zero under every adaptively selected actual response kernel. -/
theorem
    HarmonicInvisibleQuotientCorrection.expectedSelectedQuotient_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (source_compatible :
      ∀ n history,
        (choice n history).source = history (Fin.last n))
    (T : ℕ) :
    correction.expectedSelectedQuotient initial choice T =
      expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (selectedTransitionComparison
              (fun response : germ.InvisibleNeutralAction who =>
                response.kernel)
              choice))
          (T + 1))
        (fun history =>
          correction.potential (history (Fin.last T)) -
            correction.potential (history 0)) := by
  let kernel : germ.InvisibleNeutralAction who → PMF G.State :=
    fun response => response.kernel
  let comparison :=
    selectedTransitionComparison kernel choice
  let step := adaptiveMarkovStep initial comparison
  let score :=
    adaptiveSelectedTransitionCenteredScore
      kernel correction.potential choice
  have centered :
      ∀ n history,
        expect (step n history) (score n history) = 0 := by
    intro n history
    cases n with
    | zero =>
        simp [step, score]
    | succ n =>
        exact
          expect_adaptiveSelectedTransitionCenteredScore_succ
            kernel correction.potential choice n history
  have score_zero :
      expect
          (adaptiveHistoryLaw step (T + 1))
          (predictableScoreSum score (T + 1)) =
        0 :=
    expect_predictableScoreSum_eq_zero step score centered (T + 1)
  unfold expectedSelectedQuotient
  change
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          selectedTransitionCostSum choice
            (fun response => family.quotient response 0)
            T history) =
      _
  calc
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          selectedTransitionCostSum choice
            (fun response => family.quotient response 0)
            T history) =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            predictableScoreSum score (T + 1) history +
              selectedTransitionCostSum choice
                (fun response => family.quotient response 0)
                T history) := by
          rw [expect_add, score_zero, zero_add]
    _ =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            correction.potential (history (Fin.last T)) -
              correction.potential (history 0)) := by
          apply congrArg
          funext history
          exact
            correction.selectedQuotient_add_centered_eq
              choice source_compatible T history
    _ = _ := rfl

omit [DecidableEq G.State] in
/-- The expected cumulative quotient is uniformly bounded by the endpoint
motion of one finite-state potential. -/
theorem
    HarmonicInvisibleQuotientCorrection.abs_expectedSelectedQuotient_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (source_compatible :
      ∀ n history,
        (choice n history).source = history (Fin.last n))
    (T : ℕ) :
    |correction.expectedSelectedQuotient initial choice T| ≤
      2 * finiteStatePotentialBound correction.potential := by
  rw [correction.expectedSelectedQuotient_eq
    initial choice source_compatible T]
  apply abs_expect_le_of_abs_le
  intro history
  have last_bound :
      |correction.potential (history (Fin.last T))| ≤
        finiteStatePotentialBound correction.potential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.potential
        (fun _ => history (Fin.last T)) 0
  have initial_bound :
      |correction.potential (history 0)| ≤
        finiteStatePotentialBound correction.potential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.potential
        (fun _ => history 0) 0
  calc
    |correction.potential (history (Fin.last T)) -
        correction.potential (history 0)| ≤
        |correction.potential (history (Fin.last T))| +
          |correction.potential (history 0)| :=
      abs_sub _ _
    _ ≤
        finiteStatePotentialBound correction.potential +
          finiteStatePotentialBound correction.potential :=
      add_le_add last_bound initial_bound
    _ = 2 * finiteStatePotentialBound correction.potential := by ring

omit [DecidableEq G.State] in
/-- Therefore the expected cumulative quotient is asymptotically
sublinear, with no additional account hypothesis. -/
theorem
    HarmonicInvisibleQuotientCorrection.expectedSelectedQuotient_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.InvisibleNeutralAction who)
    (source_compatible :
      ∀ n history,
        (choice n history).source = history (Fin.last n)) :
    IsAsymptoticallySublinear
      (correction.expectedSelectedQuotient initial choice) := by
  rw [isAsymptoticallySublinear_iff_tendsto,
    tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun T : ℕ =>
      (T : ℝ)⁻¹ *
        (2 * finiteStatePotentialBound correction.potential))
  · filter_upwards with T
    exact norm_nonneg _
  · filter_upwards with T
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))]
    exact mul_le_mul_of_nonneg_left
      (correction.abs_expectedSelectedQuotient_le
        initial choice source_compatible T)
      (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact
      isAsymptoticallySublinear_iff_tendsto.mp
        (IsAsymptoticallySublinear.const
          (2 * finiteStatePotentialBound correction.potential))

/-- Expected cumulative quotient under a predictable behavioral mixture of
owned invisible responses. -/
def HarmonicInvisibleQuotientCorrection.expectedMixedQuotient
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (_correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (mixedTransitionComparison
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          selection))
      (T + 1))
    (fun history =>
      mixedTransitionCostSum selection
        (fun response => family.quotient response 0)
        T history)

/-- Expected cumulative nonnegative corrected-gain slack under a
predictable behavioral mixture of owned invisible responses. -/
def HarmonicInvisibleQuotientCorrection.expectedMixedSlack
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (mixedTransitionComparison
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          selection))
      (T + 1))
    (fun history =>
      mixedTransitionCostSum selection correction.slack T history)

/-- Expected one-stage corrected-gain slack under the predictable
behavioral response mixture. -/
def HarmonicInvisibleQuotientCorrection.expectedMixedSlackStage
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (t : ℕ) : ℝ :=
  expect
    (adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (mixedTransitionComparison
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          selection))
      (t + 1))
    (fun history =>
      expect (selection t history) correction.slack)

omit [DecidableEq G.State] in
/-- Exact quotient-account identity for every predictable
source-compatible behavioral mixture of invisible responses. -/
theorem
    HarmonicInvisibleQuotientCorrection.mixedQuotient_add_centered_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → G.State) :
    predictableScoreSum
          (adaptiveMixedTransitionCenteredScore
            (fun response : germ.InvisibleNeutralAction who =>
              response.kernel)
            correction.potential selection)
          (T + 1) history +
        mixedTransitionCostSum selection
          (fun response => family.quotient response 0)
          T history =
      correction.potential (history (Fin.last T)) -
        correction.potential (history 0) := by
  have account :=
    mixedTransitionCenteredScore_add_drift_eq_accountIncrement
      (fun response : germ.InvisibleNeutralAction who =>
        response.kernel)
      (fun response : germ.InvisibleNeutralAction who =>
        response.source)
      correction.potential selection source_compatible T history
  have cost_eq :
      (fun response : germ.InvisibleNeutralAction who =>
        family.quotient response 0) =
        transitionPotentialDrift
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          (fun response : germ.InvisibleNeutralAction who =>
            response.source)
          correction.potential := by
    funext response
    exact
      correction.quotient_eq_transitionPotentialDrift response
  rw [cost_eq]
  exact account

omit [DecidableEq G.State] in
/-- The expected mixed cumulative quotient is exactly the expected endpoint
motion of the bounded harmonic correction account. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedQuotient_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) :
    correction.expectedMixedQuotient initial selection T =
      expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (mixedTransitionComparison
              (fun response : germ.InvisibleNeutralAction who =>
                response.kernel)
              selection))
          (T + 1))
        (fun history =>
          correction.potential (history (Fin.last T)) -
            correction.potential (history 0)) := by
  let kernel : germ.InvisibleNeutralAction who → PMF G.State :=
    fun response => response.kernel
  let comparison :=
    mixedTransitionComparison kernel selection
  let step := adaptiveMarkovStep initial comparison
  let score :=
    adaptiveMixedTransitionCenteredScore
      kernel correction.potential selection
  have centered :
      ∀ n history,
        expect (step n history) (score n history) = 0 := by
    intro n history
    cases n with
    | zero =>
        simp [step, score]
    | succ n =>
        exact
          expect_adaptiveMixedTransitionCenteredScore_succ
            kernel correction.potential selection n history
  have score_zero :
      expect
          (adaptiveHistoryLaw step (T + 1))
          (predictableScoreSum score (T + 1)) =
        0 :=
    expect_predictableScoreSum_eq_zero step score centered (T + 1)
  unfold expectedMixedQuotient
  change
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          mixedTransitionCostSum selection
            (fun response => family.quotient response 0)
            T history) =
      _
  calc
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          mixedTransitionCostSum selection
            (fun response => family.quotient response 0)
            T history) =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            predictableScoreSum score (T + 1) history +
              mixedTransitionCostSum selection
                (fun response => family.quotient response 0)
                T history) := by
          rw [expect_add, score_zero, zero_add]
    _ =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            correction.potential (history (Fin.last T)) -
              correction.potential (history 0)) := by
          apply congrArg
          funext history
          exact
            correction.mixedQuotient_add_centered_eq
              selection source_compatible T history
    _ = _ := rfl

omit [DecidableEq G.State] in
/-- Uniform endpoint-account bound for predictable behavioral mixtures. -/
theorem
    HarmonicInvisibleQuotientCorrection.abs_expectedMixedQuotient_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) :
    |correction.expectedMixedQuotient initial selection T| ≤
      2 * finiteStatePotentialBound correction.potential := by
  rw [correction.expectedMixedQuotient_eq
    initial selection source_compatible T]
  apply abs_expect_le_of_abs_le
  intro history
  have last_bound :
      |correction.potential (history (Fin.last T))| ≤
        finiteStatePotentialBound correction.potential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.potential
        (fun _ => history (Fin.last T)) 0
  have initial_bound :
      |correction.potential (history 0)| ≤
        finiteStatePotentialBound correction.potential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.potential
        (fun _ => history 0) 0
  calc
    |correction.potential (history (Fin.last T)) -
        correction.potential (history 0)| ≤
        |correction.potential (history (Fin.last T))| +
          |correction.potential (history 0)| :=
      abs_sub _ _
    _ ≤
        finiteStatePotentialBound correction.potential +
          finiteStatePotentialBound correction.potential :=
      add_le_add last_bound initial_bound
    _ = 2 * finiteStatePotentialBound correction.potential := by ring

omit [DecidableEq G.State] in
/-- Behavioral mixed cumulative quotient drift is asymptotically
sublinear in expectation. -/
theorem
    HarmonicInvisibleQuotientCorrection.expectedMixedQuotient_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n)) :
    IsAsymptoticallySublinear
      (correction.expectedMixedQuotient initial selection) := by
  rw [isAsymptoticallySublinear_iff_tendsto,
    tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun T : ℕ =>
      (T : ℝ)⁻¹ *
        (2 * finiteStatePotentialBound correction.potential))
  · filter_upwards with T
    exact norm_nonneg _
  · filter_upwards with T
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))]
    exact mul_le_mul_of_nonneg_left
      (correction.abs_expectedMixedQuotient_le
        initial selection source_compatible T)
      (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact
      isAsymptoticallySublinear_iff_tendsto.mp
        (IsAsymptoticallySublinear.const
          (2 * finiteStatePotentialBound correction.potential))

private theorem mixedTransitionCostSum_neg
    {S I : Type*} [Finite I]
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (cost : I → ℝ) (T : ℕ)
    (history : Fin (T + 1) → S) :
    mixedTransitionCostSum selection (fun index => -cost index)
        T history =
      -mixedTransitionCostSum selection cost T history := by
  induction T with
  | zero =>
      simp
  | succ T inductionHypothesis =>
      rw [← Fin.snoc_init_self history,
        mixedTransitionCostSum_snoc,
        mixedTransitionCostSum_snoc,
        inductionHypothesis]
      have expected_neg :
          expect (selection T (Fin.init history))
              (fun index => -cost index) =
            -expect (selection T (Fin.init history)) cost := by
        calc
          expect (selection T (Fin.init history))
              (fun index => -cost index) =
              expect (selection T (Fin.init history))
                (fun index => (-1 : ℝ) * cost index) := by
                apply congrArg
                funext index
                ring
          _ = -expect (selection T (Fin.init history)) cost := by
                rw [expect_const_mul]
                ring
      rw [expected_neg]
      ring

omit [DecidableEq G.State] in
/-- The nonnegative corrected-gain slack equals the centered account score
plus the drop of the bounded combined potential. -/
theorem HarmonicInvisibleQuotientCorrection.mixedSlack_eq_centered_add_drop
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → G.State) :
    mixedTransitionCostSum selection correction.slack T history =
      predictableScoreSum
          (adaptiveMixedTransitionCenteredScore
            (fun response : germ.InvisibleNeutralAction who =>
              response.kernel)
            correction.combinedPotential selection)
          (T + 1) history +
        (correction.combinedPotential (history 0) -
          correction.combinedPotential (history (Fin.last T))) := by
  have account :=
    mixedTransitionCenteredScore_add_drift_eq_accountIncrement
      (fun response : germ.InvisibleNeutralAction who =>
        response.kernel)
      (fun response : germ.InvisibleNeutralAction who =>
        response.source)
      correction.combinedPotential selection
      source_compatible T history
  have cost_eq :
      transitionPotentialDrift
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          (fun response : germ.InvisibleNeutralAction who =>
            response.source)
          correction.combinedPotential =
        fun response => -correction.slack response := by
    funext response
    have relation :=
      correction.slack_eq_neg_transitionDrift
        span processed response
    linarith
  rw [cost_eq, mixedTransitionCostSum_neg] at account
  linarith

omit [DecidableEq G.State] in
/-- Expected behavioral correction slack is exactly the expected drop of
the bounded combined account.  This is the precise nonnegative expected
account supplied to downstream ledgers. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlack_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) :
    correction.expectedMixedSlack initial selection T =
      expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (mixedTransitionComparison
              (fun response : germ.InvisibleNeutralAction who =>
                response.kernel)
              selection))
          (T + 1))
        (fun history =>
          correction.combinedPotential (history 0) -
            correction.combinedPotential (history (Fin.last T))) := by
  let kernel : germ.InvisibleNeutralAction who → PMF G.State :=
    fun response => response.kernel
  let comparison :=
    mixedTransitionComparison kernel selection
  let step := adaptiveMarkovStep initial comparison
  let score :=
    adaptiveMixedTransitionCenteredScore
      kernel correction.combinedPotential selection
  have centered :
      ∀ n history,
        expect (step n history) (score n history) = 0 := by
    intro n history
    cases n with
    | zero =>
        simp [step, score]
    | succ n =>
        exact
          expect_adaptiveMixedTransitionCenteredScore_succ
            kernel correction.combinedPotential selection n history
  have score_zero :
      expect
          (adaptiveHistoryLaw step (T + 1))
          (predictableScoreSum score (T + 1)) =
        0 :=
    expect_predictableScoreSum_eq_zero step score centered (T + 1)
  unfold expectedMixedSlack
  change
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          mixedTransitionCostSum selection correction.slack T history) =
      _
  calc
    expect
        (adaptiveHistoryLaw step (T + 1))
        (fun history =>
          mixedTransitionCostSum selection correction.slack T history) =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            predictableScoreSum score (T + 1) history +
              (correction.combinedPotential (history 0) -
                correction.combinedPotential
                  (history (Fin.last T)))) := by
          apply congrArg
          funext history
          exact
            correction.mixedSlack_eq_centered_add_drop
              span processed selection source_compatible T history
    _ =
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            correction.combinedPotential (history 0) -
              correction.combinedPotential
                (history (Fin.last T))) := by
          rw [expect_add, score_zero, zero_add]
    _ = _ := rfl

omit [DecidableEq G.State] in
/-- Expected correction slack is nonnegative because every response's
corrected leading continuation gain is nonpositive. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlack_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) :
    0 ≤ correction.expectedMixedSlack initial selection T := by
  unfold expectedMixedSlack
  apply expect_nonneg
  intro history
  have lower :=
    mixedTransitionCostSum_mono
      selection
      (left := fun _ => 0)
      (right := correction.slack)
      correction.slack_nonneg T history
  have zero_cost :
      mixedTransitionCostSum selection (fun _ => 0) T history =
        0 := by
    rw [mixedTransitionCostSum_eq_sum_mass]
    simp
  rw [zero_cost] at lower
  exact lower

omit [DecidableEq G.State] in
/-- The expected cumulative slack grows by exactly the expected one-stage
slack. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlack_succ
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) :
    correction.expectedMixedSlack initial selection (T + 1) =
      correction.expectedMixedSlack initial selection T +
        correction.expectedMixedSlackStage initial selection T := by
  let kernel : germ.InvisibleNeutralAction who → PMF G.State :=
    fun response => response.kernel
  let comparison :=
    mixedTransitionComparison kernel selection
  let step := adaptiveMarkovStep initial comparison
  unfold expectedMixedSlack expectedMixedSlackStage
  change
    expect
        (adaptiveHistoryLaw step (T + 1 + 1))
        (fun history =>
          mixedTransitionCostSum selection correction.slack
            (T + 1) history) =
      expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            mixedTransitionCostSum selection correction.slack T history) +
        expect
          (adaptiveHistoryLaw step (T + 1))
          (fun history =>
            expect (selection T history) correction.slack)
  rw [adaptiveHistoryLaw_succ, expect_bind]
  have next :
      (fun history =>
          expect ((step (T + 1) history).map (Fin.snoc history))
            (fun extended =>
              mixedTransitionCostSum selection correction.slack
                (T + 1) extended)) =
        fun history =>
          mixedTransitionCostSum selection correction.slack T history +
            expect (selection T history) correction.slack := by
    funext history
    rw [expect_map]
    simp_rw [mixedTransitionCostSum_snoc]
    rw [expect_const]
  rw [next, expect_add]

omit [DecidableEq G.State] in
/-- Each expected one-stage slack is nonnegative. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlackStage_nonneg
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (t : ℕ) :
    0 ≤ correction.expectedMixedSlackStage initial selection t := by
  unfold expectedMixedSlackStage
  apply expect_nonneg
  intro history
  exact
    expect_nonneg _ _ fun response =>
      correction.slack_nonneg response

omit [DecidableEq G.State] in
/-- Expected cumulative slack is exactly the finite sum of the one-stage
ledger charges consumed by the integrated response ledger. -/
theorem HarmonicInvisibleQuotientCorrection.sum_expectedMixedSlackStage_eq
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) :
    (∑ t ∈ Finset.range T,
        correction.expectedMixedSlackStage initial selection t) =
      correction.expectedMixedSlack initial selection T := by
  induction T with
  | zero =>
      unfold expectedMixedSlack
      simp
  | succ T inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        correction.expectedMixedSlack_succ]

omit [DecidableEq G.State] in
/-- Uniform finite-state account bound for the total expected nonnegative
correction slack. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlack_le
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (T : ℕ) :
    correction.expectedMixedSlack initial selection T ≤
      2 * finiteStatePotentialBound correction.combinedPotential := by
  rw [correction.expectedMixedSlack_eq
    span processed initial selection source_compatible T]
  apply le_trans (le_abs_self _)
  apply abs_expect_le_of_abs_le
  intro history
  have initial_bound :
      |correction.combinedPotential (history 0)| ≤
        finiteStatePotentialBound correction.combinedPotential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.combinedPotential
        (fun _ => history 0) 0
  have last_bound :
      |correction.combinedPotential (history (Fin.last T))| ≤
        finiteStatePotentialBound correction.combinedPotential := by
    simpa [statePotentialAccount] using
      abs_statePotentialAccount_le_finiteStatePotentialBound
        correction.combinedPotential
        (fun _ => history (Fin.last T)) 0
  calc
    |correction.combinedPotential (history 0) -
        correction.combinedPotential (history (Fin.last T))| ≤
        |correction.combinedPotential (history 0)| +
          |correction.combinedPotential (history (Fin.last T))| :=
      abs_sub _ _
    _ ≤
        finiteStatePotentialBound correction.combinedPotential +
          finiteStatePotentialBound correction.combinedPotential :=
      add_le_add initial_bound last_bound
    _ = 2 * finiteStatePotentialBound correction.combinedPotential := by
      ring

omit [DecidableEq G.State] in
/-- The nonnegative behavioral correction-slack ledger is asymptotically
sublinear in expectation. -/
theorem HarmonicInvisibleQuotientCorrection.expectedMixedSlack_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n)) :
    IsAsymptoticallySublinear
      (correction.expectedMixedSlack initial selection) := by
  apply IsAsymptoticallySublinear.of_nonneg_le
  · exact correction.expectedMixedSlack_nonneg initial selection
  · exact
      correction.expectedMixedSlack_le
        span processed initial selection source_compatible
  · exact
      IsAsymptoticallySublinear.const
        (2 * finiteStatePotentialBound correction.combinedPotential)

omit [DecidableEq G.State] in
/-- Integrated-ledger form: the cumulative sum of nonnegative expected
one-stage correction slacks is asymptotically sublinear. -/
theorem
    HarmonicInvisibleQuotientCorrection.mixedSlackStageLedger_sublinear
    {jet : germ.LowerValueJet} {who : ι}
    {family : jet.InvisibleNeutralQuotientFamily who}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (correction :
      jet.HarmonicInvisibleQuotientCorrection who family)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n)) :
    IsAsymptoticallySublinear
      (fun T =>
        ∑ t ∈ Finset.range T,
          correction.expectedMixedSlackStage initial selection t) := by
  simpa only [
    correction.sum_expectedMixedSlackStage_eq initial selection] using
      correction.expectedMixedSlack_sublinear
        span processed initial selection source_compatible

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
