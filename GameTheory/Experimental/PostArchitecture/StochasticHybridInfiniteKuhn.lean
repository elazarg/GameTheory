/-
# EXP-119: hybrid unilateral infinite-policy Kuhn

This two-player perfect-monitoring stochastic game has countably infinite
public histories. One player's total-policy law correlates two distinct
history coordinates, while the other can make an off-baseline behavioral
deviation. The two consumers keep the opponents genuinely present and exercise
both heterogeneous unilateral quantifiers.
-/

import GameTheory.Stochastic.Kuhn
import GameTheory.Protocol.Predraw

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticHybridInfiniteKuhn

open GameTheory.Math.Probability GameTheory.Protocol MeasureTheory
open GameTheory.Stochastic GameTheory.Stochastic.Game

/-- Player `false` controls the next public state; both players receive an
action-dependent stage utility. -/
@[reducible]
def hybridGame : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition _ actions := PMF.pure (actions false)
  stageUtility _ actions who := if actions who then 1 else 0

local instance canonicalHistoryMeasurableSpace :
    MeasurableSpace (hybridGame.toExecution false).History := ⊤

local instance actionNonempty :
    ∀ i, Nonempty (hybridGame.Action i) := fun _ => ⟨false⟩

local instance actionFintype :
    ∀ i, Fintype (hybridGame.Action i) := fun _ => inferInstance

local instance choiceMeasurableSpace :
    ∀ i info, MeasurableSpace
      ((hybridGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => ⊤

local instance choiceDiscreteMeasurableSpace :
    ∀ i info, DiscreteMeasurableSpace
      ((hybridGame.perfectMonitoring false).Choice i info) :=
  fun _ _ => ⟨fun _ => MeasurableSet.of_discrete⟩

local instance choiceFintype :
    ∀ i info, Fintype
      ((hybridGame.perfectMonitoring false).Choice i info) :=
  fun i info => Fintype.ofEquiv Bool
    (hybridGame.actionChoiceEquiv false i info)

local instance choiceNonempty :
    ∀ i info, Nonempty
      ((hybridGame.perfectMonitoring false).Choice i info) :=
  fun i info => Nonempty.map
    (hybridGame.actionChoiceEquiv false i info) inferInstance

theorem boundedSitesFinite (horizon : ℕ) :
    ∀ i, (hybridGame.boundedInformationSites false horizon i).Finite := by
  intro i
  let M := hybridGame.perfectMonitoring false
  exact M.behavioralSupportSitesFrom_finite_of_finite_branching
    (hybridGame.fullyMixedBehaviorProfile false) horizon
    (hybridGame.toExecution false).initHistory
    (fun _ _ _ => Set.toFinite _) (fun _ => Set.toFinite _) i

/-- A noninitial public-history coordinate. -/
def laterInfo : hybridGame.PublicHistory :=
  [⟨false, fun _ => false, false⟩]

/-- Independent fair choices at every information state. -/
def fairProtocolBehavioral (i : Bool) :
    (hybridGame.perfectMonitoring false).BehavioralPolicy i :=
  fun info => PMF.uniformOfFintype
    ((hybridGame.perfectMonitoring false).Choice i info)

/-- Force one player's choices at the initial and `laterInfo` coordinates to
agree, retaining all other infinitely many coordinates. -/
def correlateFirstTwo (i : Bool)
    (policy : (hybridGame.perfectMonitoring false).Policy i) :
    (hybridGame.perfectMonitoring false).Policy i := by
  classical
  intro info
  by_cases hinfo : info = laterInfo
  · subst info
    exact hybridGame.actionChoiceEquiv false i laterInfo
      ((hybridGame.actionChoiceEquiv false i []).symm (policy []))
  · exact policy info

@[simp]
theorem correlateFirstTwo_later (i : Bool)
    (policy : (hybridGame.perfectMonitoring false).Policy i) :
    correlateFirstTwo i policy laterInfo =
      hybridGame.actionChoiceEquiv false i laterInfo
        ((hybridGame.actionChoiceEquiv false i []).symm (policy [])) := by
  simp [correlateFirstTwo]

theorem correlateFirstTwo_of_ne (i : Bool)
    (policy : (hybridGame.perfectMonitoring false).Policy i)
    {info : hybridGame.PublicHistory} (hinfo : info ≠ laterInfo) :
    correlateFirstTwo i policy info = policy info := by
  simp [correlateFirstTwo, hinfo]

theorem correlateFirstTwo_measurable (i : Bool) :
    Measurable (correlateFirstTwo i) := by
  rw [measurable_pi_iff]
  intro info
  by_cases hinfo : info = laterInfo
  · subst info
    simp_rw [correlateFirstTwo_later]
    exact (measurable_of_finite fun choice =>
      hybridGame.actionChoiceEquiv false i laterInfo
        ((hybridGame.actionChoiceEquiv false i []).symm choice)).comp
      (measurable_pi_apply [])
  · simp_rw [correlateFirstTwo_of_ne i _ hinfo]
    exact measurable_pi_apply info

/-- A genuine within-policy correlated law for either player. -/
def correlatedPolicyMeasure (i : Bool) :
    hybridGame.ProtocolPolicyMeasure false i :=
  (fairProtocolBehavioral i).toPureMeasure.map (correlateFirstTwo i)

local instance fairProtocolBehavioral_isProbability (i : Bool) :
    IsProbabilityMeasure (fairProtocolBehavioral i).toPureMeasure :=
  InformationModel.BehavioralPolicy.toPureMeasure_isProbability
    (M := hybridGame.perfectMonitoring false) (fairProtocolBehavioral i)

local instance correlatedPolicyMeasure_isProbability (i : Bool) :
    IsProbabilityMeasure (correlatedPolicyMeasure i) := by
  unfold correlatedPolicyMeasure
  infer_instance

/-- The opponent `true` uses the correlated law; the focal player starts from
an independent fair law before being replaced behaviorally. -/
def arbitraryOpponentLaws :
    hybridGame.ProtocolPolicyMeasureProfile false
  | false => (fairProtocolBehavioral false).toPureMeasure
  | true => correlatedPolicyMeasure true

local instance arbitraryOpponentLaws_isProbability :
    ∀ i, IsProbabilityMeasure (arbitraryOpponentLaws i) := by
  intro i
  cases i with
  | false =>
      simpa only [arbitraryOpponentLaws] using
        (inferInstanceAs (IsProbabilityMeasure
          (fairProtocolBehavioral false).toPureMeasure))
  | true =>
      simpa only [arbitraryOpponentLaws] using
        (inferInstanceAs
          (IsProbabilityMeasure (correlatedPolicyMeasure true)))

def falseFallback : hybridGame.PurePublicProfile := fun _ _ => false

def falseBehavioral : hybridGame.PublicProfile false :=
  fun _ _ => PMF.pure false

/-- The focal player deviates to the action excluded by the baseline support
at every public history. -/
def trueDeviation : hybridGame.PublicPolicy false :=
  fun _ => PMF.pure true

/-- Arbitrary total-plan-law opponents plus an unchanged behavioral focal
deviation consume the first heterogeneous quantifier. -/
theorem behavioral_deviation_consumer :
    ∀ horizon,
      hybridGame.protocolPolicyMeasureRun false
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            arbitraryOpponentLaws false
              (hybridGame.toBehavioralPolicy false
                trueDeviation).toPureMeasure) horizon =
        ((hybridGame.publicHorizonForm false horizon).play
          (Profile.update
            (hybridGame.policyMeasuresToPublicBehavioralWith false
              arbitraryOpponentLaws falseFallback)
            false trueDeviation)).toMeasure :=
  hybridGame.kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_allFinitePrefixes
      false arbitraryOpponentLaws falseFallback false
      trueDeviation

/-- Behavioral opponents plus an unchanged arbitrary correlated focal law
consume the reverse heterogeneous quantifier. -/
theorem policy_measure_deviation_consumer :
    ∀ horizon,
      hybridGame.protocolPolicyMeasureRun false
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            (fun i => (hybridGame.toBehavioralPolicy false
              (falseBehavioral i)).toPureMeasure)
            false (correlatedPolicyMeasure false)) horizon =
        ((hybridGame.publicHorizonForm false horizon).play
          (Profile.update falseBehavioral false
            (hybridGame.ofBehavioralPolicy false
              (InformationModel.PolicyMeasure.toBehavioralWith
                (M := hybridGame.perfectMonitoring false)
                (correlatedPolicyMeasure false)
                ((hybridGame.purePolicyEquiv false false).symm
                  (falseFallback false)))))).toMeasure :=
  hybridGame.kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_allFinitePrefixes
      false falseBehavioral false
      (correlatedPolicyMeasure false)
        (falseFallback false)

theorem stageUtility_abs_le_one (state : Bool)
    (actions : ∀ _ : Bool, Bool) (who : Bool) :
    |hybridGame.stageUtility state actions who| ≤ 1 := by
  rw [show hybridGame.stageUtility state actions who =
      (if actions who then 1 else 0) by rfl]
  split <;> norm_num

def behavioralDeviationLaws : hybridGame.ProtocolPolicyMeasureProfile false :=
  Profile.update
    (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
    arbitraryOpponentLaws false
    (hybridGame.toBehavioralPolicy false trueDeviation).toPureMeasure

def behavioralDeviationProfile : hybridGame.PublicProfile false :=
  Profile.update
    (hybridGame.policyMeasuresToPublicBehavioralWith false
      arbitraryOpponentLaws falseFallback)
    false trueDeviation

def policyMeasureDeviationLaws : hybridGame.ProtocolPolicyMeasureProfile false :=
  Profile.update
    (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
    (fun i => (hybridGame.toBehavioralPolicy false
      (falseBehavioral i)).toPureMeasure)
    false (correlatedPolicyMeasure false)

def policyMeasureDeviationProfile : hybridGame.PublicProfile false :=
  Profile.update falseBehavioral false
    (hybridGame.ofBehavioralPolicy false
      (InformationModel.PolicyMeasure.toBehavioralWith
        (M := hybridGame.perfectMonitoring false)
        (correlatedPolicyMeasure false)
        ((hybridGame.purePolicyEquiv false false).symm
          (falseFallback false))))

local instance behavioralDeviationLaws_isProbability (i : Bool) :
    IsProbabilityMeasure (behavioralDeviationLaws i) := by
  cases i with
  | false =>
      simpa [behavioralDeviationLaws] using
        (InformationModel.BehavioralPolicy.toPureMeasure_isProbability
          (M := hybridGame.perfectMonitoring false)
          (hybridGame.toBehavioralPolicy false trueDeviation))
  | true =>
      simpa [behavioralDeviationLaws] using
        (inferInstanceAs (IsProbabilityMeasure (arbitraryOpponentLaws true)))

local instance policyMeasureDeviationLaws_isProbability (i : Bool) :
    IsProbabilityMeasure (policyMeasureDeviationLaws i) := by
  cases i with
  | false =>
      simpa [policyMeasureDeviationLaws] using
        (inferInstanceAs (IsProbabilityMeasure (correlatedPolicyMeasure false)))
  | true =>
      simpa [policyMeasureDeviationLaws] using
        (InformationModel.BehavioralPolicy.toPureMeasure_isProbability
          (M := hybridGame.perfectMonitoring false)
          (hybridGame.toBehavioralPolicy false (falseBehavioral true)))

/-- The behavioral focal deviation remains unchanged through the discounted
hybrid correspondence. -/
theorem behavioral_deviation_discounted_consumer :
    ∃ hbehavioral : ∀ time, PayoffIntegrable
        ((hybridGame.perfectMonitoring false).runBehavioral
          (hybridGame.toBehaviorProfile false behavioralDeviationProfile)
          (time + 1)) (hybridGame.latestStageUtility false false),
      ∃ hsumBehavioral : Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        hybridGame.behavioralStageExpectation false
          behavioralDeviationProfile false time (hbehavioral time)),
      ∃ hmeasure : ∀ time, Integrable
          (hybridGame.latestStageUtility false false)
          ((hybridGame.perfectMonitoring false).runPolicyMeasure
            behavioralDeviationLaws (time + 1)),
        ∃ hsumMeasure : Summable (fun time => (2 : ℝ)⁻¹ ^ time *
          hybridGame.arbitraryPolicyMeasureStageExpectation false
            behavioralDeviationLaws false time (hmeasure time)),
          hybridGame.arbitraryPolicyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
              behavioralDeviationLaws false hmeasure hsumMeasure =
            hybridGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
              behavioralDeviationProfile false hbehavioral hsumBehavioral := by
  let hbound : ∀ state actions,
      |hybridGame.stageUtility state actions false| ≤ 1 :=
    fun state actions => stageUtility_abs_le_one state actions false
  let hbehavioral := fun time =>
    hybridGame.behavioralStageIntegrable_of_bounded false
      behavioralDeviationProfile false 1 hbound time
  let hsumBehavioral :=
    hybridGame.summable_discounted_behavioralStageExpectation false
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
      behavioralDeviationProfile false hbound
  obtain ⟨hmeasure, hsumMeasure, heq⟩ :=
    hybridGame.kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_discountedPayoff
      false arbitraryOpponentLaws falseFallback false trueDeviation
      (2 : ℝ)⁻¹ hbehavioral hsumBehavioral
  exact ⟨hbehavioral, hsumBehavioral, hmeasure, hsumMeasure, heq⟩

/-- The arbitrary correlated focal measure remains unchanged through the
reverse discounted hybrid correspondence. -/
theorem policy_measure_deviation_discounted_consumer :
    ∃ hbehavioral : ∀ time, PayoffIntegrable
        ((hybridGame.perfectMonitoring false).runBehavioral
          (hybridGame.toBehaviorProfile false policyMeasureDeviationProfile)
          (time + 1)) (hybridGame.latestStageUtility false false),
      ∃ hsumBehavioral : Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        hybridGame.behavioralStageExpectation false
          policyMeasureDeviationProfile false time (hbehavioral time)),
      ∃ hmeasure : ∀ time, Integrable
          (hybridGame.latestStageUtility false false)
          ((hybridGame.perfectMonitoring false).runPolicyMeasure
            policyMeasureDeviationLaws (time + 1)),
        ∃ hsumMeasure : Summable (fun time => (2 : ℝ)⁻¹ ^ time *
          hybridGame.arbitraryPolicyMeasureStageExpectation false
            policyMeasureDeviationLaws false time (hmeasure time)),
          hybridGame.arbitraryPolicyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
              policyMeasureDeviationLaws false hmeasure hsumMeasure =
            hybridGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
              policyMeasureDeviationProfile false hbehavioral hsumBehavioral := by
  let hbound : ∀ state actions,
      |hybridGame.stageUtility state actions false| ≤ 1 :=
    fun state actions => stageUtility_abs_le_one state actions false
  let hbehavioral := fun time =>
    hybridGame.behavioralStageIntegrable_of_bounded false
      policyMeasureDeviationProfile false 1 hbound time
  let hsumBehavioral :=
    hybridGame.summable_discounted_behavioralStageExpectation false
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
      policyMeasureDeviationProfile false hbound
  obtain ⟨hmeasure, hsumMeasure, heq⟩ :=
    hybridGame.kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_discountedPayoff
      false falseBehavioral false (correlatedPolicyMeasure false)
      (falseFallback false) (2 : ℝ)⁻¹ hbehavioral hsumBehavioral
  exact ⟨hbehavioral, hsumBehavioral, hmeasure, hsumMeasure, heq⟩

end GameTheory.Experimental.PostArchitecture.StochasticHybridInfiniteKuhn
