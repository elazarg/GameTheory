/-
# EXP-119: hybrid unilateral infinite-policy Kuhn

This two-player perfect-monitoring stochastic game has countably infinite
public histories. One player's total-policy law correlates two distinct
history coordinates, while the other can make an off-baseline behavioral
deviation. The two consumers keep the opponents genuinely present and exercise
both heterogeneous unilateral quantifiers.
-/

import GameTheory.Stochastic.Kuhn

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
  transition _ actions := FinDist.pure (actions false)
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

/-- A noninitial public-history coordinate. -/
def laterInfo : hybridGame.PublicHistory :=
  [⟨false, fun _ => false, false⟩]

/-- Independent fair choices at every information state. -/
def fairProtocolBehavioral (i : Bool) :
    (hybridGame.perfectMonitoring false).BehavioralPolicy i :=
  fun _ => FinDist.uniformOfFintype

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
    IsProbabilityMeasure (correlatedPolicyMeasure i) :=
  Measure.isProbabilityMeasure_map
    (correlateFirstTwo_measurable i).aemeasurable

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
  fun _ _ => FinDist.pure false

/-- The focal player deviates to the action excluded by the baseline support
at every public history. -/
def trueDeviation : hybridGame.PublicPolicy false :=
  fun _ => FinDist.pure true

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
      false arbitraryOpponentLaws falseFallback false trueDeviation

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
      false falseBehavioral false (correlatedPolicyMeasure false)
        (falseFallback false)

theorem stageUtility_abs_le_one (state : Bool)
    (actions : ∀ _ : Bool, Bool) (who : Bool) :
    |hybridGame.stageUtility state actions who| ≤ 1 := by
  rw [show hybridGame.stageUtility state actions who =
      (if actions who then 1 else 0) by rfl]
  split <;> norm_num

/-- The behavioral focal deviation remains unchanged through the discounted
hybrid correspondence. -/
theorem behavioral_deviation_discounted_consumer :
    Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        hybridGame.arbitraryPolicyMeasureStageExpectation false
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            arbitraryOpponentLaws false
              (hybridGame.toBehavioralPolicy false
                trueDeviation).toPureMeasure)
          false time) ∧
      hybridGame.arbitraryPolicyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            arbitraryOpponentLaws false
              (hybridGame.toBehavioralPolicy false
                trueDeviation).toPureMeasure)
          false =
        hybridGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update
            (hybridGame.policyMeasuresToPublicBehavioralWith false
              arbitraryOpponentLaws falseFallback)
            false trueDeviation) false := by
  apply hybridGame.kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_discountedPayoff
      false (discount := (2 : ℝ)⁻¹) (bound := 1)
      (laws := arbitraryOpponentLaws) (fallback := falseFallback)
      (who := false) (replacement := trueDeviation)
  · norm_num
  · norm_num
  · exact fun state actions => stageUtility_abs_le_one state actions false

/-- The arbitrary correlated focal measure remains unchanged through the
reverse discounted hybrid correspondence. -/
theorem policy_measure_deviation_discounted_consumer :
    Summable (fun time => (2 : ℝ)⁻¹ ^ time *
        hybridGame.arbitraryPolicyMeasureStageExpectation false
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            (fun i => (hybridGame.toBehavioralPolicy false
              (falseBehavioral i)).toPureMeasure)
            false (correlatedPolicyMeasure false)) false time) ∧
      hybridGame.arbitraryPolicyMeasureDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update
            (sig := (hybridGame.perfectMonitoring false).policyMeasureSignature)
            (fun i => (hybridGame.toBehavioralPolicy false
              (falseBehavioral i)).toPureMeasure)
            false (correlatedPolicyMeasure false)) false =
        hybridGame.behavioralDiscountedPayoff false (2 : ℝ)⁻¹
          (Profile.update falseBehavioral false
            (hybridGame.ofBehavioralPolicy false
              (InformationModel.PolicyMeasure.toBehavioralWith
                (M := hybridGame.perfectMonitoring false)
                (correlatedPolicyMeasure false)
                ((hybridGame.purePolicyEquiv false false).symm
                  (falseFallback false))))) false := by
  apply hybridGame.kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_discountedPayoff
      false (discount := (2 : ℝ)⁻¹) (bound := 1)
      (behavioral := falseBehavioral) (who := false)
      (replacement := correlatedPolicyMeasure false)
      (replacementFallback := falseFallback false)
  · norm_num
  · norm_num
  · exact fun state actions => stageUtility_abs_le_one state actions false

end GameTheory.Experimental.PostArchitecture.StochasticHybridInfiniteKuhn
