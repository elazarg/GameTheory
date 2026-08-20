/-
# Bounded Kuhn correspondence for perfect-monitoring stochastic games

Finite-action stochastic play has an infinite public-history carrier but only
finitely many counterfactual prefixes through a fixed horizon.  This module
constructs those sites from one fully supported canonical Protocol run and
specializes the finite-site Kuhn API without defining another evaluator.
-/

import GameTheory.Stochastic.History
import GameTheory.Core.Transform
import GameTheory.Protocol.PolicyMeasure

noncomputable section

namespace GameTheory.Stochastic

open GameTheory.Math.Probability MeasureTheory Protocol

universe uι us ua uo

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- A deterministic stochastic policy chooses one ordinary action after each
proof-free public history. -/
abbrev PurePublicPolicy (i : ι) := G.PublicHistory → G.Action i

/-- Profiles of deterministic proof-free public policies. -/
abbrev PurePublicProfile := (i : ι) → G.PurePublicPolicy i

/-- A mixed proof-free public policy draws one total public policy once. -/
abbrev MixedPublicPolicy (i : ι) := FinDist (G.PurePublicPolicy i)

/-- Mixed profiles draw one total deterministic public policy per player. -/
abbrev MixedPublicProfile := (i : ι) → G.MixedPublicPolicy i

/-- Protocol's certified deterministic policy and an ordinary stochastic
public policy carry exactly the same action data. -/
def purePolicyEquiv (initial : G.State) [∀ i, Nonempty (G.Action i)] (i : ι) :
    (G.perfectMonitoring initial).Policy i ≃ G.PurePublicPolicy i where
  toFun policy history :=
    (G.actionChoiceEquiv initial i history).symm (policy history)
  invFun policy history :=
    G.actionChoiceEquiv initial i history (policy history)
  left_inv policy := by
    funext history
    exact (G.actionChoiceEquiv initial i history).apply_symm_apply
      (policy history)
  right_inv policy := by
    funext history
    exact (G.actionChoiceEquiv initial i history).symm_apply_apply
      (policy history)

variable [Fintype ι]

/-- The pure public-policy horizon form is Protocol's deterministic compiler
with only its strategy carrier relabeled. -/
@[reducible]
def pureHorizonForm (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) : GameForm ι :=
  ((G.perfectMonitoring initial).toGameForm horizon).relabelStrategies
    (G.purePolicyEquiv initial)

/-- The behavioral public-policy horizon form is the existing stochastic
horizon form with its proof-free policy presentation exposed. -/
@[reducible]
def publicHorizonForm (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) : GameForm ι :=
  (G.horizonForm initial horizon).relabelStrategies
    (fun i => (G.policyEquiv initial i).symm)

@[simp]
theorem publicHorizonForm_play (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ)
    (profile : G.PublicProfile initial) :
    (G.publicHorizonForm initial horizon).play profile =
      (G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial profile) horizon :=
  rfl

namespace MixedPublicPolicy

/-- Read one mixed proof-free public policy as its conditional behavioral
policy at every public history. -/
def toBehavioral (initial : G.State) [∀ i, Nonempty (G.Action i)] {i : ι}
    (mixed : G.MixedPublicPolicy i) : G.PublicPolicy i :=
  G.ofBehavioralPolicy initial
    (InformationModel.MixedPolicy.toBehavioral
      (M := G.perfectMonitoring initial)
      (FinDist.map (G.purePolicyEquiv initial i).symm mixed))

end MixedPublicPolicy

namespace MixedPublicProfile

/-- Read a mixed public-policy profile behaviorally through Protocol's
conditional construction, then erase only its legal-choice certificates. -/
def toBehavioral (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (mixed : G.MixedPublicProfile) : G.PublicProfile initial :=
  fun i => MixedPublicPolicy.toBehavioral G initial (mixed i)

omit [Fintype ι] in
@[simp]
theorem toBehaviorProfile_toBehavioral (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (mixed : G.MixedPublicProfile) :
    G.toBehaviorProfile initial (toBehavioral G initial mixed) =
      fun i => InformationModel.MixedPolicy.toBehavioral
        (M := G.perfectMonitoring initial)
        (FinDist.map (G.purePolicyEquiv initial i).symm (mixed i)) := by
  funext i
  exact G.toBehavioralPolicy_ofBehavioralPolicy initial _

end MixedPublicProfile

/-- **Bounded stochastic mixed-to-behavioral Kuhn.** Perfect monitoring makes
the canonical conditional behavioral reading preserve every bounded history
law. -/
theorem kuhn_mixed_to_behavioral (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (mixed : G.MixedPublicProfile)
    (horizon : ℕ) :
    (G.publicHorizonForm initial horizon).play
        (MixedPublicProfile.toBehavioral G initial mixed) =
      ((G.pureHorizonForm initial horizon).mixed).play mixed := by
  rw [G.publicHorizonForm_play,
    MixedPublicProfile.toBehaviorProfile_toBehavioral,
    GameTheory.mixed_relabelStrategies_play]
  exact ((G.perfectMonitoring initial).runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall
      (G.perfectMonitoring_perfectRecall initial)) horizon
    (fun i => FinDist.map (G.purePolicyEquiv initial i).symm
      (mixed i))).symm

section FiniteActions

variable [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- A proof-free behavioral profile assigning positive mass to every action at
every public history. -/
def fullyMixedPublicProfile (initial : G.State) : G.PublicProfile initial :=
  fun _ _ => FinDist.uniformOfFintype

/-- The canonical Protocol presentation of the fully supported public profile. -/
def fullyMixedBehaviorProfile (initial : G.State) : G.BehaviorProfile initial :=
  G.toBehaviorProfile initial (G.fullyMixedPublicProfile initial)

omit [Fintype ι] in
theorem fullyMixedBehaviorProfile_mem_support (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i)
    (choice : (G.perfectMonitoring initial).Choice i info) :
    choice ∈
      (G.fullyMixedBehaviorProfile initial i info).support := by
  unfold fullyMixedBehaviorProfile toBehaviorProfile toBehavioralPolicy
    fullyMixedPublicProfile
  rw [FinDist.support_map]
  refine ⟨(G.actionChoiceEquiv initial i info).symm choice,
    FinDist.mem_support_uniformOfFintype _, ?_⟩
  exact (G.actionChoiceEquiv initial i info).apply_symm_apply choice

/-- The finite information sites visited by the fully supported canonical run
at any elapsed time through `horizon`. -/
def boundedInformationSites (initial : G.State) (horizon : ℕ)
    (i : ι) : Finset ((G.perfectMonitoring initial).InfoState i) :=
  InformationModel.behavioralSupportSitesFrom
    (G.perfectMonitoring initial) (G.fullyMixedBehaviorProfile initial)
    horizon (G.toExecution initial).initHistory i

/-- These sites cover every legal counterfactual prefix through the selected
horizon, including histories omitted by a baseline profile's support. -/
theorem boundedInformationSites_cover (initial : G.State) (horizon : ℕ) :
    (G.perfectMonitoring initial).CoversInformationSites
      (G.boundedInformationSites initial horizon) horizon :=
  InformationModel.behavioralSupportSitesFrom_covers_of_fullSupport
    (G.perfectMonitoring initial) (G.fullyMixedBehaviorProfile initial)
    horizon (G.toExecution initial).initHistory
    (G.fullyMixedBehaviorProfile_mem_support initial)

namespace PublicPolicy

/-- Select one ordinary action from every local behavioral support. -/
def supportFallback {i : ι} (policy : G.PublicPolicy i) :
    G.PurePublicPolicy i :=
  fun history => (policy history).support_nonempty.choose

/-- Predraw a public behavioral policy on every counterfactual information
site through one fixed horizon. -/
def toMixed (initial : G.State) (horizon : ℕ) {i : ι}
    (policy : G.PublicPolicy i) : FinDist (G.PurePublicPolicy i) :=
  let protocolPolicy := G.toBehavioralPolicy initial policy
  let fallback := (G.purePolicyEquiv initial i).symm policy.supportFallback
  FinDist.map (G.purePolicyEquiv initial i)
    (protocolPolicy.toMixedWithin
      (G.boundedInformationSites initial horizon i) fallback)

theorem map_symm_toMixed (initial : G.State) (horizon : ℕ) {i : ι}
    (policy : G.PublicPolicy i) :
    FinDist.map (G.purePolicyEquiv initial i).symm
        (toMixed G initial horizon policy) =
      (G.toBehavioralPolicy initial policy).toMixedWithin
        (G.boundedInformationSites initial horizon i)
        ((G.purePolicyEquiv initial i).symm policy.supportFallback) := by
  rw [toMixed, FinDist.map_comp]
  have hcomp :
      (G.purePolicyEquiv initial i).symm ∘
          G.purePolicyEquiv initial i = id := by
    funext protocolPolicy
    exact (G.purePolicyEquiv initial i).symm_apply_apply protocolPolicy
  rw [hcomp, FinDist.map_id]

end PublicPolicy

/-- **Bounded stochastic behavioral-to-mixed Kuhn.** One fixed mixed public
profile predraws every counterfactual public history through the horizon, while
the ambient `List StageRecord` carrier remains infinite. -/
theorem kuhn_behavioral_to_mixed (initial : G.State)
    (behavioral : G.PublicProfile initial) (horizon : ℕ) :
    ((G.pureHorizonForm initial horizon).mixed).play
        (fun i => PublicPolicy.toMixed G initial horizon (behavioral i)) =
      (G.publicHorizonForm initial horizon).play behavioral := by
  rw [GameTheory.mixed_relabelStrategies_play]
  simp_rw [PublicPolicy.map_symm_toMixed]
  exact (G.perfectMonitoring initial).runMixed_toMixedWithin
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (G.boundedInformationSites initial horizon)
    (G.toBehaviorProfile initial behavioral)
    (fun i => (G.purePolicyEquiv initial i).symm
      (behavioral i).supportFallback)
    horizon (G.boundedInformationSites_cover initial horizon)

/-! ## One pure-policy law for every finite prefix -/

/-- Finite perfect-monitoring choices use their canonical discrete sigma
algebra in the regular-probability layer. -/
instance perfectMonitoringChoiceMeasurableSpace (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i) :
    MeasurableSpace ((G.perfectMonitoring initial).Choice i info) := ⊤

instance perfectMonitoringChoiceDiscreteMeasurableSpace (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i) :
    DiscreteMeasurableSpace
      ((G.perfectMonitoring initial).Choice i info) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

instance perfectMonitoringChoiceTopologicalSpace (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i) :
    TopologicalSpace ((G.perfectMonitoring initial).Choice i info) := ⊥

instance perfectMonitoringChoiceDiscreteTopology (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i) :
    DiscreteTopology ((G.perfectMonitoring initial).Choice i info) :=
  discreteTopology_bot _

/-- A perfect-monitoring choice is the finite menu subtype, enumerated without
recovering a global finiteness capability. -/
instance perfectMonitoringChoiceFintype (initial : G.State)
    (i : ι) (info : (G.perfectMonitoring initial).InfoState i) :
    Fintype ((G.perfectMonitoring initial).Choice i info) :=
  Fintype.ofEquiv (G.Action i) (G.actionChoiceEquiv initial i info)

/-- The regular-probability layer underlying a public behavioral profile.  It
is one product measure over total Protocol policies; unlike `PublicPolicy.toMixed`,
it has no horizon argument. -/
def protocolPureProfileMeasure (initial : G.State)
    (behavioral : G.PublicProfile initial) :
    Measure ((i : ι) → (G.perfectMonitoring initial).Policy i) :=
  (G.perfectMonitoring initial).behavioralProfileMeasure
    (G.toBehaviorProfile initial behavioral)

instance protocolPureProfileMeasure_isProbability (initial : G.State)
    (behavioral : G.PublicProfile initial) :
    IsProbabilityMeasure
      (G.protocolPureProfileMeasure initial behavioral) := by
  unfold protocolPureProfileMeasure
  infer_instance

/-- For countable state spaces, the single total-policy profile law is a
regular probability measure. Finite stochastic games are the principal case. -/
theorem protocolPureProfileMeasure_regular (initial : G.State)
    [Countable G.State] (behavioral : G.PublicProfile initial) :
    Measure.Regular (G.protocolPureProfileMeasure initial behavioral) := by
  letI : Countable G.StageRecord :=
    (show Function.Injective
        (fun record : G.StageRecord =>
          (record.source, record.joint, record.target)) by
      intro first second hequal
      cases first
      cases second
      simp_all).countable
  letI : Countable G.PublicHistory := inferInstance
  letI (i : ι) : Countable
      ((G.perfectMonitoring initial).InfoState i) :=
    inferInstanceAs (Countable G.PublicHistory)
  unfold protocolPureProfileMeasure
  apply (G.perfectMonitoring initial).behavioralProfileMeasure_regular

/-- Draw once from `protocolPureProfileMeasure`, then feed that total pure
profile to the canonical Protocol runner for the requested prefix length. -/
def protocolPureRunMeasure (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (horizon : ℕ) :
    Measure (G.toExecution initial).History :=
  (G.perfectMonitoring initial).runPureMeasure
    (G.toBehaviorProfile initial behavioral) horizon

/-- **One-law-for-all-prefixes stochastic Kuhn.** The measure selected from a
behavioral public profile is independent of `horizon`, and integrating each
bounded canonical run against it reproduces the behavioral history law. -/
theorem kuhn_policyMeasure_allFinitePrefixes (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) :
    ∀ horizon,
      G.protocolPureRunMeasure initial behavioral horizon =
        ((G.publicHorizonForm initial horizon).play behavioral).toMeasure := by
  intro horizon
  unfold protocolPureRunMeasure
  rw [(G.perfectMonitoring initial).runPureMeasure_eq_runBehavioral
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (G.boundedInformationSites initial horizon)
    (G.toBehaviorProfile initial behavioral)
    (fun i => (G.purePolicyEquiv initial i).symm
      (behavioral i).supportFallback)
    horizon (G.boundedInformationSites_cover initial horizon)]
  rfl

/-- The utility of the most recent stochastic stage in a canonical prefix.
At horizon `time + 1` this is precisely the time-`time` stage utility; the
empty-history branch is an off-support totalization. -/
def latestStageUtility (initial : G.State) (who : ι)
    (history : (G.toExecution initial).History) : ℝ :=
  match G.publicHistoryOfTrace initial history.trace with
  | [] => 0
  | record :: _ => G.stageRecordUtility record who

/-- Expected time-`time` stage utility under behavioral play. -/
def behavioralStageExpectation (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (time : ℕ) : ℝ :=
  (G.perfectMonitoring initial).behavioralPrefixExpectation
    (G.toBehaviorProfile initial behavioral)
    (fun _ => G.latestStageUtility initial who) time

/-- Expected time-`time` stage utility after one ex-ante draw from the total
pure-policy profile measure. -/
def policyMeasureStageExpectation (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (time : ℕ) : ℝ :=
  (G.perfectMonitoring initial).pureMeasurePrefixExpectation
    (G.toBehaviorProfile initial behavioral)
    (fun _ => G.latestStageUtility initial who) time

/-- Normalized discounted behavioral payoff from the canonical finite-prefix
stage expectations. -/
def behavioralDiscountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (discount : ℝ) (behavioral : G.PublicProfile initial) (who : ι) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount
    (G.behavioralStageExpectation initial behavioral who)

/-- The corresponding normalized discounted payoff under the one total
pure-policy profile law. -/
def policyMeasureDiscountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (discount : ℝ) (behavioral : G.PublicProfile initial) (who : ι) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount
    (G.policyMeasureStageExpectation initial behavioral who)

omit [Fintype ι] [∀ i, Fintype (G.Action i)] in
theorem abs_latestStageUtility_le (initial : G.State) (who : ι)
    (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound)
    (history : (G.toExecution initial).History) :
    |G.latestStageUtility initial who history| ≤ bound := by
  unfold latestStageUtility
  split
  · have hnonneg := abs_nonneg
      (G.stageUtility initial (fun i => Classical.choice inferInstance) who)
    simpa only [abs_zero] using hnonneg.trans (hbound _ _)
  · exact hbound _ _

omit [∀ i, Fintype (G.Action i)] in
/-- A uniform stage bound also bounds each behavioral prefix expectation. -/
theorem abs_behavioralStageExpectation_le (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    |G.behavioralStageExpectation initial behavioral who time| ≤ bound := by
  unfold behavioralStageExpectation
    InformationModel.behavioralPrefixExpectation
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := ((G.perfectMonitoring initial).runBehavioral
      (G.toBehaviorProfile initial behavioral) (time + 1)).toMeasure)
    (f := G.latestStageUtility initial who) (C := bound)
    (Filter.Eventually.of_forall fun history => by
      simpa only [Real.norm_eq_abs] using
        G.abs_latestStageUtility_le initial who bound hbound history)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

omit [∀ i, Fintype (G.Action i)] in
/-- Bounded stochastic stage utility makes the behavioral discounted series
summable for every discount in `[0, 1)`. -/
theorem summable_discounted_behavioralStageExpectation
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable fun time => discount ^ time *
      G.behavioralStageExpectation initial behavioral who time := by
  have hgeom : Summable fun time : ℕ => bound * discount ^ time :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro time
  rw [Real.norm_eq_abs]
  calc
    |discount ^ time *
        G.behavioralStageExpectation initial behavioral who time| =
        discount ^ time *
          |G.behavioralStageExpectation initial behavioral who time| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 time)]
    _ ≤ discount ^ time * bound :=
      mul_le_mul_of_nonneg_left
        (G.abs_behavioralStageExpectation_le initial behavioral who bound
          hbound time)
        (pow_nonneg hdiscount0 time)
    _ = bound * discount ^ time := by ring

/-- **Discounted stochastic Kuhn.** Under the explicit boundedness and
discount hypotheses, the one regular-probability pure-policy construction has
the same normalized discounted payoff as behavioral play. -/
theorem kuhn_policyMeasure_discountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable (fun time => discount ^ time *
        G.policyMeasureStageExpectation initial behavioral who time) ∧
      G.policyMeasureDiscountedPayoff initial discount behavioral who =
        G.behavioralDiscountedPayoff initial discount behavioral who := by
  have hsummable := G.summable_discounted_behavioralStageExpectation
    initial hdiscount0 hdiscount1 behavioral who hbound
  have hresult :=
    (G.perfectMonitoring initial).normalizedDiscountedPureMeasure_eq_behavioral
      (G.perfectMonitoring_actsOnceWhereItMatters initial)
      (fun time => G.boundedInformationSites initial (time + 1))
      (G.toBehaviorProfile initial behavioral)
      (fun i => (G.purePolicyEquiv initial i).symm
        (behavioral i).supportFallback)
      (fun time => G.boundedInformationSites_cover initial (time + 1))
      (fun _ => G.latestStageUtility initial who) discount hsummable
  refine ⟨?_, ?_⟩
  · simpa only [policyMeasureStageExpectation] using hresult.1
  · unfold policyMeasureDiscountedPayoff behavioralDiscountedPayoff
    rw [show G.policyMeasureStageExpectation initial behavioral who =
        (G.perfectMonitoring initial).pureMeasurePrefixExpectation
          (G.toBehaviorProfile initial behavioral)
          (fun _ => G.latestStageUtility initial who) from rfl,
      show G.behavioralStageExpectation initial behavioral who =
        (G.perfectMonitoring initial).behavioralPrefixExpectation
          (G.toBehaviorProfile initial behavioral)
          (fun _ => G.latestStageUtility initial who) from rfl]
    exact hresult.2

section Unilateral

variable [DecidableEq ι]

/-- **Counterfactual bounded behavioral-to-mixed Kuhn.** An arbitrary mixed
deviation has the same law as its behavioral reading while every opponent
keeps the mixed public policy selected from the baseline behavioral profile.
The common finite site set covers off-path histories as well as the baseline
support. -/
theorem kuhn_behavioral_update_toMixed (initial : G.State)
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.MixedPublicPolicy who) (horizon : ℕ) :
    ((G.pureHorizonForm initial horizon).mixed).play
        (Profile.update
          (fun i => PublicPolicy.toMixed G initial horizon (behavioral i))
          who replacement) =
      (G.publicHorizonForm initial horizon).play
        (Profile.update behavioral who
          (MixedPublicPolicy.toBehavioral G initial replacement)) := by
  rw [GameTheory.mixed_relabelStrategies_play,
    G.publicHorizonForm_play,
    G.toBehaviorProfile_update]
  let protocolMixed : Profile
      (G.perfectMonitoring initial).strategicSignature.mixed :=
    fun i =>
      (G.toBehavioralPolicy initial (behavioral i)).toMixedWithin
        (G.boundedInformationSites initial horizon i)
        ((G.purePolicyEquiv initial i).symm
          (behavioral i).supportFallback)
  have hconverted :
      (fun i => FinDist.map (G.purePolicyEquiv initial i).symm
        ((Profile.update
          (sig := (G.pureHorizonForm initial horizon).sig.mixed)
          (fun i => PublicPolicy.toMixed G initial horizon (behavioral i))
          who replacement) i)) =
        Profile.update protocolMixed who
          (FinDist.map (G.purePolicyEquiv initial who).symm
            replacement) := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, Profile.update_same]
    · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi,
        PublicPolicy.map_symm_toMixed]
  rw [hconverted]
  have hreplacement :
      G.toBehavioralPolicy initial
          (MixedPublicPolicy.toBehavioral G initial replacement) =
        InformationModel.MixedPolicy.toBehavioral
          (M := G.perfectMonitoring initial)
          (FinDist.map (G.purePolicyEquiv initial who).symm
            replacement) :=
    G.toBehavioralPolicy_ofBehavioralPolicy initial _
  rw [hreplacement]
  exact (G.perfectMonitoring initial).kuhn_behavioral_update_toMixedWithin
    (G.perfectMonitoring_perfectRecall initial)
    (G.boundedInformationSites initial horizon) horizon
    (G.boundedInformationSites_cover initial horizon)
    (G.toBehaviorProfile initial behavioral)
    (fun i => (G.purePolicyEquiv initial i).symm
      (behavioral i).supportFallback)
    who (FinDist.map (G.purePolicyEquiv initial who).symm replacement)

/-- The single infinite product construction also commutes with an arbitrary
public behavioral deviation. The common counterfactual cover includes public
histories omitted by the baseline support. -/
theorem kuhn_policyMeasure_update_allFinitePrefixes (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.PublicPolicy who) :
    ∀ horizon,
      G.protocolPureRunMeasure initial
          (Profile.update behavioral who replacement) horizon =
        ((G.publicHorizonForm initial horizon).play
          (Profile.update behavioral who replacement)).toMeasure := by
  exact G.kuhn_policyMeasure_allFinitePrefixes initial
    (Profile.update behavioral who replacement)

/-- Discounted equality is stable under an arbitrary public behavioral
deviation, with the same bounded stage-utility hypothesis. -/
theorem kuhn_policyMeasure_update_discountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.PublicPolicy who)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable (fun time => discount ^ time *
        G.policyMeasureStageExpectation initial
          (Profile.update behavioral who replacement) who time) ∧
      G.policyMeasureDiscountedPayoff initial discount
          (Profile.update behavioral who replacement) who =
        G.behavioralDiscountedPayoff initial discount
          (Profile.update behavioral who replacement) who :=
  G.kuhn_policyMeasure_discountedPayoff initial hdiscount0 hdiscount1
    (Profile.update behavioral who replacement) who hbound

/-- **Counterfactual bounded mixed-to-behavioral Kuhn.** An arbitrary
behavioral deviation is realized by finite predrawing while every opponent
keeps the conditional behavioral reading of its original mixed public policy.
-/
theorem kuhn_mixed_update_toBehavioral (initial : G.State)
    (mixed : G.MixedPublicProfile) (who : ι)
    (replacement : G.PublicPolicy who) (horizon : ℕ) :
    (G.publicHorizonForm initial horizon).play
        (Profile.update
          (MixedPublicProfile.toBehavioral G initial mixed)
          who replacement) =
      ((G.pureHorizonForm initial horizon).mixed).play
        (Profile.update mixed who
          (PublicPolicy.toMixed G initial horizon replacement)) := by
  rw [G.publicHorizonForm_play,
    G.toBehaviorProfile_update,
    MixedPublicProfile.toBehaviorProfile_toBehavioral,
    GameTheory.mixed_relabelStrategies_play]
  let protocolMixed : Profile
      (G.perfectMonitoring initial).strategicSignature.mixed :=
    fun i => FinDist.map (G.purePolicyEquiv initial i).symm (mixed i)
  have hconverted :
      (fun i => FinDist.map (G.purePolicyEquiv initial i).symm
        ((Profile.update
          (sig := (G.pureHorizonForm initial horizon).sig.mixed) mixed who
          (PublicPolicy.toMixed G initial horizon replacement)) i)) =
        Profile.update protocolMixed who
          ((G.toBehavioralPolicy initial replacement).toMixedWithin
            (G.boundedInformationSites initial horizon who)
            ((G.purePolicyEquiv initial who).symm
              replacement.supportFallback)) := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, Profile.update_same,
        PublicPolicy.map_symm_toMixed]
    · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]
  rw [hconverted]
  exact (G.perfectMonitoring initial).kuhn_mixed_update_toBehavioralWithin
    (G.perfectMonitoring_perfectRecall initial)
    (G.boundedInformationSites initial horizon) horizon
    (G.boundedInformationSites_cover initial horizon) protocolMixed who
    (G.toBehavioralPolicy initial replacement)
    ((G.purePolicyEquiv initial who).symm replacement.supportFallback)

/-- A bounded behavioral Nash equilibrium becomes a mixed public-policy Nash
equilibrium by predrawing the common finite counterfactual site set. -/
theorem isNash_toMixed_of_isNash_behavioral (initial : G.State)
    (utility : (G.toExecution initial).History → ι → ℝ)
    (behavioral : G.PublicProfile initial) (horizon : ℕ)
    (hnash : IsNash (G.publicHorizonForm initial horizon)
      (euPreference utility) behavioral) :
    IsNash (G.pureHorizonForm initial horizon).mixed
      (euPreference utility)
      (fun i => PublicPolicy.toMixed G initial horizon (behavioral i)) := by
  rw [isNash_iff] at hnash ⊢
  intro who replacement
  rw [G.kuhn_behavioral_update_toMixed initial behavioral who
      replacement horizon,
    G.kuhn_behavioral_to_mixed initial behavioral horizon]
  exact hnash who
    (MixedPublicPolicy.toBehavioral G initial replacement)

/-- A bounded mixed public-policy Nash equilibrium becomes a behavioral Nash
equilibrium under the canonical conditional behavioral reading. -/
theorem isNash_toBehavioral_of_isNash_mixed (initial : G.State)
    (utility : (G.toExecution initial).History → ι → ℝ)
    (mixed : G.MixedPublicProfile) (horizon : ℕ)
    (hnash : IsNash (G.pureHorizonForm initial horizon).mixed
      (euPreference utility) mixed) :
    IsNash (G.publicHorizonForm initial horizon)
      (euPreference utility)
      (MixedPublicProfile.toBehavioral G initial mixed) := by
  rw [isNash_iff] at hnash ⊢
  intro who replacement
  rw [G.kuhn_mixed_update_toBehavioral initial mixed who replacement
      horizon,
    G.kuhn_mixed_to_behavioral initial mixed horizon]
  exact hnash who
    (PublicPolicy.toMixed G initial horizon replacement)

end Unilateral

/-- Behavioral and mixed proof-free public policies realize exactly the same
bounded canonical history laws. -/
theorem kuhn_historyLaws (initial : G.State) (horizon : ℕ) :
    { law | ∃ behavioral : G.PublicProfile initial,
        (G.publicHorizonForm initial horizon).play behavioral = law } =
      { law | ∃ mixed : G.MixedPublicProfile,
        ((G.pureHorizonForm initial horizon).mixed).play mixed = law } := by
  ext law
  constructor
  · rintro ⟨behavioral, rfl⟩
    exact ⟨fun i => PublicPolicy.toMixed G initial horizon (behavioral i),
      G.kuhn_behavioral_to_mixed initial behavioral horizon⟩
  · rintro ⟨mixed, rfl⟩
    exact ⟨MixedPublicProfile.toBehavioral G initial mixed,
      kuhn_mixed_to_behavioral G initial mixed horizon⟩

end FiniteActions

end Game

end GameTheory.Stochastic
