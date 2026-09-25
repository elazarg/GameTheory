/-
# Kuhn correspondence for perfect-monitoring stochastic games

Finite-action stochastic play may have infinitely many reachable public
histories at a fixed horizon when transitions have infinite support. Discrete
predrawing therefore takes an explicit finite-site certificate. The separate
policy-measure realization handles arbitrary bounded branching.
-/

import GameTheory.Stochastic.History
import GameTheory.Core.Transform
import GameTheory.Protocol.PolicyMeasure
import Mathlib.Probability.Distributions.Uniform

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
abbrev MixedPublicPolicy (i : ι) := PMF (G.PurePublicPolicy i)

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
      (PMF.map (G.purePolicyEquiv initial i).symm mixed))

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
        (PMF.map (G.purePolicyEquiv initial i).symm (mixed i)) := by
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
    (fun i => PMF.map (G.purePolicyEquiv initial i).symm
      (mixed i))).symm

section FiniteActions

variable [∀ i, Fintype (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- A proof-free behavioral profile assigning positive mass to every action at
every public history. -/
def fullyMixedPublicProfile (initial : G.State) : G.PublicProfile initial :=
  fun i _ => PMF.uniformOfFintype (G.Action i)

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
  rw [PMF.support_map]
  refine ⟨(G.actionChoiceEquiv initial i info).symm choice,
    PMF.mem_support_uniformOfFintype _, ?_⟩
  exact (G.actionChoiceEquiv initial i info).apply_symm_apply choice

/-- Information sites visited by the fully supported canonical run at some
elapsed time through `horizon`. This set need not be finite. -/
def boundedInformationSites (initial : G.State) (horizon : ℕ)
    (i : ι) : Set ((G.perfectMonitoring initial).InfoState i) :=
  InformationModel.behavioralSupportSitesFrom
    (G.perfectMonitoring initial) (G.fullyMixedBehaviorProfile initial)
    horizon (G.toExecution initial).initHistory i

/-- These sites cover every legal counterfactual prefix through the selected
horizon, including histories omitted by a baseline profile's support. -/
theorem boundedInformationSites_cover (initial : G.State) (horizon : ℕ) :
    ∀ later, (G.toExecution initial).ReachesWithin horizon
        (G.toExecution initial).initHistory later →
      ¬ (G.toExecution initial).terminal later.state → ∀ i,
        (G.perfectMonitoring initial).infoOf i later.trace ∈
          G.boundedInformationSites initial horizon i :=
  InformationModel.behavioralSupportSitesFrom_covers_of_fullSupport
    (G.perfectMonitoring initial) (G.fullyMixedBehaviorProfile initial)
    horizon (G.toExecution initial).initHistory
    (G.fullyMixedBehaviorProfile_mem_support initial)

/-- A finite cover certificate converts full-support reachability into the
finite site family needed by ordinary PMF predrawing. -/
theorem boundedInformationSites_finiteCover (initial : G.State) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite) :
    (G.perfectMonitoring initial).CoversInformationSites
      (fun i => (hfinite i).toFinset) horizon := by
  intro later hreach hterm i
  exact (Set.Finite.mem_toFinset (hfinite i)).2
    (G.boundedInformationSites_cover initial horizon later hreach hterm i)

namespace PublicPolicy

/-- Select one ordinary action from every local behavioral support. -/
def supportFallback {i : ι} (policy : G.PublicPolicy i) :
    G.PurePublicPolicy i :=
  fun history => (policy history).support_nonempty.choose

/-- Predraw a public behavioral policy on every counterfactual information
site through one fixed horizon. -/
def toMixed (initial : G.State) (horizon : ℕ) {i : ι}
    (policy : G.PublicPolicy i)
    (hfinite : (G.boundedInformationSites initial horizon i).Finite) :
    PMF (G.PurePublicPolicy i) :=
  let protocolPolicy := G.toBehavioralPolicy initial policy
  let fallback := (G.purePolicyEquiv initial i).symm policy.supportFallback
  PMF.map (G.purePolicyEquiv initial i)
    (protocolPolicy.toMixedWithin (G.perfectMonitoring initial)
      hfinite.toFinset fallback)

theorem map_symm_toMixed (initial : G.State) (horizon : ℕ) {i : ι}
    (policy : G.PublicPolicy i)
    (hfinite : (G.boundedInformationSites initial horizon i).Finite) :
    PMF.map (G.purePolicyEquiv initial i).symm
        (toMixed G initial horizon policy hfinite) =
      (G.toBehavioralPolicy initial policy).toMixedWithin
        (G.perfectMonitoring initial) hfinite.toFinset
        ((G.purePolicyEquiv initial i).symm policy.supportFallback) := by
  rw [toMixed, PMF.map_comp]
  have hcomp :
      (G.purePolicyEquiv initial i).symm ∘
          G.purePolicyEquiv initial i = id := by
    funext protocolPolicy
    exact (G.purePolicyEquiv initial i).symm_apply_apply protocolPolicy
  rw [hcomp, PMF.map_id]

end PublicPolicy

/-- **Bounded stochastic behavioral-to-mixed Kuhn.** One fixed mixed public
profile predraws every counterfactual public history through the horizon, while
the ambient `List StageRecord` carrier remains infinite. -/
theorem kuhn_behavioral_to_mixed (initial : G.State)
    (behavioral : G.PublicProfile initial) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite) :
    ((G.pureHorizonForm initial horizon).mixed).play
        (fun i => PublicPolicy.toMixed G initial horizon (behavioral i) (hfinite i)) =
      (G.publicHorizonForm initial horizon).play behavioral := by
  rw [GameTheory.mixed_relabelStrategies_play]
  simp_rw [PublicPolicy.map_symm_toMixed]
  exact (G.perfectMonitoring initial).runMixed_toMixedWithin
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (fun i => (hfinite i).toFinset)
    (G.toBehaviorProfile initial behavioral)
    (fun i => (G.purePolicyEquiv initial i).symm
      (behavioral i).supportFallback)
    horizon (G.boundedInformationSites_finiteCover initial horizon hfinite)

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
  let : Countable G.StageRecord :=
    (show Function.Injective
        (fun record : G.StageRecord =>
          (record.source, record.joint, record.target)) by
      intro first second hequal
      cases first
      cases second
      simp_all).countable
  let : Countable G.PublicHistory := inferInstance
  let (i : ι) : Countable
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
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) :
    ∀ horizon,
      G.protocolPureRunMeasure initial behavioral horizon =
        ((G.publicHorizonForm initial horizon).play behavioral).toMeasure := by
  intro horizon
  unfold protocolPureRunMeasure
  rw [(G.perfectMonitoring initial).runPureMeasure_eq_runBehavioral
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (G.toBehaviorProfile initial behavioral) horizon]
  rfl

/-! ## Arbitrary pure-policy measures read behaviorally -/

/-- A probability measure over one player's total certified public policy.
Unlike a PMF mixed policy, this measure may be nonatomic. -/
abbrev ProtocolPolicyMeasure (initial : G.State) (i : ι) :=
  (G.perfectMonitoring initial).PolicyMeasure i

/-- Independent arbitrary pure-policy laws, one per player. -/
abbrev ProtocolPolicyMeasureProfile (initial : G.State) :=
  (i : ι) → G.ProtocolPolicyMeasure initial i

/-- Read arbitrary certified pure-policy measures as an ordinary stochastic
behavioral profile. A proof-free pure profile supplies only zero-mass
fallback choices. -/
def policyMeasuresToPublicBehavioralWith (initial : G.State)
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile) : G.PublicProfile initial :=
  G.ofBehaviorProfile initial
    ((G.perfectMonitoring initial).policyMeasureBehavioralWith laws
      (fun i => (G.purePolicyEquiv initial i).symm (fallback i)))

/-- Draw independently from arbitrary total pure-policy measures and run the
canonical perfect-monitoring Protocol for a finite prefix. -/
def protocolPolicyMeasureRun (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial) (horizon : ℕ) :
    Measure (G.toExecution initial).History :=
  (G.perfectMonitoring initial).runPolicyMeasure laws horizon

/-- **Reverse one-law-for-all-prefixes stochastic Kuhn.** Every independent
profile of arbitrary pure-policy probability measures has one behavioral
conditional reading that reproduces all finite-prefix laws. The result needs
no regularity premise; regular laws are a supported special case. -/
theorem kuhn_arbitraryPolicyMeasure_allFinitePrefixes (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile) :
    ∀ horizon,
      G.protocolPolicyMeasureRun initial laws horizon =
        ((G.publicHorizonForm initial horizon).play
          (G.policyMeasuresToPublicBehavioralWith initial laws fallback)).toMeasure := by
  intro horizon
  unfold protocolPolicyMeasureRun
  rw [(G.perfectMonitoring initial).runPolicyMeasure_eq_runBehavioralWith
    (InformationModel.constrainsAlike_of_perfectRecall
      (G.perfectMonitoring_perfectRecall initial)) laws
    (fun i => (G.purePolicyEquiv initial i).symm (fallback i))
    horizon]
  rw [G.publicHorizonForm_play]
  congr 2
  exact (G.toBehaviorProfile_ofBehaviorProfile initial _).symm

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
    (behavioral : G.PublicProfile initial) (who : ι) (time : ℕ)
    (hintegrable : PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who)) : ℝ :=
  (G.perfectMonitoring initial).behavioralPrefixExpectation
    (G.toBehaviorProfile initial behavioral)
    (fun _ => G.latestStageUtility initial who) time hintegrable

/-- Expected time-`time` stage utility after one ex-ante draw from the total
pure-policy profile measure. -/
def policyMeasureStageExpectation (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (time : ℕ)
    (hintegrable : Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPureMeasure
        (G.toBehaviorProfile initial behavioral) (time + 1))) : ℝ :=
  (G.perfectMonitoring initial).pureMeasurePrefixExpectation
    (G.toBehaviorProfile initial behavioral)
    (fun _ => G.latestStageUtility initial who) time hintegrable

/-- Normalized discounted behavioral payoff from the canonical finite-prefix
stage expectations. -/
def behavioralDiscountedPayoff (initial : G.State)
    (discount : ℝ) (behavioral : G.PublicProfile initial) (who : ι)
    (hstage : ∀ time, PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who))
    (_hsum : Summable (fun time => discount ^ time *
      G.behavioralStageExpectation initial behavioral who time (hstage time))) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount
    (fun time => G.behavioralStageExpectation initial behavioral who time (hstage time))

/-- The corresponding normalized discounted payoff under the one total
pure-policy profile law. -/
def policyMeasureDiscountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (discount : ℝ) (behavioral : G.PublicProfile initial) (who : ι)
    (hstage : ∀ time, Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPureMeasure
        (G.toBehaviorProfile initial behavioral) (time + 1)))
    (_hsum : Summable (fun time => discount ^ time *
      G.policyMeasureStageExpectation initial behavioral who time (hstage time))) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount
    (fun time => G.policyMeasureStageExpectation initial behavioral who time (hstage time))

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

omit [(i : ι) → Fintype (G.Action i)] in
/-- A realized stage-utility bound supplies integration under each actual
behavioral prefix law. -/
theorem behavioralStageIntegrable_of_bounded (initial : G.State)
    (behavioral : G.PublicProfile initial) (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who) :=
  payoffIntegrable_of_bounded_on_support _ _ fun history _ =>
    G.abs_latestStageUtility_le initial who bound hbound history

omit [∀ i, Fintype (G.Action i)] in
/-- A uniform stage bound also bounds each behavioral prefix expectation. -/
theorem abs_behavioralStageExpectation_le (initial : G.State)
    (behavioral : G.PublicProfile initial) (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    |G.behavioralStageExpectation initial behavioral who time
      (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
        hbound time)| ≤ bound := by
  have hnonneg : 0 ≤ bound :=
    (abs_nonneg (G.stageUtility initial
      (fun i => Classical.choice inferInstance) who)).trans (hbound _ _)
  exact expect_abs_le_of_bounded hnonneg
    (fun history => G.abs_latestStageUtility_le initial who bound hbound history)
    (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
      hbound time)

omit [∀ i, Fintype (G.Action i)] in
/-- Bounded stochastic stage utility makes the behavioral discounted series
summable for every discount in `[0, 1)`. -/
theorem summable_discounted_behavioralStageExpectation
    (initial : G.State)
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable fun time => discount ^ time *
      G.behavioralStageExpectation initial behavioral who time
        (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
          hbound time) := by
  have hgeom : Summable fun time : ℕ => bound * discount ^ time :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro time
  rw [Real.norm_eq_abs]
  calc
    |discount ^ time *
        G.behavioralStageExpectation initial behavioral who time
          (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
            hbound time)| =
        discount ^ time *
          |G.behavioralStageExpectation initial behavioral who time
            (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
              hbound time)| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 time)]
    _ ≤ discount ^ time * bound :=
      mul_le_mul_of_nonneg_left
        (G.abs_behavioralStageExpectation_le initial behavioral who bound
          hbound time)
        (pow_nonneg hdiscount0 time)
    _ = bound * discount ^ time := by ring

/-- Bounded stage utility supplies integration under the actual pure-policy
runner measure at every prefix. -/
theorem policyMeasureStageIntegrable_of_bounded (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPureMeasure
        (G.toBehaviorProfile initial behavioral) (time + 1)) :=
  ((G.perfectMonitoring initial).pureMeasurePrefixIntegrable_iff_behavioral
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (G.toBehaviorProfile initial behavioral) (time + 1)
    (G.latestStageUtility initial who)).2
      (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
        hbound time)

/-- Bounded one-prefix policy-measure and behavioral expectations agree. -/
theorem policyMeasureStageExpectation_eq_behavioral_of_bounded
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    G.policyMeasureStageExpectation initial behavioral who time
        (G.policyMeasureStageIntegrable_of_bounded initial behavioral who bound
          hbound time) =
      G.behavioralStageExpectation initial behavioral who time
        (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
          hbound time) := by
  exact (G.perfectMonitoring initial).pureMeasurePrefixExpectation_eq_behavioral
    (G.perfectMonitoring_actsOnceWhereItMatters initial)
    (G.toBehaviorProfile initial behavioral) time
    (fun _ => G.latestStageUtility initial who)
    (G.behavioralStageIntegrable_of_bounded initial behavioral who bound
      hbound time)

/-- Bounded policy-measure prefix expectations have a convergent discounted
series under a strict discount. -/
theorem summable_discounted_policyMeasureStageExpectation
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable (fun time => discount ^ time *
      G.policyMeasureStageExpectation initial behavioral who time
        (G.policyMeasureStageIntegrable_of_bounded initial behavioral who bound
          hbound time)) := by
  simpa only [G.policyMeasureStageExpectation_eq_behavioral_of_bounded
    initial behavioral who bound hbound] using
    G.summable_discounted_behavioralStageExpectation initial hdiscount0
      hdiscount1 behavioral who hbound

/-- Bounded discounted payoff agrees under cover-free pure-policy measure
realization and behavioral play. -/
theorem kuhn_policyMeasure_discountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (behavioral : G.PublicProfile initial) (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    G.policyMeasureDiscountedPayoff initial discount behavioral who
        (fun time => G.policyMeasureStageIntegrable_of_bounded initial
          behavioral who bound hbound time)
        (G.summable_discounted_policyMeasureStageExpectation initial
          hdiscount0 hdiscount1 behavioral who hbound) =
      G.behavioralDiscountedPayoff initial discount behavioral who
        (fun time => G.behavioralStageIntegrable_of_bounded initial behavioral
          who bound hbound time)
        (G.summable_discounted_behavioralStageExpectation initial hdiscount0
          hdiscount1 behavioral who hbound) := by
  unfold policyMeasureDiscountedPayoff behavioralDiscountedPayoff
  congr 1
  funext time
  exact G.policyMeasureStageExpectation_eq_behavioral_of_bounded initial
    behavioral who bound hbound time

/-- Expected stage utility after independently drawing from arbitrary total
pure-policy measures. -/
def arbitraryPolicyMeasureStageExpectation (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    (who : ι) (time : ℕ)
    (hintegrable : Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPolicyMeasure laws (time + 1))) : ℝ :=
  (G.perfectMonitoring initial).policyMeasurePrefixExpectation laws
    (fun _ => G.latestStageUtility initial who) time hintegrable

/-- Normalized discounted payoff induced by arbitrary total pure-policy
measures. -/
def arbitraryPolicyMeasureDiscountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (discount : ℝ) (laws : G.ProtocolPolicyMeasureProfile initial)
    (who : ι)
    (hstage : ∀ time, Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPolicyMeasure laws (time + 1)))
    (_hsum : Summable (fun time => discount ^ time *
      G.arbitraryPolicyMeasureStageExpectation initial laws who time
        (hstage time))) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount
    (fun time => G.arbitraryPolicyMeasureStageExpectation initial laws who time
      (hstage time))

/-- A bounded stage payoff is integrable under the arbitrary policy-measure
prefix whenever its behavioral reading has the same bounded payoff. -/
theorem arbitraryPolicyMeasureStageIntegrable_of_bounded (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile)
    (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPolicyMeasure laws (time + 1)) := by
  let profile := G.policyMeasuresToPublicBehavioralWith initial laws fallback
  have hbehavioral := G.behavioralStageIntegrable_of_bounded initial profile
    who bound hbound time
  have hlaw := G.kuhn_arbitraryPolicyMeasure_allFinitePrefixes initial laws
    fallback (time + 1)
  have hmeasure : Integrable (G.latestStageUtility initial who)
      (G.protocolPolicyMeasureRun initial laws (time + 1)) := by
    rw [hlaw]
    exact (payoffIntegrable_iff_integrable
      ((G.publicHorizonForm initial (time + 1)).play profile)
      (G.latestStageUtility initial who)).mp hbehavioral
  simpa only [protocolPolicyMeasureRun] using hmeasure

/-- The actual arbitrary-policy-measure prefix and its behavioral reading
have the same guarded expected stage payoff. -/
theorem arbitraryPolicyMeasureStageExpectation_eq_behavioral_of_bounded
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile)
    (who : ι) (bound : ℝ)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) (time : ℕ) :
    G.arbitraryPolicyMeasureStageExpectation initial laws who time
        (G.arbitraryPolicyMeasureStageIntegrable_of_bounded initial laws
          fallback who bound hbound time) =
      G.behavioralStageExpectation initial
        (G.policyMeasuresToPublicBehavioralWith initial laws fallback) who time
        (G.behavioralStageIntegrable_of_bounded initial
          (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
          who bound hbound time) := by
  let profile := G.policyMeasuresToPublicBehavioralWith initial laws fallback
  have hlaw := G.kuhn_arbitraryPolicyMeasure_allFinitePrefixes initial laws
    fallback (time + 1)
  rw [G.publicHorizonForm_play] at hlaw
  have hbehavioral := G.behavioralStageIntegrable_of_bounded initial profile
    who bound hbound time
  have hvalue := (expect_eq_integral
    ((G.perfectMonitoring initial).runBehavioral
      (G.toBehaviorProfile initial profile) (time + 1))
    (G.latestStageUtility initial who) hbehavioral).symm
  have hmeasure :
      (∫ history, G.latestStageUtility initial who history
        ∂G.protocolPolicyMeasureRun initial laws (time + 1)) =
      G.behavioralStageExpectation initial profile who time hbehavioral := by
    rw [hlaw]
    simpa only [behavioralStageExpectation,
      InformationModel.behavioralPrefixExpectation] using hvalue
  simpa only [arbitraryPolicyMeasureStageExpectation,
    InformationModel.policyMeasurePrefixExpectation,
    protocolPolicyMeasureRun] using hmeasure

/-- Strict discount makes the bounded arbitrary-policy-measure stage series
summable under the actual integrated runner laws. -/
theorem summable_discounted_arbitraryPolicyMeasureStageExpectation
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile)
    (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    Summable (fun time => discount ^ time *
      G.arbitraryPolicyMeasureStageExpectation initial laws who time
        (G.arbitraryPolicyMeasureStageIntegrable_of_bounded initial laws
          fallback who bound hbound time)) := by
  simp only [G.arbitraryPolicyMeasureStageExpectation_eq_behavioral_of_bounded
    initial laws fallback who bound hbound]
  exact G.summable_discounted_behavioralStageExpectation initial hdiscount0
    hdiscount1 (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
    who hbound

/-- Guarded discounted payoff of an arbitrary policy-measure profile agrees
with its conditional behavioral reading. -/
theorem kuhn_arbitraryPolicyMeasure_discountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile)
    (who : ι)
    (hbound : ∀ state actions,
      |G.stageUtility state actions who| ≤ bound) :
    G.arbitraryPolicyMeasureDiscountedPayoff initial discount laws who
        (fun time => G.arbitraryPolicyMeasureStageIntegrable_of_bounded
          initial laws fallback who bound hbound time)
        (G.summable_discounted_arbitraryPolicyMeasureStageExpectation initial
          hdiscount0 hdiscount1 laws fallback who hbound) =
      G.behavioralDiscountedPayoff initial discount
        (G.policyMeasuresToPublicBehavioralWith initial laws fallback) who
        (fun time => G.behavioralStageIntegrable_of_bounded initial
          (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
          who bound hbound time)
        (G.summable_discounted_behavioralStageExpectation initial hdiscount0
          hdiscount1 (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
          who hbound) := by
  unfold arbitraryPolicyMeasureDiscountedPayoff behavioralDiscountedPayoff
  congr 1
  funext time
  exact G.arbitraryPolicyMeasureStageExpectation_eq_behavioral_of_bounded
    initial laws fallback who bound hbound time

omit [∀ i, Fintype (G.Action i)] in
/-- Equality of actual prefix laws transports the needed stage integration to
an arbitrary total-policy measure. -/
theorem arbitraryStageIntegrable_of_prefixLaw (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    (behavioral : G.PublicProfile initial)
    (hlaw : ∀ horizon, G.protocolPolicyMeasureRun initial laws horizon =
      ((G.publicHorizonForm initial horizon).play behavioral).toMeasure)
    (who : ι) (time : ℕ)
    (hbehavioral : PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who)) :
    Integrable (G.latestStageUtility initial who)
      ((G.perfectMonitoring initial).runPolicyMeasure laws (time + 1)) := by
  have hprefix := hlaw (time + 1)
  rw [G.publicHorizonForm_play] at hprefix
  have hmeasure : Integrable (G.latestStageUtility initial who)
      (G.protocolPolicyMeasureRun initial laws (time + 1)) := by
    rw [hprefix]
    exact (payoffIntegrable_iff_integrable _ _).mp hbehavioral
  simpa only [protocolPolicyMeasureRun] using hmeasure

omit [(i : ι) → Fintype (G.Action i)] in
/-- Equal prefix laws give equal guarded stage expectations, including for
hybrid unilateral deviations. -/
theorem arbitraryStageExpectation_eq_of_prefixLaw (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    (behavioral : G.PublicProfile initial)
    (hlaw : ∀ horizon, G.protocolPolicyMeasureRun initial laws horizon =
      ((G.publicHorizonForm initial horizon).play behavioral).toMeasure)
    (who : ι) (time : ℕ)
    (hbehavioral : PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who)) :
    G.arbitraryPolicyMeasureStageExpectation initial laws who time
        (G.arbitraryStageIntegrable_of_prefixLaw initial laws behavioral
          hlaw who time hbehavioral) =
      G.behavioralStageExpectation initial behavioral who time
        hbehavioral := by
  have hprefix := hlaw (time + 1)
  rw [G.publicHorizonForm_play] at hprefix
  have hvalue := (expect_eq_integral
    ((G.perfectMonitoring initial).runBehavioral
      (G.toBehaviorProfile initial behavioral) (time + 1))
    (G.latestStageUtility initial who) hbehavioral).symm
  have hmeasure :
      (∫ history, G.latestStageUtility initial who history
        ∂G.protocolPolicyMeasureRun initial laws (time + 1)) =
      G.behavioralStageExpectation initial behavioral who time
        hbehavioral := by
    rw [hprefix]
    simpa only [behavioralStageExpectation,
      InformationModel.behavioralPrefixExpectation] using hvalue
  simpa only [arbitraryPolicyMeasureStageExpectation,
    InformationModel.policyMeasurePrefixExpectation,
    protocolPolicyMeasureRun] using hmeasure

omit [(i : ι) → Fintype (G.Action i)] in
/-- Prefix-law equality also transports the entire discounted series once the
behavioral stage and series guards are established. -/
theorem discountedPayoff_eq_of_prefixLaw (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    (behavioral : G.PublicProfile initial)
    (hlaw : ∀ horizon, G.protocolPolicyMeasureRun initial laws horizon =
      ((G.publicHorizonForm initial horizon).play behavioral).toMeasure)
    (discount : ℝ) (who : ι)
    (hbehavioral : ∀ time, PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial behavioral) (time + 1))
      (G.latestStageUtility initial who))
    (hsummable : Summable (fun time => discount ^ time *
      G.behavioralStageExpectation initial behavioral who time
        (hbehavioral time))) :
    let hmeasure : ∀ time, Integrable (G.latestStageUtility initial who)
        ((G.perfectMonitoring initial).runPolicyMeasure laws (time + 1)) :=
      fun time => G.arbitraryStageIntegrable_of_prefixLaw initial laws
        behavioral hlaw who time (hbehavioral time)
    Summable (fun time => discount ^ time *
        G.arbitraryPolicyMeasureStageExpectation initial laws who time
          (hmeasure time)) ∧
      ∀ hsum : Summable (fun time => discount ^ time *
          G.arbitraryPolicyMeasureStageExpectation initial laws who time
            (hmeasure time)),
        G.arbitraryPolicyMeasureDiscountedPayoff initial discount laws who
            hmeasure hsum =
          G.behavioralDiscountedPayoff initial discount behavioral who
            hbehavioral hsummable := by
  dsimp only
  have hpointwise (time : ℕ) :
      G.arbitraryPolicyMeasureStageExpectation initial laws who time
          (G.arbitraryStageIntegrable_of_prefixLaw initial laws behavioral
            hlaw who time (hbehavioral time)) =
        G.behavioralStageExpectation initial behavioral who time
          (hbehavioral time) :=
    G.arbitraryStageExpectation_eq_of_prefixLaw initial laws behavioral
      hlaw who time (hbehavioral time)
  constructor
  · simpa only [hpointwise] using hsummable
  · intro hsum
    unfold arbitraryPolicyMeasureDiscountedPayoff behavioralDiscountedPayoff
    congr 1
    funext time
    exact hpointwise time

section Unilateral

variable [DecidableEq ι]

/-- **Counterfactual bounded behavioral-to-mixed Kuhn.** An arbitrary mixed
deviation has the same law as its behavioral reading while every opponent
keeps the mixed public policy selected from the baseline behavioral profile.
The common finite site set covers off-path histories as well as the baseline
support. -/
theorem kuhn_behavioral_update_toMixed (initial : G.State)
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.MixedPublicPolicy who) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite) :
    ((G.pureHorizonForm initial horizon).mixed).play
        (Profile.update
          (fun i => PublicPolicy.toMixed G initial horizon
            (behavioral i) (hfinite i))
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
         (G.perfectMonitoring initial) (hfinite i).toFinset
        ((G.purePolicyEquiv initial i).symm
          (behavioral i).supportFallback)
  have hconverted :
      (fun i => PMF.map (G.purePolicyEquiv initial i).symm
        ((Profile.update
          (sig := (G.pureHorizonForm initial horizon).sig.mixed)
           (fun i => PublicPolicy.toMixed G initial horizon
             (behavioral i) (hfinite i))
          who replacement) i)) =
        Profile.update protocolMixed who
          (PMF.map (G.purePolicyEquiv initial who).symm
            replacement) := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, Profile.update_same]
    · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi,
         PublicPolicy.map_symm_toMixed G initial horizon
           (behavioral i) (hfinite i)]
  rw [hconverted]
  have hreplacement :
      G.toBehavioralPolicy initial
          (MixedPublicPolicy.toBehavioral G initial replacement) =
        InformationModel.MixedPolicy.toBehavioral
          (M := G.perfectMonitoring initial)
          (PMF.map (G.purePolicyEquiv initial who).symm
            replacement) :=
    G.toBehavioralPolicy_ofBehavioralPolicy initial _
  rw [hreplacement]
  exact (G.perfectMonitoring initial).kuhn_behavioral_update_toMixedWithin
    (G.perfectMonitoring_perfectRecall initial)
    (fun i => (hfinite i).toFinset) horizon
    (G.boundedInformationSites_finiteCover initial horizon hfinite)
    (G.toBehaviorProfile initial behavioral)
    (fun i => (G.purePolicyEquiv initial i).symm
      (behavioral i).supportFallback)
    who (PMF.map (G.purePolicyEquiv initial who).symm replacement)

/-- The single infinite product construction also commutes with an arbitrary
public behavioral deviation. The common counterfactual cover includes public
histories omitted by the baseline support. -/
theorem kuhn_policyMeasure_update_allFinitePrefixes (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.PublicPolicy who) :
    ∀ horizon,
      G.protocolPureRunMeasure initial
          (Profile.update behavioral who replacement) horizon =
        ((G.publicHorizonForm initial horizon).play
          (Profile.update behavioral who replacement)).toMeasure := by
  exact G.kuhn_policyMeasure_allFinitePrefixes initial
    (Profile.update behavioral who replacement)

/-- The cover-free reverse arbitrary-measure construction commutes with
replacing one player's pure-policy measure at every requested prefix. -/
theorem kuhn_arbitraryPolicyMeasure_update_allFinitePrefixes
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile) (who : ι)
    (replacement : G.ProtocolPolicyMeasure initial who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : G.PurePublicPolicy who) :
    ∀ horizon,
      G.protocolPolicyMeasureRun initial
          (Profile.update
            (sig := (G.perfectMonitoring initial).policyMeasureSignature)
            laws who replacement) horizon =
        ((G.publicHorizonForm initial horizon).play
          (Profile.update
            (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
            who
            (G.ofBehavioralPolicy initial
              (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
                (M := G.perfectMonitoring initial) replacement
                ((G.purePolicyEquiv initial who).symm
                  replacementFallback))))).toMeasure := by
  intro horizon
  let protocolFallback : Profile
      (G.perfectMonitoring initial).strategicSignature := fun i =>
    (G.purePolicyEquiv initial i).symm (fallback i)
  have hbaseline : G.toBehaviorProfile initial
      (G.policyMeasuresToPublicBehavioralWith initial laws fallback) =
      (G.perfectMonitoring initial).policyMeasureBehavioralWith laws
        protocolFallback :=
    G.toBehaviorProfile_ofBehaviorProfile initial _
  have hreplacement : G.toBehavioralPolicy initial
      (G.ofBehavioralPolicy initial
        (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := G.perfectMonitoring initial) replacement
          ((G.purePolicyEquiv initial who).symm replacementFallback))) =
      Protocol.InformationModel.PolicyMeasure.toBehavioralWith
        (M := G.perfectMonitoring initial) replacement
        ((G.purePolicyEquiv initial who).symm replacementFallback) :=
    G.toBehavioralPolicy_ofBehavioralPolicy initial _
  unfold protocolPolicyMeasureRun
  rw [(G.perfectMonitoring initial).runPolicyMeasure_update_eq_runBehavioral_update
    (InformationModel.constrainsAlike_of_perfectRecall
      (G.perfectMonitoring_perfectRecall initial)) laws protocolFallback who
    replacement ((G.purePolicyEquiv initial who).symm replacementFallback)
    horizon]
  rw [G.publicHorizonForm_play, G.toBehaviorProfile_update,
    hbaseline, hreplacement]

/-- **Hybrid unilateral stochastic Kuhn, behavioral deviation.** Opponents
retain arbitrary laws over total certified public policies while the focal
player uses an arbitrary behavioral public-policy deviation. -/
theorem kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_allFinitePrefixes
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile) (who : ι)
    (replacement : G.PublicPolicy who) :
    ∀ horizon,
      G.protocolPolicyMeasureRun initial
          (Profile.update
            (sig := (G.perfectMonitoring initial).policyMeasureSignature)
            laws who
              (G.toBehavioralPolicy initial replacement).toPureMeasure)
          horizon =
        ((G.publicHorizonForm initial horizon).play
          (Profile.update
            (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
            who replacement)).toMeasure := by
  intro horizon
  let protocolFallback : Profile
      (G.perfectMonitoring initial).strategicSignature := fun i =>
    (G.purePolicyEquiv initial i).symm (fallback i)
  have hbaseline : G.toBehaviorProfile initial
      (G.policyMeasuresToPublicBehavioralWith initial laws fallback) =
      (G.perfectMonitoring initial).policyMeasureBehavioralWith laws
        protocolFallback :=
    G.toBehaviorProfile_ofBehaviorProfile initial _
  unfold protocolPolicyMeasureRun
  rw [(G.perfectMonitoring initial).runPolicyMeasure_update_toPureMeasure_eq_runBehavioral_update
      (G.perfectMonitoring_perfectRecall initial) laws protocolFallback who
      (G.toBehavioralPolicy initial replacement) horizon]
  rw [G.publicHorizonForm_play, G.toBehaviorProfile_update, hbaseline]

/-- **Hybrid unilateral stochastic Kuhn, total-policy-law deviation.** Every
opponent retains its original behavioral public policy while the focal player
uses an arbitrary probability law over total certified public policies. -/
theorem kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_allFinitePrefixes
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.ProtocolPolicyMeasure initial who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : G.PurePublicPolicy who) :
    ∀ horizon,
      G.protocolPolicyMeasureRun initial
          (Profile.update
            (sig := (G.perfectMonitoring initial).policyMeasureSignature)
            (fun i =>
              (G.toBehavioralPolicy initial (behavioral i)).toPureMeasure)
            who replacement) horizon =
        ((G.publicHorizonForm initial horizon).play
          (Profile.update behavioral who
            (G.ofBehavioralPolicy initial
              (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
                (M := G.perfectMonitoring initial) replacement
                ((G.purePolicyEquiv initial who).symm
                  replacementFallback))))).toMeasure := by
  intro horizon
  let protocolBehavioral := G.toBehaviorProfile initial behavioral
  let protocolReplacementFallback :=
    (G.purePolicyEquiv initial who).symm replacementFallback
  have hreplacement : G.toBehavioralPolicy initial
      (G.ofBehavioralPolicy initial
        (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := G.perfectMonitoring initial) replacement
          protocolReplacementFallback)) =
      Protocol.InformationModel.PolicyMeasure.toBehavioralWith
        (M := G.perfectMonitoring initial) replacement
        protocolReplacementFallback :=
    G.toBehavioralPolicy_ofBehavioralPolicy initial _
  unfold protocolPolicyMeasureRun
  show (G.perfectMonitoring initial).runPolicyMeasure
      (Profile.update
        (sig := (G.perfectMonitoring initial).policyMeasureSignature)
        (fun i => (protocolBehavioral i).toPureMeasure) who replacement)
      horizon = _
  rw [(G.perfectMonitoring initial).runPolicyMeasure_toPureMeasure_update_eq_runBehavioral_update
      (G.perfectMonitoring_perfectRecall initial) protocolBehavioral who
      replacement protocolReplacementFallback horizon]
  rw [G.publicHorizonForm_play, G.toBehaviorProfile_update, hreplacement]

/-- A behavioral unilateral deviation has the same guarded discounted value
under its one predrawn total-policy measure at every finite prefix. -/
theorem kuhn_policyMeasure_update_discountedPayoff (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.PublicPolicy who) (discount : ℝ)
    (hbehavioral : ∀ time, PayoffIntegrable
      ((G.perfectMonitoring initial).runBehavioral
        (G.toBehaviorProfile initial
          (Profile.update behavioral who replacement)) (time + 1))
      (G.latestStageUtility initial who))
    (hsummable : Summable (fun time => discount ^ time *
      G.behavioralStageExpectation initial
        (Profile.update behavioral who replacement) who time
          (hbehavioral time))) :
    let revised := Profile.update behavioral who replacement
    let hmeasure : ∀ time, Integrable (G.latestStageUtility initial who)
        ((G.perfectMonitoring initial).runPureMeasure
          (G.toBehaviorProfile initial revised) (time + 1)) :=
      fun time => ((G.perfectMonitoring initial).pureMeasurePrefixIntegrable_iff_behavioral
          (G.perfectMonitoring_actsOnceWhereItMatters initial)
          (G.toBehaviorProfile initial revised) (time + 1)
          (G.latestStageUtility initial who)).2 (hbehavioral time)
    Summable (fun time => discount ^ time *
        G.policyMeasureStageExpectation initial revised who time
          (hmeasure time)) ∧
      ∀ hsum : Summable (fun time => discount ^ time *
          G.policyMeasureStageExpectation initial revised who time
            (hmeasure time)),
        G.policyMeasureDiscountedPayoff initial discount revised who
            hmeasure hsum =
          G.behavioralDiscountedPayoff initial discount revised who
            hbehavioral hsummable := by
  dsimp only
  have hpointwise (time : ℕ) :
      G.policyMeasureStageExpectation initial
          (Profile.update behavioral who replacement) who time
          (((G.perfectMonitoring initial).pureMeasurePrefixIntegrable_iff_behavioral
              (G.perfectMonitoring_actsOnceWhereItMatters initial)
              (G.toBehaviorProfile initial
                (Profile.update behavioral who replacement)) (time + 1)
              (G.latestStageUtility initial who)).2 (hbehavioral time)) =
        G.behavioralStageExpectation initial
          (Profile.update behavioral who replacement) who time
          (hbehavioral time) :=
    (G.perfectMonitoring initial).pureMeasurePrefixExpectation_eq_behavioral
      (G.perfectMonitoring_actsOnceWhereItMatters initial)
      (G.toBehaviorProfile initial
        (Profile.update behavioral who replacement)) time
      (fun _ => G.latestStageUtility initial who) (hbehavioral time)
  constructor
  · simpa only [hpointwise] using hsummable
  · intro hsum
    unfold policyMeasureDiscountedPayoff behavioralDiscountedPayoff
    congr 1
    funext time
    exact hpointwise time

/-- An arbitrary policy-measure environment preserves the discounted value
of a behavioral unilateral deviation whenever its actual stage expectations
are integrable and its discounted series converges. -/
theorem kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_discountedPayoff
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (laws : G.ProtocolPolicyMeasureProfile initial)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : G.PurePublicProfile) (who : ι)
    (replacement : G.PublicPolicy who) (discount : ℝ) :
    let changedLaws := Profile.update
      (sig := (G.perfectMonitoring initial).policyMeasureSignature)
      laws who (G.toBehavioralPolicy initial replacement).toPureMeasure
    let revised := Profile.update
      (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
      who replacement
    ∀ (hbehavioral : ∀ time, PayoffIntegrable
        ((G.perfectMonitoring initial).runBehavioral
          (G.toBehaviorProfile initial revised) (time + 1))
        (G.latestStageUtility initial who))
      (hsummable : Summable (fun time => discount ^ time *
        G.behavioralStageExpectation initial revised who time
          (hbehavioral time))),
      ∃ (hmeasure : ∀ time, Integrable (G.latestStageUtility initial who)
          ((G.perfectMonitoring initial).runPolicyMeasure changedLaws
            (time + 1))),
        ∃ hsum : Summable (fun time => discount ^ time *
            G.arbitraryPolicyMeasureStageExpectation initial changedLaws who
              time (hmeasure time)),
          G.arbitraryPolicyMeasureDiscountedPayoff initial discount changedLaws
              who hmeasure hsum =
            G.behavioralDiscountedPayoff initial discount revised who
              hbehavioral hsummable := by
  dsimp only
  intro hbehavioral hsummable
  let changedLaws := Profile.update
    (sig := (G.perfectMonitoring initial).policyMeasureSignature)
    laws who (G.toBehavioralPolicy initial replacement).toPureMeasure
  let revised := Profile.update
    (G.policyMeasuresToPublicBehavioralWith initial laws fallback)
    who replacement
  let hlaw :=
    G.kuhn_arbitraryPolicyMeasure_opponents_behavioralDeviation_allFinitePrefixes
      initial laws fallback who replacement
  let hmeasure (time : ℕ) := G.arbitraryStageIntegrable_of_prefixLaw
    initial changedLaws revised hlaw who time (hbehavioral time)
  have hpointwise (time : ℕ) :=
    G.arbitraryStageExpectation_eq_of_prefixLaw initial changedLaws revised
      hlaw who time (hbehavioral time)
  have hsum : Summable (fun time => discount ^ time *
      G.arbitraryPolicyMeasureStageExpectation initial changedLaws who time
        (hmeasure time)) := by
    simpa only [hpointwise] using hsummable
  refine ⟨hmeasure, hsum, ?_⟩
  unfold arbitraryPolicyMeasureDiscountedPayoff behavioralDiscountedPayoff
  congr 1
  funext time
  exact hpointwise time

/-- Replacing one behavioral player by an arbitrary total-policy measure
preserves the guarded discounted value of its behavioral reading. -/
theorem kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_discountedPayoff
    (initial : G.State)
    [MeasurableSpace (G.toExecution initial).History]
    [MeasurableSingletonClass (G.toExecution initial).History]
    (behavioral : G.PublicProfile initial) (who : ι)
    (replacement : G.ProtocolPolicyMeasure initial who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : G.PurePublicPolicy who) (discount : ℝ) :
    let changedLaws := Profile.update
      (sig := (G.perfectMonitoring initial).policyMeasureSignature)
      (fun i => (G.toBehavioralPolicy initial (behavioral i)).toPureMeasure)
      who replacement
    let revised := Profile.update behavioral who
      (G.ofBehavioralPolicy initial
        (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
          (M := G.perfectMonitoring initial) replacement
          ((G.purePolicyEquiv initial who).symm replacementFallback)))
    ∀ (hbehavioral : ∀ time, PayoffIntegrable
        ((G.perfectMonitoring initial).runBehavioral
          (G.toBehaviorProfile initial revised) (time + 1))
        (G.latestStageUtility initial who))
      (hsummable : Summable (fun time => discount ^ time *
        G.behavioralStageExpectation initial revised who time
          (hbehavioral time))),
      ∃ (hmeasure : ∀ time, Integrable (G.latestStageUtility initial who)
          ((G.perfectMonitoring initial).runPolicyMeasure changedLaws
            (time + 1))),
        ∃ hsum : Summable (fun time => discount ^ time *
            G.arbitraryPolicyMeasureStageExpectation initial changedLaws who
              time (hmeasure time)),
          G.arbitraryPolicyMeasureDiscountedPayoff initial discount changedLaws
              who hmeasure hsum =
            G.behavioralDiscountedPayoff initial discount revised who
              hbehavioral hsummable := by
  dsimp only
  intro hbehavioral hsummable
  let changedLaws := Profile.update
    (sig := (G.perfectMonitoring initial).policyMeasureSignature)
    (fun i => (G.toBehavioralPolicy initial (behavioral i)).toPureMeasure)
    who replacement
  let revised := Profile.update behavioral who
    (G.ofBehavioralPolicy initial
      (Protocol.InformationModel.PolicyMeasure.toBehavioralWith
        (M := G.perfectMonitoring initial) replacement
        ((G.purePolicyEquiv initial who).symm replacementFallback)))
  let hlaw :=
    G.kuhn_behavioral_opponents_arbitraryPolicyMeasureDeviation_allFinitePrefixes
      initial behavioral who replacement replacementFallback
  let hmeasure (time : ℕ) := G.arbitraryStageIntegrable_of_prefixLaw
    initial changedLaws revised hlaw who time (hbehavioral time)
  have hpointwise (time : ℕ) :=
    G.arbitraryStageExpectation_eq_of_prefixLaw initial changedLaws revised
      hlaw who time (hbehavioral time)
  have hsum : Summable (fun time => discount ^ time *
      G.arbitraryPolicyMeasureStageExpectation initial changedLaws who time
        (hmeasure time)) := by
    simpa only [hpointwise] using hsummable
  refine ⟨hmeasure, hsum, ?_⟩
  unfold arbitraryPolicyMeasureDiscountedPayoff behavioralDiscountedPayoff
  congr 1
  funext time
  exact hpointwise time

/-- **Counterfactual bounded mixed-to-behavioral Kuhn.** An arbitrary
behavioral deviation is realized by finite predrawing while every opponent
keeps the conditional behavioral reading of its original mixed public policy.
-/
theorem kuhn_mixed_update_toBehavioral (initial : G.State)
    (mixed : G.MixedPublicProfile) (who : ι)
    (replacement : G.PublicPolicy who) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite) :
    (G.publicHorizonForm initial horizon).play
        (Profile.update
          (MixedPublicProfile.toBehavioral G initial mixed)
          who replacement) =
      ((G.pureHorizonForm initial horizon).mixed).play
        (Profile.update mixed who
          (PublicPolicy.toMixed G initial horizon replacement
            (hfinite who))) := by
  rw [G.publicHorizonForm_play,
    G.toBehaviorProfile_update,
    MixedPublicProfile.toBehaviorProfile_toBehavioral,
    GameTheory.mixed_relabelStrategies_play]
  let protocolMixed : Profile
      (G.perfectMonitoring initial).strategicSignature.mixed :=
    fun i => PMF.map (G.purePolicyEquiv initial i).symm (mixed i)
  have hconverted :
      (fun i => PMF.map (G.purePolicyEquiv initial i).symm
        ((Profile.update
          (sig := (G.pureHorizonForm initial horizon).sig.mixed) mixed who
          (PublicPolicy.toMixed G initial horizon replacement
            (hfinite who))) i)) =
        Profile.update protocolMixed who
          ((G.toBehavioralPolicy initial replacement).toMixedWithin
            (G.perfectMonitoring initial) (hfinite who).toFinset
            ((G.purePolicyEquiv initial who).symm
              replacement.supportFallback)) := by
    funext i
    by_cases hi : i = who
    · subst i
      rw [Profile.update_same, Profile.update_same,
        PublicPolicy.map_symm_toMixed G initial horizon replacement
          (hfinite who)]
    · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]
  rw [hconverted]
  exact (G.perfectMonitoring initial).kuhn_mixed_update_toBehavioralWithin
    (G.perfectMonitoring_perfectRecall initial)
    (fun i => (hfinite i).toFinset) horizon
    (G.boundedInformationSites_finiteCover initial horizon hfinite)
    protocolMixed who
    (G.toBehavioralPolicy initial replacement)
    ((G.purePolicyEquiv initial who).symm replacement.supportFallback)

/-- A bounded behavioral Nash equilibrium becomes a mixed public-policy Nash
equilibrium by predrawing the common finite counterfactual site set. -/
theorem isNash_toMixed_of_isNash_behavioral (initial : G.State)
    (utility : (G.toExecution initial).History → ι → ℝ)
    (behavioral : G.PublicProfile initial) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite)
    (hnash : IsNash (G.publicHorizonForm initial horizon)
      (euPreference utility) behavioral) :
    IsNash (G.pureHorizonForm initial horizon).mixed
      (euPreference utility)
      (fun i => PublicPolicy.toMixed G initial horizon
        (behavioral i) (hfinite i)) := by
  rw [isNash_iff] at hnash ⊢
  intro who replacement
  rw [G.kuhn_behavioral_update_toMixed initial behavioral who
       replacement horizon hfinite,
     G.kuhn_behavioral_to_mixed initial behavioral horizon hfinite]
  exact hnash who
    (MixedPublicPolicy.toBehavioral G initial replacement)

/-- A bounded mixed public-policy Nash equilibrium becomes a behavioral Nash
equilibrium under the canonical conditional behavioral reading. -/
theorem isNash_toBehavioral_of_isNash_mixed (initial : G.State)
    (utility : (G.toExecution initial).History → ι → ℝ)
    (mixed : G.MixedPublicProfile) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite)
    (hnash : IsNash (G.pureHorizonForm initial horizon).mixed
      (euPreference utility) mixed) :
    IsNash (G.publicHorizonForm initial horizon)
      (euPreference utility)
      (MixedPublicProfile.toBehavioral G initial mixed) := by
  rw [isNash_iff] at hnash ⊢
  intro who replacement
  rw [G.kuhn_mixed_update_toBehavioral initial mixed who replacement
       horizon hfinite,
    G.kuhn_mixed_to_behavioral initial mixed horizon]
  exact hnash who
     (PublicPolicy.toMixed G initial horizon replacement (hfinite who))

end Unilateral

/-- Behavioral and mixed proof-free public policies realize exactly the same
bounded canonical history laws. -/
theorem kuhn_historyLaws (initial : G.State) (horizon : ℕ)
    (hfinite : ∀ i, (G.boundedInformationSites initial horizon i).Finite) :
    { law | ∃ behavioral : G.PublicProfile initial,
        (G.publicHorizonForm initial horizon).play behavioral = law } =
      { law | ∃ mixed : G.MixedPublicProfile,
        ((G.pureHorizonForm initial horizon).mixed).play mixed = law } := by
  ext law
  constructor
  · rintro ⟨behavioral, rfl⟩
    exact ⟨fun i => PublicPolicy.toMixed G initial horizon
      (behavioral i) (hfinite i),
      G.kuhn_behavioral_to_mixed initial behavioral horizon hfinite⟩
  · rintro ⟨mixed, rfl⟩
    exact ⟨MixedPublicProfile.toBehavioral G initial mixed,
      kuhn_mixed_to_behavioral G initial mixed horizon⟩

end FiniteActions

end Game

end GameTheory.Stochastic
