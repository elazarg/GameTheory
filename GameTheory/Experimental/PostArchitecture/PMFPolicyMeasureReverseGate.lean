/-
EXP-136: cover-free reverse policy-measure realization under infinite chance.
At horizon two, geometric chance reaches infinitely many public information
sites. One nonatomic policy measure correlates a root choice with the choice at
one successor site while retaining independent fair choices elsewhere.
-/

import GameTheory.Stochastic.Kuhn
import GameTheory.Math.Probability.InfiniteProductBoundary
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.PMFPolicyMeasureReverseGate

open GameTheory.Math.Probability GameTheory.Protocol MeasureTheory
open GameTheory.Stochastic GameTheory.Stochastic.Game
open GameTheory.Experimental.PMFRestoration

@[reducible]
def chanceGame : Stochastic.Game Unit where
  State := ℕ
  Action _ := Bool
  transition state _ :=
    if state = 0 then geometric.map Nat.succ else PMF.pure state
  stageUtility _ _ _ := 0

local instance actionNonempty :
    ∀ i, Nonempty (chanceGame.Action i) := fun _ => ⟨false⟩

local instance actionFintype :
    ∀ i, Fintype (chanceGame.Action i) := fun _ => inferInstance

local instance historyMeasurableSpace :
    MeasurableSpace (chanceGame.toExecution 0).History := ⊤

local instance choiceMeasurableSpace :
    ∀ i info, MeasurableSpace
      ((chanceGame.perfectMonitoring 0).Choice i info) := fun _ _ => ⊤

local instance choiceDiscreteMeasurableSpace :
    ∀ i info, DiscreteMeasurableSpace
      ((chanceGame.perfectMonitoring 0).Choice i info) :=
  fun _ _ => ⟨fun _ => MeasurableSet.of_discrete⟩

local instance choiceFintype :
    ∀ i info, Fintype
      ((chanceGame.perfectMonitoring 0).Choice i info) :=
  fun i info => Fintype.ofEquiv Bool
    (chanceGame.actionChoiceEquiv 0 i info)

local instance choiceNonempty :
    ∀ i info, Nonempty
      ((chanceGame.perfectMonitoring 0).Choice i info) :=
  fun i info => Nonempty.map
    (chanceGame.actionChoiceEquiv 0 i info) inferInstance

def falseJoint : ∀ _ : Unit, Option Bool := fun _ => some false

theorem falseJoint_legal :
    (chanceGame.toExecution 0).Legal 0 falseJoint := by
  constructor
  · simp
  · intro i
    simp [falseJoint]

theorem chance_realized (n : ℕ) :
    n + 1 ∈ ((chanceGame.toExecution 0).step 0
      ⟨falseJoint, falseJoint_legal⟩).support := by
  show n + 1 ∈ (geometric.map Nat.succ).support
  rw [PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

def history (n : ℕ) : (chanceGame.toExecution 0).History :=
  (chanceGame.toExecution 0).initHistory.extend
    falseJoint_legal (chance_realized n)

theorem history_reaches (n : ℕ) :
    (chanceGame.toExecution 0).ReachesWithin 1
      (chanceGame.toExecution 0).initHistory (history n) := by
  simpa [history] using
    (ExecutionProtocol.ReachesWithin.step falseJoint falseJoint_legal
      (chance_realized n)
      (ExecutionProtocol.ReachesWithin.refl 0 (history n)))

def site (n : ℕ) : (chanceGame.perfectMonitoring 0).InfoState () :=
  (chanceGame.perfectMonitoring 0).infoOf () (history n).trace

theorem site_head_target (n : ℕ) :
    (site n).head?.map (fun record => record.target) = some (n + 1) := by
  simp [site, history,
    ExecutionProtocol.History.extend, ExecutionProtocol.initHistory,
    chanceGame.perfectMonitoring_infoOf_eq_publicHistoryOfTrace,
    chanceGame.publicHistoryOfTrace_extend]

theorem site_injective : Function.Injective site := by
  intro n m h
  have htarget := congrArg (fun info : chanceGame.PublicHistory =>
    info.head?.map (fun record => record.target)) h
  rw [site_head_target, site_head_target] at htarget
  exact Nat.add_right_cancel (Option.some.inj htarget)

theorem boundedSites_infinite :
    (chanceGame.boundedInformationSites 0 1 ()).Infinite := by
  apply (Set.infinite_range_of_injective site_injective).mono
  rintro _ ⟨n, rfl⟩
  exact chanceGame.boundedInformationSites_cover 0 1
    (history n) (history_reaches n) (by simp) ()

theorem boundedSites_two_infinite :
    (chanceGame.boundedInformationSites 0 2 ()).Infinite := by
  apply (Set.infinite_range_of_injective site_injective).mono
  rintro _ ⟨n, rfl⟩
  exact chanceGame.boundedInformationSites_cover 0 2
    (history n) ((history_reaches n).mono (extra := 1)) (by simp) ()

local instance siteInfinite :
    Infinite ((chanceGame.perfectMonitoring 0).InfoState ()) :=
  Infinite.of_injective site site_injective

local instance stageRecordCountable : Countable chanceGame.StageRecord := by
  apply Function.Injective.countable
    (f := fun record : chanceGame.StageRecord =>
      (record.source, record.joint, record.target))
  intro first second h
  cases first
  cases second
  simpa using h

local instance siteCountable :
    Countable ((chanceGame.perfectMonitoring 0).InfoState ()) :=
  inferInstance

private theorem tprod_const_zero_of_lt_one {α : Type*} [Infinite α]
    {r : ENNReal} (hr : r < 1) : (∏' _ : α, r) = 0 := by
  have hle (n : ℕ) : (∏' _ : α, r) ≤ r ^ n := by
    obtain ⟨s, _, hs⟩ :=
      (Set.infinite_univ (α := α)).exists_subset_card_eq n
    rw [ENNReal.tprod_eq_iInf_prod (by intro; exact hr.le)]
    calc
      (⨅ s : Finset α, ∏ i ∈ s, r) ≤ ∏ i ∈ s, r :=
        iInf_le (fun s : Finset α => ∏ i ∈ s, r) s
      _ = _ := by simp [hs]
  have hz : (∏' _ : α, r) ≤ 0 :=
    ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) hle
  exact le_antisymm hz bot_le

def fairPolicy : (chanceGame.perfectMonitoring 0).BehavioralPolicy () :=
  fun _ => PMF.uniformOfFintype _

def fairMeasure : Measure ((chanceGame.perfectMonitoring 0).Policy ()) :=
  InformationModel.BehavioralPolicy.toPureMeasure
    (M := chanceGame.perfectMonitoring 0) fairPolicy

theorem fairPolicy_isProbability :
    IsProbabilityMeasure fairMeasure :=
  InformationModel.BehavioralPolicy.toPureMeasure_isProbability
    (M := chanceGame.perfectMonitoring 0) fairPolicy

theorem fairPolicy_singleton_zero
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    fairMeasure {policy} = 0 := by
  have hcoord (info : (chanceGame.perfectMonitoring 0).InfoState ()) :
      (fairPolicy info).toMeasure {policy info} = (1 / 2 : ENNReal) := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have hcard : Fintype.card
        ((chanceGame.perfectMonitoring 0).Choice () info) = 2 := by
      calc
        _ = Fintype.card Bool :=
          Fintype.card_congr (chanceGame.actionChoiceEquiv 0 () info).symm
        _ = 2 := by decide
    simp [fairPolicy, PMF.uniformOfFintype_apply, hcard]
  rw [fairMeasure, InformationModel.BehavioralPolicy.toPureMeasure,
    Measure.infinitePi_singleton]
  simp only [hcoord]
  exact tprod_const_zero_of_lt_one (by norm_num : (1 / 2 : ENNReal) < 1)

private theorem root_ne_site :
    ([] : (chanceGame.perfectMonitoring 0).InfoState ()) ≠ site 0 := by
  intro h
  have htarget := congrArg (fun info : chanceGame.PublicHistory =>
    info.head?.map (fun record => record.target)) h
  rw [site_head_target] at htarget
  cases htarget

/-- Copy the root choice into the first successor site's choice, leaving all
other total-policy coordinates intact. -/
def correlate
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    (chanceGame.perfectMonitoring 0).Policy () := by
  classical
  intro info
  by_cases hinfo : info = site 0
  · exact chanceGame.actionChoiceEquiv 0 () info
      ((chanceGame.actionChoiceEquiv 0 () []).symm (policy []))
  · exact policy info

theorem correlate_at_site
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    correlate policy (site 0) =
      chanceGame.actionChoiceEquiv 0 () (site 0)
        ((chanceGame.actionChoiceEquiv 0 () []).symm (policy [])) := by
  simp [correlate]

theorem correlate_at_root
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    correlate policy [] = policy [] := by
  simp [correlate]

theorem correlate_decoded_agree
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    (chanceGame.actionChoiceEquiv 0 () (site 0)).symm
        (correlate policy (site 0)) =
      (chanceGame.actionChoiceEquiv 0 () []).symm
        (correlate policy []) := by
  rw [correlate_at_site, correlate_at_root]
  simp

def agreeSet : Set ((chanceGame.perfectMonitoring 0).Policy ()) :=
  {policy |
    (chanceGame.actionChoiceEquiv 0 () (site 0)).symm (policy (site 0)) =
      (chanceGame.actionChoiceEquiv 0 () []).symm (policy [])}

theorem agreeSet_measurable : MeasurableSet agreeSet := by
  unfold agreeSet
  have hleft : Measurable (fun policy : (chanceGame.perfectMonitoring 0).Policy () =>
      (chanceGame.actionChoiceEquiv 0 () (site 0)).symm
        (policy (site 0))) :=
    (measurable_of_finite _).comp (measurable_pi_apply (site 0))
  have hright : Measurable (fun policy : (chanceGame.perfectMonitoring 0).Policy () =>
      (chanceGame.actionChoiceEquiv 0 () []).symm (policy [])) :=
    (measurable_of_finite _).comp (measurable_pi_apply [])
  exact measurableSet_eq_fun hleft hright

theorem correlate_measurable : Measurable correlate := by
  rw [measurable_pi_iff]
  intro info
  by_cases hinfo : info = site 0
  · subst info
    simp_rw [correlate_at_site]
    exact (measurable_of_finite fun choice =>
      chanceGame.actionChoiceEquiv 0 () (site 0)
        ((chanceGame.actionChoiceEquiv 0 () []).symm choice)).comp
      (measurable_pi_apply [])
  · have hcoordinate : ∀ policy,
        correlate policy info = policy info := by
      intro policy
      simp [correlate, hinfo]
    simp_rw [hcoordinate]
    exact measurable_pi_apply info

def correlatedMeasure : Measure ((chanceGame.perfectMonitoring 0).Policy ()) :=
  fairMeasure.map correlate

local instance correlatedMeasure_isProbability :
    IsProbabilityMeasure correlatedMeasure := by
  let : IsProbabilityMeasure fairMeasure := fairPolicy_isProbability
  unfold correlatedMeasure
  infer_instance

private def restore
    (target : (chanceGame.perfectMonitoring 0).Policy ())
    (choice : (chanceGame.perfectMonitoring 0).Choice () (site 0)) :
    (chanceGame.perfectMonitoring 0).Policy () := by
  classical
  intro info
  by_cases hinfo : info = site 0
  · subst info
    exact choice
  · exact target info

private theorem correlate_preimage_finite
    (target : (chanceGame.perfectMonitoring 0).Policy ()) :
    (correlate ⁻¹' {target}).Finite := by
  apply (Set.finite_range (restore target)).subset
  intro policy hpolicy
  refine ⟨policy (site 0), ?_⟩
  funext info
  by_cases hinfo : info = site 0
  · subst info
    simp [restore]
  · have hvalue := congrFun hpolicy info
    simp [correlate, hinfo] at hvalue
    simpa [restore, hinfo] using hvalue.symm

/-- No total policy is an atom of the correlated measure. In particular, this
measure is not a PMF on total policies disguised as a measure. -/
theorem correlatedMeasure_singleton_zero
    (policy : (chanceGame.perfectMonitoring 0).Policy ()) :
    correlatedMeasure {policy} = 0 := by
  have : NullSingletonClass fairMeasure :=
    ⟨fairPolicy_singleton_zero⟩
  rw [correlatedMeasure,
    Measure.map_apply correlate_measurable (measurableSet_singleton policy)]
  exact (correlate_preimage_finite policy).countable.measure_zero fairMeasure

theorem correlated_choices_agree : correlatedMeasure agreeSet = 1 := by
  let : IsProbabilityMeasure fairMeasure := fairPolicy_isProbability
  rw [correlatedMeasure,
    Measure.map_apply correlate_measurable agreeSet_measurable]
  have hpreimage : correlate ⁻¹' agreeSet = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro policy
    exact correlate_decoded_agree policy
  rw [hpreimage, measure_univ]

theorem correlatedMeasure_not_pmf :
    ¬ ∃ law : PMF ((chanceGame.perfectMonitoring 0).Policy ()),
        law.toMeasure = correlatedMeasure := by
  rintro ⟨law, hmeasure⟩
  obtain ⟨policy, hpositive⟩ := law.support_nonempty
  have hmass := PMF.toMeasure_apply_singleton law policy
    (measurableSet_singleton policy)
  rw [hmeasure, correlatedMeasure_singleton_zero] at hmass
  exact hpositive hmass.symm

/-- The copied choice is genuinely random: the root marginal remains fair. -/
theorem correlated_root_marginal :
    correlatedMeasure.map (fun policy => policy []) =
      (fairPolicy []).toMeasure := by
  have hroot : (fun policy : (chanceGame.perfectMonitoring 0).Policy () =>
      correlate policy []) = (fun policy => policy []) := by
    funext policy
    exact correlate_at_root policy
  unfold correlatedMeasure fairMeasure
  rw [Measure.map_map (measurable_pi_apply []) correlate_measurable]
  rw [show (fun policy => policy []) ∘ correlate =
    (fun policy => policy []) from hroot]
  exact Measure.infinitePi_map_eval _ []

def rootChoice (answer : Bool) :
    (chanceGame.perfectMonitoring 0).Choice () [] :=
  chanceGame.actionChoiceEquiv 0 () [] answer

theorem correlated_root_choice_mass (answer : Bool) :
    correlatedMeasure {policy | policy [] = rootChoice answer} =
      (1 / 2 : ENNReal) := by
  have heval : Measurable
      (fun policy : (chanceGame.perfectMonitoring 0).Policy () => policy []) :=
    measurable_pi_apply []
  have hset : {policy : (chanceGame.perfectMonitoring 0).Policy () |
      policy [] = rootChoice answer} =
      (fun policy => policy []) ⁻¹' {rootChoice answer} := rfl
  rw [hset, ← Measure.map_apply heval (measurableSet_singleton _),
    correlated_root_marginal,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hcard : Fintype.card
      ((chanceGame.perfectMonitoring 0).Choice () []) = 2 := by
    calc
      _ = Fintype.card Bool :=
        Fintype.card_congr (chanceGame.actionChoiceEquiv 0 () []).symm
      _ = 2 := by decide
  norm_num [fairPolicy, PMF.uniformOfFintype_apply, hcard]

def laws : chanceGame.ProtocolPolicyMeasureProfile 0 :=
  fun _ => correlatedMeasure

local instance laws_isProbability :
    ∀ i, IsProbabilityMeasure (laws i) :=
  fun _ => correlatedMeasure_isProbability

def fallback : chanceGame.PurePublicProfile := fun _ _ => false

/-- The canonical stochastic runner reads the correlated nonatomic measure
behaviorally at every finite horizon, including horizons with infinitely many
reachable information sites. -/
theorem all_prefixes :
    ∀ horizon,
      chanceGame.protocolPolicyMeasureRun 0 laws horizon =
        ((chanceGame.publicHorizonForm 0 horizon).play
          (chanceGame.policyMeasuresToPublicBehavioralWith 0
            laws fallback)).toMeasure :=
  chanceGame.kuhn_arbitraryPolicyMeasure_allFinitePrefixes 0 laws fallback

theorem horizon_two_with_infinite_sites :
    (chanceGame.boundedInformationSites 0 2 ()).Infinite ∧
      chanceGame.protocolPolicyMeasureRun 0 laws 2 =
        ((chanceGame.publicHorizonForm 0 2).play
          (chanceGame.policyMeasuresToPublicBehavioralWith 0
            laws fallback)).toMeasure :=
  ⟨boundedSites_two_infinite, all_prefixes 2⟩

end GameTheory.Experimental.PostArchitecture.PMFPolicyMeasureReverseGate
