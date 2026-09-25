import GameTheory.Protocol.Strategic
import GameTheory.Protocol.StrategicRealization
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.HistoryPathMass
import GameTheory.Math.Discounted
import GameTheory.Math.Probability.Measure
import GameTheory.Math.Probability.FiniteSampling
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.ConditionalProbability

/-!
# Policy-measure realization

Independent product measures over total pure policies provide a behavioral
realization even when no PMF on those policies has the requested marginals.
Forward finite-prefix laws need no finite information-site cover. Conditional
reading of an arbitrary policy measure uses countable choice coordinates.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability MeasureTheory

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

variable [∀ i info, MeasurableSpace (M.Choice i info)]

namespace BehavioralPolicy

/-- Independently draw a pure policy's action at every information coordinate. -/
def toPureMeasure {i : ι} (policy : M.BehavioralPolicy i) :
    Measure (M.Policy i) :=
  Measure.infinitePi fun info => (policy info).toMeasure

instance toPureMeasure_isProbability {i : ι}
    (policy : M.BehavioralPolicy i) :
    IsProbabilityMeasure policy.toPureMeasure := by
  unfold toPureMeasure
  constructor
  rw [← cylinder_univ ∅, cylinder,
    ← Measure.map_apply (Finset.measurable_restrict _) MeasurableSet.univ,
    Measure.infinitePi_map_restrict, measure_univ]

theorem toPureMeasure_map_restrict {i : ι}
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i)) :
    policy.toPureMeasure.map sites.restrict =
      (independentProduct fun info : sites => policy info).toMeasure := by
  rw [toPureMeasure, Measure.infinitePi_map_restrict,
    toMeasure_independentProduct]

end BehavioralPolicy

variable [Fintype ι]

/-- Independent product of the players' measures on pure policies. -/
def behavioralProfileMeasure (policy : (i : ι) → M.BehavioralPolicy i) :
    Measure ((i : ι) → M.Policy i) :=
  Measure.pi fun i => (policy i).toPureMeasure

instance behavioralProfileMeasure_isProbability
    (policy : (i : ι) → M.BehavioralPolicy i) :
    IsProbabilityMeasure (M.behavioralProfileMeasure policy) := by
  unfold behavioralProfileMeasure
  infer_instance

/-- Every selected policy coordinate has its original behavioral PMF measure
as a marginal of the infinite product over pure policies. -/
theorem behavioralProfileMeasure_map_eval
    (policy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (info : M.InfoState i) :
    (M.behavioralProfileMeasure policy).map (fun pure => pure i info) =
      (policy i info).toMeasure := by
  classical
  have heval : (fun pure : (j : ι) → M.Policy j => pure i info) =
      (fun p : M.Policy i => p info) ∘ (fun pure => pure i) := rfl
  rw [heval, ← Measure.map_map (measurable_pi_apply info)
    (measurable_pi_apply i), behavioralProfileMeasure,
    Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  exact Measure.infinitePi_map_eval (fun info => (policy i info).toMeasure) info

/-- Almost every pre-drawn table uses a supported behavioral choice at any
fixed information coordinate. -/
theorem ae_behavioralProfileMeasure_eval_mem_support
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (info : M.InfoState i) :
    ∀ᵐ pure ∂M.behavioralProfileMeasure policy,
      pure i info ∈ (policy i info).support := by
  let p := policy i info
  have hfull : p.support ∈ ae p.toMeasure := by
    rw [mem_ae_iff]
    exact (p.toMeasure_apply_eq_zero_iff
      (p.support_countable.measurableSet.compl)).2 (by
        apply Set.disjoint_left.mpr
        intro choice hsupport hnot
        exact hnot hsupport)
  have hfull' : ∀ᵐ choice ∂p.toMeasure, choice ∈ p.support := hfull
  have heval : Measurable (fun pure : (j : ι) → M.Policy j => pure i info) := by
    fun_prop
  have hmarginal := M.behavioralProfileMeasure_map_eval policy i info
  exact MeasureTheory.ae_of_ae_map heval.aemeasurable
    (by simpa [p, hmarginal] using hfull')

/-- Almost every pre-drawn table is supported at every information coordinate
visited by the behavioral law through the specified horizon. -/
theorem ae_behavioralProfileMeasure_supportSites
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (horizon : ℕ) :
    ∀ᵐ pure ∂M.behavioralProfileMeasure policy,
      ∀ i info, info ∈ M.behavioralSupportSitesFrom policy horizon E.initHistory i →
        pure i info ∈ (policy i info).support := by
  apply ae_all_iff.mpr
  intro i
  let sites := M.behavioralSupportSitesFrom policy horizon E.initHistory i
  let : Countable sites :=
    (M.behavioralSupportSitesFrom_countable policy horizon E.initHistory i).to_subtype
  have hsites : ∀ᵐ pure ∂M.behavioralProfileMeasure policy,
      ∀ info : sites, pure i info.1 ∈ (policy i info.1).support := by
    apply ae_all_iff.mpr
    intro info
    exact M.ae_behavioralProfileMeasure_eval_mem_support policy i info.1
  filter_upwards [hsites] with pure hpure info hinfo
  exact hpure ⟨info, hinfo⟩

/-- Read each player's pure policy at the selected information sites. -/
def restrictPolicies (sites : (i : ι) → Finset (M.InfoState i))
    (policies : (i : ι) → M.Policy i) :
    (i : ι) → (info : sites i) → M.Choice i info :=
  fun i info => policies i info

/-- Independently sample behavioral choices at finitely many sites per player. -/
def finitePolicyDraws
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) :
    PMF ((i : ι) → (info : sites i) → M.Choice i info) :=
  independentProduct fun i => independentProduct fun info : sites i => policy i info

theorem behavioralProfileMeasure_map_restrict
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) :
    (M.behavioralProfileMeasure policy).map (M.restrictPolicies sites) =
      (M.finitePolicyDraws policy sites).toMeasure := by
  classical
  have hrestrict : M.restrictPolicies sites =
      fun policies : (i : ι) → M.Policy i =>
        fun i => (sites i).restrict (policies i) := rfl
  rw [behavioralProfileMeasure, hrestrict,
    Measure.pi_map_pi (fun i =>
      (Finset.measurable_restrict (sites i)).aemeasurable)]
  rw [finitePolicyDraws, toMeasure_independentProduct]
  congr 1
  funext i
  exact (BehavioralPolicy.toPureMeasure_map_restrict (M := M)
    (policy i) (sites i))

/-- Fill selected policy coordinates from sampled choices and use the fallback elsewhere. -/
def assemblePolicies
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i)
    (draws : (i : ι) → (info : sites i) → M.Choice i info) :
    (i : ι) → M.Policy i := by
  classical
  exact fun i => FiniteAssignment.resolve (fallback i) (sites i) (draws i)

omit [∀ i info, MeasurableSpace (M.Choice i info)] in
theorem finitePolicyDraws_map_assemble
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) :
    (M.finitePolicyDraws policy sites).map
        (M.assemblePolicies sites fallback) =
      independentProduct fun i =>
        (policy i).toMixedWithin M (sites i) (fallback i) := by
  classical
  have hassemble : M.assemblePolicies sites fallback =
      fun draws i => FiniteAssignment.resolve (fallback i) (sites i) (draws i) := rfl
  rw [finitePolicyDraws, hassemble, independentProduct_map]
  congr 1
  funext i
  exact (BehavioralPolicy.toMixedWithin_eq_sampleOn M
    (policy i) (sites i) (fallback i)).symm

omit [∀ i info, MeasurableSpace (M.Choice i info)] [Fintype ι] in
theorem run_assemble_restrict
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback policies : (i : ι) → M.Policy i) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.run (M.assemblePolicies sites fallback
        (M.restrictPolicies sites policies)) horizon =
      M.run policies horizon := by
  classical
  apply M.runFrom_congr_of_act_eq horizon E.initHistory
  intro later hreach hterm i
  have hmem := hcover later hreach hterm i
  simpa only [assemblePolicies, restrictPolicies, Policy.act] using
    congrArg Subtype.val (FiniteAssignment.resolve_of_mem
      (fallback i) (sites i) ((M.restrictPolicies sites policies) i) hmem)

/-- Draw a complete pure profile, run it, and retain its finite-horizon history law. -/
def runPureMeasure [MeasurableSpace E.History]
    (policy : (i : ι) → M.BehavioralPolicy i) (horizon : ℕ) :
    Measure E.History :=
  (M.behavioralProfileMeasure policy).bind fun pure =>
    (M.run pure horizon).toMeasure

/-- The pure-run mass of a fixed target is almost everywhere measurable under
the policy product: it reads only that target's finite trace coordinates. -/
theorem aemeasurable_run_mass
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (horizon : ℕ) (target : E.History)
    (fallback : (i : ι) → M.Policy i) :
    AEMeasurable
      (fun pure : (i : ι) → M.Policy i => M.run pure horizon target)
      (M.behavioralProfileMeasure policy) := by
  classical
  let sites : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let draws := M.finitePolicyDraws policy sites
  let mass := fun assignment => M.run (assemble assignment) horizon target
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hmarginal : (M.behavioralProfileMeasure policy).map restrict =
      draws.toMeasure := M.behavioralProfileMeasure_map_restrict policy sites
  have hfull : draws.toMeasure draws.supportᶜ = 0 :=
    (draws.toMeasure_apply_eq_zero_iff draws.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro assignment hsupport hnot
        exact hnot hsupport)
  have hmass : AEMeasurable mass draws.toMeasure :=
    aemeasurable_of_countable_full_set draws.toMeasure mass draws.support
      draws.support_countable hfull
  have hmassMapped : AEMeasurable mass
      ((M.behavioralProfileMeasure policy).map restrict) := by
    rw [hmarginal]
    exact hmass
  have hpointwise (pure : (i : ι) → M.Policy i) :
      M.run pure horizon target = mass (restrict pure) := by
    apply M.run_apply_congr_of_queriedInfos pure (assemble (restrict pure))
      horizon target
    intro i info hmem
    exact (FiniteAssignment.resolve_restrict_of_mem
      (fallback i) (pure i) (sites i) (by simpa [sites] using hmem)).symm
  apply (hmassMapped.comp_measurable hrestrict).congr
  exact Filter.Eventually.of_forall fun pure => (hpointwise pure).symm

/-- The point mass of any target, integrated over independently
pre-drawn pure policies, equals its behavioral point mass. Each integrand
depends on only the finitely many coordinates in the target trace. -/
theorem lintegral_run_mass
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i)
    (horizon : ℕ) (target : E.History) :
    (∫⁻ pure, M.run pure horizon target ∂M.behavioralProfileMeasure policy) =
      M.runBehavioral policy horizon target := by
  classical
  let sites : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let draws := M.finitePolicyDraws policy sites
  let mass := fun assignment => M.run (assemble assignment) horizon target
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hmarginal : (M.behavioralProfileMeasure policy).map restrict =
      draws.toMeasure := M.behavioralProfileMeasure_map_restrict policy sites
  have hfull : draws.toMeasure draws.supportᶜ = 0 :=
    (draws.toMeasure_apply_eq_zero_iff draws.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro assignment hsupport hnot
        exact hnot hsupport)
  have hmass : AEMeasurable mass draws.toMeasure :=
    aemeasurable_of_countable_full_set draws.toMeasure mass draws.support
      draws.support_countable hfull
  have hmassMapped : AEMeasurable mass
      ((M.behavioralProfileMeasure policy).map restrict) := by
    rw [hmarginal]
    exact hmass
  have hpointwise (pure : (i : ι) → M.Policy i) :
      M.run pure horizon target = mass (restrict pure) := by
    apply M.run_apply_congr_of_queriedInfos pure (assemble (restrict pure))
      horizon target
    intro i info hmem
    exact (FiniteAssignment.resolve_restrict_of_mem
      (fallback i) (pure i) (sites i) (by simpa [sites] using hmem)).symm
  have hdrawRun : draws.bind
      (fun assignment => M.run (assemble assignment) horizon) =
        M.runMixed
          (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
          horizon := by
    unfold draws InformationModel.runMixed InformationModel.runMixedFrom InformationModel.run
    rw [← M.finitePolicyDraws_map_assemble policy sites fallback, PMF.bind_map]
    rfl
  have hlocal : (draws.bind
      (fun assignment => M.run (assemble assignment) horizon)) target =
        M.runBehavioral policy horizon target := by
    rw [hdrawRun]
    exact M.runMixed_toMixedWithin_apply_of_queriedInfos hactsOnce
      sites policy fallback horizon target
      (by intro i info hmem; simpa [sites] using hmem)
  calc
    (∫⁻ pure, M.run pure horizon target ∂M.behavioralProfileMeasure policy) =
        ∫⁻ pure, mass (restrict pure) ∂M.behavioralProfileMeasure policy := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall hpointwise
    _ = ∫⁻ assignment, mass assignment ∂draws.toMeasure := by
      rw [← hmarginal]
      exact (lintegral_map' hmassMapped hrestrict.aemeasurable).symm
    _ = (draws.bind fun assignment => M.run (assemble assignment) horizon) target := by
      rw [← PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target),
        ← toMeasure_bind draws (fun assignment => M.run (assemble assignment) horizon),
        Measure.bind_apply (measurableSet_singleton target)
          (aemeasurable_toMeasure_kernel draws
            (fun assignment => M.run (assemble assignment) horizon))]
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun assignment =>
        (PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)).symm
    _ = M.runBehavioral policy horizon target := hlocal

/-- Almost every pre-drawn pure run has no outcomes outside the support of
the corresponding behavioral run. The proof integrates target atoms over that
countable support and uses probability mass one. -/
theorem ae_run_support_subset_runBehavioral
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ) :
    ∀ᵐ pure ∂M.behavioralProfileMeasure policy,
      (M.run pure horizon).support ⊆ (M.runBehavioral policy horizon).support := by
  classical
  let s : Set E.History := (M.runBehavioral policy horizon).support
  let : Countable s := (M.runBehavioral policy horizon).support_countable.to_subtype
  let mass : s → ((i : ι) → M.Policy i) → ENNReal :=
    fun history pure => M.run pure horizon history.1
  let total : ((i : ι) → M.Policy i) → ENNReal :=
    fun pure => ∑' history : s, mass history pure
  have hmass (history : s) : AEMeasurable (mass history)
      (M.behavioralProfileMeasure policy) :=
    M.aemeasurable_run_mass policy horizon history.1 fallback
  have htotal : AEMeasurable total (M.behavioralProfileMeasure policy) :=
    AEMeasurable.tsum hmass
  have htotalLe (pure : (i : ι) → M.Policy i) : total pure ≤ 1 := by
    calc
      total pure = ∑' history : E.History,
          s.indicator (fun history => M.run pure horizon history) history := by
        exact tsum_subtype s _
      _ ≤ ∑' history : E.History, M.run pure horizon history := by
        apply ENNReal.tsum_le_tsum
        intro history
        by_cases hmem : history ∈ s <;> simp [hmem]
      _ = 1 := (M.run pure horizon).tsum_coe
  have htotalIntegral :
      (∫⁻ pure, total pure ∂M.behavioralProfileMeasure policy) = 1 := by
    rw [show (∫⁻ pure, total pure ∂M.behavioralProfileMeasure policy) =
        ∑' history : s, ∫⁻ pure, mass history pure
          ∂M.behavioralProfileMeasure policy from lintegral_tsum hmass]
    simp only [mass, M.lintegral_run_mass hactsOnce policy fallback horizon]
    calc
      (∑' history : s, M.runBehavioral policy horizon history.1) =
          ∑' history : E.History,
            s.indicator (M.runBehavioral policy horizon) history :=
        tsum_subtype s _
      _ = ∑' history : E.History, M.runBehavioral policy horizon history := by
        apply tsum_congr
        intro history
        by_cases hmem : history ∈ s
        · simp [hmem]
        · have hzero : M.runBehavioral policy horizon history = 0 :=
            not_ne_iff.mp hmem
          simp [hmem, hzero]
      _ = 1 := (M.runBehavioral policy horizon).tsum_coe
  have htotalOne : total =ᵐ[M.behavioralProfileMeasure policy]
      (fun _ => 1) := by
    apply (lintegral_eq_iff_ae_eq_of_ae_le
      (by rw [htotalIntegral]; exact ENNReal.one_ne_top)
      aemeasurable_const (Filter.Eventually.of_forall htotalLe)).1
    rw [htotalIntegral]
    simp
  filter_upwards [htotalOne] with pure hpure
  apply ((M.run pure horizon).toMeasure_apply_eq_one_iff
    (show MeasurableSet s from (M.runBehavioral policy horizon).support_countable.measurableSet)).1
  rw [PMF.toMeasure_apply
    (M.run pure horizon)
    (show MeasurableSet s from (M.runBehavioral policy horizon).support_countable.measurableSet)]
  rw [← tsum_subtype s]
  exact hpure

/-- The canonical pure-run measure kernel is almost everywhere measurable
under the infinite independent policy product, without a finite site cover. -/
theorem aemeasurable_runPure_kernel
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ) :
    AEMeasurable
      (fun pure : (i : ι) → M.Policy i => (M.run pure horizon).toMeasure)
      (M.behavioralProfileMeasure policy) := by
  let s := (M.runBehavioral policy horizon).support
  apply aemeasurable_toMeasure_of_countable_support
    (M.behavioralProfileMeasure policy)
    (fun pure => M.run pure horizon) s
    (M.runBehavioral policy horizon).support_countable
    (M.ae_run_support_subset_runBehavioral hactsOnce policy fallback horizon)
  intro history _
  exact M.aemeasurable_run_mass policy horizon history fallback

/-- Independent measure-valued predrawing of every pure policy coordinate
realizes the canonical behavioral history law at any finite horizon. No finite
set of information sites is needed, even with infinite chance branching. -/
theorem runPureMeasure_eq_runBehavioral
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (horizon : ℕ) :
    M.runPureMeasure policy horizon =
      (M.runBehavioral policy horizon).toMeasure := by
  classical
  let fallback : (i : ι) → M.Policy i :=
    fun i => (policy i).supportFallback M
  let s : Set E.History := (M.runBehavioral policy horizon).support
  have hs : MeasurableSet s :=
    (M.runBehavioral policy horizon).support_countable.measurableSet
  have hkernel := M.aemeasurable_runPure_kernel hactsOnce policy fallback horizon
  have hsupport := M.ae_run_support_subset_runBehavioral
    hactsOnce policy fallback horizon
  have hfullPure : (M.runPureMeasure policy horizon) sᶜ = 0 := by
    rw [runPureMeasure, Measure.bind_apply hs.compl hkernel]
    have hzero : ∀ᵐ pure ∂M.behavioralProfileMeasure policy,
        (M.run pure horizon).toMeasure sᶜ = 0 := by
      filter_upwards [hsupport] with pure hpure
      apply ((M.run pure horizon).toMeasure_apply_eq_zero_iff hs.compl).2
      apply Set.disjoint_left.mpr
      intro history hmem hnot
      exact hnot (hpure hmem)
    calc
      (∫⁻ pure, (M.run pure horizon).toMeasure sᶜ
          ∂M.behavioralProfileMeasure policy) =
          ∫⁻ pure, (0 : ENNReal) ∂M.behavioralProfileMeasure policy :=
        lintegral_congr_ae hzero
      _ = 0 := by simp
  have hfullBehavioral : (M.runBehavioral policy horizon).toMeasure sᶜ = 0 := by
    apply ((M.runBehavioral policy horizon).toMeasure_apply_eq_zero_iff hs.compl).2
    apply Set.disjoint_left.mpr
    intro history hmem hnot
    exact hnot hmem
  apply measure_ext_of_countable_full_set
    (M.runPureMeasure policy horizon)
    (M.runBehavioral policy horizon).toMeasure s
    (M.runBehavioral policy horizon).support_countable
    hfullPure hfullBehavioral
  intro target _
  rw [runPureMeasure, Measure.bind_apply (measurableSet_singleton target) hkernel,
    PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)]
  calc
    (∫⁻ pure, (M.run pure horizon).toMeasure {target}
        ∂M.behavioralProfileMeasure policy) =
        ∫⁻ pure, M.run pure horizon target
          ∂M.behavioralProfileMeasure policy := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun pure =>
        PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)
    _ = M.runBehavioral policy horizon target :=
      M.lintegral_run_mass hactsOnce policy fallback horizon target

/-- The cover-free forward law also applies after a behavioral replacement of
one player. -/
theorem runPureMeasure_update_eq_runBehavioral_update
    [DecidableEq ι]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : Profile M.behavioralSignature)
    (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runPureMeasure
        (Profile.update (sig := M.behavioralSignature)
          policy who replacement) horizon =
      (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          policy who replacement) horizon).toMeasure :=
  M.runPureMeasure_eq_runBehavioral hactsOnce
    (Profile.update (sig := M.behavioralSignature)
      policy who replacement) horizon

/-! ## Reading arbitrary laws over total deterministic policies -/

/-- A law over one player's total deterministic policies. -/
abbrev PolicyMeasure (i : ι) := Measure (M.Policy i)

/-- The profile signature for independent policy-measure laws. -/
abbrev policyMeasureSignature : GameSignature ι where
  Strategy i := M.PolicyMeasure i
  Outcome := E.History

omit [Fintype ι] in
/-- A finite own-play record determines a measurable cylinder. -/
theorem measurableSet_consistent
    {i : ι} [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (record : List (M.InfoState i × E.Action i)) :
    MeasurableSet (M.Consistent i record) := by
  induction record with
  | nil => simp [InformationModel.Consistent]
  | cons step rest ih =>
    have hchoice : MeasurableSet
        {choice : M.Choice i step.1 | choice.1 = some step.2} := by
      apply Set.Finite.measurableSet
      apply Set.Subsingleton.finite
      intro first hfirst second hsecond
      exact Subtype.ext (hfirst.trans hsecond.symm)
    have hhead : MeasurableSet
        {policy : M.Policy i | (policy step.1).1 = some step.2} :=
      (measurable_pi_apply step.1) hchoice
    rw [show M.Consistent i (step :: rest) =
        {policy : M.Policy i | (policy step.1).1 = some step.2} ∩
          M.Consistent i rest by
      ext policy
      simp [InformationModel.Consistent]]
    exact hhead.inter ih

omit [Fintype ι] in
/-- The own-record consistency cylinder at an information state is measurable. -/
theorem measurableSet_consistentAt
    {i : ι} [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (info : M.InfoState i) :
    MeasurableSet (M.ConsistentAt i info) :=
  M.measurableSet_consistent (M.recordAt i info)

namespace PolicyMeasure

open Classical

/-- Read a policy measure behaviorally by conditioning on the player's own
record. Only a countable choice carrier can be read back as a PMF. -/
noncomputable def toBehavioralWith {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (law : M.PolicyMeasure i) [IsProbabilityMeasure law]
    (fallback : M.Policy i) : M.BehavioralPolicy i := fun info =>
  if hpos : law (M.ConsistentAt i info) ≠ 0 then
    let conditioned := ProbabilityTheory.cond law (M.ConsistentAt i info)
    letI : IsProbabilityMeasure conditioned :=
      ProbabilityTheory.cond_isProbabilityMeasure hpos
    let pushed := conditioned.map (fun policy => policy info)
    letI : IsProbabilityMeasure pushed := inferInstance
    pushed.toPMF
  else
    PMF.pure (fallback info)

omit [Fintype ι] in
/-- The behavioral reading respects equality of policy measures. -/
theorem toBehavioralWith_congr {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (first second : M.PolicyMeasure i)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (fallback : M.Policy i) (h : first = second) :
    PolicyMeasure.toBehavioralWith (M := M) first fallback =
      PolicyMeasure.toBehavioralWith (M := M) second fallback := by
  subst second
  rfl

omit [Fintype ι] in
/-- The measure-theoretic behavioral reading agrees with the reading of a
mixed PMF through its canonical measure. -/
theorem toBehavioralWith_toMeasure {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (mixed : M.MixedPolicy i) (fallback : M.Policy i)
    (info : M.InfoState i) :
    PolicyMeasure.toBehavioralWith (M := M) mixed.toMeasure fallback info =
      mixed.toBehavioralWith fallback info := by
  classical
  let consistent := M.ConsistentAt i info
  have hconsistent : MeasurableSet consistent :=
    M.measurableSet_consistentAt info
  by_cases hmeet : ∃ policy ∈ consistent, policy ∈ mixed.support
  · have hmass : mixed.toMeasure consistent ≠ 0 := by
      intro hzero
      obtain ⟨policy, hpolicy, hsupport⟩ := hmeet
      exact (Set.disjoint_left.mp
        ((mixed.toMeasure_apply_eq_zero_iff hconsistent).1 hzero))
        hsupport hpolicy
    rw [PolicyMeasure.toBehavioralWith, MixedPolicy.toBehavioralWith,
      dite_eq_left hmass, dite_eq_left hmeet]
    exact toPMF_map_cond_toMeasure mixed consistent hconsistent hmeet
      (fun policy => policy info) (measurable_pi_apply info)
  · have hmass : mixed.toMeasure consistent = 0 := by
      apply (mixed.toMeasure_apply_eq_zero_iff hconsistent).2
      exact Set.disjoint_left.mpr fun policy hsupport hcons =>
        hmeet ⟨policy, hcons, hsupport⟩
    rw [PolicyMeasure.toBehavioralWith, MixedPolicy.toBehavioralWith,
      dite_eq_right hmeet, dite_eq_right (not_ne_iff.mpr hmass)]

/-- Restrict an arbitrary policy measure to finitely many coordinates, read
that countable marginal as a PMF, and fill the other coordinates. -/
noncomputable def toMixedWithin {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (law : M.PolicyMeasure i) [IsProbabilityMeasure law]
    (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) : M.MixedPolicy i := by
  classical
  let restricted := law.map sites.restrict
  letI : IsProbabilityMeasure restricted := inferInstance
  exact restricted.toPMF.map (FiniteAssignment.resolve fallback sites)

omit [Fintype ι] in
/-- A finite marginal of the independent total-policy measure recovers the
canonical finite predraw without finite action carriers. -/
theorem toMixedWithin_toPureMeasure {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) :
    PolicyMeasure.toMixedWithin (M := M) policy.toPureMeasure sites fallback =
      policy.toMixedWithin M sites fallback := by
  classical
  have hdraw : (policy.toPureMeasure.map sites.restrict).toPMF =
      independentProduct (fun info : sites => policy info) := by
    apply PMF.ext
    intro draw
    rw [Measure.toPMF_apply,
      BehavioralPolicy.toPureMeasure_map_restrict]
    exact PMF.toMeasure_apply_singleton _ draw (measurableSet_singleton draw)
  simp only [PolicyMeasure.toMixedWithin, hdraw,
    BehavioralPolicy.toMixedWithin_eq_sampleOn,
    FiniteAssignment.sampleOn]

omit [Fintype ι] in
/-- Finite predrawing from an arbitrary policy measure is the pushforward of
that measure through restriction and fallback assembly. -/
theorem toMixedWithin_toMeasure {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (law : M.PolicyMeasure i) [IsProbabilityMeasure law]
    (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) :
    (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toMeasure =
      law.map (fun policy => FiniteAssignment.resolve fallback sites
        (sites.restrict policy)) := by
  classical
  have hassemble : Measurable (FiniteAssignment.resolve fallback sites) :=
    measurable_of_countable _
  have hrestrict : Measurable
      (sites.restrict : M.Policy i → (info : sites) → M.Choice i info) :=
    Finset.measurable_restrict sites
  have hread : ((law.map sites.restrict).toPMF).toMeasure =
      law.map sites.restrict := Measure.toPMF_toMeasure _
  simp only [PolicyMeasure.toMixedWithin]
  rw [← PMF.toMeasure_map (p := (law.map sites.restrict).toPMF)
      (f := FiniteAssignment.resolve fallback sites) hassemble,
    hread,
    Measure.map_map hassemble hrestrict]
  rfl

omit [Fintype ι] in
/-- A measurable transformation preserving the own-record cylinder and the
current choice coordinate leaves the behavioral reading unchanged. -/
theorem toBehavioralWith_map_eq_of_preserves {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (law : M.PolicyMeasure i) [IsProbabilityMeasure law]
    (fallback : M.Policy i) (info : M.InfoState i)
    (transform : M.Policy i → M.Policy i) (htransform : Measurable transform)
    [IsProbabilityMeasure (law.map transform)]
    (hconsistent : ∀ policy,
      transform policy ∈ M.ConsistentAt i info ↔
        policy ∈ M.ConsistentAt i info)
    (hchoice : ∀ policy, transform policy info = policy info) :
    PolicyMeasure.toBehavioralWith (M := M) (law.map transform) fallback info =
      PolicyMeasure.toBehavioralWith (M := M) law fallback info := by
  let consistent := M.ConsistentAt i info
  have hmeasurable : MeasurableSet consistent := M.measurableSet_consistentAt info
  have hpreimage : transform ⁻¹' consistent = consistent := by
    ext policy
    exact hconsistent policy
  have hmass : (law.map transform) consistent = law consistent := by
    rw [Measure.map_apply htransform hmeasurable, hpreimage]
  by_cases hpos : law consistent ≠ 0
  · have hmappos : (law.map transform) consistent ≠ 0 := by
      rw [hmass]
      exact hpos
    have hpushed :
        (ProbabilityTheory.cond (law.map transform) consistent).map
            (fun policy => policy info) =
          (ProbabilityTheory.cond law consistent).map
            (fun policy => policy info) := by
      ext event hevent
      let answer := (fun policy : M.Policy i => policy info) ⁻¹' event
      have hanswer : MeasurableSet answer := (measurable_pi_apply info) hevent
      have hinter : MeasurableSet (consistent ∩ answer) :=
        hmeasurable.inter hanswer
      have hinterPreimage : transform ⁻¹' (consistent ∩ answer) =
          consistent ∩ answer := by
        ext policy
        have hanswerEq : transform policy ∈ answer ↔ policy ∈ answer := by
          simp only [answer, Set.mem_preimage, hchoice policy]
        simp only [Set.mem_preimage, Set.mem_inter_iff, hanswerEq]
        rw [show transform policy ∈ consistent ↔ policy ∈ consistent from
          hconsistent policy]
      rw [Measure.map_apply (measurable_pi_apply info) hevent,
        Measure.map_apply (measurable_pi_apply info) hevent,
        ProbabilityTheory.cond_apply hmeasurable,
        ProbabilityTheory.cond_apply hmeasurable,
        hmass, Measure.map_apply htransform hinter, hinterPreimage]
    dsimp only [consistent] at hpos hmappos hpushed ⊢
    simp only [PolicyMeasure.toBehavioralWith,
      dite_eq_left hmappos, dite_eq_left hpos]
    apply PMF.ext
    intro choice
    rw [Measure.toPMF_apply, Measure.toPMF_apply]
    exact congrArg (fun ν : Measure (M.Choice i info) => ν {choice}) hpushed
  · have hmapzero : (law.map transform) consistent = 0 := by
      rw [hmass]
      exact not_ne_iff.mp hpos
    dsimp only [consistent] at hpos hmapzero ⊢
    simp only [PolicyMeasure.toBehavioralWith,
      dite_eq_right hpos, dite_eq_right (not_ne_iff.mpr hmapzero)]

omit [Fintype ι] in
/-- A finite marginal preserving the current site and every coordinate of its
own-play record has the same behavioral reading as the original measure. -/
theorem toMixedWithin_toBehavioralWith {i : ι}
    [∀ info, Countable (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (law : M.PolicyMeasure i) [IsProbabilityMeasure law]
    (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) (info : M.InfoState i)
    (hinfo : info ∈ sites)
    (hrecord : ∀ step ∈ M.recordAt i info, step.1 ∈ sites) :
    (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toBehavioralWith
        fallback info =
      PolicyMeasure.toBehavioralWith (M := M) law fallback info := by
  classical
  let transform : M.Policy i → M.Policy i := fun policy =>
    FiniteAssignment.resolve fallback sites (sites.restrict policy)
  have hassemble : Measurable (FiniteAssignment.resolve fallback sites) :=
    measurable_of_countable _
  have hrestrict : Measurable
      (sites.restrict : M.Policy i → (site : sites) → M.Choice i site) :=
    Finset.measurable_restrict sites
  have htransform : Measurable transform := hassemble.comp hrestrict
  let : IsProbabilityMeasure (law.map transform) := inferInstance
  have hchoice (policy : M.Policy i) : transform policy info = policy info :=
    FiniteAssignment.resolve_restrict_of_mem fallback policy sites hinfo
  have hconsistent (policy : M.Policy i) :
      transform policy ∈ M.ConsistentAt i info ↔
        policy ∈ M.ConsistentAt i info := by
    constructor
    · intro hp step hstep
      have hanswer := hp step hstep
      have hchoiceAt : transform policy step.1 = policy step.1 :=
        FiniteAssignment.resolve_restrict_of_mem fallback policy sites
          (hrecord step hstep)
      rw [hchoiceAt] at hanswer
      exact hanswer
    · intro hp step hstep
      have hanswer := hp step hstep
      have hchoiceAt : transform policy step.1 = policy step.1 :=
        FiniteAssignment.resolve_restrict_of_mem fallback policy sites
          (hrecord step hstep)
      rw [hchoiceAt]
      exact hanswer
  calc
    (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toBehavioralWith
        fallback info =
        PolicyMeasure.toBehavioralWith (M := M)
          (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toMeasure
          fallback info :=
      (PolicyMeasure.toBehavioralWith_toMeasure (M := M)
        (PolicyMeasure.toMixedWithin (M := M) law sites fallback)
        fallback info).symm
    _ = PolicyMeasure.toBehavioralWith (M := M) (law.map transform)
        fallback info := by
      exact congrFun (PolicyMeasure.toBehavioralWith_congr (M := M)
        (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toMeasure
        (law.map transform) fallback
        (PolicyMeasure.toMixedWithin_toMeasure (M := M) law sites fallback)) info
    _ = PolicyMeasure.toBehavioralWith (M := M) law fallback info :=
      PolicyMeasure.toBehavioralWith_map_eq_of_preserves (M := M)
        law fallback info transform htransform hconsistent hchoice

/-- Enlarge a finite site family with all coordinates in its recalled records. -/
noncomputable def recordClosure {i : ι}
    (sites : Finset (M.InfoState i)) : Finset (M.InfoState i) := by
  classical
  exact sites ∪ sites.biUnion fun info =>
    (M.recordAt i info).map Prod.fst |>.toFinset

omit [Fintype ι] [∀ i info, MeasurableSpace (M.Choice i info)] in
/-- Record closure contains the original finite sites. -/
theorem mem_recordClosure {i : ι} (sites : Finset (M.InfoState i))
    {info : M.InfoState i} (hinfo : info ∈ sites) :
    info ∈ PolicyMeasure.recordClosure (M := M) sites := by
  classical
  simp [PolicyMeasure.recordClosure, hinfo]

omit [Fintype ι] [∀ i info, MeasurableSpace (M.Choice i info)] in
/-- Record closure contains every site named by each retained own-play record. -/
theorem record_mem_recordClosure {i : ι}
    (sites : Finset (M.InfoState i)) {info : M.InfoState i}
    (hinfo : info ∈ sites) {step : M.InfoState i × E.Action i}
    (hstep : step ∈ M.recordAt i info) :
    step.1 ∈ PolicyMeasure.recordClosure (M := M) sites := by
  classical
  rw [PolicyMeasure.recordClosure, Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  exact ⟨info, hinfo, by
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨step, hstep, rfl⟩⟩

end PolicyMeasure

/-- The independent finite-player product of arbitrary policy measures. -/
def policyProfileMeasure (laws : (i : ι) → M.PolicyMeasure i) :
    Measure ((i : ι) → M.Policy i) :=
  Measure.pi laws

instance policyProfileMeasure_isProbability
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)] :
    IsProbabilityMeasure (M.policyProfileMeasure laws) := by
  unfold policyProfileMeasure
  infer_instance

/-- The finite PMF of player-indexed coordinate marginals of arbitrary
policy measures. Countability is needed only when reading each marginal. -/
noncomputable def finitePolicyMeasureDraws
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i)) :
    PMF ((i : ι) → (info : sites i) → M.Choice i info) := by
  classical
  let restricted := fun i => (laws i).map (sites i).restrict
  letI (i : ι) : IsProbabilityMeasure (restricted i) := inferInstance
  exact independentProduct fun i => (restricted i).toPMF

/-- Finite restrictions of the independent policy-profile measure are exactly
those finite PMF marginals. -/
theorem policyProfileMeasure_map_restrict
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i)) :
    (M.policyProfileMeasure laws).map (M.restrictPolicies sites) =
      (M.finitePolicyMeasureDraws laws sites).toMeasure := by
  classical
  have hrestrict : M.restrictPolicies sites =
      fun policies : (i : ι) → M.Policy i =>
        fun i => (sites i).restrict (policies i) := rfl
  rw [policyProfileMeasure, hrestrict,
    Measure.pi_map_pi (fun i =>
      (Finset.measurable_restrict (sites i)).aemeasurable)]
  rw [finitePolicyMeasureDraws, toMeasure_independentProduct]
  congr 1
  funext i
  exact (Measure.toPMF_toMeasure _).symm

/-- Assembling arbitrary finite policy-measure marginals coordinatewise gives
the corresponding mixed PMF profile. -/
theorem finitePolicyMeasureDraws_map_assemble
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) :
    (M.finitePolicyMeasureDraws laws sites).map
        (M.assemblePolicies sites fallback) =
      independentProduct fun i =>
        PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i) := by
  classical
  have hassemble : M.assemblePolicies sites fallback =
      fun draws i => FiniteAssignment.resolve (fallback i) (sites i) (draws i) := rfl
  rw [finitePolicyMeasureDraws, hassemble, independentProduct_map]
  rfl

/-- Integrate the canonical deterministic runner after independently drawing
one total policy from each player's arbitrary policy measure. -/
def runPolicyMeasure [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i) (horizon : ℕ) :
    Measure E.History :=
  (M.policyProfileMeasure laws).bind fun pure =>
    (M.run pure horizon).toMeasure

/-- A covered bounded run under arbitrary policy measures depends only on the
finite marginals consumed by the existing mixed runner. -/
theorem runPolicyMeasure_eq_runMixedWithin
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.runPolicyMeasure laws horizon =
      (M.runMixed
        (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i)) horizon).toMeasure := by
  classical
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let kernel := fun draws => (M.run (assemble draws) horizon).toMeasure
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hmarginal : (M.policyProfileMeasure laws).map restrict =
      (M.finitePolicyMeasureDraws laws sites).toMeasure :=
    M.policyProfileMeasure_map_restrict laws sites
  have hkernel : AEMeasurable kernel
      ((M.policyProfileMeasure laws).map restrict) := by
    rw [hmarginal]
    exact aemeasurable_toMeasure_kernel (M.finitePolicyMeasureDraws laws sites)
      (fun draws => M.run (assemble draws) horizon)
  have hpointwise (pure : (i : ι) → M.Policy i) :
      (M.run pure horizon).toMeasure = kernel (restrict pure) := by
    exact congrArg PMF.toMeasure
      (M.run_assemble_restrict sites fallback pure horizon hcover).symm
  have hbindMap :
      (M.policyProfileMeasure laws).bind
          (fun pure => kernel (restrict pure)) =
        ((M.policyProfileMeasure laws).map restrict).bind kernel := by
    unfold Measure.bind
    exact congrArg Measure.join (AEMeasurable.map_map_of_aemeasurable
      hkernel hrestrict.aemeasurable).symm
  have hfiniteBind :
      (M.finitePolicyMeasureDraws laws sites).toMeasure.bind kernel =
        ((M.finitePolicyMeasureDraws laws sites).bind fun draws =>
          M.run (assemble draws) horizon).toMeasure :=
    toMeasure_bind (M.finitePolicyMeasureDraws laws sites)
      (fun draws => M.run (assemble draws) horizon)
  have hdrawRun :
      (M.finitePolicyMeasureDraws laws sites).bind
          (fun draws => M.run (assemble draws) horizon) =
        M.runMixed
          (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
            (sites i) (fallback i)) horizon := by
    unfold InformationModel.runMixed InformationModel.runMixedFrom
      InformationModel.run
    rw [← M.finitePolicyMeasureDraws_map_assemble laws sites fallback,
      PMF.bind_map]
    rfl
  unfold runPolicyMeasure
  calc
    (M.policyProfileMeasure laws).bind
        (fun pure => (M.run pure horizon).toMeasure) =
        (M.policyProfileMeasure laws).bind
          (fun pure => kernel (restrict pure)) :=
      Measure.bind_congr_right (Filter.Eventually.of_forall hpointwise)
    _ = ((M.policyProfileMeasure laws).map restrict).bind kernel := hbindMap
    _ = (M.finitePolicyMeasureDraws laws sites).toMeasure.bind kernel := by rw [hmarginal]
    _ = ((M.finitePolicyMeasureDraws laws sites).bind fun draws =>
        M.run (assemble draws) horizon).toMeasure := hfiniteBind
    _ = (M.runMixed
        (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i)) horizon).toMeasure := congrArg _ hdrawRun

/-- Read each independent policy measure through its own-record conditional
PMF, using the fixed fallback only at zero-mass records. -/
noncomputable def policyMeasureBehavioralWith
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i) :
    (i : ι) → M.BehavioralPolicy i := fun i =>
  PolicyMeasure.toBehavioralWith (M := M) (laws i) (fallback i)

/-- The pure-run mass at one target is measurable under arbitrary independent
policy measures: that mass reads only the target's finite trace coordinates. -/
theorem aemeasurable_runPolicy_mass
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i)
    (horizon : ℕ) (target : E.History) :
    AEMeasurable
      (fun pure : (i : ι) → M.Policy i => M.run pure horizon target)
      (M.policyProfileMeasure laws) := by
  classical
  let sites : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let draws := M.finitePolicyMeasureDraws laws sites
  let mass := fun assignment => M.run (assemble assignment) horizon target
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hmarginal : (M.policyProfileMeasure laws).map restrict =
      draws.toMeasure := M.policyProfileMeasure_map_restrict laws sites
  have hfull : draws.toMeasure draws.supportᶜ = 0 :=
    (draws.toMeasure_apply_eq_zero_iff draws.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro assignment hsupport hnot
        exact hnot hsupport)
  have hmass : AEMeasurable mass draws.toMeasure :=
    aemeasurable_of_countable_full_set draws.toMeasure mass draws.support
      draws.support_countable hfull
  have hmassMapped : AEMeasurable mass
      ((M.policyProfileMeasure laws).map restrict) := by
    rw [hmarginal]
    exact hmass
  have hpointwise (pure : (i : ι) → M.Policy i) :
      M.run pure horizon target = mass (restrict pure) := by
    apply M.run_apply_congr_of_queriedInfos pure (assemble (restrict pure))
      horizon target
    intro i info hmem
    exact (FiniteAssignment.resolve_restrict_of_mem
      (fallback i) (pure i) (sites i) (by simpa [sites] using hmem)).symm
  apply (hmassMapped.comp_measurable hrestrict).congr
  exact Filter.Eventually.of_forall fun pure => (hpointwise pure).symm

/-- The mass integral at one target is the mixed-law mass of any finite
policy-coordinate marginal containing that target's queried sites. -/
theorem lintegral_runPolicy_mass_eq_runMixedWithin_of_queriedInfos
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ) (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i) :
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure laws) =
      M.runMixed (fun i => PolicyMeasure.toMixedWithin (M := M)
        (laws i) (sites i) (fallback i)) horizon target := by
  classical
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let draws := M.finitePolicyMeasureDraws laws sites
  let mass := fun assignment => M.run (assemble assignment) horizon target
  let finiteMixed : (i : ι) → M.MixedPolicy i := fun i =>
    PolicyMeasure.toMixedWithin (M := M) (laws i) (sites i) (fallback i)
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hmarginal : (M.policyProfileMeasure laws).map restrict =
      draws.toMeasure := M.policyProfileMeasure_map_restrict laws sites
  have hfull : draws.toMeasure draws.supportᶜ = 0 :=
    (draws.toMeasure_apply_eq_zero_iff draws.support_countable.measurableSet.compl).2
      (by
        apply Set.disjoint_left.mpr
        intro assignment hsupport hnot
        exact hnot hsupport)
  have hmass : AEMeasurable mass draws.toMeasure :=
    aemeasurable_of_countable_full_set draws.toMeasure mass draws.support
      draws.support_countable hfull
  have hmassMapped : AEMeasurable mass
      ((M.policyProfileMeasure laws).map restrict) := by
    rw [hmarginal]
    exact hmass
  have hpointwise (pure : (i : ι) → M.Policy i) :
      M.run pure horizon target = mass (restrict pure) := by
    apply M.run_apply_congr_of_queriedInfos pure (assemble (restrict pure))
      horizon target
    intro i info hmem
    exact (FiniteAssignment.resolve_restrict_of_mem
      (fallback i) (pure i) (sites i) (hqueried i info hmem)).symm
  have hdrawRun : draws.bind
      (fun assignment => M.run (assemble assignment) horizon) =
        M.runMixed finiteMixed horizon := by
    unfold draws InformationModel.runMixed InformationModel.runMixedFrom
      InformationModel.run
    rw [← M.finitePolicyMeasureDraws_map_assemble laws sites fallback,
      PMF.bind_map]
    rfl
  calc
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure laws) =
        ∫⁻ pure, mass (restrict pure) ∂M.policyProfileMeasure laws := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall hpointwise
    _ = ∫⁻ assignment, mass assignment ∂draws.toMeasure := by
      rw [← hmarginal]
      exact (lintegral_map' hmassMapped hrestrict.aemeasurable).symm
    _ = (draws.bind fun assignment => M.run (assemble assignment) horizon)
        target := by
      rw [PMF.bind_apply]
      conv_lhs => rw [← draws.restrict_toMeasure_support]
      rw [lintegral_countable _ draws.support_countable]
      rw [tsum_subtype draws.support
        (fun assignment => mass assignment * draws.toMeasure {assignment})]
      apply tsum_congr
      intro assignment
      by_cases ha : assignment ∈ draws.support
      · simp [ha, mass, PMF.toMeasure_apply_singleton draws assignment
          (measurableSet_singleton assignment), mul_comm]
      · have hzero : draws assignment = 0 := not_ne_iff.mp ha
        simp [ha, hzero]
    _ = M.runMixed finiteMixed horizon target :=
      congrArg (fun law : PMF E.History => law target) hdrawRun

/-- Each reverse-realization atom is determined by the target's finitely many
queried sites and the finite own-play records needed to read their choices. -/
theorem lintegral_runPolicy_mass
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (hconstrain : M.ConstrainsAlike)
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i)
    (horizon : ℕ) (target : E.History) :
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure laws) =
      M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
        horizon target := by
  classical
  let queried : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let sites : (i : ι) → Finset (M.InfoState i) := fun i =>
    PolicyMeasure.recordClosure (M := M) (queried i)
  have hqueried : ∀ i info,
      info ∈ M.queriedInfos i target.trace → info ∈ sites i := by
    intro i info hinfo
    exact PolicyMeasure.mem_recordClosure (M := M) (queried i)
      (by simpa [queried] using hinfo)
  calc
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure laws) =
        M.runMixed (fun i => PolicyMeasure.toMixedWithin (M := M)
          (laws i) (sites i) (fallback i)) horizon target :=
      M.lintegral_runPolicy_mass_eq_runMixedWithin_of_queriedInfos
        laws fallback sites horizon target hqueried
    _ = M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
        horizon target := by
      rw [M.runMixed_toBehavioralWith hconstrain fallback horizon]
      apply M.runBehavioral_apply_congr_of_queriedInfos
      intro i info hinfo
      have hsite : info ∈ queried i := by simpa [queried] using hinfo
      exact PolicyMeasure.toMixedWithin_toBehavioralWith (M := M)
        (laws i) (sites i) (fallback i) info
        (PolicyMeasure.mem_recordClosure (M := M) (queried i) hsite)
        (fun step hstep =>
          PolicyMeasure.record_mem_recordClosure (M := M) (queried i)
            hsite hstep)
/-- Targetwise integrated mass identities force almost every pure run to be
supported on the target law's countable support. -/
theorem ae_runPolicy_support_subset_of_lintegral_mass
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i)
    (horizon : ℕ) (behavioral : PMF E.History)
    (hatom : ∀ history : E.History,
      (∫⁻ pure, M.run pure horizon history ∂M.policyProfileMeasure laws) =
        behavioral history) :
    ∀ᵐ pure ∂M.policyProfileMeasure laws,
      (M.run pure horizon).support ⊆ behavioral.support := by
  classical
  let s : Set E.History := behavioral.support
  let : Countable s := behavioral.support_countable.to_subtype
  let mass : s → ((i : ι) → M.Policy i) → ENNReal :=
    fun history pure => M.run pure horizon history.1
  let total : ((i : ι) → M.Policy i) → ENNReal :=
    fun pure => ∑' history : s, mass history pure
  have hmass (history : s) : AEMeasurable (mass history)
      (M.policyProfileMeasure laws) :=
    M.aemeasurable_runPolicy_mass laws fallback horizon history.1
  have htotal : AEMeasurable total (M.policyProfileMeasure laws) :=
    AEMeasurable.tsum hmass
  have htotalLe (pure : (i : ι) → M.Policy i) : total pure ≤ 1 := by
    calc
      total pure = ∑' history : E.History,
          s.indicator (fun history => M.run pure horizon history) history := by
        exact tsum_subtype s _
      _ ≤ ∑' history : E.History, M.run pure horizon history := by
        apply ENNReal.tsum_le_tsum
        intro history
        by_cases hmem : history ∈ s <;> simp [hmem]
      _ = 1 := (M.run pure horizon).tsum_coe
  have htotalIntegral :
      (∫⁻ pure, total pure ∂M.policyProfileMeasure laws) = 1 := by
    rw [show (∫⁻ pure, total pure ∂M.policyProfileMeasure laws) =
        ∑' history : s, ∫⁻ pure, mass history pure
          ∂M.policyProfileMeasure laws from lintegral_tsum hmass]
    simp only [mass, hatom]
    calc
      (∑' history : s, behavioral history.1) =
          ∑' history : E.History, s.indicator behavioral history :=
        tsum_subtype s _
      _ = ∑' history : E.History, behavioral history := by
        apply tsum_congr
        intro history
        by_cases hmem : history ∈ s
        · simp [hmem]
        · have hzero : behavioral history = 0 := not_ne_iff.mp hmem
          simp [hmem, hzero]
      _ = 1 := behavioral.tsum_coe
  have htotalOne : total =ᵐ[M.policyProfileMeasure laws]
      (fun _ => 1) := by
    apply (lintegral_eq_iff_ae_eq_of_ae_le
      (by rw [htotalIntegral]; exact ENNReal.one_ne_top)
      aemeasurable_const (Filter.Eventually.of_forall htotalLe)).1
    rw [htotalIntegral]
    simp
  filter_upwards [htotalOne] with pure hpure
  apply ((M.run pure horizon).toOuterMeasure_apply_eq_one_iff s).1
  rw [PMF.toOuterMeasure_apply, ← tsum_subtype s]
  exact hpure

/-- Integrated point masses determine a common countable support and hence
almost-everywhere measurability of the pure-run measure kernel. -/
theorem aemeasurable_runPolicy_kernel_of_lintegral_mass
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (behavioral : PMF E.History)
    (hatom : ∀ history : E.History,
      (∫⁻ pure, M.run pure horizon history ∂M.policyProfileMeasure laws) =
        behavioral history) :
    AEMeasurable
      (fun pure : (i : ι) → M.Policy i => (M.run pure horizon).toMeasure)
      (M.policyProfileMeasure laws) := by
  let s := behavioral.support
  apply aemeasurable_toMeasure_of_countable_support
    (M.policyProfileMeasure laws) (fun pure => M.run pure horizon) s
    behavioral.support_countable
    (M.ae_runPolicy_support_subset_of_lintegral_mass
      laws fallback horizon behavioral hatom)
  intro history _
  exact M.aemeasurable_runPolicy_mass laws fallback horizon history

/-- Targetwise integrated mass equality reconstructs the whole finite-horizon
policy-measure law, without a measurable-singleton history assumption. -/
theorem runPolicyMeasure_eq_toMeasure_of_lintegral_mass
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (behavioral : PMF E.History)
    (hatom : ∀ history : E.History,
      (∫⁻ pure, M.run pure horizon history ∂M.policyProfileMeasure laws) =
        behavioral history) :
    M.runPolicyMeasure laws horizon =
      behavioral.toMeasure := by
  classical
  let s : Set E.History := behavioral.support
  let : Countable s := behavioral.support_countable.to_subtype
  have hkernel := M.aemeasurable_runPolicy_kernel_of_lintegral_mass
    laws fallback horizon behavioral hatom
  have hsupport := M.ae_runPolicy_support_subset_of_lintegral_mass
    laws fallback horizon behavioral hatom
  ext event hevent
  have heventMass (history : s) : AEMeasurable
      (fun pure : (i : ι) → M.Policy i =>
        event.indicator (fun h => M.run pure horizon h) history.1)
      (M.policyProfileMeasure laws) := by
    by_cases hh : history.1 ∈ event
    · simp only [Set.indicator_of_mem hh]
      exact M.aemeasurable_runPolicy_mass laws fallback horizon history.1
    · simp [Set.indicator_of_notMem hh]
  have hrestricted (pure : (i : ι) → M.Policy i)
      (hpure : (M.run pure horizon).support ⊆ s) :
      (M.run pure horizon).toMeasure event =
        ∑' history : s, event.indicator (M.run pure horizon) history.1 := by
    rw [PMF.toMeasure_apply (p := M.run pure horizon) hevent]
    calc
      (∑' history : E.History,
          event.indicator (M.run pure horizon) history) =
          ∑' history : E.History,
            s.indicator (event.indicator (M.run pure horizon)) history := by
        apply tsum_congr
        intro history
        by_cases hh : history ∈ s
        · simp [hh]
        · have hzero : M.run pure horizon history = 0 :=
            (M.run pure horizon).apply_eq_zero_iff history |>.2
              (Set.notMem_subset hpure hh)
          simp [hh, hzero]
      _ = ∑' history : s, event.indicator (M.run pure horizon)
          history.1 := (tsum_subtype s _).symm
  rw [runPolicyMeasure, Measure.bind_apply hevent hkernel,
    PMF.toMeasure_apply (p := behavioral) hevent]
  calc
    (∫⁻ pure, (M.run pure horizon).toMeasure event
        ∂M.policyProfileMeasure laws) =
        ∫⁻ pure, ∑' history : s,
          event.indicator (M.run pure horizon) history.1
          ∂M.policyProfileMeasure laws := by
      apply lintegral_congr_ae
      filter_upwards [hsupport] with pure hpure
      exact hrestricted pure hpure
    _ = ∑' history : s, ∫⁻ pure,
          event.indicator (M.run pure horizon) history.1
          ∂M.policyProfileMeasure laws := lintegral_tsum heventMass
    _ = ∑' history : s,
          event.indicator behavioral history.1 := by
      apply tsum_congr
      intro history
      by_cases hh : history.1 ∈ event
      · simp only [Set.indicator_of_mem hh]
        exact hatom history.1
      · simp [Set.indicator_of_notMem hh]
    _ = ∑' history : E.History,
          event.indicator behavioral history := by
      calc
        (∑' history : s, event.indicator behavioral history.1) =
            ∑' history : E.History,
              s.indicator (event.indicator behavioral) history :=
          tsum_subtype s _
        _ = ∑' history : E.History,
            event.indicator behavioral history := by
          apply tsum_congr
          intro history
          by_cases hh : history ∈ s
          · simp [hh]
          · have hzero : behavioral history = 0 := not_ne_iff.mp hh
            by_cases he : history ∈ event <;> simp [hh, he, hzero]

/-- Arbitrary independent policy measures induce their behavioral reading at
every bounded horizon. Each target mass uses only finitely many policy sites;
no finite set need cover all histories. -/
theorem runPolicyMeasure_eq_runBehavioralWith
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ) :
    M.runPolicyMeasure laws horizon =
      (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
        horizon).toMeasure := by
  apply M.runPolicyMeasure_eq_toMeasure_of_lintegral_mass laws fallback
    horizon _
  exact M.lintegral_runPolicy_mass hconstrain laws fallback horizon

/-- The cover-free reverse law remains valid after replacing one player's
arbitrary policy measure. -/
theorem runPolicyMeasure_update_eq_runBehavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (horizon : ℕ) :
    M.runPolicyMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement) horizon =
      (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon).toMeasure := by
  let updatedLaws : Profile M.policyMeasureSignature :=
    Profile.update (sig := M.policyMeasureSignature) laws who replacement
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update (sig := M.strategicSignature) fallback who
      replacementFallback
  let : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
    by_cases hi : i = who
    · subst i
      simpa only [updatedLaws, Profile.update_same] using
        (inferInstanceAs (IsProbabilityMeasure replacement))
    · simpa only [updatedLaws, Profile.update_of_ne _ _ hi] using
        (inferInstanceAs (IsProbabilityMeasure (laws i)))
  have hprofile : M.policyMeasureBehavioralWith updatedLaws updatedFallback =
      Profile.update (sig := M.behavioralSignature)
        (M.policyMeasureBehavioralWith laws fallback) who
        (PolicyMeasure.toBehavioralWith (M := M) replacement
          replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp only [policyMeasureBehavioralWith, updatedLaws, updatedFallback,
        Profile.update_same]
      exact PolicyMeasure.toBehavioralWith_congr (M := M)
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement who)
        replacement replacementFallback
        (Profile.update_same laws who replacement)
    · simp only [policyMeasureBehavioralWith, updatedLaws, updatedFallback,
        Profile.update_of_ne _ _ hi]
      exact PolicyMeasure.toBehavioralWith_congr (M := M)
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement i)
        (laws i) (fallback i)
        (Profile.update_of_ne laws replacement hi)
  calc
    M.runPolicyMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement) horizon =
        M.runPolicyMeasure updatedLaws horizon := rfl
    _ = (M.runBehavioral
          (M.policyMeasureBehavioralWith updatedLaws updatedFallback)
          horizon).toMeasure :=
      M.runPolicyMeasure_eq_runBehavioralWith hconstrain updatedLaws
        updatedFallback horizon
    _ = (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon).toMeasure :=
      congrArg (fun profile => (M.runBehavioral profile horizon).toMeasure)
        hprofile

/-- A behavioral deviation against arbitrary policy-measure opponents has the
correct target mass without a global finite information-site cover. -/
private theorem lintegral_runPolicy_mass_update_toPureMeasure
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (hrecall : M.PerfectRecall)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (horizon : ℕ) (target : E.History) :
    (∫⁻ pure, M.run pure horizon target
      ∂M.policyProfileMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement.toPureMeasure)) =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who replacement)
        horizon target := by
  classical
  let queried : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let sites : (i : ι) → Finset (M.InfoState i) := fun i =>
    PolicyMeasure.recordClosure (M := M) (queried i)
  let replacementFallback : M.Policy who := replacement.supportFallback M
  let finiteMixed : Profile M.strategicSignature.mixed := fun i =>
    PolicyMeasure.toMixedWithin (M := M) (laws i) (sites i) (fallback i)
  let updatedLaws : Profile M.policyMeasureSignature :=
    Profile.update (sig := M.policyMeasureSignature)
      laws who replacement.toPureMeasure
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update (sig := M.strategicSignature)
      fallback who replacementFallback
  let : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
    by_cases hi : i = who
    · subst i
      simpa only [updatedLaws, Profile.update_same] using
        (inferInstanceAs (IsProbabilityMeasure replacement.toPureMeasure))
    · simpa only [updatedLaws, Profile.update_of_ne _ _ hi] using
        (inferInstanceAs (IsProbabilityMeasure (laws i)))
  have hqueried : ∀ i info,
      info ∈ M.queriedInfos i target.trace → info ∈ sites i := by
    intro i info hinfo
    exact PolicyMeasure.mem_recordClosure (M := M) (queried i)
      (by simpa [queried] using hinfo)
  have hfiniteProfile :
      (fun i => PolicyMeasure.toMixedWithin (M := M) (updatedLaws i)
        (sites i) (updatedFallback i)) =
        Profile.update (sig := M.strategicSignature.mixed)
          finiteMixed who
            (replacement.toMixedWithin M (sites who)
              replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp only [updatedLaws, updatedFallback, Profile.update_same]
      exact PolicyMeasure.toMixedWithin_toPureMeasure
        (M := M) replacement (sites who) replacementFallback
    · simp only [updatedLaws, updatedFallback, finiteMixed,
        Profile.update_of_ne _ _ hi]
  have hbehavioral :
      M.runBehavioral
          (Profile.update (sig := M.behavioralSignature)
            (fun i => InformationModel.MixedPolicy.toBehavioralWith
              (M := M) (finiteMixed i) (fallback i)) who replacement)
          horizon target =
        M.runBehavioral
          (Profile.update (sig := M.behavioralSignature)
            (M.policyMeasureBehavioralWith laws fallback) who replacement)
          horizon target := by
    apply M.runBehavioral_apply_congr_of_queriedInfos
    intro i info hinfo
    by_cases hi : i = who
    · subst i
      simp only [Profile.update_same]
    · simp only [Profile.update_of_ne _ _ hi, finiteMixed,
        policyMeasureBehavioralWith]
      have hsite : info ∈ sites i := hqueried i info hinfo
      exact PolicyMeasure.toMixedWithin_toBehavioralWith (M := M)
        (laws i) (sites i) (fallback i) info hsite
        (fun step hstep =>
          PolicyMeasure.record_mem_recordClosure (M := M) (queried i)
            (by simpa [queried] using hinfo) hstep)
  have hfiniteKuhn :=
    M.kuhn_mixed_update_toBehavioralWithinWith_apply_of_queriedInfos
      hrecall sites horizon target hqueried finiteMixed fallback who
        replacement replacementFallback
  calc
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure updatedLaws) =
        M.runMixed
          (fun i => PolicyMeasure.toMixedWithin (M := M)
            (updatedLaws i) (sites i) (updatedFallback i)) horizon target :=
      M.lintegral_runPolicy_mass_eq_runMixedWithin_of_queriedInfos
        updatedLaws updatedFallback sites horizon target hqueried
    _ = M.runMixed
          (Profile.update (sig := M.strategicSignature.mixed)
            finiteMixed who (replacement.toMixedWithin M (sites who)
              replacementFallback)) horizon target := by rw [hfiniteProfile]
    _ = M.runBehavioral
          (Profile.update (sig := M.behavioralSignature)
            (fun i => InformationModel.MixedPolicy.toBehavioralWith
              (M := M) (finiteMixed i) (fallback i)) who replacement)
          horizon target := hfiniteKuhn.symm
    _ = M.runBehavioral
          (Profile.update (sig := M.behavioralSignature)
            (M.policyMeasureBehavioralWith laws fallback) who replacement)
          horizon target := hbehavioral

/-- Hybrid unilateral realization with arbitrary policy-measure opponents and
an unchanged behavioral deviation by the focal player. -/
theorem runPolicyMeasure_update_toPureMeasure_eq_runBehavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hrecall : M.PerfectRecall)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runPolicyMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement.toPureMeasure) horizon =
      (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who replacement)
        horizon).toMeasure := by
  classical
  let updatedLaws : Profile M.policyMeasureSignature :=
    Profile.update (sig := M.policyMeasureSignature)
      laws who replacement.toPureMeasure
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update (sig := M.strategicSignature)
      fallback who (replacement.supportFallback M)
  let : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
    by_cases hi : i = who
    · subst i
      simpa only [updatedLaws, Profile.update_same] using
        (inferInstanceAs (IsProbabilityMeasure replacement.toPureMeasure))
    · simpa only [updatedLaws, Profile.update_of_ne _ _ hi] using
        (inferInstanceAs (IsProbabilityMeasure (laws i)))
  apply M.runPolicyMeasure_eq_toMeasure_of_lintegral_mass
    updatedLaws updatedFallback horizon _
  intro target
  exact M.lintegral_runPolicy_mass_update_toPureMeasure
    hrecall laws fallback who replacement horizon target
/-- An arbitrary focal policy measure against behavioral opponents has the
correct target mass without a global finite information-site cover. -/
private theorem lintegral_runPolicy_mass_toPureMeasure_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature)
    (who : ι) (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (horizon : ℕ) (target : E.History) :
    (∫⁻ pure, M.run pure horizon target
      ∂M.policyProfileMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          (fun i => (behavioral i).toPureMeasure) who replacement)) =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) behavioral who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon target := by
  classical
  let queried : (i : ι) → Finset (M.InfoState i) :=
    fun i => (M.queriedInfos i target.trace).toFinset
  let sites : (i : ι) → Finset (M.InfoState i) := fun i =>
    PolicyMeasure.recordClosure (M := M) (queried i)
  let fallback : Profile M.strategicSignature := fun i =>
    (behavioral i).supportFallback M
  let replacementMixed : M.MixedPolicy who :=
    PolicyMeasure.toMixedWithin (M := M) replacement
      (sites who) replacementFallback
  let updatedLaws : Profile M.policyMeasureSignature :=
    Profile.update (sig := M.policyMeasureSignature)
      (fun i => (behavioral i).toPureMeasure) who replacement
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update (sig := M.strategicSignature)
      fallback who replacementFallback
  let : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
    by_cases hi : i = who
    · subst i
      simpa only [updatedLaws, Profile.update_same] using
        (inferInstanceAs (IsProbabilityMeasure replacement))
    · simpa only [updatedLaws, Profile.update_of_ne _ _ hi] using
        (inferInstanceAs
          (IsProbabilityMeasure (behavioral i).toPureMeasure))
  have hqueried : ∀ i info,
      info ∈ M.queriedInfos i target.trace → info ∈ sites i := by
    intro i info hinfo
    exact PolicyMeasure.mem_recordClosure (M := M) (queried i)
      (by simpa [queried] using hinfo)
  have hfiniteProfile :
      (fun i => PolicyMeasure.toMixedWithin (M := M) (updatedLaws i)
        (sites i) (updatedFallback i)) =
        Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixedWithin M
            (sites i) (fallback i)) who replacementMixed := by
    funext i
    by_cases hi : i = who
    · subst i
      simp only [updatedLaws, updatedFallback, replacementMixed,
        Profile.update_same]
    · simp only [updatedLaws, updatedFallback, Profile.update_of_ne _ _ hi]
      exact PolicyMeasure.toMixedWithin_toPureMeasure
        (M := M) (behavioral i) (sites i) (fallback i)
  have hbehavioral :
      M.runBehavioral
          (Profile.update (sig := M.behavioralSignature) behavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) replacementMixed replacementFallback))
          horizon target =
        M.runBehavioral
          (Profile.update (sig := M.behavioralSignature) behavioral who
            (PolicyMeasure.toBehavioralWith (M := M) replacement
              replacementFallback)) horizon target := by
    apply M.runBehavioral_apply_congr_of_queriedInfos
    intro i info hinfo
    by_cases hi : i = who
    · subst i
      simp only [Profile.update_same, replacementMixed]
      exact PolicyMeasure.toMixedWithin_toBehavioralWith (M := M)
        replacement (sites who) replacementFallback info
        (hqueried who info hinfo)
        (fun step hstep =>
          PolicyMeasure.record_mem_recordClosure (M := M) (queried who)
            (by simpa [queried] using hinfo) hstep)
    · simp only [Profile.update_of_ne _ _ hi]
  have hfiniteKuhn :=
    M.kuhn_behavioral_update_toMixedWithinWith_apply_of_queriedInfos
      hrecall sites horizon target hqueried behavioral fallback who
        replacementMixed replacementFallback
  calc
    (∫⁻ pure, M.run pure horizon target ∂M.policyProfileMeasure updatedLaws) =
        M.runMixed
          (fun i => PolicyMeasure.toMixedWithin (M := M)
            (updatedLaws i) (sites i) (updatedFallback i)) horizon target :=
      M.lintegral_runPolicy_mass_eq_runMixedWithin_of_queriedInfos
        updatedLaws updatedFallback sites horizon target hqueried
    _ = M.runMixed
          (Profile.update (sig := M.strategicSignature.mixed)
            (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i))
            who replacementMixed) horizon target := by rw [hfiniteProfile]
    _ = M.runBehavioral
          (Profile.update (sig := M.behavioralSignature) behavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) replacementMixed replacementFallback))
          horizon target := hfiniteKuhn
    _ = M.runBehavioral
          (Profile.update (sig := M.behavioralSignature) behavioral who
            (PolicyMeasure.toBehavioralWith (M := M) replacement
              replacementFallback)) horizon target := hbehavioral

/-- Reverse hybrid realization with unchanged behavioral opponents and an
arbitrary focal measure over total pure policies. -/
theorem runPolicyMeasure_toPureMeasure_update_eq_runBehavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature)
    (who : ι) (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who) (horizon : ℕ) :
    M.runPolicyMeasure
        (Profile.update (sig := M.policyMeasureSignature)
          (fun i => (behavioral i).toPureMeasure) who replacement) horizon =
      (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) behavioral who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon).toMeasure := by
  classical
  let updatedLaws : Profile M.policyMeasureSignature :=
    Profile.update (sig := M.policyMeasureSignature)
      (fun i => (behavioral i).toPureMeasure) who replacement
  let fallback : Profile M.strategicSignature := fun i =>
    (behavioral i).supportFallback M
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update (sig := M.strategicSignature)
      fallback who replacementFallback
  let : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
    by_cases hi : i = who
    · subst i
      simpa only [updatedLaws, Profile.update_same] using
        (inferInstanceAs (IsProbabilityMeasure replacement))
    · simpa only [updatedLaws, Profile.update_of_ne _ _ hi] using
        (inferInstanceAs
          (IsProbabilityMeasure (behavioral i).toPureMeasure))
  apply M.runPolicyMeasure_eq_toMeasure_of_lintegral_mass
    updatedLaws updatedFallback horizon _
  intro target
  exact M.lintegral_runPolicy_mass_toPureMeasure_update
    hrecall behavioral who replacement replacementFallback horizon target
/-! ## Regularity of the independent product laws -/

omit [Fintype ι] in
/-- Under countable-product regularity hypotheses, a behavioral policy's
ex-ante law is a regular probability measure. -/
theorem BehavioralPolicy.toPureMeasure_regular {i : ι}
    [Countable (M.InfoState i)]
    [∀ info, TopologicalSpace (M.Choice i info)]
    [∀ info, BorelSpace (M.Choice i info)]
    [∀ info, SecondCountableTopology (M.Choice i info)]
    [∀ info,
      TopologicalSpace.IsCompletelyPseudoMetrizableSpace (M.Choice i info)]
    (policy : M.BehavioralPolicy i) :
    Measure.Regular policy.toPureMeasure := by
  infer_instance

/-- The finite-player product of regular behavioral policy laws is regular. -/
theorem behavioralProfileMeasure_regular
    [∀ i, Countable (M.InfoState i)]
    [∀ i info, TopologicalSpace (M.Choice i info)]
    [∀ i info, BorelSpace (M.Choice i info)]
    [∀ i info, SecondCountableTopology (M.Choice i info)]
    [∀ i info,
      TopologicalSpace.IsCompletelyPseudoMetrizableSpace (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i) :
    Measure.Regular (M.behavioralProfileMeasure policy) := by
  infer_instance

/-! ## Guarded finite-prefix expectations -/

/-- The behavioral prefix value is the canonical guarded PMF expectation. -/
def behavioralPrefixExpectation
    (policy : (i : ι) → M.BehavioralPolicy i)
    (observable : ℕ → E.History → ℝ) (time : ℕ)
    (h : PayoffIntegrable (M.runBehavioral policy (time + 1))
      (observable time)) : ℝ :=
  expect (M.runBehavioral policy (time + 1)) (observable time) h

/-- A pure-policy measure prefix value requires integrability under the
actual integrated runner law. -/
def pureMeasurePrefixExpectation [MeasurableSpace E.History]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (observable : ℕ → E.History → ℝ) (time : ℕ)
    (_h : Integrable (observable time) (M.runPureMeasure policy (time + 1))) : ℝ :=
  ∫ history, observable time history ∂M.runPureMeasure policy (time + 1)

/-- Equality of the prefix laws identifies the exact integrability
conditions on the measure and PMF sides. -/
theorem pureMeasurePrefixIntegrable_iff_behavioral
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (horizon : ℕ)
    (f : E.History → ℝ) :
    Integrable f (M.runPureMeasure policy horizon) ↔
      PayoffIntegrable (M.runBehavioral policy horizon) f := by
  rw [M.runPureMeasure_eq_runBehavioral hactsOnce policy horizon]
  exact (payoffIntegrable_iff_integrable
    (M.runBehavioral policy horizon) f).symm

/-- A single behavioral integrability certificate determines the guarded
pure-measure prefix value and identifies it with PMF expectation. -/
theorem pureMeasurePrefixExpectation_eq_behavioral
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (time : ℕ)
    (observable : ℕ → E.History → ℝ)
    (hbehavioral : PayoffIntegrable (M.runBehavioral policy (time + 1))
      (observable time)) :
    M.pureMeasurePrefixExpectation policy observable time
        ((M.pureMeasurePrefixIntegrable_iff_behavioral hactsOnce policy
          (time + 1) (observable time)).2 hbehavioral) =
      M.behavioralPrefixExpectation policy observable time hbehavioral := by
  unfold pureMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPureMeasure_eq_runBehavioral hactsOnce policy (time + 1)]
  exact (expect_eq_integral (M.runBehavioral policy (time + 1))
    (observable time) hbehavioral).symm

/-- A finite-prefix observable under independently drawn policy measures is
integrated only when it is integrable under the actual runner law. -/
def policyMeasurePrefixExpectation [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i)
    (observable : ℕ → E.History → ℝ) (time : ℕ)
    (_h : Integrable (observable time) (M.runPolicyMeasure laws (time + 1))) : ℝ :=
  ∫ history, observable time history ∂M.runPolicyMeasure laws (time + 1)

/-- Reverse policy-measure realization identifies its exact prefix
integrability condition with the behavioral PMF condition. -/
theorem policyMeasurePrefixIntegrable_iff_behavioralWith
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (horizon : ℕ)
    (f : E.History → ℝ) :
    Integrable f (M.runPolicyMeasure laws horizon) ↔
      PayoffIntegrable
        (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback) horizon) f := by
  rw [M.runPolicyMeasure_eq_runBehavioralWith hconstrain laws fallback horizon]
  exact (payoffIntegrable_iff_integrable
    (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback) horizon) f).symm

/-- A behavioral integrability certificate supplies the measure certificate
and yields equality of the guarded prefix expectations. -/
theorem policyMeasurePrefixExpectation_eq_behavioralWith
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (time : ℕ)
    (observable : ℕ → E.History → ℝ)
    (hbehavioral : PayoffIntegrable
      (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback) (time + 1))
      (observable time)) :
    M.policyMeasurePrefixExpectation laws observable time
        ((M.policyMeasurePrefixIntegrable_iff_behavioralWith hconstrain laws
          fallback (time + 1) (observable time)).2 hbehavioral) =
      M.behavioralPrefixExpectation
        (M.policyMeasureBehavioralWith laws fallback) observable time hbehavioral := by
  unfold policyMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPolicyMeasure_eq_runBehavioralWith hconstrain laws fallback
    (time + 1)]
  exact (expect_eq_integral
    (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback) (time + 1))
    (observable time) hbehavioral).symm

/-- Replacing one policy measure preserves the precise prefix integrability
condition under its conditional behavioral reading. -/
theorem policyMeasureUpdatePrefixIntegrable_iff_behavioral
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (horizon : ℕ)
    (f : E.History → ℝ) :
    Integrable f (M.runPolicyMeasure
      (Profile.update (sig := M.policyMeasureSignature) laws who replacement)
      horizon) ↔
      PayoffIntegrable (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon) f := by
  rw [M.runPolicyMeasure_update_eq_runBehavioral_update hconstrain laws
    fallback who replacement replacementFallback horizon]
  exact (payoffIntegrable_iff_integrable _ f).symm

/-- The same unilateral replacement preserves guarded prefix expectation. -/
theorem policyMeasureUpdatePrefixExpectation_eq_behavioral
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (time : ℕ)
    (observable : ℕ → E.History → ℝ)
    (hbehavioral : PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature)
        (M.policyMeasureBehavioralWith laws fallback) who
        (PolicyMeasure.toBehavioralWith (M := M) replacement
          replacementFallback)) (time + 1)) (observable time)) :
    M.policyMeasurePrefixExpectation
        (Profile.update (sig := M.policyMeasureSignature) laws who replacement)
        observable time
        ((M.policyMeasureUpdatePrefixIntegrable_iff_behavioral hconstrain laws
          fallback who replacement replacementFallback (time + 1)
          (observable time)).2 hbehavioral) =
      M.behavioralPrefixExpectation
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) observable time hbehavioral := by
  unfold policyMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPolicyMeasure_update_eq_runBehavioral_update hconstrain laws
    fallback who replacement replacementFallback (time + 1)]
  exact (expect_eq_integral _ (observable time) hbehavioral).symm

/-- Hybrid behavioral deviations transport prefix integrability from the
behavioral runner to the independently drawn policy laws. -/
theorem hybridBehavioralPrefixIntegrable_iff
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (horizon : ℕ)
    (f : E.History → ℝ) :
    Integrable f (M.runPolicyMeasure
      (Profile.update (sig := M.policyMeasureSignature)
        laws who replacement.toPureMeasure) horizon) ↔
      PayoffIntegrable (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who replacement)
        horizon) f := by
  rw [M.runPolicyMeasure_update_toPureMeasure_eq_runBehavioral_update
    hrecall laws fallback who replacement horizon]
  exact (payoffIntegrable_iff_integrable _ f).symm

/-- Guarded prefix expectation is unchanged by the hybrid behavioral
deviation realization. -/
theorem policyMeasurePrefixExpectation_update_toPureMeasure_eq_behavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (time : ℕ)
    (observable : ℕ → E.History → ℝ)
    (hbehavioral : PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature)
        (M.policyMeasureBehavioralWith laws fallback) who replacement)
      (time + 1)) (observable time)) :
    M.policyMeasurePrefixExpectation
        (Profile.update (sig := M.policyMeasureSignature)
          laws who replacement.toPureMeasure) observable time
        ((M.hybridBehavioralPrefixIntegrable_iff hrecall laws fallback who
          replacement (time + 1) (observable time)).2
          hbehavioral) =
      M.behavioralPrefixExpectation
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who replacement)
        observable time hbehavioral := by
  unfold policyMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPolicyMeasure_update_toPureMeasure_eq_runBehavioral_update
    hrecall laws fallback who replacement (time + 1)]
  exact (expect_eq_integral _ (observable time) hbehavioral).symm

/-- Hybrid policy-law deviations transport prefix integrability to their
conditional behavioral reading. -/
theorem hybridPolicyMeasurePrefixIntegrable_iff
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature)
    (who : ι) (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (horizon : ℕ)
    (f : E.History → ℝ) :
    Integrable f (M.runPolicyMeasure
      (Profile.update (sig := M.policyMeasureSignature)
        (fun i => (behavioral i).toPureMeasure) who replacement) horizon) ↔
      PayoffIntegrable (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) behavioral who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon) f := by
  rw [M.runPolicyMeasure_toPureMeasure_update_eq_runBehavioral_update
    hrecall behavioral who replacement replacementFallback horizon]
  exact (payoffIntegrable_iff_integrable _ f).symm

/-- Guarded prefix expectation is unchanged by the hybrid policy-law
deviation realization. -/
theorem policyMeasurePrefixExpectation_toPureMeasure_update_eq_behavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature)
    (who : ι) (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (time : ℕ)
    (observable : ℕ → E.History → ℝ)
    (hbehavioral : PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature) behavioral who
        (PolicyMeasure.toBehavioralWith (M := M) replacement
          replacementFallback)) (time + 1)) (observable time)) :
    M.policyMeasurePrefixExpectation
        (Profile.update (sig := M.policyMeasureSignature)
          (fun i => (behavioral i).toPureMeasure) who replacement)
        observable time
        ((M.hybridPolicyMeasurePrefixIntegrable_iff hrecall behavioral who
          replacement replacementFallback (time + 1)
          (observable time)).2 hbehavioral) =
      M.behavioralPrefixExpectation
        (Profile.update (sig := M.behavioralSignature) behavioral who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) observable time hbehavioral := by
  unfold policyMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPolicyMeasure_toPureMeasure_update_eq_runBehavioral_update
    hrecall behavioral who replacement replacementFallback (time + 1)]
  exact (expect_eq_integral _ (observable time) hbehavioral).symm

/-! ## Guarded discounted expectations -/

/-- Prefix integrability and weighted-series summability transport discounted
values from a behavioral policy to its independently drawn pure-policy law. -/
theorem normalizedDiscountedPureMeasure_eq_behavioral
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hbehavioral : ∀ time,
      PayoffIntegrable (M.runBehavioral policy (time + 1)) (observable time))
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation policy observable time (hbehavioral time)) :
    let hmeasure : ∀ time,
        Integrable (observable time) (M.runPureMeasure policy (time + 1)) :=
      fun time => (M.pureMeasurePrefixIntegrable_iff_behavioral hactsOnce
        policy (time + 1) (observable time)).2 (hbehavioral time)
    Summable (fun time => discount ^ time *
        M.pureMeasurePrefixExpectation policy observable time (hmeasure time)) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.pureMeasurePrefixExpectation policy observable time
            (hmeasure time)) =
        GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.behavioralPrefixExpectation policy observable time
            (hbehavioral time)) := by
  dsimp only
  have hpointwise (time : ℕ) :
      M.pureMeasurePrefixExpectation policy observable time
          ((M.pureMeasurePrefixIntegrable_iff_behavioral hactsOnce
            policy (time + 1) (observable time)).2 (hbehavioral time)) =
        M.behavioralPrefixExpectation policy observable time
          (hbehavioral time) :=
    M.pureMeasurePrefixExpectation_eq_behavioral hactsOnce
      policy time observable (hbehavioral time)
  simp only [hpointwise]
  exact ⟨hsummable, trivial⟩

/-- Reverse policy-measure realization also preserves guarded discounted
values whenever every prefix is integrable and the weighted series converges. -/
theorem normalizedDiscountedPolicyMeasure_eq_behavioralWith
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature)
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hbehavioral : ∀ time, PayoffIntegrable
      (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback) (time + 1))
      (observable time))
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation
        (M.policyMeasureBehavioralWith laws fallback) observable time
        (hbehavioral time)) :
    let hmeasure : ∀ time,
        Integrable (observable time) (M.runPolicyMeasure laws (time + 1)) :=
      fun time => (M.policyMeasurePrefixIntegrable_iff_behavioralWith
        hconstrain laws fallback (time + 1)
        (observable time)).2 (hbehavioral time)
    Summable (fun time => discount ^ time *
        M.policyMeasurePrefixExpectation laws observable time (hmeasure time)) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.policyMeasurePrefixExpectation laws observable time
            (hmeasure time)) =
        GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.behavioralPrefixExpectation
            (M.policyMeasureBehavioralWith laws fallback) observable time
            (hbehavioral time)) := by
  dsimp only
  have hpointwise (time : ℕ) :
      M.policyMeasurePrefixExpectation laws observable time
          ((M.policyMeasurePrefixIntegrable_iff_behavioralWith hconstrain laws
            fallback (time + 1)
            (observable time)).2 (hbehavioral time)) =
        M.behavioralPrefixExpectation
          (M.policyMeasureBehavioralWith laws fallback) observable time
          (hbehavioral time) :=
    M.policyMeasurePrefixExpectation_eq_behavioralWith hconstrain laws
      fallback time observable (hbehavioral time)
  simp only [hpointwise]
  exact ⟨hsummable, trivial⟩

/-- A hybrid behavioral deviation preserves its guarded discounted value
against arbitrary independent policy-measure opponents. -/
theorem normalizedDiscountedPolicyMeasure_update_toPureMeasure_eq_behavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hbehavioral : ∀ time, PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature)
        (M.policyMeasureBehavioralWith laws fallback) who replacement)
      (time + 1)) (observable time))
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who replacement)
        observable time (hbehavioral time)) :
    let hmeasure : ∀ time, Integrable (observable time)
        (M.runPolicyMeasure
          (Profile.update (sig := M.policyMeasureSignature)
            laws who replacement.toPureMeasure) (time + 1)) :=
      fun time => (M.hybridBehavioralPrefixIntegrable_iff hrecall laws
        fallback who replacement (time + 1)
        (observable time)).2 (hbehavioral time)
    Summable (fun time => discount ^ time *
        M.policyMeasurePrefixExpectation
          (Profile.update (sig := M.policyMeasureSignature)
            laws who replacement.toPureMeasure) observable time
          (hmeasure time)) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.policyMeasurePrefixExpectation
            (Profile.update (sig := M.policyMeasureSignature)
              laws who replacement.toPureMeasure) observable time
            (hmeasure time)) =
        GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.behavioralPrefixExpectation
            (Profile.update (sig := M.behavioralSignature)
              (M.policyMeasureBehavioralWith laws fallback) who replacement)
            observable time (hbehavioral time)) := by
  dsimp only
  have hpointwise (time : ℕ) :
      M.policyMeasurePrefixExpectation
          (Profile.update (sig := M.policyMeasureSignature)
            laws who replacement.toPureMeasure) observable time
          ((M.hybridBehavioralPrefixIntegrable_iff hrecall laws fallback who
            replacement (time + 1)
            (observable time)).2 (hbehavioral time)) =
        M.behavioralPrefixExpectation
          (Profile.update (sig := M.behavioralSignature)
            (M.policyMeasureBehavioralWith laws fallback) who replacement)
          observable time (hbehavioral time) :=
    M.policyMeasurePrefixExpectation_update_toPureMeasure_eq_behavioral_update
      hrecall laws fallback who replacement time
      observable (hbehavioral time)
  simp only [hpointwise]
  exact ⟨hsummable, trivial⟩

/-- A hybrid arbitrary policy-law deviation preserves its guarded discounted
value against behavioral opponents. -/
theorem normalizedDiscountedPolicyMeasure_toPureMeasure_update_eq_behavioral_update
    [DecidableEq ι]
    [∀ i info, Countable (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History] [MeasurableSingletonClass E.History]
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature)
    (who : ι) (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hbehavioral : ∀ time, PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature) behavioral who
        (PolicyMeasure.toBehavioralWith (M := M) replacement
          replacementFallback)) (time + 1)) (observable time))
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation
        (Profile.update (sig := M.behavioralSignature) behavioral who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) observable time (hbehavioral time)) :
    let hmeasure : ∀ time, Integrable (observable time)
        (M.runPolicyMeasure
          (Profile.update (sig := M.policyMeasureSignature)
            (fun i => (behavioral i).toPureMeasure) who replacement)
          (time + 1)) :=
      fun time => (M.hybridPolicyMeasurePrefixIntegrable_iff hrecall
        behavioral who replacement replacementFallback (time + 1)
        (observable time)).2 (hbehavioral time)
    Summable (fun time => discount ^ time *
        M.policyMeasurePrefixExpectation
          (Profile.update (sig := M.policyMeasureSignature)
            (fun i => (behavioral i).toPureMeasure) who replacement)
          observable time (hmeasure time)) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.policyMeasurePrefixExpectation
            (Profile.update (sig := M.policyMeasureSignature)
              (fun i => (behavioral i).toPureMeasure) who replacement)
            observable time (hmeasure time)) =
        GameTheory.Math.normalizedDiscountedSum discount
          (fun time => M.behavioralPrefixExpectation
            (Profile.update (sig := M.behavioralSignature) behavioral who
              (PolicyMeasure.toBehavioralWith (M := M) replacement
                replacementFallback)) observable time
            (hbehavioral time)) := by
  dsimp only
  have hpointwise (time : ℕ) :
      M.policyMeasurePrefixExpectation
          (Profile.update (sig := M.policyMeasureSignature)
            (fun i => (behavioral i).toPureMeasure) who replacement)
          observable time
          ((M.hybridPolicyMeasurePrefixIntegrable_iff hrecall behavioral who
            replacement replacementFallback (time + 1)
            (observable time)).2 (hbehavioral time)) =
        M.behavioralPrefixExpectation
          (Profile.update (sig := M.behavioralSignature) behavioral who
            (PolicyMeasure.toBehavioralWith (M := M) replacement
              replacementFallback)) observable time (hbehavioral time) :=
    M.policyMeasurePrefixExpectation_toPureMeasure_update_eq_behavioral_update
      hrecall behavioral who replacement replacementFallback time
      observable (hbehavioral time)
  simp only [hpointwise]
  exact ⟨hsummable, trivial⟩

end InformationModel
end GameTheory.Protocol
