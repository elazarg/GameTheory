/-
# Probability laws over total deterministic policies

A behavioral policy may randomize at infinitely many information states, so
its ex-ante law over total deterministic policies is generally not a
`FinDist`.  This module uses Mathlib's ordinary infinite product measure.  The
finite-coordinate marginals reconnect that measure to the executable
finite-law layer; bounded execution continues to use the sole Protocol runner.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Math.Discounted
import GameTheory.Math.Probability.Measure
import Mathlib.MeasureTheory.Measure.RegularityCompacts

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability MeasureTheory

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

section PolicyLaw

variable [∀ i info, MeasurableSpace (M.Choice i info)]

namespace BehavioralPolicy

/-- The independent product law over total deterministic policies induced by
one behavioral policy.  Unlike `toMixed`, this is an ordinary probability
measure and requires no finiteness assumption on the information states. -/
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

/-- Every finite coordinate restriction of the infinite policy law is the
corresponding finite independent predraw. -/
theorem toPureMeasure_map_restrict {i : ι}
    [∀ info, Fintype (M.Choice i info)]
    [∀ info, MeasurableSingletonClass (M.Choice i info)]
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i)) :
    policy.toPureMeasure.map sites.restrict =
      (FinDist.pi fun info : sites => policy info).toMeasure := by
  rw [toPureMeasure, Measure.infinitePi_map_restrict,
    GameTheory.Math.Probability.FinDist.toMeasure_pi]

end BehavioralPolicy

/-- The independent product of the players' ex-ante pure-policy laws.  This is
one law over total profiles, not a family indexed by a horizon. -/
def behavioralProfileMeasure (policy : (i : ι) → M.BehavioralPolicy i) :
    Measure ((i : ι) → M.Policy i) :=
  Measure.infinitePi fun i => (policy i).toPureMeasure

instance behavioralProfileMeasure_isProbability
    (policy : (i : ι) → M.BehavioralPolicy i) :
    IsProbabilityMeasure (M.behavioralProfileMeasure policy) := by
  unfold behavioralProfileMeasure
  infer_instance

/-- Restrict a total deterministic profile to player-indexed finite site
families. -/
def restrictPolicies (sites : (i : ι) → Finset (M.InfoState i))
    (policies : (i : ι) → M.Policy i) :
    (i : ι) → (info : sites i) → M.Choice i info :=
  fun i info => policies i info

/-- The executable finite law of the choices at a finite family of sites. -/
def finitePolicyDraws [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) :
    FinDist ((i : ι) → (info : sites i) → M.Choice i info) :=
  FinDist.pi fun i => FinDist.pi fun info : sites i => policy i info

/-- Simultaneously restricting the single infinite profile law to any finite
site family gives exactly the executable finite predraw. -/
theorem behavioralProfileMeasure_map_restrict [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) :
    (M.behavioralProfileMeasure policy).map
        (M.restrictPolicies sites) =
      (M.finitePolicyDraws policy sites).toMeasure := by
  classical
  rw [behavioralProfileMeasure]
  have hrestrict : M.restrictPolicies sites =
      fun policies : (i : ι) → M.Policy i =>
        fun i => (sites i).restrict (policies i) :=
    rfl
  rw [hrestrict]
  have hmeasurable : ∀ i, Measurable
      ((sites i).restrict : M.Policy i →
        ((info : sites i) → M.Choice i info)) :=
    fun i => Finset.measurable_restrict (sites i)
  letI (i : ι) (info : sites i) : Fintype (M.Choice i info) :=
    inferInstance
  letI (i : ι) : IsProbabilityMeasure
      ((policy i).toPureMeasure.map (sites i).restrict) :=
    Measure.isProbabilityMeasure_map (hmeasurable i).aemeasurable
  have hfactor (i : ι) :
      (policy i).toPureMeasure.map (sites i).restrict =
        (FinDist.pi fun info : sites i => policy i info).toMeasure := by
    exact BehavioralPolicy.toPureMeasure_map_restrict
      (M := M) (policy i) (sites i)
  rw [Measure.infinitePi_map_pi
      (μ := fun i => (policy i).toPureMeasure)
      (f := fun i => (sites i).restrict) hmeasurable,
    Measure.infinitePi_eq_pi]
  rw [show (fun i =>
      (policy i).toPureMeasure.map (sites i).restrict) =
      (fun i =>
        (FinDist.pi fun info : sites i => policy i info).toMeasure) from
    funext hfactor]
  rw [← GameTheory.Math.Probability.FinDist.toMeasure_pi]
  rfl

/-! ## Bounded execution from the single policy law -/

/-- Fill a total deterministic profile from finite coordinate draws and a
deterministic fallback outside those coordinates. -/
def assemblePolicies
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i)
    (draws : (i : ι) → (info : sites i) → M.Choice i info) :
    (i : ι) → M.Policy i := by
  exact fun i => Policy.assembleWithin M (fallback i) (sites i) (draws i)

omit [∀ i info, MeasurableSpace (M.Choice i info)] in
/-- Assembling the finite marginal coordinatewise gives exactly the bounded
mixed profile already consumed by the Protocol runner. -/
theorem finitePolicyDraws_map_assemble [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) :
    FinDist.map (M.assemblePolicies sites fallback)
        (M.finitePolicyDraws policy sites) =
      FinDist.pi fun i =>
        (policy i).toMixedWithin (sites i) (fallback i) := by
  classical
  unfold finitePolicyDraws assemblePolicies
  rw [← FinDist.pi_map]
  congr 1
  funext i
  exact (BehavioralPolicy.toMixedWithin_eq_map_pi
    (M := M) (policy i) (sites i) (fallback i)).symm

omit [∀ i info, MeasurableSpace (M.Choice i info)] in
/-- A covered bounded run depends only on the corresponding finite restriction
of a total deterministic profile. -/
theorem run_assemble_restrict [Fintype ι]
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
  unfold assemblePolicies Policy.assembleWithin restrictPolicies Policy.act
  rw [FinDist.DependentAssignment.resolve_of_mem _ _ _ hmem]

/-- Integrate the canonical finite-support runner after drawing one total pure
policy profile from the infinite product law. -/
def runPureMeasure [MeasurableSpace E.History]
    (policy : (i : ι) → M.BehavioralPolicy i) (horizon : ℕ) :
    Measure E.History :=
  (M.behavioralProfileMeasure policy).bind fun pure =>
    (M.run pure horizon).toMeasure

/-- **Infinite-product behavioral-to-pure Kuhn.** One probability law over
total pure-policy profiles works simultaneously for every bounded horizon:
integrating the unchanged Protocol runner against that law gives the
behavioral finite-prefix law.  `sites` is proof data for this horizon; the
profile measure on the left does not depend on it. -/
theorem runPureMeasure_eq_runBehavioral [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.runPureMeasure policy horizon =
      (M.runBehavioral policy horizon).toMeasure := by
  classical
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let kernel := fun draws => (M.run (assemble draws) horizon).toMeasure
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hkernel : Measurable kernel :=
    measurable_of_finite kernel
  have hpointwise (pure : (i : ι) → M.Policy i) :
      (M.run pure horizon).toMeasure = kernel (restrict pure) := by
    apply congrArg GameTheory.Math.Probability.FinDist.toMeasure
    exact (M.run_assemble_restrict sites fallback pure horizon hcover).symm
  have hbindMap :
      (M.behavioralProfileMeasure policy).bind
          (fun pure => kernel (restrict pure)) =
        ((M.behavioralProfileMeasure policy).map restrict).bind kernel := by
    unfold Measure.bind
    rw [Measure.map_map hkernel hrestrict]
    rfl
  have hfiniteBind :
      (M.finitePolicyDraws policy sites).toMeasure.bind kernel =
        ((M.finitePolicyDraws policy sites).bind fun draws =>
          M.run (assemble draws) horizon).toMeasure :=
    GameTheory.Math.Probability.FinDist.toMeasure_bind
      (M.finitePolicyDraws policy sites)
      (fun draws => M.run (assemble draws) horizon)
  have hdrawRun :
      (M.finitePolicyDraws policy sites).bind
          (fun draws => M.run (assemble draws) horizon) =
        M.runMixed
          (fun i => (policy i).toMixedWithin (sites i) (fallback i))
          horizon := by
    unfold InformationModel.runMixed InformationModel.runMixedFrom
      InformationModel.run
    rw [← M.finitePolicyDraws_map_assemble policy sites fallback,
      FinDist.bind_map]
  unfold runPureMeasure
  calc
    (M.behavioralProfileMeasure policy).bind
        (fun pure => (M.run pure horizon).toMeasure) =
        (M.behavioralProfileMeasure policy).bind
          (fun pure => kernel (restrict pure)) :=
      Measure.bind_congr_right (Filter.Eventually.of_forall hpointwise)
    _ = ((M.behavioralProfileMeasure policy).map restrict).bind kernel :=
      hbindMap
    _ = (M.finitePolicyDraws policy sites).toMeasure.bind kernel := by
      rw [M.behavioralProfileMeasure_map_restrict policy sites]
    _ = ((M.finitePolicyDraws policy sites).bind fun draws =>
        M.run (assemble draws) horizon).toMeasure := hfiniteBind
    _ = (M.runMixed
        (fun i => (policy i).toMixedWithin (sites i) (fallback i))
        horizon).toMeasure := congrArg _ hdrawRun
    _ = (M.runBehavioral policy horizon).toMeasure := congrArg _
      (M.runMixed_toMixedWithin hactsOnce sites policy fallback
        horizon hcover)

/-- **Unilateral infinite-product Kuhn.** The same construction applies after
an arbitrary behavioral replacement.  Counterfactual site coverage makes the
finite-prefix statement independent of the baseline support, while the policy
law itself remains the one unbounded product law of the updated profile. -/
theorem runPureMeasure_update_eq_runBehavioral_update [Fintype ι]
    [DecidableEq ι]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (behavioral : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.runPureMeasure
        (Profile.update (sig := M.behavioralSignature)
          behavioral who replacement) horizon =
      (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who replacement)
        horizon).toMeasure :=
  M.runPureMeasure_eq_runBehavioral hactsOnce sites
    (Profile.update (sig := M.behavioralSignature)
      behavioral who replacement)
    (Profile.update (sig := M.strategicSignature)
      fallback who replacementFallback) horizon hcover

/-! ## Discounted finite-prefix consequences -/

/-- Expected value of a time-indexed observable under the behavioral
finite-prefix law.  A stochastic specialization supplies stage utility as the
observable. -/
def behavioralPrefixExpectation [Fintype ι] [MeasurableSpace E.History]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (observable : ℕ → E.History → ℝ) (time : ℕ) : ℝ :=
  ∫ history, observable time history ∂
    (M.runBehavioral policy (time + 1)).toMeasure

/-- The same prefix observable, evaluated after the ex-ante draw of one total
pure-policy profile. -/
def pureMeasurePrefixExpectation [Fintype ι] [MeasurableSpace E.History]
    (policy : (i : ι) → M.BehavioralPolicy i)
    (observable : ℕ → E.History → ℝ) (time : ℕ) : ℝ :=
  ∫ history, observable time history ∂M.runPureMeasure policy (time + 1)

/-- Equality of all finite-prefix laws gives equality of every prefix
expectation. -/
theorem pureMeasurePrefixExpectation_eq_behavioral [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : ℕ → (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i)
    (hcover : ∀ time,
      M.CoversInformationSites (sites time) (time + 1))
    (observable : ℕ → E.History → ℝ) (time : ℕ) :
    M.pureMeasurePrefixExpectation policy observable time =
      M.behavioralPrefixExpectation policy observable time := by
  unfold pureMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPureMeasure_eq_runBehavioral hactsOnce (sites time)
    policy fallback (time + 1) (hcover time)]

/-- Discounted payoff equality for the one pure-policy law.  The summability
premise is explicit: the theorem does not infer convergence from the mere
existence of finite-prefix laws.  It also returns summability of the pure-law
series, which follows termwise. -/
theorem normalizedDiscountedPureMeasure_eq_behavioral [Fintype ι]
    [∀ i info, Fintype (M.Choice i info)]
    [∀ i info, MeasurableSingletonClass (M.Choice i info)]
    [MeasurableSpace E.History]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : ℕ → (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i)
    (hcover : ∀ time,
      M.CoversInformationSites (sites time) (time + 1))
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation policy observable time) :
    Summable (fun time => discount ^ time *
        M.pureMeasurePrefixExpectation policy observable time) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (M.pureMeasurePrefixExpectation policy observable) =
        GameTheory.Math.normalizedDiscountedSum discount
          (M.behavioralPrefixExpectation policy observable) := by
  have hpointwise : M.pureMeasurePrefixExpectation policy observable =
      M.behavioralPrefixExpectation policy observable := by
    funext time
    exact M.pureMeasurePrefixExpectation_eq_behavioral hactsOnce sites
      policy fallback hcover observable time
  rw [hpointwise]
  exact ⟨hsummable, rfl⟩

/-! ## Regularity -/

/-- Under the standard countable-product hypotheses, the ex-ante law of one
behavioral policy is a regular probability measure on total pure policies. -/
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

/-- With countably many players and countably many information states, the
single product law over total pure-policy profiles is regular as well as
probabilistic. Finite games satisfy the player-countability premise directly. -/
theorem behavioralProfileMeasure_regular [Countable ι]
    [∀ i, Countable (M.InfoState i)]
    [∀ i info, TopologicalSpace (M.Choice i info)]
    [∀ i info, BorelSpace (M.Choice i info)]
    [∀ i info, SecondCountableTopology (M.Choice i info)]
    [∀ i info,
      TopologicalSpace.IsCompletelyPseudoMetrizableSpace (M.Choice i info)]
    (policy : (i : ι) → M.BehavioralPolicy i) :
    Measure.Regular (M.behavioralProfileMeasure policy) := by
  infer_instance

end PolicyLaw

end InformationModel

end GameTheory.Protocol
