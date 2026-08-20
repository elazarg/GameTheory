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
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.ConditionalProbability

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

/-! ## Reading an arbitrary pure-policy measure behaviorally -/

section ReversePolicyLaw

variable [∀ i info, MeasurableSpace (M.Choice i info)]
  [∀ i info, Fintype (M.Choice i info)]
  [∀ i info, MeasurableSingletonClass (M.Choice i info)]

/-- An ordinary law over one player's total deterministic policies. Unlike
`MixedPolicy`, this law need not have finite support. -/
abbrev PolicyMeasure (i : ι) := Measure (M.Policy i)

/-- The dependent profile signature for laws over total pure policies. -/
abbrev policyMeasureSignature : GameSignature ι where
  Strategy i := M.PolicyMeasure i
  Outcome := E.History

/-- A finite own-play record determines a measurable cylinder in the total
policy space. -/
theorem measurableSet_consistent {i : ι}
    (record : List (M.InfoState i × E.Action i)) :
    MeasurableSet (M.Consistent i record) := by
  induction record with
  | nil => simp [InformationModel.Consistent]
  | cons step rest ih =>
      have hchoice : MeasurableSet
          {choice : M.Choice i step.1 | choice.1 = some step.2} :=
        (Set.toFinite _).measurableSet
      have hhead : MeasurableSet
          {policy : M.Policy i | (policy step.1).1 = some step.2} :=
        (measurable_pi_apply step.1) hchoice
      rw [show M.Consistent i (step :: rest) =
          {policy : M.Policy i | (policy step.1).1 = some step.2} ∩
            M.Consistent i rest by
        ext policy
        simp [InformationModel.Consistent]]
      exact hhead.inter ih

/-- The policies compatible with reaching an information state form a
measurable finite-coordinate cylinder. -/
theorem measurableSet_consistentAt {i : ι} (info : M.InfoState i) :
    MeasurableSet (M.ConsistentAt i info) :=
  M.measurableSet_consistent (M.recordAt i info)

namespace PolicyMeasure

/-- Read an arbitrary probability law over total pure policies as local
randomization. At a positive-mass information state this is the conditional
law of the prescribed choice given the player's own recalled record. A fixed
total policy supplies choices only at zero-mass cylinders. -/
noncomputable def toBehavioralWith {i : ι} (law : M.PolicyMeasure i)
    [IsProbabilityMeasure law] (fallback : M.Policy i) :
    M.BehavioralPolicy i := fun info =>
  if hpos : law (M.ConsistentAt i info) ≠ 0 then
    let conditioned := ProbabilityTheory.cond law (M.ConsistentAt i info)
    letI : IsProbabilityMeasure conditioned :=
      ProbabilityTheory.cond_isProbabilityMeasure hpos
    let pushed := conditioned.map (fun policy => policy info)
    letI : IsProbabilityMeasure pushed :=
      Measure.isProbabilityMeasure_map
        (measurable_pi_apply info).aemeasurable
    FinDist.ofMeasure pushed
  else
    FinDist.pure (fallback info)

/-- The reading respects equality of policy measures; probability-instance
proofs carry no data. -/
theorem toBehavioralWith_congr {i : ι} (first second : M.PolicyMeasure i)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (fallback : M.Policy i) (h : first = second) :
    PolicyMeasure.toBehavioralWith (M := M) first fallback =
      PolicyMeasure.toBehavioralWith (M := M) second fallback := by
  subst second
  rfl

/-- The measure-theoretic behavioral reading extends the existing finite-law
reading exactly. -/
theorem toBehavioralWith_toMeasure {i : ι} (mixed : M.MixedPolicy i)
    (fallback : M.Policy i) (info : M.InfoState i) :
    PolicyMeasure.toBehavioralWith (M := M) mixed.toMeasure fallback info =
      mixed.toBehavioralWith fallback info := by
  classical
  let consistent := M.ConsistentAt i info
  have hconsistent : MeasurableSet consistent :=
    M.measurableSet_consistentAt info
  by_cases hmeet : ∃ policy ∈ consistent, policy ∈ mixed.support
  · have hmass : mixed.toMeasure consistent ≠ 0 := by
      rw [← measureReal_ne_zero_iff]
      rw [GameTheory.Math.Probability.FinDist.toMeasure_real_apply
        mixed hconsistent]
      exact (FinDist.probOf_pos hmeet).ne'
    rw [PolicyMeasure.toBehavioralWith, MixedPolicy.toBehavioralWith,
      dif_pos hmass, dif_pos hmeet]
    exact GameTheory.Math.Probability.FinDist.ofMeasure_map_cond_toMeasure
      mixed consistent hconsistent hmeet hmass (fun policy => policy info)
      (measurable_pi_apply info)
  · have hmass : mixed.toMeasure consistent = 0 := by
      rw [GameTheory.Math.Probability.FinDist.toMeasure_apply_eq_zero_iff
        mixed hconsistent]
      exact Set.disjoint_left.mpr fun policy hsupport hcons =>
        hmeet ⟨policy, hcons, hsupport⟩
    rw [PolicyMeasure.toBehavioralWith, MixedPolicy.toBehavioralWith,
      dif_neg hmeet, dif_neg (not_ne_iff.mpr hmass)]

/-- The behavioral reading depends only on the own-record cylinder and the
current choice coordinate. Any measurable policy transformation preserving
those data is invisible to the reading. -/
theorem toBehavioralWith_map_eq_of_preserves {i : ι}
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
  classical
  let consistent := M.ConsistentAt i info
  have hmeasurable : MeasurableSet consistent :=
    M.measurableSet_consistentAt info
  have hpreimage : transform ⁻¹' consistent = consistent := by
    ext policy
    exact hconsistent policy
  have hmass : (law.map transform) consistent = law consistent := by
    rw [Measure.map_apply htransform hmeasurable, hpreimage]
  by_cases hpos : law consistent ≠ 0
  · have hmappos : (law.map transform) consistent ≠ 0 := by
      rw [hmass]
      exact hpos
    dsimp only [consistent] at hmass hpos hmappos ⊢
    simp only [PolicyMeasure.toBehavioralWith, dif_pos hmappos, dif_pos hpos]
    apply FinDist.ext_of_prob
    intro choice
    let answer := (fun policy : M.Policy i => policy info) ⁻¹'
      ({choice} : Set (M.Choice i info))
    have hanswer : MeasurableSet answer :=
      (measurable_pi_apply info) (measurableSet_singleton choice)
    have hinter : MeasurableSet (consistent ∩ answer) :=
      hmeasurable.inter hanswer
    have hinterPreimage : transform ⁻¹' (consistent ∩ answer) =
        consistent ∩ answer := by
      ext policy
      show (transform policy ∈ M.ConsistentAt i info ∧
          transform policy info = choice) ↔
        (policy ∈ M.ConsistentAt i info ∧ policy info = choice)
      rw [hconsistent policy, hchoice policy]
    have hinterMass : (law.map transform) (consistent ∩ answer) =
        law (consistent ∩ answer) := by
      rw [Measure.map_apply htransform hinter, hinterPreimage]
    rw [GameTheory.Math.Probability.FinDist.prob_ofMeasure,
      GameTheory.Math.Probability.FinDist.prob_ofMeasure,
      measureReal_def, measureReal_def,
      Measure.map_apply (measurable_pi_apply info)
        (measurableSet_singleton choice),
      Measure.map_apply (measurable_pi_apply info)
        (measurableSet_singleton choice),
      ProbabilityTheory.cond_apply hmeasurable,
      ProbabilityTheory.cond_apply hmeasurable,
      hmass, hinterMass]
  · have hmapzero : (law.map transform) consistent = 0 := by
      rw [hmass]
      exact not_ne_iff.mp hpos
    dsimp only [consistent] at hpos hmapzero ⊢
    simp only [PolicyMeasure.toBehavioralWith, dif_neg hpos,
      dif_neg (not_ne_iff.mpr hmapzero)]

omit [∀ i info, MeasurableSpace (M.Choice i info)]
  [∀ i info, Fintype (M.Choice i info)]
  [∀ i info, MeasurableSingletonClass (M.Choice i info)] in
/-- Restricting and then assembling preserves every retained coordinate. -/
theorem assembleWithin_restrict_apply {i : ι} (policy fallback : M.Policy i)
    (sites : Finset (M.InfoState i)) {info : M.InfoState i}
    (hinfo : info ∈ sites) :
    Policy.assembleWithin M fallback sites (sites.restrict policy) info =
      policy info := by
  classical
  unfold Policy.assembleWithin
  rw [FinDist.DependentAssignment.resolve_of_mem _ _ _ hinfo]
  rfl

/-- Restrict an arbitrary pure-policy probability law to finitely many
coordinates, convert that finite marginal to `FinDist`, and fill the omitted
coordinates from a fixed policy. -/
noncomputable def toMixedWithin {i : ι} (law : M.PolicyMeasure i)
    [IsProbabilityMeasure law] (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) : M.MixedPolicy i := by
  classical
  letI (info : sites) : Fintype (M.Choice i info) := inferInstance
  let restricted := law.map sites.restrict
  letI : IsProbabilityMeasure restricted :=
    Measure.isProbabilityMeasure_map
      (Finset.measurable_restrict sites).aemeasurable
  exact FinDist.map (Policy.assembleWithin M fallback sites)
    (FinDist.ofMeasure restricted)

/-- The finite approximation is precisely the pushforward that forgets all
coordinates outside `sites` and fills them from `fallback`. -/
theorem toMixedWithin_toMeasure {i : ι} (law : M.PolicyMeasure i)
    [IsProbabilityMeasure law] (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) :
    (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toMeasure =
      law.map (fun policy =>
        Policy.assembleWithin M fallback sites (sites.restrict policy)) := by
  classical
  letI (info : sites) : Fintype (M.Choice i info) := inferInstance
  have hassemble : Measurable (Policy.assembleWithin M fallback sites) :=
    measurable_of_finite _
  have hrestrict : Measurable
      (sites.restrict : M.Policy i → (info : sites) → M.Choice i info) :=
    Finset.measurable_restrict sites
  letI : IsProbabilityMeasure (law.map sites.restrict) :=
    Measure.isProbabilityMeasure_map hrestrict.aemeasurable
  show (FinDist.map (Policy.assembleWithin M fallback sites)
      (FinDist.ofMeasure (law.map sites.restrict))).toMeasure = _
  rw [← GameTheory.Math.Probability.FinDist.toMeasure_map _ _ hassemble,
    GameTheory.Math.Probability.FinDist.toMeasure_ofMeasure,
    Measure.map_map hassemble hrestrict]
  rfl

/-- If a finite coordinate set contains the current information state and its
whole own-record cylinder, the finite approximation and the original measure
have exactly the same behavioral reading there. -/
theorem toMixedWithin_toBehavioralWith {i : ι} (law : M.PolicyMeasure i)
    [IsProbabilityMeasure law] (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) (info : M.InfoState i)
    (hinfo : info ∈ sites)
    (hrecord : ∀ step ∈ M.recordAt i info, step.1 ∈ sites) :
    (PolicyMeasure.toMixedWithin (M := M) law sites fallback).toBehavioralWith
        fallback info =
      PolicyMeasure.toBehavioralWith (M := M) law fallback info := by
  classical
  let transform : M.Policy i → M.Policy i := fun policy =>
    Policy.assembleWithin M fallback sites (sites.restrict policy)
  letI (site : sites) : Fintype (M.Choice i site) := inferInstance
  have hassemble : Measurable (Policy.assembleWithin M fallback sites) :=
    measurable_of_finite _
  have hrestrict : Measurable
      (sites.restrict : M.Policy i → (site : sites) → M.Choice i site) :=
    Finset.measurable_restrict sites
  have htransform : Measurable transform := hassemble.comp hrestrict
  letI : IsProbabilityMeasure (law.map transform) :=
    Measure.isProbabilityMeasure_map htransform.aemeasurable
  have hchoice (policy : M.Policy i) : transform policy info = policy info := by
    exact PolicyMeasure.assembleWithin_restrict_apply (M := M)
      policy fallback sites hinfo
  have hconsistent (policy : M.Policy i) :
      transform policy ∈ M.ConsistentAt i info ↔
        policy ∈ M.ConsistentAt i info := by
    constructor
    · intro hp step hstep
      have hanswer := hp step hstep
      have hchoiceAt : transform policy step.1 = policy step.1 :=
        PolicyMeasure.assembleWithin_restrict_apply (M := M)
          policy fallback sites (hrecord step hstep)
      rw [hchoiceAt] at hanswer
      exact hanswer
    · intro hp step hstep
      have hanswer := hp step hstep
      have hchoiceAt : transform policy step.1 = policy step.1 :=
        PolicyMeasure.assembleWithin_restrict_apply (M := M)
          policy fallback sites (hrecord step hstep)
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

/-- Enlarge a finite family of information states by every information-state
coordinate appearing in their own recalled records. -/
noncomputable def recordClosure {i : ι}
    (sites : Finset (M.InfoState i)) : Finset (M.InfoState i) := by
  classical
  exact sites ∪ sites.biUnion fun info =>
    (M.recordAt i info).map Prod.fst |>.toFinset

omit [∀ i info, MeasurableSpace (M.Choice i info)]
  [∀ i info, Fintype (M.Choice i info)]
  [∀ i info, MeasurableSingletonClass (M.Choice i info)] in
/-- The record closure retains every original information state. -/
theorem mem_recordClosure {i : ι} (sites : Finset (M.InfoState i))
    {info : M.InfoState i} (hinfo : info ∈ sites) :
    info ∈ PolicyMeasure.recordClosure (M := M) sites := by
  classical
  simp [PolicyMeasure.recordClosure, hinfo]

omit [∀ i info, MeasurableSpace (M.Choice i info)]
  [∀ i info, Fintype (M.Choice i info)]
  [∀ i info, MeasurableSingletonClass (M.Choice i info)] in
/-- Every coordinate in the own record of an original site belongs to its
record closure. -/
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

variable [Fintype ι]

/-- The independent product of arbitrary per-player pure-policy probability
laws. A general joint law would be a correlated strategy, not a mixed profile. -/
def policyProfileMeasure (laws : (i : ι) → M.PolicyMeasure i) :
    Measure ((i : ι) → M.Policy i) :=
  Measure.pi laws

instance policyProfileMeasure_isProbability
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)] :
    IsProbabilityMeasure (M.policyProfileMeasure laws) := by
  unfold policyProfileMeasure
  infer_instance

/-- The executable finite law obtained from all player-indexed finite
coordinate marginals. -/
noncomputable def finitePolicyMeasureDraws
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i)) :
    FinDist ((i : ι) → (info : sites i) → M.Choice i info) := by
  classical
  letI (i : ι) (info : sites i) : Fintype (M.Choice i info) :=
    inferInstance
  let restricted := fun i => (laws i).map (sites i).restrict
  letI (i : ι) : IsProbabilityMeasure (restricted i) :=
    Measure.isProbabilityMeasure_map
      (Finset.measurable_restrict (sites i)).aemeasurable
  exact FinDist.pi fun i => FinDist.ofMeasure (restricted i)

/-- Restricting the independent profile measure to any finite family of sites
is exactly the executable finite marginal. -/
theorem policyProfileMeasure_map_restrict
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i)) :
    (M.policyProfileMeasure laws).map (M.restrictPolicies sites) =
      (M.finitePolicyMeasureDraws laws sites).toMeasure := by
  classical
  have hrestrict : M.restrictPolicies sites =
      fun policies : (i : ι) → M.Policy i =>
        fun i => (sites i).restrict (policies i) :=
    rfl
  rw [policyProfileMeasure, hrestrict,
    Measure.pi_map_pi (fun i =>
      (Finset.measurable_restrict (sites i)).aemeasurable)]
  unfold finitePolicyMeasureDraws
  rw [GameTheory.Math.Probability.FinDist.toMeasure_pi]
  congr 1
  funext i
  rw [GameTheory.Math.Probability.FinDist.toMeasure_ofMeasure]

/-- Assembling the finite marginals coordinatewise gives the corresponding
profile of finite-support mixed policies. -/
theorem finitePolicyMeasureDraws_map_assemble
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) :
    FinDist.map (M.assemblePolicies sites fallback)
        (M.finitePolicyMeasureDraws laws sites) =
      FinDist.pi fun i =>
        PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i) := by
  classical
  unfold finitePolicyMeasureDraws PolicyMeasure.toMixedWithin
    InformationModel.assemblePolicies
  rw [← FinDist.pi_map]

/-- Integrate the sole Protocol runner after independently drawing one total
pure policy from each player's arbitrary policy law. -/
def runPolicyMeasure [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i) (horizon : ℕ) :
    Measure E.History :=
  (M.policyProfileMeasure laws).bind fun pure =>
    (M.run pure horizon).toMeasure

/-- Read independent per-player pure-policy measures as one behavioral
profile, using fixed fallbacks only on zero-mass own-record cylinders. -/
noncomputable def policyMeasureBehavioralWith
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    (fallback : (i : ι) → M.Policy i) :
    (i : ι) → M.BehavioralPolicy i := fun i =>
  PolicyMeasure.toBehavioralWith (M := M) (laws i) (fallback i)

/-- A covered bounded run under arbitrary policy measures depends only on the
finite marginals consumed by the existing mixed runner. -/
theorem runPolicyMeasure_eq_runMixedWithin
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    [MeasurableSpace E.History]
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.runPolicyMeasure laws horizon =
      (M.runMixed
        (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i))
        horizon).toMeasure := by
  classical
  let restrict := M.restrictPolicies sites
  let assemble := M.assemblePolicies sites fallback
  let kernel := fun draws => (M.run (assemble draws) horizon).toMeasure
  have hrestrict : Measurable restrict := by
    unfold restrict InformationModel.restrictPolicies
    fun_prop
  have hkernel : Measurable kernel := measurable_of_finite kernel
  have hpointwise (pure : (i : ι) → M.Policy i) :
      (M.run pure horizon).toMeasure = kernel (restrict pure) := by
    apply congrArg GameTheory.Math.Probability.FinDist.toMeasure
    exact (M.run_assemble_restrict sites fallback pure horizon hcover).symm
  have hbindMap :
      (M.policyProfileMeasure laws).bind
          (fun pure => kernel (restrict pure)) =
        ((M.policyProfileMeasure laws).map restrict).bind kernel := by
    unfold Measure.bind
    rw [Measure.map_map hkernel hrestrict]
    rfl
  have hfiniteBind :
      (M.finitePolicyMeasureDraws laws sites).toMeasure.bind kernel =
        ((M.finitePolicyMeasureDraws laws sites).bind fun draws =>
          M.run (assemble draws) horizon).toMeasure :=
    GameTheory.Math.Probability.FinDist.toMeasure_bind
      (M.finitePolicyMeasureDraws laws sites)
      (fun draws => M.run (assemble draws) horizon)
  have hdrawRun :
      (M.finitePolicyMeasureDraws laws sites).bind
          (fun draws => M.run (assemble draws) horizon) =
        M.runMixed
          (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
            (sites i) (fallback i))
          horizon := by
    unfold InformationModel.runMixed InformationModel.runMixedFrom
      InformationModel.run
    rw [← M.finitePolicyMeasureDraws_map_assemble laws sites fallback,
      FinDist.bind_map]
  unfold runPolicyMeasure
  calc
    (M.policyProfileMeasure laws).bind
        (fun pure => (M.run pure horizon).toMeasure) =
        (M.policyProfileMeasure laws).bind
          (fun pure => kernel (restrict pure)) :=
      Measure.bind_congr_right (Filter.Eventually.of_forall hpointwise)
    _ = ((M.policyProfileMeasure laws).map restrict).bind kernel := hbindMap
    _ = (M.finitePolicyMeasureDraws laws sites).toMeasure.bind kernel := by
      rw [M.policyProfileMeasure_map_restrict laws sites]
    _ = ((M.finitePolicyMeasureDraws laws sites).bind fun draws =>
        M.run (assemble draws) horizon).toMeasure := hfiniteBind
    _ = (M.runMixed
        (fun i => PolicyMeasure.toMixedWithin (M := M) (laws i)
          (sites i) (fallback i))
        horizon).toMeasure := congrArg _ hdrawRun

/-- **Infinite-policy-measure mixed-to-behavioral Kuhn.** Under the same
own-record condition as the finite-support reverse theorem, one independent
probability measure over total pure policies per player induces exactly the
finite-prefix law of its behavioral conditional reading. The measures and the
behavioral profile are independent of the horizon; finite site families are
used only inside the proof. -/
theorem runPolicyMeasure_eq_runBehavioralWith
    (hconstrain : M.ConstrainsAlike)
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    [MeasurableSpace E.History]
    (sites : (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
    M.runPolicyMeasure laws horizon =
      (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
        horizon).toMeasure := by
  classical
  let closedSites : (i : ι) → Finset (M.InfoState i) := fun i =>
    PolicyMeasure.recordClosure (M := M) (sites i)
  let finiteMixed : (i : ι) → M.MixedPolicy i := fun i =>
    PolicyMeasure.toMixedWithin (M := M) (laws i)
      (closedSites i) (fallback i)
  have hclosedCover : M.CoversInformationSites closedSites horizon := by
    intro later hreach hterm i
    exact PolicyMeasure.mem_recordClosure (M := M) (sites i)
      (hcover later hreach hterm i)
  have hbehavioral :
      M.runBehavioral
          (fun i => (finiteMixed i).toBehavioralWith (fallback i)) horizon =
        M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
          horizon := by
    apply M.runBehavioralFrom_congr horizon E.initHistory
    intro later hreach hterm i
    have hinfo : M.infoOf i later.trace ∈ sites i :=
      hcover later hreach hterm i
    exact PolicyMeasure.toMixedWithin_toBehavioralWith (M := M)
      (laws i) (closedSites i) (fallback i) (M.infoOf i later.trace)
      (PolicyMeasure.mem_recordClosure (M := M) (sites i) hinfo)
      (fun step hstep =>
        PolicyMeasure.record_mem_recordClosure (M := M) (sites i)
          hinfo hstep)
  calc
    M.runPolicyMeasure laws horizon =
        (M.runMixed finiteMixed horizon).toMeasure :=
      M.runPolicyMeasure_eq_runMixedWithin laws closedSites fallback horizon
        hclosedCover
    _ = (M.runBehavioral
          (fun i => (finiteMixed i).toBehavioralWith (fallback i))
          horizon).toMeasure :=
      congrArg _ (M.runMixed_toBehavioralWith hconstrain fallback horizon
        finiteMixed)
    _ = (M.runBehavioral (M.policyMeasureBehavioralWith laws fallback)
          horizon).toMeasure := congrArg _ hbehavioral

/-- The same reverse equivalence holds after replacing one player's arbitrary
pure-policy measure. Counterfactual site coverage makes the statement valid
for deviations outside the baseline play support. -/
theorem runPolicyMeasure_update_eq_runBehavioral_update
    [DecidableEq ι] (hconstrain : M.ConstrainsAlike)
    (laws : Profile M.policyMeasureSignature)
    [∀ i, IsProbabilityMeasure (laws i)]
    [MeasurableSpace E.History]
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.PolicyMeasure who)
    [IsProbabilityMeasure replacement]
    (replacementFallback : M.Policy who)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon) :
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
  letI : ∀ i, IsProbabilityMeasure (updatedLaws i) := fun i => by
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
      M.runPolicyMeasure_eq_runBehavioralWith hconstrain updatedLaws sites
        updatedFallback horizon hcover
    _ = (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (M.policyMeasureBehavioralWith laws fallback) who
          (PolicyMeasure.toBehavioralWith (M := M) replacement
            replacementFallback)) horizon).toMeasure :=
      congrArg (fun profile => (M.runBehavioral profile horizon).toMeasure)
        hprofile

/-- Expected value of a finite-prefix observable after independently drawing
one total pure policy from each player's arbitrary policy measure. -/
def policyMeasurePrefixExpectation [MeasurableSpace E.History]
    (laws : (i : ι) → M.PolicyMeasure i)
    (observable : ℕ → E.History → ℝ) (time : ℕ) : ℝ :=
  ∫ history, observable time history ∂M.runPolicyMeasure laws (time + 1)

/-- Equality of every finite-prefix law identifies the corresponding
expectations under an arbitrary pure-policy measure and its behavioral
conditional reading. -/
theorem policyMeasurePrefixExpectation_eq_behavioralWith
    (hconstrain : M.ConstrainsAlike)
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    [MeasurableSpace E.History]
    (sites : ℕ → (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i)
    (hcover : ∀ time,
      M.CoversInformationSites (sites time) (time + 1))
    (observable : ℕ → E.History → ℝ) (time : ℕ) :
    M.policyMeasurePrefixExpectation laws observable time =
      M.behavioralPrefixExpectation
        (M.policyMeasureBehavioralWith laws fallback) observable time := by
  unfold policyMeasurePrefixExpectation behavioralPrefixExpectation
  rw [M.runPolicyMeasure_eq_runBehavioralWith hconstrain laws (sites time)
    fallback (time + 1) (hcover time)]

/-- Discounted payoff equality for the reverse infinite-policy-measure Kuhn
law. The explicit summability premise separates the probabilistic equivalence
from analytic convergence; the same theorem applies to every updated law in
the unilateral-deviation result above. -/
theorem normalizedDiscountedPolicyMeasure_eq_behavioralWith
    (hconstrain : M.ConstrainsAlike)
    (laws : (i : ι) → M.PolicyMeasure i)
    [∀ i, IsProbabilityMeasure (laws i)]
    [MeasurableSpace E.History]
    (sites : ℕ → (i : ι) → Finset (M.InfoState i))
    (fallback : (i : ι) → M.Policy i)
    (hcover : ∀ time,
      M.CoversInformationSites (sites time) (time + 1))
    (observable : ℕ → E.History → ℝ) (discount : ℝ)
    (hsummable : Summable fun time => discount ^ time *
      M.behavioralPrefixExpectation
        (M.policyMeasureBehavioralWith laws fallback) observable time) :
    Summable (fun time => discount ^ time *
        M.policyMeasurePrefixExpectation laws observable time) ∧
      GameTheory.Math.normalizedDiscountedSum discount
          (M.policyMeasurePrefixExpectation laws observable) =
        GameTheory.Math.normalizedDiscountedSum discount
          (M.behavioralPrefixExpectation
            (M.policyMeasureBehavioralWith laws fallback) observable) := by
  have hpointwise : M.policyMeasurePrefixExpectation laws observable =
      M.behavioralPrefixExpectation
        (M.policyMeasureBehavioralWith laws fallback) observable := by
    funext time
    exact M.policyMeasurePrefixExpectation_eq_behavioralWith hconstrain
      laws sites fallback hcover observable time
  rw [hpointwise]
  exact ⟨hsummable, rfl⟩

end ReversePolicyLaw

end InformationModel

end GameTheory.Protocol
