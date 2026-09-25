/-
# Correlation and strict dominance

Correlated equilibrium has an operational reading after a recommendation is
observed: conditional on receiving an action of positive probability, obeying
is at least as good as replacing it.  That conditional statement is the bridge
from correlation to the canonical relative-dominance predicate in `Response`.

The results are specialized to expected utility.  They introduce neither a
second equilibrium predicate nor a second conditioning interface, and they do
not require finite strategy carriers.

Primary reference: R. J. Aumann, “Subjectivity and Correlation in Randomized
Strategies,” *Journal of Mathematical Economics* 1 (1974).
-/

import GameTheory.Core.Response
import GameTheory.Math.Probability.ExpectationConditioning

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [DecidableEq ι]
variable {F : GameForm ι} {utility : F.sig.Outcome → ι → ℝ}

/-- Conditional obedience: after a positive-probability recommendation,
following it weakly beats every fixed replacement in conditional expected
utility. -/
theorem IsCorrelatedEq.conditional_obedience
    {law : PMF (Profile F.sig)}
    (hce : IsCorrelatedEq F (euPreference utility) law)
    (who : ι) (recommended replacement : F.sig.Strategy who)
    (hrecommended : recommended ∈
      (law.map fun profile => profile who).support) :
    euPreference utility who
      (F.outcomeLaw (fiberPosterior law (fun profile => profile who)
        recommended hrecommended))
      ((fiberPosterior law (fun profile => profile who)
        recommended hrecommended).bind fun profile =>
          F.play (Profile.update profile who replacement)) := by
  classical
  let respond : F.sig.Strategy who → F.sig.Strategy who :=
    fun action => if action = recommended then replacement else action
  let marginal := law.map fun profile => profile who
  let posterior := fun action ha =>
    fiberPosterior law (fun profile => profile who) action ha
  let baseKernel : ∀ action, action ∈ marginal.support → PMF F.sig.Outcome :=
    fun action ha => (posterior action ha).bind F.play
  let responseKernel : ∀ action, action ∈ marginal.support → PMF F.sig.Outcome :=
    fun action ha => (posterior action ha).bind fun profile =>
      F.play (Profile.update profile who (respond (profile who)))
  have hbaseDecomp : marginal.bindOnSupport baseKernel = law.bind F.play := by
    calc
      marginal.bindOnSupport baseKernel =
          (marginal.bindOnSupport posterior).bind F.play := by
        rw [bindOnSupport_bind]
      _ = law.bind F.play := by rw [fiberPosterior_reconstruct]
  have hresponseDecomp : marginal.bindOnSupport responseKernel =
      law.bind (fun profile =>
        F.play (Profile.update profile who (respond (profile who)))) := by
    calc
      marginal.bindOnSupport responseKernel =
          (marginal.bindOnSupport posterior).bind fun profile =>
            F.play (Profile.update profile who (respond (profile who))) := by
        rw [bindOnSupport_bind]
      _ = law.bind (fun profile =>
          F.play (Profile.update profile who (respond (profile who)))) := by
        rw [fiberPosterior_reconstruct]
  have hglobal := (isCorrelatedEq_iff law).mp hce who respond
  rcases hglobal with ⟨hbase, hresponse, hle⟩
  have hbase' : UtilityIntegrable utility who
      (marginal.bindOnSupport baseKernel) :=
    payoffIntegrable_congr_law hbaseDecomp.symm hbase
  have hresponse' : UtilityIntegrable utility who
      (marginal.bindOnSupport responseKernel) :=
    payoffIntegrable_congr_law hresponseDecomp.symm hresponse
  have hle' : expect (marginal.bindOnSupport responseKernel)
      (fun outcome => utility outcome who) hresponse' ≤
    expect (marginal.bindOnSupport baseKernel)
      (fun outcome => utility outcome who) hbase' := by
    have hle'' : expect (law.bind (fun profile =>
        F.play (Profile.update profile who (respond (profile who)))))
        (fun outcome => utility outcome who) hresponse ≤
      expect (law.bind F.play) (fun outcome => utility outcome who) hbase := by
      simpa only [expectedUtility, GameForm.outcomeLaw] using hle
    calc
      _ = expect (law.bind (fun profile =>
          F.play (Profile.update profile who (respond (profile who)))))
          (fun outcome => utility outcome who) hresponse :=
        expect_congr_law hresponseDecomp
          (fun outcome => utility outcome who) hresponse' hresponse
      _ ≤ expect (law.bind F.play) (fun outcome => utility outcome who) hbase :=
        hle''
      _ = expect (marginal.bindOnSupport baseKernel)
          (fun outcome => utility outcome who) hbase' :=
        (expect_congr_law hbaseDecomp
          (fun outcome => utility outcome who) hbase' hbase).symm
  have hlocal := expect_bindOnSupport_le_of_le_of_eq_off marginal baseKernel
    responseKernel (fun outcome => utility outcome who) hbase' hresponse'
    hle' recommended hrecommended (by
      intro action ha hne
      apply bind_congr_on_support
      intro profile hprofile
      have hfiber : profile who = action := by
        have hmem := hprofile
        rw [fiberPosterior_support] at hmem
        simpa only [Set.mem_ofPred_eq] using hmem.1
      have hne' : profile who ≠ recommended := by rw [hfiber]; exact hne
      simp [respond, hne', Profile.update_eq_self])
  have hbaseEq : baseKernel recommended hrecommended =
      F.outcomeLaw (posterior recommended hrecommended) := rfl
  have hresponseEq : responseKernel recommended hrecommended =
      (posterior recommended hrecommended).bind fun profile =>
        F.play (Profile.update profile who replacement) := by
    unfold responseKernel
    apply bind_congr_on_support
    intro profile hprofile
    have hfiber : profile who = recommended := by
      have hmem := hprofile
      rw [fiberPosterior_support] at hmem
      simpa only [Set.mem_ofPred_eq] using hmem.1
    simp [respond, hfiber]
  have hbaseLocal := payoffIntegrable_bindOnSupport_conditional_on_support
    marginal baseKernel (fun outcome => utility outcome who)
    hbase' recommended hrecommended
  have hresponseLocal := payoffIntegrable_bindOnSupport_conditional_on_support
    marginal responseKernel (fun outcome => utility outcome who)
    hresponse' recommended hrecommended
  refine ⟨?_, ?_, ?_⟩
  · exact payoffIntegrable_congr_law hbaseEq hbaseLocal
  · exact payoffIntegrable_congr_law hresponseEq hresponseLocal
  · simpa only [expectedUtility, hbaseEq, hresponseEq] using hlocal

/-- For expected utility, correlated equilibrium is exactly obedience after
each recommendation that can actually be observed, together with integration
of every actual ex-ante response law. Local obedience alone does not supply
integrability under an arbitrary mixture of recommendation cells.
Recommendations outside the law's support impose no condition.

The reverse implication disintegrates the law by the deviator's observed
recommendation.  Thus the local replacement checks jointly cover an arbitrary
recommendation-dependent response without requiring the strategy type itself
to be finite. -/
theorem isCorrelatedEq_iff_conditional_obedience
    (law : PMF (Profile F.sig)) :
    IsCorrelatedEq F (euPreference utility) law ↔
      (∀ who (respond : F.sig.Strategy who → F.sig.Strategy who),
        UtilityIntegrable utility who
          (law.bind fun profile =>
            F.play (Profile.update profile who (respond (profile who))))) ∧
      (∀ who recommended replacement,
        ∀ hrecommended : recommended ∈
          (law.map fun profile => profile who).support,
          euPreference utility who
            (F.outcomeLaw (fiberPosterior law (fun profile => profile who)
              recommended hrecommended))
            ((fiberPosterior law (fun profile => profile who)
              recommended hrecommended).bind fun profile =>
                F.play (Profile.update profile who replacement))) := by
  constructor
  · intro hce
    constructor
    · intro who respond
      rcases (isCorrelatedEq_iff law).mp hce who respond with
        ⟨_, hresponse, _⟩
      exact hresponse
    · intro who recommended replacement hrecommended
      exact hce.conditional_obedience who recommended replacement hrecommended
  · rintro ⟨hguards, hobedient⟩
    rw [isCorrelatedEq_iff]
    intro who respond
    classical
    let marginal := law.map fun profile => profile who
    let posterior := fun action ha =>
      fiberPosterior law (fun profile => profile who) action ha
    let baseKernel : ∀ action, action ∈ marginal.support → PMF F.sig.Outcome :=
      fun action ha => (posterior action ha).bind F.play
    let responseKernel : ∀ action, action ∈ marginal.support → PMF F.sig.Outcome :=
      fun action ha => (posterior action ha).bind fun profile =>
        F.play (Profile.update profile who (respond (profile who)))
    let responseActionKernel : ∀ action, action ∈ marginal.support → PMF F.sig.Outcome :=
      fun action ha => (posterior action ha).bind fun profile =>
        F.play (Profile.update profile who (respond action))
    have hbaseDecomp : marginal.bindOnSupport baseKernel = law.bind F.play := by
      calc
        marginal.bindOnSupport baseKernel =
            (marginal.bindOnSupport posterior).bind F.play := by
          rw [bindOnSupport_bind]
        _ = law.bind F.play := by rw [fiberPosterior_reconstruct]
    have hresponseDecomp : marginal.bindOnSupport responseKernel =
        law.bind (fun profile =>
          F.play (Profile.update profile who (respond (profile who)))) := by
      calc
        marginal.bindOnSupport responseKernel =
            (marginal.bindOnSupport posterior).bind fun profile =>
              F.play (Profile.update profile who (respond (profile who))) := by
          rw [bindOnSupport_bind]
        _ = law.bind (fun profile =>
            F.play (Profile.update profile who (respond (profile who)))) := by
          rw [fiberPosterior_reconstruct]
    have hidLaw : law.bind (fun profile =>
        F.play (Profile.update profile who (profile who))) = law.bind F.play := by
      apply bind_congr_on_support
      intro profile _
      rw [Profile.update_eq_self]
    have hbaseDev := hguards who (fun action => action)
    have hbase := payoffIntegrable_congr_law hidLaw hbaseDev
    have hresponse := hguards who respond
    have hbase' : UtilityIntegrable utility who
        (marginal.bindOnSupport baseKernel) :=
      payoffIntegrable_congr_law hbaseDecomp.symm hbase
    have hresponse' : UtilityIntegrable utility who
        (marginal.bindOnSupport responseKernel) :=
      payoffIntegrable_congr_law hresponseDecomp.symm hresponse
    have hpointwise : ∀ action, ∀ ha : action ∈ marginal.support,
        ∀ hbaseAction : UtilityIntegrable utility who
          (baseKernel action ha),
        ∀ hresponseAction : UtilityIntegrable utility who
          (responseKernel action ha),
          expect (responseKernel action ha) (fun outcome => utility outcome who)
            hresponseAction ≤
          expect (baseKernel action ha) (fun outcome => utility outcome who)
            hbaseAction := by
      intro action ha hbaseAction hresponseAction
      have hpref := hobedient who action (respond action) ha
      have hresponseEq : responseKernel action ha = responseActionKernel action ha := by
        apply bind_congr_on_support
        intro profile hprofile
        have hfiber : profile who = action := by
          have hmem := hprofile
          rw [fiberPosterior_support] at hmem
          simpa only [Set.mem_ofPred_eq] using hmem.1
        simp [hfiber]
      have hresponseFixed := payoffIntegrable_congr_law hresponseEq hresponseAction
      have hlePref := (euPreference_iff utility who _ _ hbaseAction
        hresponseFixed).mp hpref
      have hresponseActual := payoffIntegrable_congr_law hresponseEq.symm
        hresponseFixed
      calc
        expect (responseKernel action ha) (fun outcome => utility outcome who)
            hresponseAction =
          expect (responseKernel action ha) (fun outcome => utility outcome who)
            hresponseActual := expect_proof_irrel _ _ _ _
        _ = expect (responseActionKernel action ha)
            (fun outcome => utility outcome who) hresponseFixed :=
          expect_congr_law hresponseEq (fun outcome => utility outcome who)
            hresponseActual hresponseFixed
        _ ≤ expect (baseKernel action ha) (fun outcome => utility outcome who)
            hbaseAction := hlePref
    have hle := expect_bindOnSupport_mono_on_support marginal responseKernel
      baseKernel (fun outcome => utility outcome who) hresponse' hbase'
      (fun action ha hresp hbase => hpointwise action ha hbase hresp)
    refine ⟨hbase, hresponse, ?_⟩
    have hle' : expect (law.bind (fun profile =>
        F.play (Profile.update profile who (respond (profile who)))))
        (fun outcome => utility outcome who) hresponse ≤
      expect (law.bind F.play) (fun outcome => utility outcome who) hbase := by
      calc
        _ = expect (marginal.bindOnSupport responseKernel)
            (fun outcome => utility outcome who) hresponse' :=
          expect_congr_law hresponseDecomp
            (fun outcome => utility outcome who) hresponse' hresponse |>.symm
        _ ≤ expect (marginal.bindOnSupport baseKernel)
            (fun outcome => utility outcome who) hbase' := hle
        _ = expect (law.bind F.play) (fun outcome => utility outcome who) hbase :=
          expect_congr_law hbaseDecomp
            (fun outcome => utility outcome who) hbase' hbase
    simpa only [expectedUtility, GameForm.outcomeLaw] using hle'

/-- A correlated equilibrium never recommends an action that is strictly
dominated on a product set carrying the whole support.  The relative form is
the one needed by iterated elimination: the product set may shrink between
rounds. -/
theorem IsCorrelatedEq.support_avoids_strictlyDominatedOn
    {law : PMF (Profile F.sig)}
    (hce : IsCorrelatedEq F (euPreference utility) law)
    (allowed : ∀ j, Set (F.sig.Strategy j))
    (hsupport : ∀ profile ∈ law.support, ∀ j, profile j ∈ allowed j)
    (who : ι) {preferred dominated : F.sig.Strategy who}
    (hdom : StrictlyDominatesOn F (euPreference utility) who allowed preferred dominated) :
    ∀ profile ∈ law.support, profile who ≠ dominated := by
  intro witness hwitness heq
  let observation : Profile F.sig → F.sig.Strategy who := fun profile => profile who
  have hrecommended : dominated ∈ (law.map observation).support := by
    rw [PMF.support_map]
    exact ⟨witness, hwitness, heq⟩
  let posterior := fiberPosterior law observation dominated hrecommended
  let baseKernel : Profile F.sig → PMF F.sig.Outcome := F.play
  let deviationKernel : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile who preferred)
  have hwitnessPosterior : witness ∈ posterior.support := by
    rw [fiberPosterior_support]
    exact ⟨heq, hwitness⟩
  have hobey := hce.conditional_obedience who dominated preferred hrecommended
  rcases hobey with ⟨hbase, hdeviation, hle⟩
  have hbaseCond := payoffIntegrable_bind_conditional_on_support
    posterior baseKernel (fun outcome => utility outcome who) hbase
  have hdeviationCond := payoffIntegrable_bind_conditional_on_support
    posterior deviationKernel (fun outcome => utility outcome who) hdeviation
  let baseValue : Profile F.sig → ℝ := extendFromSupport posterior
    (fun profile hprofile => expectedUtility utility who (baseKernel profile)
      (hbaseCond profile hprofile))
  let deviationValue : Profile F.sig → ℝ := extendFromSupport posterior
    (fun profile hprofile => expectedUtility utility who (deviationKernel profile)
      (hdeviationCond profile hprofile))
  have hbaseAgree : ∀ profile, ∀ hprofile : profile ∈ posterior.support,
      baseValue profile = expectedUtility utility who (baseKernel profile)
        (hbaseCond profile hprofile) := by
    intro profile hprofile
    have hne : posterior profile ≠ 0 :=
      (posterior.mem_support_iff profile).mp hprofile
    simp [baseValue, extendFromSupport, hne]
  have hdeviationAgree : ∀ profile,
      ∀ hprofile : profile ∈ posterior.support,
        deviationValue profile = expectedUtility utility who
          (deviationKernel profile) (hdeviationCond profile hprofile) := by
    intro profile hprofile
    have hne : posterior profile ≠ 0 :=
      (posterior.mem_support_iff profile).mp hprofile
    simp [deviationValue, extendFromSupport, hne]
  have hbaseValueIntegrable := payoffIntegrable_bind_conditionalValue_on_support
    posterior baseKernel (fun outcome => utility outcome who) hbase baseValue
    hbaseAgree
  have hdeviationValueIntegrable :=
    payoffIntegrable_bind_conditionalValue_on_support posterior deviationKernel
      (fun outcome => utility outcome who) hdeviation deviationValue hdeviationAgree
  have hbaseTower := expect_bind_tower_on_support posterior baseKernel
    (fun outcome => utility outcome who) hbase baseValue hbaseAgree
  have hdeviationTower := expect_bind_tower_on_support posterior deviationKernel
    (fun outcome => utility outcome who) hdeviation deviationValue hdeviationAgree
  have hlePointwise : ∀ profile, profile ∈ posterior.support →
      baseValue profile ≤ deviationValue profile := by
    intro profile hprofile
    have hmem : profile ∈ law.support := by
      have hmem := hprofile
      rw [fiberPosterior_support] at hmem
      exact hmem.2
    have hfiber : profile who = dominated := by
      have hmem' := hprofile
      rw [fiberPosterior_support] at hmem'
      simpa only [Set.mem_ofPred_eq] using hmem'.1
    have hstrict := hdom profile (hsupport profile hmem)
    have hself : Profile.update profile who dominated = profile := by
      rw [← hfiber]
      exact Profile.update_eq_self profile who
    simp only [Preference.strict] at hstrict
    rw [hself] at hstrict
    have hbaseGuard := hbaseCond profile hprofile
    have hdeviationGuard := hdeviationCond profile hprofile
    have hleValue := (euPreference_iff utility who
      (deviationKernel profile) (baseKernel profile)
      hdeviationGuard hbaseGuard).mp hstrict.1
    have hneReverse : ¬ expect (deviationKernel profile)
        (fun outcome => utility outcome who) hdeviationGuard ≤
      expect (baseKernel profile) (fun outcome => utility outcome who) hbaseGuard := by
      intro hreverse
      apply hstrict.2
      exact (euPreference_iff utility who (baseKernel profile)
        (deviationKernel profile) hbaseGuard hdeviationGuard).mpr hreverse
    have hneValues :
        expect (baseKernel profile) (fun outcome => utility outcome who) hbaseGuard ≠
          expect (deviationKernel profile) (fun outcome => utility outcome who)
            hdeviationGuard := by
      intro heq
      apply hneReverse
      rw [heq]
    have hlt := lt_of_le_of_ne hleValue hneValues
    calc
      baseValue profile = expectedUtility utility who (baseKernel profile)
          (hbaseCond profile hprofile) := hbaseAgree profile hprofile
      _ ≤ expectedUtility utility who (deviationKernel profile)
          (hdeviationCond profile hprofile) := hlt.le
      _ = deviationValue profile := (hdeviationAgree profile hprofile).symm
  have hltWitness : baseValue witness < deviationValue witness := by
    have hfiber : witness who = dominated := heq
    have hallowed := hsupport witness hwitness
    have hstrict := hdom witness hallowed
    have hself : Profile.update witness who dominated = witness := by
      rw [← heq]
      exact Profile.update_eq_self witness who
    simp only [Preference.strict] at hstrict
    rw [hself] at hstrict
    have hbaseGuard := hbaseCond witness hwitnessPosterior
    have hdeviationGuard := hdeviationCond witness hwitnessPosterior
    have hleValue := (euPreference_iff utility who
      (deviationKernel witness) (baseKernel witness)
      hdeviationGuard hbaseGuard).mp hstrict.1
    have hneReverse : ¬ expect (deviationKernel witness)
        (fun outcome => utility outcome who) hdeviationGuard ≤
      expect (baseKernel witness) (fun outcome => utility outcome who) hbaseGuard := by
      intro hreverse
      apply hstrict.2
      exact (euPreference_iff utility who (baseKernel witness)
        (deviationKernel witness) hbaseGuard hdeviationGuard).mpr hreverse
    have hneValues :
        expect (baseKernel witness) (fun outcome => utility outcome who) hbaseGuard ≠
          expect (deviationKernel witness) (fun outcome => utility outcome who)
            hdeviationGuard := by
      intro heq
      apply hneReverse
      rw [heq]
    have hlt := lt_of_le_of_ne hleValue hneValues
    calc
      baseValue witness = expectedUtility utility who (baseKernel witness)
          (hbaseCond witness hwitnessPosterior) :=
        hbaseAgree witness hwitnessPosterior
      _ < expectedUtility utility who (deviationKernel witness)
          (hdeviationCond witness hwitnessPosterior) := hlt
      _ = deviationValue witness :=
        (hdeviationAgree witness hwitnessPosterior).symm
  have hstrictExpectation := expect_lt_of_mem_support hbaseValueIntegrable
    hdeviationValueIntegrable hlePointwise witness hwitnessPosterior hltWitness
  have hconditionalOrder : expect (posterior.bind deviationKernel)
      (fun outcome => utility outcome who) hdeviation ≤
    expect (posterior.bind baseKernel) (fun outcome => utility outcome who) hbase := by
    simpa only [expectedUtility, GameForm.outcomeLaw, posterior,
      deviationKernel, baseKernel] using hle
  rw [hdeviationTower, hbaseTower] at hconditionalOrder
  linarith

/-- A coarse correlated equilibrium supported at a profile of strictly
dominant actions is concentrated coordinatewise at those actions. -/
theorem IsCoarseCorrelatedEq.support_plays_strictDominant
    {law : PMF (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law)
    (who : ι) (dominant : F.sig.Strategy who)
    (hdom : IsStrictDominant F (euPreference utility) who dominant) :
    ∀ profile ∈ law.support, profile who = dominant := by
  intro witness hwitness
  by_contra hne
  let baseKernel : Profile F.sig → PMF F.sig.Outcome := F.play
  let deviationKernel : Profile F.sig → PMF F.sig.Outcome := fun profile =>
    F.play (Profile.update profile who dominant)
  have hglobal := (isCoarseCorrelatedEq_iff law).mp hcce who dominant
  rcases hglobal with ⟨hbase, hdeviation, hle⟩
  have hbase' : UtilityIntegrable utility who (law.bind baseKernel) := by
    simpa only [GameForm.outcomeLaw] using hbase
  have hdeviation' : UtilityIntegrable utility who (law.bind deviationKernel) :=
    hdeviation
  have hlePointwise : ∀ profile, ∀ hprofile : profile ∈ law.support,
      expect (baseKernel profile) (fun outcome => utility outcome who)
          (payoffIntegrable_bind_conditional_on_support law baseKernel
            (fun outcome => utility outcome who) hbase' profile hprofile) ≤
        expect (deviationKernel profile) (fun outcome => utility outcome who)
          (payoffIntegrable_bind_conditional_on_support law deviationKernel
            (fun outcome => utility outcome who) hdeviation' profile hprofile) := by
    intro profile hprofile
    dsimp only [baseKernel, deviationKernel]
    have hbaseCond := payoffIntegrable_bind_conditional_on_support law F.play
      (fun outcome => utility outcome who) hbase' profile hprofile
    have hdeviationCond := payoffIntegrable_bind_conditional_on_support law
      deviationKernel (fun outcome => utility outcome who) hdeviation' profile hprofile
    by_cases heq : profile who = dominant
    · have hsame : F.play (Profile.update profile who dominant) = F.play profile := by
        rw [← heq]
        exact congrArg F.play (Profile.update_eq_self profile who)
      have heqExpect := expect_congr_law hsame (fun outcome => utility outcome who)
        hdeviationCond hbaseCond
      exact heqExpect.symm.le
    · have hstrict := hdom (profile who) heq profile (fun _ => Set.mem_univ _)
      have hself : Profile.update profile who (profile who) = profile :=
        Profile.update_eq_self profile who
      rw [hself] at hstrict
      simp only [Preference.strict] at hstrict
      have hpreferred := (euPreference_iff utility who
        (F.play (Profile.update profile who dominant)) (F.play profile)
        hdeviationCond hbaseCond).mp hstrict.1
      exact hpreferred
  have hstrictWitness : expect (baseKernel witness)
      (fun outcome => utility outcome who)
      (payoffIntegrable_bind_conditional_on_support law baseKernel
        (fun outcome => utility outcome who) hbase' witness hwitness) <
    expect (deviationKernel witness) (fun outcome => utility outcome who)
      (payoffIntegrable_bind_conditional_on_support law deviationKernel
        (fun outcome => utility outcome who) hdeviation' witness hwitness) := by
    dsimp only [baseKernel, deviationKernel]
    have hbaseCond := payoffIntegrable_bind_conditional_on_support law F.play
      (fun outcome => utility outcome who) hbase' witness hwitness
    have hdeviationCond := payoffIntegrable_bind_conditional_on_support law
      deviationKernel (fun outcome => utility outcome who) hdeviation' witness hwitness
    have hstrict := hdom (witness who) hne witness (fun _ => Set.mem_univ _)
    have hself : Profile.update witness who (witness who) = witness :=
      Profile.update_eq_self witness who
    rw [hself] at hstrict
    simp only [Preference.strict] at hstrict
    have hpreferred := (euPreference_iff utility who
      (F.play (Profile.update witness who dominant)) (F.play witness)
      hdeviationCond hbaseCond).mp hstrict.1
    have hnotReverse : ¬ expect (F.play (Profile.update witness who dominant))
        (fun outcome => utility outcome who) hdeviationCond ≤
      expect (F.play witness) (fun outcome => utility outcome who) hbaseCond := by
      intro hreverse
      apply hstrict.2
      exact (euPreference_iff utility who
        (F.play witness) (F.play (Profile.update witness who dominant))
        hbaseCond hdeviationCond).mpr
        hreverse
    exact lt_of_le_of_ne hpreferred (fun heq => hnotReverse heq.symm.le)
  have hstrictAggregate := expect_bind_lt_on_support law baseKernel deviationKernel
    (fun outcome => utility outcome who) hbase' hdeviation' hlePointwise witness
    hwitness hstrictWitness
  have hglobalOrder : expect (law.bind deviationKernel)
      (fun outcome => utility outcome who) hdeviation' ≤
    expect (law.bind baseKernel) (fun outcome => utility outcome who) hbase' := by
    simpa only [expectedUtility, GameForm.outcomeLaw, baseKernel, deviationKernel]
      using hle
  exact (not_le_of_gt hstrictAggregate) hglobalOrder

/-- If every coordinate of a profile is strictly dominant, that profile's
point mass is the unique coarse correlated equilibrium. -/
theorem strictDominant_isCoarseCorrelatedEq_iff
    {profile : Profile F.sig}
    (hdom : ∀ who, IsStrictDominant F (euPreference utility) who (profile who))
    (hincumbent : ∀ who, UtilityIntegrable utility who (F.play profile))
    {law : PMF (Profile F.sig)} :
    IsCoarseCorrelatedEq F (euPreference utility) law ↔ law = PMF.pure profile := by
  constructor
  · intro hcce
    have hsubset : law.support ⊆ ({profile} : Set (Profile F.sig)) := by
      intro candidate hcandidate
      apply Set.mem_singleton_iff.mpr
      funext who
      exact hcce.support_plays_strictDominant who (profile who) (hdom who)
        candidate hcandidate
    have hsupport : law.support = ({profile} : Set (Profile F.sig)) := by
      apply Set.Subset.antisymm hsubset
      obtain ⟨candidate, hcandidate⟩ := law.support_nonempty
      have heq := Set.mem_singleton_iff.mp (hsubset hcandidate)
      rw [← heq]
      exact Set.singleton_subset_iff.mpr hcandidate
    apply PMF.ext
    intro candidate
    by_cases heq : candidate = profile
    · subst candidate
      simp [PMF.pure_apply]
      exact (law.apply_eq_one_iff profile).2 hsupport
    · simp only [PMF.pure_apply, heq, ite_false]
      have hnot : candidate ∉ law.support := by
        intro hcandidate
        exact heq (Set.mem_singleton_iff.mp (hsubset hcandidate))
      exact law.apply_eq_zero_iff candidate |>.2 hnot
  · rintro rfl
    have hself : ∀ who,
        euPreference utility who (F.play profile) (F.play profile) := by
      intro who
      exact (euPreference_iff utility who (F.play profile) (F.play profile)
        (hincumbent who) (hincumbent who)).mpr le_rfl
    have hnash := isNash_of_forall_isStrictDominant hself hdom
    exact hnash.isCorrelatedEq.isCoarseCorrelatedEq

/-- Strictly dominant actions also pin the unique correlated equilibrium, as
an immediate consequence of the coarse result. -/
theorem strictDominant_isCorrelatedEq_iff
    {profile : Profile F.sig}
    (hdom : ∀ who, IsStrictDominant F (euPreference utility) who (profile who))
    (hincumbent : ∀ who, UtilityIntegrable utility who (F.play profile))
    {law : PMF (Profile F.sig)} :
    IsCorrelatedEq F (euPreference utility) law ↔ law = PMF.pure profile := by
  constructor
  · intro hce
    exact (strictDominant_isCoarseCorrelatedEq_iff hdom hincumbent).mp
      hce.isCoarseCorrelatedEq
  · rintro rfl
    have hself : ∀ who,
        euPreference utility who (F.play profile) (F.play profile) := by
      intro who
      exact (euPreference_iff utility who (F.play profile) (F.play profile)
        (hincumbent who) (hincumbent who)).mpr le_rfl
    exact (isNash_of_forall_isStrictDominant hself hdom).isCorrelatedEq

end GameTheory
