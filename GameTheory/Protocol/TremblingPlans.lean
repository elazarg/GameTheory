/-
# Independent local trembles on decision plans

A law over pure decision plans can be trembled coordinatewise: at every
decision site the prescribed choice is mixed, independently of all other
sites, with the uniform law on the site's menu. The trembled mixed policy keeps
a floor at every choice of its behavioral reading, whatever correlation the
prescribed plans carry, because under decision recall conditioning on the
player's own past never restricts the current coordinate. Conversely, a
behavioral table with that floor at every site is the tremble of independent
residual plans.
-/

import GameTheory.Math.Probability.ProductConditioning
import GameTheory.Math.Probability.UniformTremble
import GameTheory.Protocol.DecisionPlan
import GameTheory.Protocol.PolicyRandomization

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E} {who : ι}

instance InformationSite.choice_nonempty (site : M.InformationSite who) :
    Nonempty (M.Choice who site.1) := by
  obtain ⟨_history, _nonterminal, action, permitted⟩ := site.2
  exact ⟨⟨some action, permitted⟩⟩

/-- Every recorded own action was taken at a decision site whose menu offers
it. -/
theorem exists_informationSite_of_mem_ownPlay {state : E.State} (trace : E.Trace state)
    {recorded : M.InfoState who × E.Action who} (member : recorded ∈ M.ownPlay who trace) :
    ∃ site : M.InformationSite who, site.1 = recorded.1 ∧
      some recorded.2 ∈ M.menu who site.1 := by
  induction trace with
  | start => simp only [InfoSignals.ownPlay, List.not_mem_nil] at member
  | @extend source target prior joint legal realized induction =>
    cases acted : joint who with
    | none =>
      simp only [InfoSignals.ownPlay, acted] at member
      exact induction member
    | some action =>
      simp only [InfoSignals.ownPlay, acted, List.mem_cons] at member
      rcases member with same | member
      · subst recorded
        have permitted : some action ∈ M.menu who (M.infoOf who prior) := by
          rw [← acted]
          exact (M.menu_adequate who prior (joint who)).mpr
            (E.legalOption_of_legal legal who)
        exact ⟨M.informationSite who ⟨source, prior⟩ action legal.1 permitted, rfl, permitted⟩
      · exact induction member

/-- Under decision recall, a decision site does not occur in its own record. -/
theorem InformationSite.not_mem_recordAt (recall : M.DecisionRecall)
    (site : M.InformationSite who) (action : E.Action who) :
    (site.1, action) ∉ M.recordAt who site.1 := by
  obtain ⟨history, nonterminal, _witness, _permitted⟩ := site.2
  obtain ⟨joint, legal⟩ := E.exists_legal nonterminal
  obtain ⟨chosen, acted⟩ := (E.legalOption_of_legal legal who).exists_eq_some_of_active
    (joint who) (InformationSite.active M site history)
  obtain ⟨next, realized⟩ := (E.step history.1.state ⟨joint, legal⟩).support_nonempty
  let extended : E.Trace next := .extend history.1.trace joint legal realized
  have noRepeat := recall.actsOnceAtEachInfoState who extended
  simp only [extended, InfoSignals.actedAt, acted, List.nodup_cons] at noRepeat
  rw [recall.recordAt_eq_ownPlay who site history]
  intro member
  exact noRepeat.1 (by
    rw [history.2, M.actedAt_eq_map_ownPlay]
    exact List.mem_map.mpr ⟨_, member, rfl⟩)

/-- The choices at one table coordinate compatible with the player's own
record on reaching another decision site. -/
def InformationSite.recordChoices (current site : M.InformationSite who) :
    Set (M.Choice who site.1) :=
  {choice | ∀ recorded ∈ M.recordAt who current.1,
    recorded.1 = site.1 → choice.1 = some recorded.2}

/-- The player's record on reaching a site does not restrict that site. -/
theorem InformationSite.recordChoices_self (recall : M.DecisionRecall)
    (current : M.InformationSite who) : current.recordChoices current = Set.univ := by
  ext choice
  simp only [InformationSite.recordChoices, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro recorded member same
  exact (current.not_mem_recordAt recall recorded.2 (same ▸ member)).elim

/-- Decision recall makes the record's restrictions jointly satisfiable: no
coordinate is required to record two different own actions. -/
theorem InformationSite.recordChoices_nonempty (recall : M.DecisionRecall)
    (current site : M.InformationSite who) : (current.recordChoices site).Nonempty := by
  classical
  obtain ⟨history, _nonterminal, _action, _permitted⟩ := current.2
  have record := recall.recordAt_eq_ownPlay who current history
  have noRepeat : ((M.recordAt who current.1).map Prod.fst).Nodup := by
    rw [record, ← M.actedAt_eq_map_ownPlay]
    exact recall.actsOnceAtEachInfoState who _
  by_cases visited : ∃ recorded ∈ M.recordAt who current.1, recorded.1 = site.1
  · obtain ⟨recorded, member, same⟩ := visited
    have past : recorded ∈ M.ownPlay who history.1.trace := record ▸ member
    obtain ⟨earlier, earlierSame, permitted⟩ :=
      M.exists_informationSite_of_mem_ownPlay history.1.trace past
    have legal : some recorded.2 ∈ M.menu who site.1 := by
      simpa only [earlierSame, same] using permitted
    refine ⟨⟨some recorded.2, legal⟩, ?_⟩
    intro other otherMember otherSame
    have equal := List.inj_on_of_nodup_map noRepeat otherMember member
      (otherSame.trans same.symm)
    exact congrArg (fun pair : M.InfoState who × E.Action who => some pair.2) equal.symm
  · refine ⟨Classical.choice (inferInstance : Nonempty (M.Choice who site.1)), ?_⟩
    intro recorded member same
    exact (visited ⟨recorded, member, same⟩).elim

/-- An extended decision table could have brought play to a decision site
exactly when every coordinate is compatible with the record there. -/
theorem DecisionPlan.consistentAt_extend_iff (recall : M.DecisionRecall)
    (plan : M.DecisionPlan who) (fallback : M.Policy who)
    (current : M.InformationSite who) :
    plan.extend fallback ∈ M.ConsistentAt who current.1 ↔
      ∀ site, plan site ∈ current.recordChoices site := by
  constructor
  · intro compatible site recorded member same
    have agreement := compatible recorded member
    rw [same, DecisionPlan.extend_site] at agreement
    exact agreement
  · intro compatible recorded member
    obtain ⟨history, _nonterminal, _action, _permitted⟩ := current.2
    have past : recorded ∈ M.ownPlay who history.1.trace := by
      simpa only [recall.recordAt_eq_ownPlay who current history] using member
    obtain ⟨site, same, _permitted⟩ :=
      M.exists_informationSite_of_mem_ownPlay history.1.trace past
    rw [← same, DecisionPlan.extend_site]
    exact compatible site recorded member same.symm

variable [Fintype (M.InformationSite who)]
  [∀ site : M.InformationSite who, Fintype (M.Choice who site.1)]

/-- Independently tremble every coordinate of a plan: at each decision site,
the prescribed choice is mixed with the uniform law on the menu, the uniform
law receiving that site's tremble mass. -/
def DecisionPlan.tremble (plan : M.DecisionPlan who) (mass : M.InformationSite who → ℝ)
    (nonnegative : ∀ site, 0 ≤ mass site) (atMostOne : ∀ site, mass site ≤ 1) :
    PMF (M.DecisionPlan who) :=
  independentProduct fun site =>
    mix (mass site) (nonnegative site) (atMostOne site) (PMF.uniformOfFintype _)
      (PMF.pure (plan site))

/-- Before any conditioning, each coordinate of a trembled plan is its own
uniform tremble of the prescribed choice. -/
theorem DecisionPlan.tremble_marginal (plan : M.DecisionPlan who)
    (mass : M.InformationSite who → ℝ) (nonnegative : ∀ site, 0 ≤ mass site)
    (atMostOne : ∀ site, mass site ≤ 1) (site : M.InformationSite who) :
    (plan.tremble mass nonnegative atMostOne).map (fun realized => realized site) =
      mix (mass site) (nonnegative site) (atMostOne site) (PMF.uniformOfFintype _)
        (PMF.pure (plan site)) := by
  classical
  exact independentProduct_map_eval _ site

/-- Positive trembles reach every plan. -/
theorem DecisionPlan.mem_support_tremble (plan : M.DecisionPlan who)
    (mass : M.InformationSite who → ℝ) (positive : ∀ site, 0 < mass site)
    (atMostOne : ∀ site, mass site ≤ 1) (realized : M.DecisionPlan who) :
    realized ∈ (plan.tremble mass (fun site => (positive site).le) atMostOne).support :=
  (independentProduct_support_iff _ _).mpr fun site =>
    mem_support_mix_uniform (mass site) (positive site) (atMostOne site) _ (realized site)

/-- Draw a prescribed plan, tremble its coordinates independently, and extend
the realized table to a whole policy. -/
def trembledMixedPolicy (plans : PMF (M.DecisionPlan who))
    (mass : M.InformationSite who → ℝ) (nonnegative : ∀ site, 0 ≤ mass site)
    (atMostOne : ∀ site, mass site ≤ 1) (fallback : M.Policy who) : M.MixedPolicy who :=
  (plans.bind fun plan => plan.tremble mass nonnegative atMostOne).map
    (fun plan => plan.extend fallback)

/-- Under positive trembles every decision site is compatible with some
supported policy, whatever correlation the prescribed plans carry. -/
theorem trembledMixedPolicy_consistent (recall : M.DecisionRecall)
    (plans : PMF (M.DecisionPlan who)) (mass : M.InformationSite who → ℝ)
    (positive : ∀ site, 0 < mass site) (atMostOne : ∀ site, mass site ≤ 1)
    (fallback : M.Policy who) (current : M.InformationSite who) :
    ∃ policy ∈ M.ConsistentAt who current.1, policy ∈
      (trembledMixedPolicy plans mass (fun site => (positive site).le) atMostOne
        fallback).support := by
  classical
  let realized : M.DecisionPlan who := fun site =>
    (current.recordChoices_nonempty recall site).choose
  have compatible : ∀ site, realized site ∈ current.recordChoices site :=
    fun site => (current.recordChoices_nonempty recall site).choose_spec
  obtain ⟨prescribed, supported⟩ := plans.support_nonempty
  refine ⟨realized.extend fallback,
    (realized.consistentAt_extend_iff recall fallback current).mpr compatible, ?_⟩
  rw [trembledMixedPolicy, PMF.support_map]
  refine ⟨realized, ?_, rfl⟩
  rw [PMF.support_bind]
  exact Set.mem_iUnion₂.mpr
    ⟨prescribed, supported, prescribed.mem_support_tremble mass positive atMostOne realized⟩

/-- **Trembled plans keep their floor.** The behavioral reading of a trembled
mixed policy gives every choice at a decision site at least that site's share
of its tremble mass. -/
theorem div_card_le_trembledMixedPolicy_toBehavioralWith (recall : M.DecisionRecall)
    (plans : PMF (M.DecisionPlan who)) (mass : M.InformationSite who → ℝ)
    (positive : ∀ site, 0 < mass site) (atMostOne : ∀ site, mass site ≤ 1)
    (fallback : M.Policy who) (current : M.InformationSite who)
    (action : M.Choice who current.1) :
    mass current / Fintype.card (M.Choice who current.1) ≤
      (((trembledMixedPolicy plans mass (fun site => (positive site).le) atMostOne
        fallback).toBehavioralWith fallback current.1) action).toReal := by
  classical
  let law := plans.bind fun plan => plan.tremble mass (fun site => (positive site).le) atMostOne
  let extend : M.DecisionPlan who → M.Policy who := fun plan => plan.extend fallback
  let event : Set (M.DecisionPlan who) :=
    {plan | ∀ site, plan site ∈ current.recordChoices site}
  have event_eq : extend ⁻¹' M.ConsistentAt who current.1 = event := by
    ext plan
    exact plan.consistentAt_extend_iff recall fallback current
  have answer_eq : extend ⁻¹' (fun policy : M.Policy who => policy current.1) ⁻¹' {action} =
      (fun plan : M.DecisionPlan who => plan current) ⁻¹' {action} := by
    ext plan
    simp [extend]
  have supported := trembledMixedPolicy_consistent recall plans mass positive atMostOne
    fallback current
  have table_positive : ∃ plan ∈ event, plan ∈ law.support := by
    obtain ⟨policy, compatible, present⟩ := supported
    rw [trembledMixedPolicy, PMF.support_map] at present
    obtain ⟨plan, present, rfl⟩ := present
    exact ⟨plan, (plan.consistentAt_extend_iff recall fallback current).mp compatible, present⟩
  have lower := le_prob_filter_mixture_independentProduct plans
    (fun plan site => mix (mass site) (positive site).le (atMostOne site)
      (PMF.uniformOfFintype _) (PMF.pure (plan site)))
    current.recordChoices current (current.recordChoices_self recall) action _
    (fun plan _ => div_card_le_mix_uniform_apply _ (positive current).le (atMostOne current)
      _ action)
    table_positive
  change _ ≤ ((MixedPolicy.toBehavioralWith (M := M)
    (law.map extend) fallback current.1) action).toReal
  change ∃ policy ∈ M.ConsistentAt who current.1,
    policy ∈ (law.map extend).support at supported
  rw [MixedPolicy.toBehavioralWith, dite_eq_left supported,
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    toOuterMeasure_filter_apply, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    Set.preimage_inter, event_eq, answer_eq]
  refine lower.trans_eq (congrArg ENNReal.toReal ?_)
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact toOuterMeasure_filter_apply _ _ _ _

/-- Independent residual plans of a behavioral table giving every choice at
least its site's share of the tremble mass. -/
def BehavioralDecisionPlan.residualPlans (policy : M.BehavioralDecisionPlan who)
    (mass : M.InformationSite who → ℝ) (nonnegative : ∀ site, 0 ≤ mass site)
    (belowOne : ∀ site, mass site < 1)
    (floor : ∀ site (choice : M.Choice who site.1),
      mass site / Fintype.card (M.Choice who site.1) ≤ ((policy site) choice).toReal) :
    PMF (M.DecisionPlan who) :=
  independentProduct fun site =>
    (exists_mix_uniform_eq_of_floor (policy site) (mass site) (nonnegative site)
      (belowOne site) (floor site)).choose

/-- **Floors are trembles of residual plans.** Independent residual plans,
trembled independently, recover the product law of the behavioral table. -/
theorem BehavioralDecisionPlan.residualPlans_tremble (policy : M.BehavioralDecisionPlan who)
    (mass : M.InformationSite who → ℝ) (nonnegative : ∀ site, 0 ≤ mass site)
    (belowOne : ∀ site, mass site < 1)
    (floor : ∀ site (choice : M.Choice who site.1),
      mass site / Fintype.card (M.Choice who site.1) ≤ ((policy site) choice).toReal) :
    (policy.residualPlans mass nonnegative belowOne floor).bind
        (fun plan => plan.tremble mass nonnegative fun site => (belowOne site).le) =
      independentProduct policy := by
  refine (independentProduct_bind _ fun site (choice : M.Choice who site.1) =>
    mix (mass site) (nonnegative site) (belowOne site).le (PMF.uniformOfFintype _)
      (PMF.pure choice)).trans (congrArg independentProduct (funext fun site => ?_))
  rw [bind_mix_pure]
  exact (exists_mix_uniform_eq_of_floor (policy site) (mass site) (nonnegative site)
    (belowOne site) (floor site)).choose_spec

end GameTheory.Protocol.InformationModel
