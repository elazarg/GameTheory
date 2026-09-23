/-
# Bayes assessments for fully supported behavioral play

Full support at each reached decision site makes every legal history have
positive probability. Thus Bayes beliefs exist simultaneously at every site,
including sites that can have zero mass in a later limit.
-/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Analysis.Protocol.CounterfactualReach

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Full support at decision sites suffices for all legal joint actions;
inactive coordinates have a unique legal choice. -/
theorem behavioralJoint_fullSupport
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    (M.behavioralJoint strategy trace hterm).FullSupport := by
  intro joint
  apply M.mem_support_behavioralJoint strategy trace hterm joint.1 joint.2
  intro i
  let choice : M.Choice i (M.infoOf i trace) :=
    ⟨joint.1 i, (M.menu_adequate i trace (joint.1 i)).mpr
      (E.legalOption_of_legal joint.2 i)⟩
  show choice ∈ (strategy i (M.infoOf i trace)).support
  cases hchoice : joint.1 i with
  | none =>
      have hinactive : ¬ E.active state i := by
        have hlegal := E.legalOption_of_legal joint.2 i
        simpa [LegalOption, hchoice] using hlegal
      let := M.subsingleton_choice_of_not_active trace hinactive
      rw [FinDist.eq_pure_of_subsingleton (strategy i (M.infoOf i trace)) choice]
      exact FinDist.mem_support_pure.mpr rfl
  | some action =>
      have hmenu : some action ∈ M.menu i (M.infoOf i trace) := by
        rw [← hchoice]
        exact choice.2
      exact hfull i (M.informationSite i ⟨state, trace⟩ action hterm hmenu) choice

/-- Every legal history has positive reach under fully supported play. -/
theorem historyReachProbability_pos_of_fullSupport
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    (history : E.History) : 0 < M.historyReachProbability strategy history := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start =>
      show 0 < (FinDist.pure E.initHistory).prob E.initHistory
      rw [FinDist.prob_pure_self]
      norm_num
  | @extend source target prior joint isLegal realized ih =>
      rw [M.historyReachProbability_extend strategy prior joint isLegal realized]
      apply mul_pos ih
      unfold stepProb
      apply mul_pos
      · exact FinDist.prob_pos_iff.mpr
          (M.behavioralJoint_fullSupport strategy hfull prior isLegal.1 ⟨joint, isLegal⟩)
      · exact FinDist.prob_pos_iff.mpr realized

/-- Every finite decision information event has positive mass under full support. -/
theorem informationMass_pos_of_fullSupport
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    (i : ι) (site : M.InformationSite i)
    [Fintype (M.InformationHistory i site.1)] :
    0 < M.informationMass strategy i site := by
  obtain ⟨history, _, _⟩ := site.2
  unfold informationMass
  exact Finset.sum_pos' (fun h _ =>
    (M.historyReachProbability_pos_of_fullSupport strategy hfull h.1).le)
    ⟨history, Finset.mem_univ _,
      M.historyReachProbability_pos_of_fullSupport strategy hfull history.1⟩

/-- The canonical Bayes assessment of a fully supported strategy. -/
def bayesAssessment
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    (hantichain : M.DecisionInformationAntichain)
    [∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1)] :
    M.BehavioralAssessment where
  strategy := strategy
  belief i site := M.bayesBelief strategy i site (hantichain i site)
    (M.informationMass_pos_of_fullSupport strategy hfull i site)

@[simp] theorem bayesAssessment_strategy
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    (hantichain : M.DecisionInformationAntichain)
    [∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1)] :
    (M.bayesAssessment strategy hfull hantichain).strategy = strategy := rfl

theorem bayesAssessment_isBayesConsistent
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i), (strategy i site.1).FullSupport)
    (hantichain : M.DecisionInformationAntichain)
    [∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1)] :
    BehavioralAssessment.IsBayesConsistent M
      (M.bayesAssessment strategy hfull hantichain) hantichain := by
  intro i site _hmass history
  exact M.bayesBelief_prob strategy i site (hantichain i site)
    (M.informationMass_pos_of_fullSupport strategy hfull i site) history

end GameTheory.Protocol.InformationModel
