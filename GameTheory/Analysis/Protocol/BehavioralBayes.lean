/-
# Bayes assessments for fully supported behavioral play

Full support at each reached decision site makes every legal history have
positive probability. Thus Bayes beliefs exist simultaneously at every site,
including sites that can have zero mass in a later limit.
-/

import GameTheory.Analysis.Protocol.Sequential

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
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    ∀ joint : {joint : ∀ i, Option (E.Action i) // E.Legal state joint},
      joint ∈ (M.behavioralJoint strategy trace hterm).support := by
  intro joint
  let draws : (i : ι) → M.Choice i (M.infoOf i trace) :=
    fun i => ⟨joint.1 i, (M.menu_adequate i trace (joint.1 i)).mpr
      (E.legalOption_of_legal joint.2 i)⟩
  rw [behavioralJoint, PMF.support_map]
  refine ⟨draws, ?_, ?_⟩
  · rw [independentProduct_support_iff]
    intro i
    cases hchoice : joint.1 i with
    | none =>
        have hinactive : ¬ E.active state i := by
          have hlegal := E.legalOption_of_legal joint.2 i
          simpa only [LegalOption, hchoice] using hlegal
        have hsubsingleton :
            Subsingleton (M.Choice i (M.infoOf i trace)) :=
          M.subsingleton_choice_of_not_active trace hinactive
        rw [eq_pure_of_subsingleton (strategy i (M.infoOf i trace))
          (draws i)]
        simp [draws, hchoice]
    | some action =>
        have hlegal :
            E.active state i ∧ action ∈ E.available state i := by
          have hlegal := E.legalOption_of_legal joint.2 i
          simpa only [LegalOption, hchoice] using hlegal
        have hmenu : some action ∈ M.menu i (M.infoOf i trace) :=
          (M.menu_adequate i trace (some action)).mpr hlegal
        let history : E.History := ⟨state, trace⟩
        let site : M.InformationSite i :=
          ⟨M.infoOf i trace, ⟨⟨history, rfl⟩, hterm, action, hmenu⟩⟩
        exact hfull i site (draws i)
  · apply Subtype.ext
    rfl

/-- Every legal history has positive canonical history weight
when each local action choice has positive support. -/
theorem historyReachWeight_pos_of_fullSupport
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    (history : E.History) :
    0 < M.historyReachWeight strategy history := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start =>
      apply (PMF.apply_pos_iff _ _).2
      rw [runBehavioral,
        show ExecutionProtocol.Trace.start.length = 0 from rfl,
        runBehavioralFrom]
      rw [ExecutionProtocol.runRandomizedFor_zero, PMF.mem_support_pure_iff]
      rfl
  | @extend source target prior joint isLegal realized ih =>
      let previous : E.History := ⟨source, prior⟩
      let next : E.History := ⟨target, prior.extend joint isLegal realized⟩
      have hprev : previous ∈
          (M.runBehavioralFrom strategy prior.length E.initHistory).support :=
        (PMF.apply_pos_iff _ _).mp ih
      have hdraw :
          (⟨joint, isLegal⟩ : {action : ∀ i, Option (E.Action i) //
            E.Legal source action}) ∈
            (M.behavioralJoint strategy prior isLegal.1).support :=
        M.behavioralJoint_fullSupport strategy hfull prior isLegal.1
          ⟨joint, isLegal⟩
      have hstep : next ∈
          (M.runBehavioralFrom strategy 1 previous).support := by
        rw [M.runBehavioralFrom_succ_of_not_terminal strategy 0 isLegal.1,
          PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨⟨joint, isLegal⟩, hdraw, ?_⟩
        rw [PMF.support_bindOnSupport]
        refine Set.mem_iUnion₂.mpr ⟨target, realized, ?_⟩
        rw [runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero,
          PMF.mem_support_pure_iff]
        rfl
      have hmem : next ∈
          (M.runBehavioralFrom strategy (prior.length + 1) E.initHistory).support := by
        rw [M.runBehavioralFrom_add, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨previous, hprev, hstep⟩
      have hpositive :
          0 < M.runBehavioralFrom strategy (prior.length + 1) E.initHistory next :=
        (PMF.apply_pos_iff _ _).mpr hmem
      simpa [historyReachWeight, runBehavioral, next,
        ExecutionProtocol.Trace.length] using hpositive

/-- Every decision information event has positive mass under full
support. -/
theorem informationMass_pos_of_fullSupport
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    (i : ι) (site : M.InformationSite i) :
    0 < M.informationMass strategy i site := by
  obtain ⟨history, _, _⟩ := site.2
  apply (M.informationMass_pos_iff strategy i site).2
  exact ⟨history,
    M.historyReachWeight_pos_of_fullSupport strategy hfull history.1⟩

/-- The canonical Bayes assessment of a fully supported strategy. -/
def bayesAssessment
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    (hantichain : M.DecisionInformationAntichain) :
    M.BehavioralAssessment where
  strategy := strategy
  belief i site := M.bayesBelief strategy i site (hantichain i site)
    (M.informationMass_pos_of_fullSupport strategy hfull i site)

@[simp] theorem bayesAssessment_strategy
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    (hantichain : M.DecisionInformationAntichain) :
    (M.bayesAssessment strategy hfull hantichain).strategy = strategy := rfl

theorem bayesAssessment_isBayesConsistent
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (hfull : ∀ i (site : M.InformationSite i)
      (choice : M.Choice i site.1), choice ∈ (strategy i site.1).support)
    (hantichain : M.DecisionInformationAntichain) :
    BehavioralAssessment.IsBayesConsistent M
      (M.bayesAssessment strategy hfull hantichain) hantichain := by
  intro i site _hmass history
  exact M.bayesBelief_apply strategy i site (hantichain i site)
    (M.informationMass_pos_of_fullSupport strategy hfull i site) history

end GameTheory.Protocol.InformationModel
