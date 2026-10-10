/-
# Decision plans

A pure plan need only answer at decision sites: information values reached by
some nonterminal history at which the player has a genuine action. Tables
indexed by those sites, pure or behavioral, extend to whole policies through
any fallback, and the extension of a policy's restriction plays exactly like
the policy from every history. With finitely many histories the tables are
finite even when the information carrier is not.
-/

import GameTheory.Protocol.FiniteInformation

noncomputable section

namespace GameTheory.Protocol.InformationModel

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E}

/-- A pure plan records only legal decision sites, retaining each site's menu. -/
abbrev DecisionPlan (who : ι) :=
  (site : M.InformationSite who) → M.Choice who site.1

instance DecisionPlan.finite (who : ι) [Finite E.History]
    [∀ site : M.InformationSite who, Finite (M.Choice who site.1)] :
    Finite (M.DecisionPlan who) := by
  unfold DecisionPlan
  infer_instance

/-- Restrict an existing policy to the decision sites it can encounter. -/
def Policy.restrictToDecisions {who : ι} (policy : M.Policy who) : M.DecisionPlan who :=
  fun site => policy site.1

/-- Two policies agree on every information state where a genuine decision can occur. -/
def Policy.AgreesAtDecisions {who : ι} (first second : M.Policy who) : Prop :=
  first.restrictToDecisions = second.restrictToDecisions

/-- Decision agreement determines the choice at every nonterminal history;
inactive choices are uniquely determined. -/
theorem Policy.AgreesAtDecisions.at_history {who : ι} {first second : M.Policy who}
    (agree : first.AgreesAtDecisions second) (history : E.History)
    (nonterminal : ¬ E.terminal history.state) :
    first (M.infoOf who history.trace) = second (M.infoOf who history.trace) := by
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same]
    exact congrFun agree site
  · have := M.subsingleton_choice_of_not_active history.trace active
    exact Subsingleton.elim _ _

/-- Agreement at decisions preserves the complete pure continuation law. -/
theorem runFrom_eq_of_agreesAtDecisions
    {first second : (who : ι) → M.Policy who}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who))
    (fuel : ℕ) (history : E.History) :
    M.runFrom first fuel history = M.runFrom second fuel history := by
  apply M.runFrom_congr_of_act_eq fuel history
  intro later _ nonterminal who
  exact congrArg Subtype.val ((agree who).at_history later nonterminal)

/-- Extend a finite decision table using a legal fallback at other information
values. The fallback need not agree with the table. -/
def DecisionPlan.extend {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) : M.Policy who := by
  classical
  exact fun info =>
    if available : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info then
      plan ⟨info, available⟩
    else fallback info

@[simp]
theorem DecisionPlan.extend_site {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) (site : M.InformationSite who) :
    plan.extend fallback site.1 = plan site := by
  unfold DecisionPlan.extend
  split
  · rfl
  · rename_i unavailable
    exact absurd site.2 unavailable

@[simp]
theorem DecisionPlan.restrict_extend {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) :
    (plan.extend fallback).restrictToDecisions = plan := by
  funext site
  exact plan.extend_site fallback site

/-- Restriction followed by extension preserves every choice execution can
consult, including the uniquely determined choice of an inactive player. -/
theorem Policy.extend_restrict_at_history {who : ι} (policy fallback : M.Policy who)
    (history : E.History) (nonterminal : ¬ E.terminal history.state) :
    policy.restrictToDecisions.extend fallback (M.infoOf who history.trace) =
      policy (M.infoOf who history.trace) := by
  classical
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same, DecisionPlan.extend_site]
    rfl
  · have := M.subsingleton_choice_of_not_active history.trace active
    exact Subsingleton.elim _ _

/-- Finite decision tables preserve the complete history law from every legal
continuation, independently of the chosen fallback policies. -/
theorem runFrom_extend_restrict (policies fallback : (who : ι) → M.Policy who)
    (fuel : ℕ) (history : E.History) :
    M.runFrom (fun who => (policies who).restrictToDecisions.extend (fallback who))
        fuel history = M.runFrom policies fuel history := by
  apply M.runFrom_congr_of_act_eq fuel history
  intro later _ nonterminal who
  exact congrArg Subtype.val
    ((policies who).extend_restrict_at_history (fallback who) later nonterminal)

/-- Local randomization over the same finite decision table. -/
abbrev BehavioralDecisionPlan (who : ι) :=
  (site : M.InformationSite who) → PMF (M.Choice who site.1)

/-- Restrict an existing behavioral policy to its legal decision sites. -/
def BehavioralPolicy.restrictToDecisions {who : ι} (policy : M.BehavioralPolicy who) :
    M.BehavioralDecisionPlan who := fun site => policy site.1

/-- Two behavioral policies agree on the laws at every genuine decision site. -/
def BehavioralPolicy.AgreesAtDecisions {who : ι}
    (first second : M.BehavioralPolicy who) : Prop :=
  first.restrictToDecisions = second.restrictToDecisions

/-- Behavioral agreement determines every law consulted at a nonterminal history. -/
theorem BehavioralPolicy.AgreesAtDecisions.at_history {who : ι}
    {first second : M.BehavioralPolicy who} (agree : first.AgreesAtDecisions second)
    (history : E.History) (nonterminal : ¬ E.terminal history.state) :
    first (M.infoOf who history.trace) = second (M.infoOf who history.trace) := by
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same]
    exact congrFun agree site
  · exact M.behavioral_eq_of_not_active _ _ history.trace active

/-- Agreement at decisions preserves the complete behavioral continuation law. -/
theorem runBehavioralFrom_eq_of_agreesAtDecisions [Fintype ι]
    {first second : (who : ι) → M.BehavioralPolicy who}
    (agree : ∀ who, (first who).AgreesAtDecisions (second who))
    (fuel : ℕ) (history : E.History) :
    M.runBehavioralFrom first fuel history = M.runBehavioralFrom second fuel history := by
  apply M.runBehavioralFrom_congr fuel history
  intro later _ nonterminal who
  exact (agree who).at_history later nonterminal

/-- Extend a local randomized decision table using a behavioral fallback. -/
def BehavioralDecisionPlan.extend {who : ι} (plan : M.BehavioralDecisionPlan who)
    (fallback : M.BehavioralPolicy who) : M.BehavioralPolicy who := by
  classical
  exact fun info =>
    if available : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info then
      plan ⟨info, available⟩
    else fallback info

@[simp]
theorem BehavioralDecisionPlan.extend_site {who : ι} (plan : M.BehavioralDecisionPlan who)
    (fallback : M.BehavioralPolicy who) (site : M.InformationSite who) :
    plan.extend fallback site.1 = plan site := by
  unfold BehavioralDecisionPlan.extend
  split
  · rfl
  · rename_i unavailable
    exact absurd site.2 unavailable

@[simp]
theorem BehavioralDecisionPlan.restrict_extend {who : ι}
    (plan : M.BehavioralDecisionPlan who) (fallback : M.BehavioralPolicy who) :
    (plan.extend fallback).restrictToDecisions = plan := by
  funext site
  exact plan.extend_site fallback site

/-- Behavioral restriction and extension preserve every law at a nonterminal
legal history; inactivity makes the fallback law unique there. -/
theorem BehavioralPolicy.extend_restrict_at_history {who : ι}
    (policy fallback : M.BehavioralPolicy who)
    (history : E.History) (nonterminal : ¬ E.terminal history.state) :
    policy.restrictToDecisions.extend fallback (M.infoOf who history.trace) =
      policy (M.infoOf who history.trace) := by
  classical
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same, BehavioralDecisionPlan.extend_site]
    rfl
  · exact M.behavioral_eq_of_not_active _ _ history.trace active

/-- Behavioral decision tables preserve every complete continuation law. -/
theorem runBehavioralFrom_extend_restrict [Fintype ι]
    (policies fallback : (who : ι) → M.BehavioralPolicy who)
    (fuel : ℕ) (history : E.History) :
    M.runBehavioralFrom
        (fun who => (policies who).restrictToDecisions.extend (fallback who)) fuel history =
      M.runBehavioralFrom policies fuel history := by
  apply M.runBehavioralFrom_congr fuel history
  intro later _ nonterminal who
  exact (policies who).extend_restrict_at_history (fallback who) later nonterminal

/-- The pure continuation law of a decision plan is independent of its fallback. -/
theorem runFrom_extend_eq (plans : (who : ι) → M.DecisionPlan who)
    (first second : (who : ι) → M.Policy who) (fuel : ℕ) (history : E.History) :
    M.runFrom (fun who => (plans who).extend (first who)) fuel history =
      M.runFrom (fun who => (plans who).extend (second who)) fuel history := by
  apply runFrom_eq_of_agreesAtDecisions
  intro who
  exact ((plans who).restrict_extend (first who)).trans
    ((plans who).restrict_extend (second who)).symm

/-- The behavioral continuation law of a decision plan is independent of its fallback. -/
theorem runBehavioralFrom_extend_eq [Fintype ι]
    (plans : (who : ι) → M.BehavioralDecisionPlan who)
    (first second : (who : ι) → M.BehavioralPolicy who) (fuel : ℕ) (history : E.History) :
    M.runBehavioralFrom (fun who => (plans who).extend (first who)) fuel history =
      M.runBehavioralFrom (fun who => (plans who).extend (second who)) fuel history := by
  apply runBehavioralFrom_eq_of_agreesAtDecisions
  intro who
  exact ((plans who).restrict_extend (first who)).trans
    ((plans who).restrict_extend (second who)).symm

end GameTheory.Protocol.InformationModel
