/-
# Sequential rationality and Nash separate at a site of mass zero

The incumbent exits at the root and would punish at the decision. Read as a
behavioral assessment with the only possible beliefs, it is Bayes consistent
and the game has decision recall. Exiting is behavioral Nash for the
exit-preferring utility, but punishing at the decision site is not
sequentially rational, and that site has mass zero. So the zero-mass term of
the gap between sequential rationality and Nash is not vacuous.
-/

import GameTheory.Analysis.Protocol.InformationLocalization
import GameTheory.Analysis.Protocol.SubgameLocalizationTest

noncomputable section

namespace GameTheory.Tests.InformationLocalization

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.SubgamePerfect GameTheory.Tests.SubgameLocalization
open InformationModel

/-- The incumbent read as a behavioral assessment. -/
def assessment : model.BehavioralAssessment :=
  BehavioralAssessment.ofStrategy fun who => (incumbentProfile who).toBehavioral

theorem terminal_eq (profile : Profile model.strategicSignature) (history : arena.History) :
    model.runBehavioralTerminalFrom arena_wellFoundedHistories
        (fun who => (profile who).toBehavioral) history =
      arena.historyBackwardLaw arena_wellFoundedHistories (model.historyChooser profile) history :=
  model.runBehavioralTerminalFrom_toBehavioral _ _ _

theorem expect_observe (law : PMF arena.History) :
    expect (law.map observe) (utility · ()) = expect law fun history => payoff history () := by
  rw [expect_map]
  exact congrArg _ utility_observe

theorem expect_le_two (law : PMF arena.History) :
    expect law (fun history => payoff history ()) ≤ 2 :=
  calc
    _ ≤ expect law (fun _ => 2) := expect_mono (fun history _ => payoff_le_two history)
      (payoff_integrable _) (payoffIntegrable_constant _ _)
    _ = 2 := expect_constant _ _

/-- Exiting is behavioral Nash for the exit-preferring utility. -/
theorem root_holds (who : Unit) (deviation : model.BehavioralPolicy who) :
    (model.behavioralRootComparison arena_wellFoundedHistories observe assessment.strategy who
      deviation).Holds (utility · who) := by
  cases who
  rw [IncentiveComparison.holds_iff]
  change expect ((model.runBehavioralTerminalFrom arena_wellFoundedHistories _ _).map observe) _ ≤
    expect ((model.runBehavioralTerminalFrom arena_wellFoundedHistories
      (fun who => (incumbentProfile who).toBehavioral) arena.initHistory).map observe) _
  rw [expect_observe, expect_observe, terminal_eq]
  have hvalue := incumbent_value_root
  unfold ExecutionProtocol.historyBackwardValue at hvalue
  rw [hvalue]
  exact expect_le_two _

/-- The decision information site. -/
def decisionSite : model.InformationSite () :=
  ⟨State.decision, ⟨⟨decisionHistory, signals_infoOf_state decisionTrace⟩, decision_not_terminal,
    .reward, by simp [SubgamePerfect.menu]⟩⟩

theorem eq_decisionHistory_of_mem (history : model.InformationHistory () decisionSite.1) :
    history.1 = decisionHistory :=
  eq_decisionHistory history.1 ((signals_infoOf_state history.1.trace).symm.trans history.2)

theorem belief_decisionSite :
    assessment.belief () decisionSite =
      PMF.pure ⟨decisionHistory, signals_infoOf_state decisionTrace⟩ := by
  change PMF.pure _ = _
  congr 1
  exact Subtype.ext (eq_decisionHistory_of_mem _)

/-- Punishing at the unreached decision is not sequentially rational. -/
theorem decision_fails :
    ¬ (model.assessmentComparison arena_wellFoundedHistories observe assessment ()
      (decisionSite, (rewardingPolicy).toBehavioral)).Holds (utility · ()) := by
  rw [IncentiveComparison.holds_iff]
  simp only [assessmentComparison_prescribed, assessmentComparison_alternative,
    assessmentLaw, assessmentLawWith, belief_decisionSite, PMF.pure_bind]
  have hincumbent : Profile.update (sig := model.behavioralSignature) assessment.strategy ()
      (assessment.strategy ()) = fun who => (incumbentProfile who).toBehavioral :=
    Profile.update_eq_self _ _
  have hrewarding : Profile.update (sig := model.behavioralSignature) assessment.strategy ()
      rewardingPolicy.toBehavioral =
        fun who => ((Profile.update incumbentProfile () rewardingPolicy) who).toBehavioral := by
    funext who
    cases who
    simp
  rw [hincumbent, hrewarding, expect_observe, expect_observe, terminal_eq, terminal_eq]
  have hlow := incumbent_value_decision
  have hhigh := rewarding_value_decision
  unfold ExecutionProtocol.historyBackwardValue at hlow hhigh
  rw [hlow, hhigh]
  norm_num

/-- The decision site has mass zero: the incumbent exits first. -/
theorem decisionSite_mass : model.informationMass assessment.strategy () decisionSite = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun history => ?_
  rw [eq_decisionHistory_of_mem history, historyReachWeight]
  change model.runBehavioralFrom (fun who => (incumbentProfile who).toBehavioral) 1
    arena.initHistory decisionHistory = 0
  rw [runBehavioralFrom_toBehavioral]
  change model.run incumbentProfile 1 decisionHistory = 0
  have hne : decisionHistory ≠ exitedHistory := fun hsame => by
    have hstate := congrArg (fun history : arena.History => history.state) hsame
    simp [decisionHistory, exitedHistory] at hstate
  rw [incumbent_run_one]
  exact PMF.pure_apply_of_ne _ _ hne

/-! ## The assessment satisfies the gap theorem's hypotheses -/

/-- Every decision site is the root or the decision, each reached by one history. -/
theorem site_history_unique (site : model.InformationSite ())
    (first second : model.InformationHistory () site.1) : first.1 = second.1 := by
  obtain ⟨_, _, action, haction⟩ := site.2
  rcases first with ⟨⟨firstState, firstTrace⟩, hfirst⟩
  rcases second with ⟨⟨secondState, secondTrace⟩, hsecond⟩
  have hfirstState : firstState = site.1 := (signals_infoOf_state firstTrace).symm.trans hfirst
  have hsecondState : secondState = site.1 :=
    (signals_infoOf_state secondTrace).symm.trans hsecond
  have hmenu : some action ∈ SubgamePerfect.menu firstState := by
    rw [hfirstState]
    exact haction
  have hsame : secondState = firstState := hsecondState.trans hfirstState.symm
  cases firstState with
  | root =>
      exact (eq_initHistory_of_root firstTrace rfl).trans
        (eq_initHistory_of_root secondTrace hsame).symm
  | decision =>
      exact (eq_decisionHistory ⟨_, firstTrace⟩ rfl).trans
        (eq_decisionHistory ⟨_, secondTrace⟩ hsame).symm
  | exited => simp [SubgamePerfect.menu] at hmenu
  | punished => simp [SubgamePerfect.menu] at hmenu
  | rewarded => simp [SubgamePerfect.menu] at hmenu

theorem decisionRecall : model.DecisionRecall := fun _ site first second => by
  rw [site_history_unique site first second]

theorem bayes :
    BehavioralAssessment.IsBayesConsistent model assessment
      decisionRecall.decisionInformationAntichain := by
  intro who site hmass history
  cases who
  have hsingle (other : model.InformationHistory () site.1) : other = history :=
    Subtype.ext (site_history_unique site other history)
  have hbelief : assessment.belief () site history = 1 := by
    change PMF.pure _ history = 1
    rw [hsingle (Classical.choose site.2)]
    exact PMF.pure_apply_self _
  have hmassEq : model.informationMass assessment.strategy () site =
      model.historyReachWeight assessment.strategy history.1 :=
    tsum_eq_single history fun other hne => absurd (hsingle other) hne
  rw [hbelief, ← hmassEq, ENNReal.div_self hmass.ne'
    (ne_of_lt (lt_of_le_of_lt (model.informationMass_le_one _ () site
      (decisionRecall.decisionInformationAntichain () site)) ENNReal.one_lt_top))]

/-- **Nash does not imply sequential rationality** for this Bayes-consistent
assessment with decision recall; the failing comparison sits at a site of mass
zero, as the gap theorem requires. -/
theorem nash_not_implies_sequentiallyRational :
    ¬ IncentiveComparison.Implies
      (model.behavioralRootComparison arena_wellFoundedHistories observe assessment.strategy)
      (model.assessmentComparison arena_wellFoundedHistories observe assessment) :=
  fun himplies => decision_fails (himplies utility root_holds () _)

end GameTheory.Tests.InformationLocalization
