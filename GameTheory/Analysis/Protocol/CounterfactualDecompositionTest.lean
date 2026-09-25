/-
# Hostile across-information-set decomposition probe

The incumbent chooses `false,false`; the alternative chooses `true,true`.
Changing either baseline-reached decision alone is harmless, but the whole
policy gains one.  A correct counterfactual decomposition must recover that
gain at the off-path second-after-true information site.
-/

import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualDecompositionTest

open GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest
open GameTheory.Tests.SubgameOneShot

local instance : Fintype
    (information.InformationHistory () firstSite.1) :=
  Fintype.ofEquiv Bool firstHistoryEquivBool.symm

def incumbentBehavioralPolicy : information.BehavioralPolicy () :=
  (prescribedPolicy false false).toBehavioral

def incumbentBehavioralStrategy (_who : Unit) :
    information.BehavioralPolicy () :=
  incumbentBehavioralPolicy

def alternativeBehavioralPolicy : information.BehavioralPolicy () :=
  (prescribedPolicy true true).toBehavioral

def alternativeBehavioralStrategy (_who : Unit) :
    information.BehavioralPolicy () :=
  alternativeBehavioralPolicy

/-- The bounded terminal payoff integrates under every continuation law. -/
theorem continuationIntegrable
    (strategy : (who : Unit) → information.BehavioralPolicy who)
    (alternative : information.BehavioralPolicy ())
    (fuel : ℕ) (history : twoStage.History) :
    PayoffIntegrable
      (information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          strategy () alternative) fuel history) terminalPayoff :=
  terminalPayoff_integrable _

/-- Every counterfactual continuation used by this bounded fixture is integrable. -/
theorem counterfactualIntegrable
    (strategy : (who : Unit) → information.BehavioralPolicy who)
    (site : information.InformationSite ())
    (alternative : information.BehavioralPolicy ()) (fuel : ℕ) :
    information.CounterfactualContinuationIntegrable strategy () site
      alternative terminalPayoff fuel := by
  intro history _
  exact continuationIntegrable strategy alternative fuel history.1

/-- Counterfactual reach of either first-decision history is exactly nature's
fair-coin mass; the focal player's policy is omitted. -/
theorem counterfactualReach_first (hidden : Bool) :
    information.counterfactualReachProbability incumbentBehavioralStrategy ()
      (firstHistory hidden).trace = 1 / 2 := by
  rw [firstHistory, InformationModel.counterfactualReachProbability]
  simp only [InformationModel.counterfactualReachProbability_start, one_mul]
  unfold InformationModel.counterfactualStepProb
    InformationModel.opponentsStepProb
  simp only [Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty]
  rw [pmf_map_apply_of_injective natureLaw
    (fun _ _ h => State.first.inj h) hidden]
  cases hidden <;>
    norm_num [InformationModel.counterfactualStepProb,
      InformationModel.opponentsStepProb, twoStage, natureLaw,
      mix_apply, PMF.pure_apply]

/-- The second decision site after a specified first action. -/
@[reducible]
def secondSite (firstAction : Bool) : information.InformationSite () :=
  ⟨secondKnowledge firstAction,
    ⟨⟨secondHistory false firstAction,
        infoOf_secondHistory false firstAction⟩,
      second_not_terminal false firstAction, false, by
        simp [GameTheory.Tests.SubgameOneShot.menu,
          GameTheory.Tests.SubgameOneShot.stageMenu, secondKnowledge]⟩⟩

def secondInformationHistory (firstAction hidden : Bool) :
    information.InformationHistory () (secondSite firstAction).1 :=
  ⟨secondHistory hidden firstAction,
    infoOf_secondHistory hidden firstAction⟩

def secondHistoryEquivBool (firstAction : Bool) :
    information.InformationHistory () (secondSite firstAction).1 ≃ Bool where
  toFun history :=
    match history.1.state with
    | .second hidden _ => hidden
    | _ => false
  invFun := secondInformationHistory firstAction
  left_inv history := by
    rcases history with ⟨history, hinfo⟩
    rcases history with ⟨state, trace⟩
    have hstage := knowledge_stage trace
    rw [hinfo] at hstage
    cases state with
    | root => simp [secondKnowledge, State.stage] at hstage
    | first hidden => simp [secondKnowledge, State.stage] at hstage
    | second hidden actualFirst =>
        have hcanonical :
            ({state := .second hidden actualFirst, trace := trace} :
              twoStage.History) = secondHistory hidden actualFirst :=
          history_eq_of_state_eq rfl
        have hinfo' := hinfo
        rw [hcanonical, infoOf_secondHistory] at hinfo'
        have hfirst : actualFirst = firstAction := by
          simpa [secondKnowledge] using congrArg List.head? (congrArg Prod.snd hinfo')
        subst actualFirst
        apply Subtype.ext
        exact history_eq_of_state_eq rfl
    | done hidden firstAction secondAction =>
        simp [secondKnowledge, State.stage] at hstage
  right_inv hidden := by
    simp [secondInformationHistory, secondHistory]

local instance (firstAction : Bool) : Fintype
    (information.InformationHistory () (secondSite firstAction).1) :=
  Fintype.ofEquiv Bool (secondHistoryEquivBool firstAction).symm

def secondChoice (firstAction action : Bool) :
    information.Choice () (secondSite firstAction).1 :=
  ⟨some action, by
    simp [GameTheory.Tests.SubgameOneShot.menu,
      GameTheory.Tests.SubgameOneShot.stageMenu, secondKnowledge]⟩

theorem expect_commit_of_info_eq
    (policy : information.BehavioralPolicy ())
    (info : Knowledge) (choice : information.Choice () info)
    {current : Knowledge} (hinfo : current = info)
    (observable : Option Bool → ℝ) :
    expect (policy.commit info choice current)
        (fun selected => observable selected.1)
        (payoffIntegrable_of_finite _ _) = observable choice.1 := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_self (M := information),
    expect_pure]

theorem commit_eq_pure_of_info_eq
    (policy : information.BehavioralPolicy ())
    (info : Knowledge) (choice : information.Choice () info)
    {current : Knowledge} (hinfo : current = info)
    (currentChoice : information.Choice () current)
    (hchoice : currentChoice.1 = choice.1) :
    policy.commit info choice current = PMF.pure currentChoice := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_self (M := information)]
  exact congrArg PMF.pure (Subtype.ext hchoice.symm)

def firstChoiceAtHistory (hidden action : Bool) :
    information.Choice ()
      (information.infoOf () (firstHistory hidden).trace) :=
  ⟨some action, (information.menu_adequate ()
    (firstHistory hidden).trace (some action)).mpr ⟨first_active hidden,
      Set.mem_univ action⟩⟩

theorem commit_of_ne_eq_pure_of_info_eq
    (policy : information.BehavioralPolicy ())
    (installed : Knowledge) (choice : information.Choice () installed)
    (target : Knowledge) (targetChoice : information.Choice () target)
    (hne : target ≠ installed)
    (hpolicy : policy target = PMF.pure targetChoice)
    {current : Knowledge} (hcurrent : current = target)
    (currentChoice : information.Choice () current)
    (hchoice : currentChoice.1 = targetChoice.1) :
    policy.commit installed choice current = PMF.pure currentChoice := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_of_ne
    (M := information) _ _ _ hne, hpolicy]
  exact congrArg PMF.pure (Subtype.ext hchoice.symm)

def secondChoiceAtHistory (hidden firstAction action : Bool) :
    information.Choice ()
      (information.infoOf () (secondHistory hidden firstAction).trace) :=
  ⟨some action, (information.menu_adequate ()
    (secondHistory hidden firstAction).trace (some action)).mpr
      ⟨second_active hidden firstAction, Set.mem_univ action⟩⟩

theorem secondSite_allNonterminal (firstAction : Bool) :
    InformationSite.AllNonterminal information (secondSite firstAction) := by
  intro history
  rw [← (secondHistoryEquivBool firstAction).symm_apply_apply history]
  exact second_not_terminal _ firstAction

/-- Counterfactual reach at either second-decision history is still the fair
nature mass: the focal first action is excluded from the coefficient. -/
theorem counterfactualReach_second (hidden firstAction : Bool) :
    information.counterfactualReachProbability incumbentBehavioralStrategy ()
      (secondHistory hidden firstAction).trace = 1 / 2 := by
  rw [secondHistory, InformationModel.counterfactualReachProbability,
    counterfactualReach_first]
  unfold InformationModel.counterfactualStepProb
    InformationModel.opponentsStepProb
  simp only [Finset.univ_unique, Finset.erase_singleton,
    Finset.prod_empty, one_mul]
  simp [chosenAction, moveJoint]

/-- The alternative has unit own reach at the first decision. -/
theorem alternativeOwnReach_first (hidden : Bool) :
    information.playerReachProbability alternativeBehavioralStrategy ()
      (firstHistory hidden).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_firstHistory]
  rfl

/-- At the second decision, alternative own reach selects exactly the
`second-after-true` site. The baseline-reached `second-after-false` site gets
weight zero in the whole-deviation decomposition. -/
theorem alternativeOwnReach_second (hidden firstAction : Bool) :
    information.playerReachProbability alternativeBehavioralStrategy ()
      (secondHistory hidden firstAction).trace =
        if firstAction then 1 else 0 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
  rw [show decodeRecord [(Stage.first, firstAction)] =
      [(firstKnowledge, firstAction)] by rfl,
    InformationModel.ownPlayReachProbability]
  have hpolicy :
      alternativeBehavioralPolicy firstKnowledge =
        PMF.pure (firstChoice true) := by rfl
  rw [show alternativeBehavioralStrategy () firstKnowledge =
      PMF.pure (firstChoice true) from hpolicy]
  rw [PMF.pure_map]
  cases firstAction <;>
    simp [PMF.pure_apply, firstChoice,
      InformationModel.ownPlayReachProbability]

set_option backward.isDefEq.respectTransparency false in
/-- A pure second-site commitment reaches the terminal complementarity payoff
in one step. -/
theorem behavioralContinuation_second_committed
    (hidden firstAction action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit (secondSite firstAction).1
          (secondChoice firstAction action))
        terminalPayoff 1 (secondHistory hidden firstAction)
        (continuationIntegrable incumbentBehavioralStrategy
          (incumbentBehavioralPolicy.commit (secondSite firstAction).1
            (secondChoice firstAction action)) 1
          (secondHistory hidden firstAction)) =
      if firstAction && action then 1 else 0 := by
  have hLaw :
      information.runBehavioralFrom
          (Profile.update (sig := information.behavioralSignature)
            incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit (secondSite firstAction).1
              (secondChoice firstAction action)))
          1 (secondHistory hidden firstAction) =
        PMF.pure (terminalHistory hidden firstAction action) := by
    rw [information.runBehavioralFrom_succ_of_not_terminal
      (h := secondHistory hidden firstAction) _ 0
      (second_not_terminal hidden firstAction)]
    rw [information.behavioralJoint_eq_map_of_at_most_one_active _
      (secondHistory hidden firstAction).trace
      (second_not_terminal hidden firstAction) () (by
        intro who _hactive
        exact Subsingleton.elim who ())]
    have hchoiceLaw :
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit (secondSite firstAction).1
            (secondChoice firstAction action))) ()
          (information.infoOf () (secondHistory hidden firstAction).trace) =
        PMF.pure (secondChoiceAtHistory hidden firstAction action) := by
      rw [Profile.update_same]
      exact commit_eq_pure_of_info_eq incumbentBehavioralPolicy
        (secondSite firstAction).1 (secondChoice firstAction action)
        (infoOf_secondHistory hidden firstAction)
        (secondChoiceAtHistory hidden firstAction action) rfl
    simp only [hchoiceLaw, PMF.pure_map, PMF.pure_bind]
    simp [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor, twoStage,
      terminalHistory, secondHistory, chosenAction,
      ExecutionProtocol.History.extend, secondChoiceAtHistory,
      ExecutionProtocol.singletonJoint]
    congr 3
  unfold InformationModel.behavioralContinuationValue
  rw [expect_congr_law hLaw terminalPayoff _ (terminalPayoff_integrable _)]
  rw [expect_pure]
  cases firstAction <;> cases action <;>
    simp [terminalPayoff, utility]

/-- Counterfactual pure-action utility at a second site is the same
complementarity payoff on both hidden branches; their two half-masses sum to
one. -/
theorem counterfactualActionUtility_second
    (firstAction action : Bool) :
    information.counterfactualActionUtility incumbentBehavioralStrategy ()
        (secondSite firstAction) terminalPayoff 1
        (secondChoice firstAction action)
        (counterfactualIntegrable incumbentBehavioralStrategy
          (secondSite firstAction)
          (incumbentBehavioralPolicy.commit (secondSite firstAction).1
            (secondChoice firstAction action)) 1) =
      if firstAction && action then 1 else 0 := by
  unfold InformationModel.counterfactualActionUtility
    InformationModel.counterfactualContinuationValue
  let value (history : information.InformationHistory ()
      (secondSite firstAction).1) : ℝ :=
    if hreach : information.counterfactualReachProbability
        incumbentBehavioralStrategy () history.1.trace ≠ 0 then
      information.counterfactualReachProbability
          incumbentBehavioralStrategy () history.1.trace *
        information.behavioralContinuationValue
          incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit (secondSite firstAction).1
            (secondChoice firstAction action)) terminalPayoff 1 history.1
          (continuationIntegrable incumbentBehavioralStrategy
            (incumbentBehavioralPolicy.commit (secondSite firstAction).1
              (secondChoice firstAction action)) 1 history.1)
    else 0
  calc
    _ = ∑ history : information.InformationHistory ()
        (secondSite firstAction).1, value history := rfl
    _ = ∑ hidden : Bool,
        value (secondInformationHistory firstAction hidden) := by
      exact Fintype.sum_equiv (secondHistoryEquivBool firstAction)
        value (fun hidden => value (secondInformationHistory firstAction hidden))
        (fun history => by
          have hinverse :=
            (secondHistoryEquivBool firstAction).symm_apply_apply history
          exact congrArg value hinverse.symm)
    _ = ∑ _hidden : Bool, (1 / 2 : ℝ) *
          (if firstAction && action then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro hidden _
      simp only [value, secondInformationHistory]
      rw [dite_eq_left (by rw [counterfactualReach_second]; norm_num)]
      rw [counterfactualReach_second,
        behavioralContinuation_second_committed]
    _ = _ := by
      rw [Fintype.univ_bool]
      cases firstAction <;> cases action <;> norm_num

theorem incumbentBehavioralPolicy_secondSite (firstAction : Bool) :
    incumbentBehavioralPolicy (secondSite firstAction).1 =
      PMF.pure (secondChoice firstAction false) := by
  rfl

/-- The off-path `second-after-true` site carries the entire unit local regret
of changing its action to true. -/
theorem offPathSecond_counterfactualActionRegret :
    information.counterfactualActionRegret incumbentBehavioralStrategy ()
      (secondSite true) terminalPayoff 1 (secondChoice true true)
      (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
        (incumbentBehavioralPolicy.commit (secondSite true).1
          (secondChoice true true)) 1)
      (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
        incumbentBehavioralPolicy 1) = 1 := by
  obtain ⟨_, hregret⟩ := information.counterfactualActionRegret_eq_sub_expect
    information_actsOnce incumbentBehavioralStrategy () (secondSite true)
      (secondSite_allNonterminal true) terminalPayoff 0
      (secondChoice true true)
      (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
        (incumbentBehavioralPolicy.commit (secondSite true).1
          (secondChoice true true)) 1)
      (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
        incumbentBehavioralPolicy 1)
      (fun other _ => counterfactualIntegrable incumbentBehavioralStrategy
        (secondSite true)
        (incumbentBehavioralPolicy.commit (secondSite true).1 other) 1)
  rw [hregret, counterfactualActionUtility_second]
  simp only [incumbentBehavioralStrategy]
  simp only [show incumbentBehavioralPolicy (secondKnowledge true) =
    PMF.pure (secondChoice true false) by rfl]
  rw [expect_pure]
  simp [extendFromSupport, counterfactualActionUtility_second]

theorem incumbentFirstCommit_secondLaw
    (hidden firstAction action : Bool) :
    incumbentBehavioralPolicy.commit firstKnowledge (firstChoice action)
        (information.infoOf ()
          (secondHistory hidden firstAction).trace) =
      PMF.pure (secondChoiceAtHistory hidden firstAction false) := by
  exact commit_of_ne_eq_pure_of_info_eq incumbentBehavioralPolicy
    firstKnowledge (firstChoice action) (secondSite firstAction).1
    (secondChoice firstAction false) (by
      simp [firstKnowledge, secondKnowledge])
    (incumbentBehavioralPolicy_secondSite firstAction)
    (infoOf_secondHistory hidden firstAction)
    (secondChoiceAtHistory hidden firstAction false) rfl

set_option backward.isDefEq.respectTransparency false in
/-- Once the first commitment has selected a branch, the incumbent still plays
`false` at the second site, so the remaining one-step payoff is zero. -/
theorem behavioralContinuation_firstCommit_at_second
    (hidden firstAction action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
        terminalPayoff 1 (secondHistory hidden firstAction)
        (continuationIntegrable incumbentBehavioralStrategy
          (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
          1 (secondHistory hidden firstAction)) = 0 := by
  have hLaw :
      information.runBehavioralFrom
          (Profile.update (sig := information.behavioralSignature)
            incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice action)))
          1 (secondHistory hidden firstAction) =
        PMF.pure (terminalHistory hidden firstAction false) := by
    rw [information.runBehavioralFrom_succ_of_not_terminal
      (h := secondHistory hidden firstAction) _ 0
      (second_not_terminal hidden firstAction)]
    rw [information.behavioralJoint_eq_map_of_at_most_one_active _
      (secondHistory hidden firstAction).trace
      (second_not_terminal hidden firstAction) () (by
        intro who _hactive
        exact Subsingleton.elim who ())]
    have hchoiceLaw :
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit firstSite.1
            (firstChoice action))) ()
          (information.infoOf () (secondHistory hidden firstAction).trace) =
        PMF.pure (secondChoiceAtHistory hidden firstAction false) := by
      rw [Profile.update_same]
      exact incumbentFirstCommit_secondLaw hidden firstAction action
    simp only [hchoiceLaw, PMF.pure_map, PMF.pure_bind]
    simp [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor, twoStage,
      terminalHistory, secondHistory, chosenAction,
      ExecutionProtocol.History.extend, secondChoiceAtHistory,
      ExecutionProtocol.singletonJoint]
    congr 3
  unfold InformationModel.behavioralContinuationValue
  rw [expect_congr_law hLaw terminalPayoff _ (terminalPayoff_integrable _)]
  rw [expect_pure]
  simp [terminalPayoff, utility]

theorem firstCommit_second_run_eq_pure
    (hidden firstAction action : Bool) :
    information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit firstSite.1
            (firstChoice action)))
        1 (secondHistory hidden firstAction) =
      PMF.pure (terminalHistory hidden firstAction false) := by
  rw [information.runBehavioralFrom_succ_of_not_terminal
    (h := secondHistory hidden firstAction) _ 0
    (second_not_terminal hidden firstAction)]
  rw [information.behavioralJoint_eq_map_of_at_most_one_active _
    (secondHistory hidden firstAction).trace
    (second_not_terminal hidden firstAction) () (by
      intro who _hactive
      exact Subsingleton.elim who ())]
  have hchoiceLaw :
      (Profile.update (sig := information.behavioralSignature)
        incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit firstSite.1
          (firstChoice action))) ()
        (information.infoOf () (secondHistory hidden firstAction).trace) =
      PMF.pure (secondChoiceAtHistory hidden firstAction false) := by
    rw [Profile.update_same]
    exact incumbentFirstCommit_secondLaw hidden firstAction action
  simp only [hchoiceLaw, PMF.pure_map, PMF.pure_bind]
  simp [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor, twoStage,
    terminalHistory, secondHistory, chosenAction,
    ExecutionProtocol.History.extend, secondChoiceAtHistory,
    ExecutionProtocol.singletonJoint]
  congr 3

/-- Changing only the first action leaves the incumbent's downstream second
action false, so its two-step continuation payoff remains zero. -/
theorem behavioralContinuation_first_committed
    (hidden action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
        terminalPayoff 2 (firstHistory hidden)
        (continuationIntegrable incumbentBehavioralStrategy
          (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
          2 (firstHistory hidden)) = 0 := by
  have hLaw :
      information.runBehavioralFrom
          (Profile.update (sig := information.behavioralSignature)
            incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice action)))
          2 (firstHistory hidden) =
        PMF.pure (terminalHistory hidden action false) := by
    rw [information.runBehavioralFrom_succ_of_not_terminal
      (h := firstHistory hidden) _ 1 (first_not_terminal hidden)]
    rw [information.behavioralJoint_eq_map_of_at_most_one_active _
      (firstHistory hidden).trace (first_not_terminal hidden) () (by
        intro who _hactive
        exact Subsingleton.elim who ())]
    have hchoiceLaw :
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit firstSite.1
            (firstChoice action))) ()
          (information.infoOf () (firstHistory hidden).trace) =
        PMF.pure (firstChoiceAtHistory hidden action) := by
      rw [Profile.update_same]
      exact commit_eq_pure_of_info_eq incumbentBehavioralPolicy
        firstKnowledge (firstChoice action)
        (infoOf_firstHistory hidden)
        (firstChoiceAtHistory hidden action) rfl
    simp only [hchoiceLaw, PMF.pure_map, PMF.pure_bind,
      PMF.pure_bindOnSupport]
    rw [← firstCommit_second_run_eq_pure hidden action action]
    congr 1
  unfold InformationModel.behavioralContinuationValue
  rw [expect_congr_law hLaw terminalPayoff _ (terminalPayoff_integrable _)]
  rw [expect_pure]
  simp [terminalPayoff, utility]

/-- A first-site action has zero counterfactual utility against the incumbent's
unchanged downstream action. Both hidden branches contribute zero. -/
theorem counterfactualActionUtility_first (action : Bool) :
    information.counterfactualActionUtility incumbentBehavioralStrategy ()
        firstSite terminalPayoff 2 (firstChoice action)
        (counterfactualIntegrable incumbentBehavioralStrategy firstSite
          (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action)) 2) = 0 := by
  unfold InformationModel.counterfactualActionUtility
    InformationModel.counterfactualContinuationValue
  let value (history : information.InformationHistory () firstSite.1) : ℝ :=
    if hreach : information.counterfactualReachProbability
        incumbentBehavioralStrategy () history.1.trace ≠ 0 then
      information.counterfactualReachProbability
          incumbentBehavioralStrategy () history.1.trace *
        information.behavioralContinuationValue incumbentBehavioralStrategy ()
          (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
          terminalPayoff 2 history.1
          (continuationIntegrable incumbentBehavioralStrategy
            (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
            2 history.1)
    else 0
  calc
    _ = ∑ history : information.InformationHistory () firstSite.1,
        value history := rfl
    _ = ∑ hidden : Bool, value (firstInformationHistory hidden) := by
      exact Fintype.sum_equiv firstHistoryEquivBool
        value (fun hidden => value (firstInformationHistory hidden))
        (fun history => by
          have hinverse := firstHistoryEquivBool.symm_apply_apply history
          exact congrArg value hinverse.symm)
    _ = ∑ _hidden : Bool, (1 / 2 : ℝ) * 0 := by
      apply Finset.sum_congr rfl
      intro hidden _
      simp only [value, firstInformationHistory]
      rw [dite_eq_left (by rw [counterfactualReach_first]; norm_num)]
      rw [counterfactualReach_first,
        behavioralContinuation_first_committed]
    _ = 0 := by rw [Fintype.univ_bool]; norm_num

theorem incumbentBehavioralPolicy_firstSite :
    incumbentBehavioralPolicy firstSite.1 =
      PMF.pure (firstChoice false) := by
  rfl

/-- The first action contributes no local regret: its benefit appears only
when the alternative also changes the downstream off-path site. -/
theorem first_counterfactualActionRegret :
    information.counterfactualActionRegret incumbentBehavioralStrategy ()
      firstSite terminalPayoff 2 (firstChoice true)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) 2)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        incumbentBehavioralPolicy 2) = 0 := by
  obtain ⟨_, hregret⟩ := information.counterfactualActionRegret_eq_sub_expect
    information_actsOnce incumbentBehavioralStrategy () firstSite
      firstSite_allNonterminal terminalPayoff 1
      (firstChoice true)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) 2)
      (counterfactualIntegrable incumbentBehavioralStrategy firstSite
        incumbentBehavioralPolicy 2)
      (fun other _ => counterfactualIntegrable incumbentBehavioralStrategy
        firstSite (incumbentBehavioralPolicy.commit firstSite.1 other) 2)
  rw [hregret, counterfactualActionUtility_first]
  simp only [incumbentBehavioralStrategy]
  simp only [show incumbentBehavioralPolicy firstKnowledge =
    PMF.pure (firstChoice false) by rfl]
  rw [expect_pure]
  simp [extendFromSupport, counterfactualActionUtility_first]

/-- The exact hostile identity: alternative own reach selects the off-path
second site, whose local counterfactual regret recovers the whole unit gain. -/
theorem hostile_exact_decomposition :
    continuationValue (profileOf jointAlternative) twoStage.initHistory -
        continuationValue incumbent twoStage.initHistory =
      information.playerReachProbability alternativeBehavioralStrategy ()
          (firstHistory false).trace *
        information.counterfactualActionRegret
          incumbentBehavioralStrategy () firstSite terminalPayoff 2
            (firstChoice true)
            (counterfactualIntegrable incumbentBehavioralStrategy firstSite
              (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) 2)
            (counterfactualIntegrable incumbentBehavioralStrategy firstSite
              incumbentBehavioralPolicy 2) +
      information.playerReachProbability alternativeBehavioralStrategy ()
          (secondHistory false true).trace *
        information.counterfactualActionRegret incumbentBehavioralStrategy ()
          (secondSite true) terminalPayoff 1 (secondChoice true true)
          (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
            (incumbentBehavioralPolicy.commit (secondSite true).1
              (secondChoice true true)) 1)
          (counterfactualIntegrable incumbentBehavioralStrategy (secondSite true)
            incumbentBehavioralPolicy 1) := by
  rw [jointAlternative_value, incumbent_value,
    alternativeOwnReach_first, first_counterfactualActionRegret,
    alternativeOwnReach_second, offPathSecond_counterfactualActionRegret]
  norm_num

/-- Baseline reach would put zero weight on the decisive off-path site, so it
cannot replace alternative own reach in a whole-deviation decomposition. -/
theorem baselineReach_misses_decisive_site :
    information.playerReachProbability incumbentBehavioralStrategy ()
        (secondHistory false true).trace = 0 ∧
      information.playerReachProbability alternativeBehavioralStrategy ()
        (secondHistory false true).trace = 1 := by
  constructor
  · rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
      ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
    rw [show decodeRecord [(Stage.first, true)] =
        [(firstKnowledge, true)] by rfl,
      InformationModel.ownPlayReachProbability]
    have hpolicy : incumbentBehavioralPolicy firstKnowledge =
        PMF.pure (firstChoice false) := by rfl
    rw [show incumbentBehavioralStrategy () firstKnowledge =
      PMF.pure (firstChoice false) from hpolicy]
    rw [PMF.pure_map]
    simp [PMF.pure_apply, firstChoice,
      InformationModel.ownPlayReachProbability]
  · exact alternativeOwnReach_second false true

theorem firstSite_commonDepth :
    InformationSite.CommonDepth information firstSite 1 := by
  intro history
  calc
    history.1.trace.length =
        (firstInformationHistory
          (firstHistoryEquivBool history)).1.trace.length := by
      exact congrArg
        (fun current : information.InformationHistory () firstSite.1 =>
          current.1.trace.length)
        (firstHistoryEquivBool.symm_apply_apply history).symm
    _ = 1 := by rfl

theorem secondSite_commonDepth (firstAction : Bool) :
    InformationSite.CommonDepth information (secondSite firstAction) 2 := by
  intro history
  calc
    history.1.trace.length =
        (secondInformationHistory firstAction
          (secondHistoryEquivBool firstAction history)).1.trace.length := by
      exact congrArg
        (fun current : information.InformationHistory ()
            (secondSite firstAction).1 => current.1.trace.length)
        ((secondHistoryEquivBool firstAction).symm_apply_apply history).symm
    _ = 2 := by rfl

theorem firstCommit_prefix_eq :
    information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          incumbentBehavioralStrategy ()
            (incumbentBehavioralPolicy.commit firstSite.1
              (firstChoice true))) 1 =
      information.runBehavioral incumbentBehavioralStrategy 1 := by
  exact information.runBehavioral_prefix_eq_of_agree_off_site
    incumbentBehavioralStrategy () firstSite
      (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)) 1
      firstSite_commonDepth (fun hne =>
        InformationModel.BehavioralPolicy.commit_of_ne
          incumbentBehavioralPolicy firstSite.1 (firstChoice true) hne)

def firstCommittedPolicy : information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.commit firstSite.1 (firstChoice true)

def firstCommittedStrategy (_who : Unit) :
    information.BehavioralPolicy () :=
  firstCommittedPolicy

theorem secondCommit_prefix_eq :
    information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 2 =
      information.runBehavioral firstCommittedStrategy 2 := by
  exact information.runBehavioral_prefix_eq_of_agree_off_site
    firstCommittedStrategy () (secondSite true)
      (firstCommittedPolicy.commit (secondSite true).1
        (secondChoice true true)) 2
      (secondSite_commonDepth true) (fun hne =>
        InformationModel.BehavioralPolicy.commit_of_ne firstCommittedPolicy
          (secondSite true).1 (secondChoice true true) hne)

def secondCommitCutGain (history : twoStage.History) : ℝ :=
  expect
      (information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 1 history)
      terminalPayoff (terminalPayoff_integrable _) -
    expect (information.runBehavioralFrom firstCommittedStrategy 1 history)
      terminalPayoff (terminalPayoff_integrable _)

theorem secondCommitCutGain_bound (history : twoStage.History) :
    |secondCommitCutGain history| ≤ 2 := by
  have hbound : ∀ current : twoStage.History,
      |terminalPayoff current| ≤ 1 := by
    intro current
    exact utility_bound current
  let first : ℝ := expect
    (information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        firstCommittedStrategy ()
          (firstCommittedPolicy.commit (secondSite true).1
            (secondChoice true true))) 1 history)
    terminalPayoff (terminalPayoff_integrable _)
  let second : ℝ := expect
    (information.runBehavioralFrom firstCommittedStrategy 1 history)
    terminalPayoff (terminalPayoff_integrable _)
  have hfirst : |first| ≤ 1 :=
    expect_abs_le_of_bounded (by norm_num : (0 : ℝ) ≤ 1)
      hbound (terminalPayoff_integrable _)
  have hsecond : |second| ≤ 1 :=
    expect_abs_le_of_bounded (by norm_num : (0 : ℝ) ≤ 1)
      hbound (terminalPayoff_integrable _)
  show |first - second| ≤ 2
  calc
    |first - second| ≤ |first| + |second| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le first (-second)
    _ ≤ 1 + 1 := add_le_add hfirst hsecond
    _ = 2 := by norm_num

theorem secondCommitCutGain_integrable :
    PayoffIntegrable (information.runBehavioral firstCommittedStrategy 2)
      secondCommitCutGain :=
  payoffIntegrable_of_bounded _ _ secondCommitCutGain_bound

/-- The generic D48 cut theorem now reaches the decisive off-path update: the
three-step root gain is exactly the expected one-step continuation gain under
the unchanged two-step prefix law. -/
theorem secondCommit_rootGain_eq_cutExpectation :
    expect (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 3) terminalPayoff
      (terminalPayoff_integrable _) -
      expect (information.runBehavioral firstCommittedStrategy 3)
        terminalPayoff (terminalPayoff_integrable _) =
    expect (information.runBehavioral firstCommittedStrategy 2)
      secondCommitCutGain secondCommitCutGain_integrable := by
  obtain ⟨gain, hgain, hpoint, heq⟩ :=
    information.rootGain_eq_prefixExpectation
      (Profile.update (sig := information.behavioralSignature)
        firstCommittedStrategy ()
          (firstCommittedPolicy.commit (secondSite true).1
            (secondChoice true true)))
      firstCommittedStrategy terminalPayoff 2 1 secondCommit_prefix_eq
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
  rw [heq]
  apply expect_congr_on_support _ hgain secondCommitCutGain_integrable
  intro history hhistory
  obtain ⟨hfirst, hsecond, hvalue⟩ := hpoint history hhistory
  rw [hvalue]
  rfl

end GameTheory.Analysis.Protocol.CounterfactualDecompositionTest
