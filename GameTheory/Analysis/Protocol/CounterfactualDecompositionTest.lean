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

open GameTheory Probability Protocol
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
  rw [FinDist.prob_map_of_injective State.first
    (fun _ _ h => State.first.inj h)]
  cases hidden <;>
    norm_num [InformationModel.counterfactualStepProb,
      InformationModel.opponentsStepProb, twoStage, natureLaw,
      FinDist.prob_pure_eq_ite]

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
    (policy.commit info choice current).expect
        (fun selected => observable selected.1) = observable choice.1 := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_self (M := information),
    FinDist.expect_pure]

theorem commit_eq_pure_of_info_eq
    (policy : information.BehavioralPolicy ())
    (info : Knowledge) (choice : information.Choice () info)
    {current : Knowledge} (hinfo : current = info)
    (currentChoice : information.Choice () current)
    (hchoice : currentChoice.1 = choice.1) :
    policy.commit info choice current = FinDist.pure currentChoice := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_self (M := information)]
  exact congrArg FinDist.pure (Subtype.ext hchoice.symm)

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
    (hpolicy : policy target = FinDist.pure targetChoice)
    {current : Knowledge} (hcurrent : current = target)
    (currentChoice : information.Choice () current)
    (hchoice : currentChoice.1 = targetChoice.1) :
    policy.commit installed choice current = FinDist.pure currentChoice := by
  subst current
  rw [InformationModel.BehavioralPolicy.commit_of_ne
    (M := information) _ _ _ hne, hpolicy]
  exact congrArg FinDist.pure (Subtype.ext hchoice.symm)

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
  simp [firstHistory, twoStage, chosenAction, moveJoint]

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
        FinDist.pure (firstChoice true) := by rfl
  rw [show alternativeBehavioralStrategy () firstKnowledge =
      FinDist.pure (firstChoice true) from hpolicy]
  cases firstAction <;>
    simp [FinDist.prob_pure_eq_ite, firstChoice,
      InformationModel.ownPlayReachProbability]

/-- A pure second-site commitment reaches the terminal complementarity payoff
in one step. -/
theorem behavioralContinuation_second_committed
    (hidden firstAction action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit (secondSite firstAction).1
          (secondChoice firstAction action))
        terminalPayoff 1 (secondHistory hidden firstAction) =
      if firstAction && action then 1 else 0 := by
  unfold InformationModel.behavioralContinuationValue
  rw [information.runBehavioralFrom_succ_of_not_terminal _ 0
    (second_not_terminal hidden firstAction)]
  rw [information.behavioralJoint_eq_map_of_at_most_one_active _
    (secondHistory hidden firstAction).trace
    (second_not_terminal hidden firstAction) () (by
      intro who _hactive
      exact Subsingleton.elim who ())]
  rw [Profile.update_same]
  simp [FinDist.expect_bind, FinDist.expect_pure,
    InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor,
    twoStage, terminalPayoff, utility, secondHistory, secondKnowledge,
    chosenAction]
  have hinfo :
      signals.infoOf ()
          ((firstHistory hidden).trace.extend (moveJoint firstAction)
            (moveJoint_legal_first hidden firstAction)
            (FinDist.mem_support_pure.mpr rfl)) =
        (Stage.second, [(Stage.first, firstAction)]) := by
    simpa [secondHistory, chosenAction, moveJoint] using
      infoOf_secondHistory hidden firstAction
  let currentChoice : information.Choice ()
      (Stage.second, [(Stage.first, firstAction)]) :=
    ⟨some action, by
      simp [GameTheory.Tests.SubgameOneShot.menu,
        GameTheory.Tests.SubgameOneShot.stageMenu]⟩
  have hchoice : secondChoice firstAction action = currentChoice := by
    apply Subtype.ext
    rfl
  rw [hchoice]
  calc
    _ = (match State.done hidden firstAction action with
        | .done _ true true => (1 : ℝ)
        | _ => 0) := by
      convert expect_commit_of_info_eq incumbentBehavioralPolicy
          (Stage.second, [(Stage.first, firstAction)])
          currentChoice
          hinfo (fun selected =>
            match State.done hidden firstAction (selected.getD false) with
            | .done _ true true => (1 : ℝ)
            | _ => 0) using 1 <;> simp [currentChoice]
      congr
    _ = _ := by cases firstAction <;> cases action <;> rfl

/-- Counterfactual pure-action utility at a second site is the same
complementarity payoff on both hidden branches; their two half-masses sum to
one. -/
theorem counterfactualActionUtility_second
    (firstAction action : Bool) :
    information.counterfactualActionUtility incumbentBehavioralStrategy ()
        (secondSite firstAction) terminalPayoff 1
        (secondChoice firstAction action) =
      if firstAction && action then 1 else 0 := by
  unfold InformationModel.counterfactualActionUtility
    InformationModel.counterfactualContinuationValue
  calc
    (∑ history : information.InformationHistory ()
          (secondSite firstAction).1,
        information.counterfactualReachProbability
            incumbentBehavioralStrategy () history.1.trace *
          information.behavioralContinuationValue
            incumbentBehavioralStrategy ()
              (incumbentBehavioralPolicy.commit
                (secondSite firstAction).1
                (secondChoice firstAction action))
              terminalPayoff 1 history.1) =
      ∑ hidden : Bool,
        information.counterfactualReachProbability
            incumbentBehavioralStrategy ()
              (secondHistory hidden firstAction).trace *
          information.behavioralContinuationValue
            incumbentBehavioralStrategy ()
              (incumbentBehavioralPolicy.commit
                (secondSite firstAction).1
                (secondChoice firstAction action))
              terminalPayoff 1 (secondHistory hidden firstAction) := by
        exact Fintype.sum_equiv (secondHistoryEquivBool firstAction)
          (fun history =>
            information.counterfactualReachProbability
                incumbentBehavioralStrategy () history.1.trace *
              information.behavioralContinuationValue
                incumbentBehavioralStrategy ()
                  (incumbentBehavioralPolicy.commit
                    (secondSite firstAction).1
                    (secondChoice firstAction action))
                  terminalPayoff 1 history.1)
          (fun hidden =>
            information.counterfactualReachProbability
                incumbentBehavioralStrategy ()
                  (secondHistory hidden firstAction).trace *
              information.behavioralContinuationValue
                incumbentBehavioralStrategy ()
                  (incumbentBehavioralPolicy.commit
                    (secondSite firstAction).1
                    (secondChoice firstAction action))
                  terminalPayoff 1 (secondHistory hidden firstAction))
          (fun history => by
            have hinverse :=
              (secondHistoryEquivBool firstAction).symm_apply_apply history
            exact congrArg
              (fun current : information.InformationHistory ()
                  (secondSite firstAction).1 =>
                information.counterfactualReachProbability
                    incumbentBehavioralStrategy () current.1.trace *
                  information.behavioralContinuationValue
                    incumbentBehavioralStrategy ()
                      (incumbentBehavioralPolicy.commit
                        (secondSite firstAction).1
                        (secondChoice firstAction action))
                      terminalPayoff 1 current.1)
              hinverse.symm)
    _ = ∑ _hidden : Bool, (1 / 2 : ℝ) *
          (if firstAction && action then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro hidden _
      rw [counterfactualReach_second,
        behavioralContinuation_second_committed]
    _ = _ := by
      rw [Fintype.univ_bool]
      cases firstAction <;> cases action <;> norm_num

theorem incumbentBehavioralPolicy_secondSite (firstAction : Bool) :
    incumbentBehavioralPolicy (secondSite firstAction).1 =
      FinDist.pure (secondChoice firstAction false) := by
  rfl

/-- The off-path `second-after-true` site carries the entire unit local regret
of changing its action to true. -/
theorem offPathSecond_counterfactualActionRegret :
    information.counterfactualActionRegret incumbentBehavioralStrategy ()
      (secondSite true) terminalPayoff 1 (secondChoice true true) = 1 := by
  rw [information.counterfactualActionRegret_eq_sub_expect
    information_actsOnce incumbentBehavioralStrategy () (secondSite true)
      (secondSite_allNonterminal true) terminalPayoff 0,
    counterfactualActionUtility_second,
    show incumbentBehavioralStrategy () = incumbentBehavioralPolicy by rfl,
    incumbentBehavioralPolicy_secondSite, FinDist.expect_pure,
    counterfactualActionUtility_second]
  norm_num

theorem incumbentFirstCommit_secondLaw
    (hidden firstAction action : Bool) :
    incumbentBehavioralPolicy.commit firstKnowledge (firstChoice action)
        (information.infoOf ()
          (secondHistory hidden firstAction).trace) =
      FinDist.pure (secondChoiceAtHistory hidden firstAction false) := by
  exact commit_of_ne_eq_pure_of_info_eq incumbentBehavioralPolicy
    firstKnowledge (firstChoice action) (secondSite firstAction).1
    (secondChoice firstAction false) (by
      simp [firstKnowledge, secondKnowledge])
    (incumbentBehavioralPolicy_secondSite firstAction)
    (infoOf_secondHistory hidden firstAction)
    (secondChoiceAtHistory hidden firstAction false) rfl

/-- Once the first commitment has selected a branch, the incumbent still plays
`false` at the second site, so the remaining one-step payoff is zero. -/
theorem behavioralContinuation_firstCommit_at_second
    (hidden firstAction action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
        terminalPayoff 1 (secondHistory hidden firstAction) = 0 := by
  unfold InformationModel.behavioralContinuationValue
  rw [information.runBehavioralFrom_succ_of_not_terminal _ 0
    (second_not_terminal hidden firstAction)]
  rw [information.behavioralJoint_eq_map_of_at_most_one_active _
    (secondHistory hidden firstAction).trace
    (second_not_terminal hidden firstAction) () (by
      intro who _hactive
      exact Subsingleton.elim who ())]
  rw [Profile.update_same, FinDist.expect_bind, FinDist.expect_map,
    incumbentFirstCommit_secondLaw, FinDist.expect_pure]
  simp [FinDist.expect_pure, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor, twoStage, terminalPayoff, utility,
    secondHistory, secondChoiceAtHistory, chosenAction]

/-- Changing only the first action leaves the incumbent's downstream second
action false, so its two-step continuation payoff remains zero. -/
theorem behavioralContinuation_first_committed
    (hidden action : Bool) :
    information.behavioralContinuationValue incumbentBehavioralStrategy ()
        (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice action))
        terminalPayoff 2 (firstHistory hidden) = 0 := by
  unfold InformationModel.behavioralContinuationValue
  rw [information.runBehavioralFrom_succ_of_not_terminal _ 1
    (first_not_terminal hidden)]
  rw [information.behavioralJoint_eq_map_of_at_most_one_active _
    (firstHistory hidden).trace (first_not_terminal hidden) () (by
      intro who _hactive
      exact Subsingleton.elim who ())]
  rw [Profile.update_same]
  rw [FinDist.expect_bind, FinDist.expect_map]
  rw [commit_eq_pure_of_info_eq incumbentBehavioralPolicy firstKnowledge
      (firstChoice action) (infoOf_firstHistory hidden)
      (firstChoiceAtHistory hidden action) rfl,
    FinDist.expect_pure]
  calc
    _ = ((twoStage.step (firstHistory hidden).state
            ⟨twoStage.singletonJoint ()
              (firstChoiceAtHistory hidden action).1, by
                exact ExecutionProtocol.legal_of_legalOption
                  (first_not_terminal hidden) fun who => by
                    cases who
                    exact ⟨first_active hidden, Set.mem_univ action⟩⟩).bindOnSupport
          fun target realized =>
            information.runBehavioralFrom
              (Profile.update (sig := information.behavioralSignature)
                incumbentBehavioralStrategy ()
                (incumbentBehavioralPolicy.commit firstSite.1
                  (firstChoice action)))
              1 ((firstHistory hidden).extend (by
                exact ExecutionProtocol.legal_of_legalOption
                  (first_not_terminal hidden) fun who => by
                    cases who
                    exact ⟨first_active hidden, Set.mem_univ action⟩)
                realized)).expect (fun _ => 0) := by
      apply FinDist.expect_bindOnSupport_congr
      intro target realized
      have htarget : target = .second hidden action := by
        simpa [twoStage, firstHistory, firstChoiceAtHistory,
          chosenAction] using realized
      subst target
      have hhistory :
          (firstHistory hidden).extend _ realized =
            secondHistory hidden action :=
        history_eq_of_state_eq rfl
      rw [hhistory]
      calc
        _ = 0 :=
          behavioralContinuation_firstCommit_at_second hidden action action
        _ = _ := (FinDist.expect_const _ 0).symm
    _ = 0 := FinDist.expect_const _ 0

/-- A first-site action has zero counterfactual utility against the incumbent's
unchanged downstream action. Both hidden branches contribute zero. -/
theorem counterfactualActionUtility_first (action : Bool) :
    information.counterfactualActionUtility incumbentBehavioralStrategy ()
        firstSite terminalPayoff 2 (firstChoice action) = 0 := by
  unfold InformationModel.counterfactualActionUtility
    InformationModel.counterfactualContinuationValue
  calc
    (∑ history : information.InformationHistory () firstSite.1,
        information.counterfactualReachProbability
            incumbentBehavioralStrategy () history.1.trace *
          information.behavioralContinuationValue
            incumbentBehavioralStrategy ()
              (incumbentBehavioralPolicy.commit firstSite.1
                (firstChoice action))
              terminalPayoff 2 history.1) =
      ∑ hidden : Bool,
        information.counterfactualReachProbability
            incumbentBehavioralStrategy () (firstHistory hidden).trace *
          information.behavioralContinuationValue
            incumbentBehavioralStrategy ()
              (incumbentBehavioralPolicy.commit firstSite.1
                (firstChoice action))
              terminalPayoff 2 (firstHistory hidden) := by
        exact Fintype.sum_equiv firstHistoryEquivBool
          (fun history =>
            information.counterfactualReachProbability
                incumbentBehavioralStrategy () history.1.trace *
              information.behavioralContinuationValue
                incumbentBehavioralStrategy ()
                  (incumbentBehavioralPolicy.commit firstSite.1
                    (firstChoice action))
                  terminalPayoff 2 history.1)
          (fun hidden =>
            information.counterfactualReachProbability
                incumbentBehavioralStrategy () (firstHistory hidden).trace *
              information.behavioralContinuationValue
                incumbentBehavioralStrategy ()
                  (incumbentBehavioralPolicy.commit firstSite.1
                    (firstChoice action))
                  terminalPayoff 2 (firstHistory hidden))
          (fun history => by
            have hinverse := firstHistoryEquivBool.symm_apply_apply history
            exact congrArg
              (fun current : information.InformationHistory () firstSite.1 =>
                information.counterfactualReachProbability
                    incumbentBehavioralStrategy () current.1.trace *
                  information.behavioralContinuationValue
                    incumbentBehavioralStrategy ()
                      (incumbentBehavioralPolicy.commit firstSite.1
                        (firstChoice action))
                      terminalPayoff 2 current.1)
              hinverse.symm)
    _ = ∑ _hidden : Bool, (1 / 2 : ℝ) * 0 := by
      apply Finset.sum_congr rfl
      intro hidden _
      rw [counterfactualReach_first,
        behavioralContinuation_first_committed]
    _ = 0 := by rw [Fintype.univ_bool]; norm_num

theorem incumbentBehavioralPolicy_firstSite :
    incumbentBehavioralPolicy firstSite.1 =
      FinDist.pure (firstChoice false) := by
  rfl

/-- The first action contributes no local regret: its benefit appears only
when the alternative also changes the downstream off-path site. -/
theorem first_counterfactualActionRegret :
    information.counterfactualActionRegret incumbentBehavioralStrategy ()
      firstSite terminalPayoff 2 (firstChoice true) = 0 := by
  rw [information.counterfactualActionRegret_eq_sub_expect
    information_actsOnce incumbentBehavioralStrategy () firstSite
      firstSite_allNonterminal terminalPayoff 1,
    counterfactualActionUtility_first,
    show incumbentBehavioralStrategy () = incumbentBehavioralPolicy by rfl,
    incumbentBehavioralPolicy_firstSite, FinDist.expect_pure,
    counterfactualActionUtility_first]
  norm_num

/-- The exact hostile identity: alternative own reach selects the off-path
second site, whose local counterfactual regret recovers the whole unit gain. -/
theorem hostile_exact_decomposition :
    continuationValue (profileOf jointAlternative) twoStage.initHistory -
        continuationValue incumbent twoStage.initHistory =
      information.playerReachProbability alternativeBehavioralStrategy ()
          (firstHistory false).trace *
        information.counterfactualActionRegret
          incumbentBehavioralStrategy () firstSite terminalPayoff 2
            (firstChoice true) +
      information.playerReachProbability alternativeBehavioralStrategy ()
          (secondHistory false true).trace *
        information.counterfactualActionRegret incumbentBehavioralStrategy ()
          (secondSite true) terminalPayoff 1 (secondChoice true true) := by
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
        FinDist.pure (firstChoice false) := by rfl
    rw [show incumbentBehavioralStrategy () firstKnowledge =
      FinDist.pure (firstChoice false) from hpolicy]
    simp [FinDist.prob_pure_eq_ite, firstChoice,
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

/-- The generic D48 cut theorem now reaches the decisive off-path update: the
three-step root gain is exactly the expected one-step continuation gain under
the unchanged two-step prefix law. -/
theorem secondCommit_rootGain_eq_cutExpectation :
    (information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          firstCommittedStrategy ()
            (firstCommittedPolicy.commit (secondSite true).1
              (secondChoice true true))) 3).expect terminalPayoff -
      (information.runBehavioral firstCommittedStrategy 3).expect
        terminalPayoff =
    (information.runBehavioral firstCommittedStrategy 2).expect
      (fun history =>
        (information.runBehavioralFrom
          (Profile.update (sig := information.behavioralSignature)
            firstCommittedStrategy ()
              (firstCommittedPolicy.commit (secondSite true).1
                (secondChoice true true))) 1 history).expect terminalPayoff -
        (information.runBehavioralFrom firstCommittedStrategy 1 history).expect
          terminalPayoff) := by
  exact information.rootGain_eq_prefixExpectation _ _ terminalPayoff 2 1
    secondCommit_prefix_eq

end GameTheory.Analysis.Protocol.CounterfactualDecompositionTest
