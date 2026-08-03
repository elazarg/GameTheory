/-
EFG-facing Kuhn integration test.

The underlying protocol is the existing hostile two-vote model: a player moves
twice, and the perfect-recall signal records which decision is being made and
the action already chosen. Thus local and ex-ante randomization agree for a
substantive reason, not because play has only one decision.
-/

import GameTheory.Languages.EFG.Kuhn
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests.EFGKuhn

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Tests.Randomized

/-- No transition in the two-vote protocol returns to the initial state. -/
theorem start_not_mem_step (source : Round)
    (joint : Unit → Option Vote) (isLegal : twice.Legal source joint) :
    Round.start ∉ (twice.step source ⟨joint, isLegal⟩).support := by
  have hstopped := stopped_eq_false_of_legal isLegal
  have hactive : twice.active source () := hstopped
  obtain ⟨vote, hvote⟩ :=
    LegalOption.exists_eq_some_of_active (joint ())
      (ExecutionProtocol.legalOption_of_legal isLegal ()) hactive
  have hjoint : joint = fun _ => some vote := by
    funext who
    cases who
    exact hvote
  subst joint
  rw [step_eq_pure source hstopped vote isLegal, FinDist.mem_support_pure]
  cases source with
  | start => simp [stepTo]
  | after first => simp [stepTo]
  | done first second => simp [Round.stopped] at hstopped

/-- A realized target in the deterministic two-vote protocol determines its
predecessor and legal joint action. -/
theorem step_predecessor_unique
    {target firstSource secondSource : Round}
    {firstJoint secondJoint : Unit → Option Vote}
    (firstLegal : twice.Legal firstSource firstJoint)
    (secondLegal : twice.Legal secondSource secondJoint)
    (firstRealized :
      target ∈ (twice.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (secondRealized :
      target ∈ (twice.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirstStopped := stopped_eq_false_of_legal firstLegal
  have hsecondStopped := stopped_eq_false_of_legal secondLegal
  have hfirstActive : twice.active firstSource () := hfirstStopped
  have hsecondActive : twice.active secondSource () := hsecondStopped
  obtain ⟨firstVote, hfirstVote⟩ :=
    LegalOption.exists_eq_some_of_active (firstJoint ())
      (ExecutionProtocol.legalOption_of_legal firstLegal ()) hfirstActive
  obtain ⟨secondVote, hsecondVote⟩ :=
    LegalOption.exists_eq_some_of_active (secondJoint ())
      (ExecutionProtocol.legalOption_of_legal secondLegal ()) hsecondActive
  have hfirstJoint : firstJoint = fun _ => some firstVote := by
    funext who
    cases who
    exact hfirstVote
  have hsecondJoint : secondJoint = fun _ => some secondVote := by
    funext who
    cases who
    exact hsecondVote
  subst firstJoint
  subst secondJoint
  rw [step_eq_pure firstSource hfirstStopped firstVote firstLegal,
    FinDist.mem_support_pure] at firstRealized
  rw [step_eq_pure secondSource hsecondStopped secondVote secondLegal,
    FinDist.mem_support_pure] at secondRealized
  have htarget :
      stepTo firstSource firstVote = stepTo secondSource secondVote :=
    firstRealized.symm.trans secondRealized
  cases firstSource with
  | start =>
      cases secondSource with
      | start =>
          injection htarget with hvote
          subst secondVote
          exact ⟨rfl, rfl⟩
      | after secondFirst => cases htarget
      | done secondFirst secondSecond =>
          simp [Round.stopped] at hsecondStopped
  | after firstFirst =>
      cases secondSource with
      | start => cases htarget
      | after secondFirst =>
          injection htarget with hfirst hvote
          subst secondFirst
          subst secondVote
          exact ⟨rfl, rfl⟩
      | done secondFirst secondSecond =>
          simp [Round.stopped] at hsecondStopped
  | done firstFirst firstSecond =>
      simp [Round.stopped] at hfirstStopped

theorem twice_treeShaped : twice.IsTreeShaped :=
  ExecutionProtocol.isTreeShaped_of_predecessor_unique start_not_mem_step
    (fun firstLegal secondLegal firstRealized secondRealized =>
      step_predecessor_unique firstLegal secondLegal firstRealized secondRealized)

/-- The two-vote state records the entire action prefix, so its realized
histories form a tree. -/
theorem trace_unique {state : Round} (first second : twice.Trace state) :
    first = second :=
  (twice_treeShaped state).elim first second

/-- The hostile perfect-recall protocol viewed through the transparent EFG
specialization. -/
@[reducible]
def recallGame : Languages.EFG.Game Unit where
  execution := twice
  information := recallModel
  treeShaped := twice_treeShaped
  singleMover := by
    intro state first second _ _
    cases first
    cases second
    rfl

theorem recallGame_actsOnce :
    recallGame.information.ActsOnceWhereItMatters :=
  recallModel.actsOnceWhereItMatters_of_actsOnce
    recall_actsOnceAtEachInfoState

theorem recallGame_perfectRecall :
    recallGame.information.PerfectRecall :=
  recall_perfectRecall

end GameTheory.Tests.EFGKuhn

namespace GameTheory.Tests.EFGKuhn

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Probability

/-- The EFG wrapper exposes the constructive behavioral-to-mixed direction on
the two-decision perfect-recall game. -/
theorem behavioral_to_mixed
    (behavioral : Profile recallGame.behavioralSignature)
    (horizon : ℕ) :
    ∃ mixed : Profile recallGame.strategicSignature.mixed,
      recallGame.information.runMixed mixed horizon =
        recallGame.information.runBehavioral behavioral horizon :=
  recallGame.kuhn_behavioral_to_mixed
    recallGame_actsOnce behavioral horizon

/-- The converse EFG wrapper uses the discharged perfect-recall proof. -/
theorem mixed_to_behavioral
    (mixed : Profile recallGame.strategicSignature.mixed)
    (horizon : ℕ) :
    ∃ behavioral : Profile recallGame.behavioralSignature,
      recallGame.information.runBehavioral behavioral horizon =
        recallGame.information.runMixed mixed horizon :=
  recallGame.kuhn_mixed_to_behavioral
    recallGame_perfectRecall mixed horizon

/-- Both strategy presentations realize exactly the same history laws through
the EFG surface. -/
theorem historyLaws (horizon : ℕ) :
    { law | ∃ behavioral : Profile recallGame.behavioralSignature,
        recallGame.information.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : Profile recallGame.strategicSignature.mixed,
        recallGame.information.runMixed mixed horizon = law } :=
  recallGame.kuhn_historyLaws
    recallGame_actsOnce recallGame_perfectRecall horizon

/-- The language-facing utility corollary retains arbitrary, nonconstant
history-dependent utility. -/
theorem behavioral_to_mixed_expectedUtility
    (behavioral : Profile recallGame.behavioralSignature)
    (horizon : ℕ) (utility : recallGame.History → Unit → ℝ) :
    ∃ mixed : Profile recallGame.strategicSignature.mixed,
      ∀ who,
        expectedUtility utility who
            (recallGame.information.runMixed mixed horizon) =
          expectedUtility utility who
            (recallGame.information.runBehavioral behavioral horizon) :=
  recallGame.kuhn_behavioral_to_mixed_expectedUtility
    recallGame_actsOnce behavioral horizon utility

end GameTheory.Tests.EFGKuhn
