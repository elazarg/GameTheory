/-
# EXP-060 signal-timing witnesses

Concrete checks over the two-round source/serialization slice. This file
contains no profile translation or runner comparison.
-/

import GameTheory.Experimental.PostArchitecture.FOSGToEFGTwoRound

noncomputable section

namespace GameTheory.Experimental.FOSGToEFGTwoRound.Witnesses

open GameTheory.Protocol
open GameTheory.Experimental.FOSGToEFGTwoRound

def startFalse : Serial.ChoiceAt Source.execution.initHistory false :=
  ⟨some false, by
    exact ⟨by simp [Source.active], Set.mem_univ _⟩⟩

def startTrue : Serial.ChoiceAt Source.execution.initHistory true :=
  ⟨some true, by
    exact ⟨by simp [Source.active], Set.mem_univ _⟩⟩

theorem source_start_not_terminal : ¬ Source.execution.terminal .start := by
  simp [Source.terminal]

def afterFirstFalse :
    (Serial.execution false).Trace
      (.afterFirst Source.execution.initHistory startFalse) :=
  .extend (Serial.boundaryTrace false Source.execution.initHistory)
    (Serial.selectedJoint false startFalse.1)
    (Serial.firstSlotLegal false Source.execution.initHistory
      source_start_not_terminal startFalse)
    (Serial.firstSlot_realized false Source.execution.initHistory
      source_start_not_terminal startFalse)

def readyFalse :
    (Serial.execution false).Trace
      (.ready Source.execution.initHistory startFalse startTrue) :=
  .extend afterFirstFalse (Serial.selectedJoint true startTrue.1)
    (Serial.secondSlotLegal false Source.execution.initHistory
      source_start_not_terminal startFalse startTrue)
    (Serial.secondSlot_realized false Source.execution.initHistory
      source_start_not_terminal startFalse startTrue)

def afterFirstTrace (first : Bool)
    (history : Source.execution.History)
    (hterm : ¬ Source.execution.terminal history.state)
    (choice : Serial.ChoiceAt history first) :
    (Serial.execution first).Trace (.afterFirst history choice) :=
  .extend (Serial.boundaryTrace first history)
    (Serial.selectedJoint first choice.1)
    (Serial.firstSlotLegal first history hterm choice)
    (Serial.firstSlot_realized first history hterm choice)

def firstSelectionEvent : (Serial.execution false).StepEvent :=
  ⟨.boundary Source.execution.initHistory,
    Serial.selectedJoint false startFalse.1,
    Serial.firstSlotLegal false Source.execution.initHistory
      source_start_not_terminal startFalse,
    .afterFirst Source.execution.initHistory startFalse,
    Serial.firstSlot_realized false Source.execution.initHistory
      source_start_not_terminal startFalse⟩

def secondSelectionEvent : (Serial.execution false).StepEvent :=
  ⟨.afterFirst Source.execution.initHistory startFalse,
    Serial.selectedJoint true startTrue.1,
    Serial.secondSlotLegal false Source.execution.initHistory
      source_start_not_terminal startFalse startTrue,
    .ready Source.execution.initHistory startFalse startTrue,
    Serial.secondSlot_realized false Source.execution.initHistory
      source_start_not_terminal startFalse startTrue⟩

theorem first_selection_public_admin :
    Serial.publicSignalOfEvent firstSelectionEvent = .admin .secondSlot := rfl

theorem first_selection_private_admin (player : Bool) :
    Serial.privateSignalOfEvent player firstSelectionEvent = .admin := rfl

theorem second_selection_public_admin :
    Serial.publicSignalOfEvent secondSelectionEvent = .admin .resolving := rfl

theorem second_selection_private_admin (player : Bool) :
    Serial.privateSignalOfEvent player secondSelectionEvent = .admin := rfl

theorem first_selection_source_unchanged (player : Bool) :
    ((Serial.signals false).infoOf player afterFirstFalse).source =
      Source.signals.infoOf player Source.execution.initHistory.trace := by
  rw [Serial.infoOf_eq_viewOfState]
  rfl

theorem second_selection_source_unchanged (player : Bool) :
    ((Serial.signals false).infoOf player readyFalse).source =
      Source.signals.infoOf player Source.execution.initHistory.trace := by
  rw [Serial.infoOf_eq_viewOfState]
  rfl

theorem boundary_source_exact (first player : Bool)
    (history : Source.execution.History) :
    ((Serial.signals first).infoOf player (Serial.boundaryTrace first history)).source =
      Source.signals.infoOf player history.trace := by
  rw [Serial.infoOf_eq_viewOfState]
  rfl

theorem later_selection_hides_prefix (first : Bool)
    (history : Source.execution.History)
    (one two : Serial.ChoiceAt history first) :
    (Serial.viewOfState (!first) (.afterFirst history one)).source =
      (Serial.viewOfState (!first) (.afterFirst history two)).source := rfl

theorem source_public_replayed (player left right hiddenActiveBit : Bool) :
    (Serial.viewOfState (first := false) player
      (.boundary (Source.round2History left right false hiddenActiveBit))).source ≠
    (Serial.viewOfState (first := false) player
      (.boundary (Source.round2History left right true hiddenActiveBit))).source := by
  simpa only [Serial.viewOfState, Serial.State.history] using
    Source.public_bit_is_observed player left right hiddenActiveBit

theorem source_private_replayed (left publicBit hiddenActiveBit : Bool) :
    (Serial.viewOfState (first := false) false
      (.boundary (Source.round2History left false publicBit hiddenActiveBit))).source ≠
    (Serial.viewOfState (first := false) false
      (.boundary (Source.round2History left true publicBit hiddenActiveBit))).source := by
  simpa only [Serial.viewOfState, Serial.State.history] using
    Source.opponent_first_action_is_private left publicBit hiddenActiveBit

theorem source_own_action_replayed (right publicBit hiddenActiveBit : Bool) :
    (Serial.viewOfState (first := false) false
      (.boundary (Source.round2History false right publicBit hiddenActiveBit))).source ≠
    (Serial.viewOfState (first := false) false
      (.boundary (Source.round2History true right publicBit hiddenActiveBit))).source := by
  simpa only [Serial.viewOfState, Serial.State.history] using
    Source.own_first_action_is_remembered right publicBit hiddenActiveBit

theorem false_later_view_hides_true_activity
    (left right publicBit : Bool) :
    (Serial.viewOfState (first := true) false
      (.afterFirst (Source.round2History left right publicBit false)
        ⟨none, by
          show ¬ Source.active (.round2 publicBit false) true
          simp [Source.active]⟩)).source =
    (Serial.viewOfState (first := true) false
      (.afterFirst (Source.round2History left right publicBit true)
        ⟨some false, by
          exact ⟨by simp [Source.round2History, Source.active], Set.mem_univ _⟩⟩)).source := by
  simpa only [Serial.viewOfState, Serial.State.history] using
    Source.false_does_not_observe_hidden_activity left right publicBit

theorem false_later_view_hides_true_action
    (left right publicBit : Bool) :
    (Serial.viewOfState (first := true) false
      (.afterFirst (Source.round2History left right publicBit true)
        ⟨some false, by
          exact ⟨by simp [Source.round2History, Source.active], Set.mem_univ _⟩⟩)).source =
    (Serial.viewOfState (first := true) false
      (.afterFirst (Source.round2History left right publicBit true)
        ⟨some true, by
          exact ⟨by simp [Source.round2History, Source.active], Set.mem_univ _⟩⟩)).source := rfl

theorem false_policy_view_hides_true_activity
    (left right publicBit : Bool) :
    (Serial.information true).infoOf false
        (afterFirstTrace true
          (Source.round2History left right publicBit false)
          (by
            show ¬ Source.terminal (.round2 publicBit false)
            simp [Source.terminal])
          ⟨none, by
            show ¬ Source.active (.round2 publicBit false) true
            simp [Source.active]⟩) =
      (Serial.information true).infoOf false
        (afterFirstTrace true
          (Source.round2History left right publicBit true)
          (by
            show ¬ Source.terminal (.round2 publicBit true)
            simp [Source.terminal])
          ⟨some false, by
            exact ⟨by simp [Source.round2History, Source.active],
              Set.mem_univ _⟩⟩) := by
  rw [Serial.infoOf_eq_viewOfState, Serial.infoOf_eq_viewOfState]
  unfold Serial.viewOfState
  simp only [Serial.phaseOfState, Source.round2History,
    Serial.State.history]
  exact congrArg
    (fun source => Serial.View.mk .secondSlot source)
    (Source.false_does_not_observe_hidden_activity
      left right publicBit)

theorem false_policy_view_hides_true_action
    (left right publicBit : Bool) :
    (Serial.information true).infoOf false
        (afterFirstTrace true
          (Source.round2History left right publicBit true)
          (by
            show ¬ Source.terminal (.round2 publicBit true)
            simp [Source.terminal])
          ⟨some false, by
            exact ⟨by simp [Source.round2History, Source.active],
              Set.mem_univ _⟩⟩) =
      (Serial.information true).infoOf false
        (afterFirstTrace true
          (Source.round2History left right publicBit true)
          (by
            show ¬ Source.terminal (.round2 publicBit true)
            simp [Source.terminal])
          ⟨some true, by
            exact ⟨by simp [Source.round2History, Source.active],
              Set.mem_univ _⟩⟩) := by
  rw [Serial.infoOf_eq_viewOfState, Serial.infoOf_eq_viewOfState]
  rfl

def falseSignalAction : Source.View → Option Bool
  | .round1 => some false
  | .round2 publicBit opponentAction _ ownAction =>
      some (Bool.xor (Bool.xor publicBit opponentAction) ownAction)
  | .done .. => none

def falseSignalChoice (view : Source.View) :
    Source.information.Choice false view :=
  ⟨falseSignalAction view, by
    cases view with
    | round1 => simp [falseSignalAction, Source.menu]
    | round2 publicBit opponentAction hiddenActiveBit ownAction =>
        cases publicBit <;> cases opponentAction <;> cases ownAction <;>
          simp [falseSignalAction, Source.menu]
    | done => simp [falseSignalAction, Source.menu]⟩

def falseSignalPolicy : Source.information.BehavioralPolicy false :=
  fun view => GameTheory.Math.Probability.FinDist.pure (falseSignalChoice view)

def falseSignalOptionLaw (view : Source.View) :
    GameTheory.Math.Probability.FinDist (Option Bool) :=
  GameTheory.Math.Probability.FinDist.map Subtype.val (falseSignalPolicy view)

theorem pure_some_false_ne_true :
    GameTheory.Math.Probability.FinDist.pure (some false) ≠
      GameTheory.Math.Probability.FinDist.pure (some true) := by
  intro hequal
  have hprob := congrArg
    (fun law : GameTheory.Math.Probability.FinDist (Option Bool) =>
      law.prob (some false)) hequal
  norm_num [GameTheory.Math.Probability.FinDist.prob_pure_eq_ite] at hprob

theorem false_signal_policy_reads_public :
    falseSignalOptionLaw (.round2 false false none false) ≠
      falseSignalOptionLaw (.round2 true false none false) := by
  simpa [falseSignalOptionLaw, falseSignalPolicy, falseSignalChoice,
    falseSignalAction] using pure_some_false_ne_true

theorem false_signal_policy_reads_private :
    falseSignalOptionLaw (.round2 false false none false) ≠
      falseSignalOptionLaw (.round2 false true none false) := by
  simpa [falseSignalOptionLaw, falseSignalPolicy, falseSignalChoice,
    falseSignalAction] using pure_some_false_ne_true

theorem false_signal_policy_reads_own_action :
    falseSignalOptionLaw (.round2 false false none false) ≠
      falseSignalOptionLaw (.round2 false false none true) := by
  simpa [falseSignalOptionLaw, falseSignalPolicy, falseSignalChoice,
    falseSignalAction] using pure_some_false_ne_true


end GameTheory.Experimental.FOSGToEFGTwoRound.Witnesses
