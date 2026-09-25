/-
# Epistemic ownership boundary

Static knowledge and agreement use the canonical Setoid/PMF development. This
experiment retains the Protocol counterexample: a merged execution state may
carry distinct history-local information states.
-/

import GameTheory.Protocol.Information
import GameTheory.Epistemic.Agreement

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.KnowledgeOwnership

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open ExecutionProtocol
/-! ## Why Protocol information is not this object -/

/-- One decision followed by a merged terminal state. -/
inductive MergeState
  | initial
  | merged

/-- Both actions reach the same execution state. -/
@[reducible]
def mergingExecution : ExecutionProtocol Unit where
  State := MergeState
  Action _ := Bool
  init := .initial
  active state _ :=
    match state with
    | .initial => True
    | .merged => False
  available _ _ := Set.univ
  terminal state :=
    match state with
    | .initial => False
    | .merged => True
  step state joint :=
    match state with
    | .initial => PMF.pure .merged
    | .merged => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterminal
    cases state with
    | initial =>
        exact ⟨fun _ => some false, fun _ =>
          ⟨trivial, Set.mem_univ _⟩⟩
    | merged =>
        exact False.elim (hterminal trivial)

/-- The player remembers which action led to the merged state. -/
inductive MergeView
  | acting
  | done (action : Bool)
  deriving DecidableEq

/-- History-local signals for the merging execution. -/
@[reducible]
def mergingSignals : InfoSignals mergingExecution where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := MergeView
  initInfo _ _ _ := .acting
  pushInfo _ prior ownAction _ _ :=
    match ownAction with
    | some action => .done action
    | none => prior

/-- The local menu depends only on the history-local phase. -/
def mergingMenu (_ : Unit) : MergeView → Set (Option Bool)
  | .acting => { choice | ∃ action, choice = some action }
  | .done _ => {none}

/-- Menu adequacy holds even though the final execution state has two views. -/
theorem mergingMenu_adequate {state : mergingExecution.State}
    (trace : Trace mergingExecution state)
    (choice : Option Bool) :
    choice ∈ mergingMenu () (mergingSignals.infoOf () trace) ↔
      LegalOption mergingExecution state () choice := by
  cases trace with
  | start =>
      cases choice <;> simp [mergingMenu, LegalOption, mergingExecution]
  | @extend source target prior joint isLegal realized =>
      cases source with
      | merged =>
          exact False.elim (isLegal.1 trivial)
      | initial =>
          have htarget : state = MergeState.merged := by
            simpa [mergingExecution] using realized
          subst state
          have hjoint := isLegal.2 ()
          cases h : joint () with
          | none =>
              rw [h] at hjoint
              exact False.elim (hjoint trivial)
          | some action =>
              rw [InfoSignals.infoOf_extend]
              cases choice <;>
                simp [mergingMenu, LegalOption, mergingExecution, h]

/-- The accepted information model on the merging execution. -/
@[reducible]
def mergingInformation : InformationModel mergingExecution where
  toInfoSignals := mergingSignals
  menu := mergingMenu
  menu_adequate := by
    intro _ _ trace choice
    exact mergingMenu_adequate trace choice

/-- The legal joint action selecting `action`. -/
def mergeJoint (action : Bool) : ∀ _ : Unit, Option Bool :=
  fun _ => some action

theorem mergeJoint_legal (action : Bool) :
    mergingExecution.Legal .initial (mergeJoint action) :=
  ⟨by simp, fun _ =>
    ⟨trivial, Set.mem_univ _⟩⟩

theorem mergeJoint_realized (action : Bool) :
    MergeState.merged ∈
      (mergingExecution.step .initial
        ⟨mergeJoint action, mergeJoint_legal action⟩).support := by
  simp [mergingExecution]

/-- The history remembering one of the two actions. -/
def mergeTrace (action : Bool) : Trace mergingExecution .merged :=
  .extend .start (mergeJoint action) (mergeJoint_legal action)
    (mergeJoint_realized action)

@[simp]
theorem infoOf_mergeTrace (action : Bool) :
    mergingInformation.infoOf () (mergeTrace action) = .done action := rfl

/-- The one terminal execution state belongs to both distinct information
sets. Hence Protocol `InfoSet`s are not a partition of states in general. -/
theorem merged_mem_two_infoSets :
    MergeState.merged ∈
        mergingInformation.InfoSet () (.done false) ∩
      mergingInformation.InfoSet () (.done true) :=
  ⟨⟨mergeTrace false, infoOf_mergeTrace false⟩,
    ⟨mergeTrace true, infoOf_mergeTrace true⟩⟩

/-- No function of execution state alone can recover all history-local
information states of this valid model. -/
theorem no_state_view_represents_infoOf :
    ¬ ∃ view : MergeState → MergeView,
      ∀ {state : MergeState} (trace : Trace mergingExecution state),
        view state = mergingInformation.infoOf () trace := by
  rintro ⟨view, hview⟩
  have hfalse := hview (mergeTrace false)
  have htrue := hview (mergeTrace true)
  have hequal : MergeView.done false = .done true :=
    hfalse.symm.trans htrue
  cases hequal

end GameTheory.Experimental.PostArchitecture.KnowledgeOwnership
