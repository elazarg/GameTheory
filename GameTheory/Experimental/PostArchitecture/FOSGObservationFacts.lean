/-
# EXP-058 witness: reachable-observation proof-machine retirement

The pinned reachable-history observation layer assumes that a terminal state
has no active player and exposes raw player-view lists.  Neither convention is
part of the accepted Protocol semantics: terminality prevents execution from
asking for a joint action, while activity and local menus may remain
nontrivial; information states may also compress the history.

These hostile witnesses show that the old terminal-menu and raw-view recovery
claims cannot be promoted as general FOSG facts.  Their useful replacements
are already the operation-local Protocol theorems.
-/

import GameTheory.Languages.FOSG.Kuhn
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Experimental.FOSGObservationFacts

open GameTheory.Protocol GameTheory.Tests

/-- A protocol may stop while retaining a nontrivial activity annotation.
The annotation is observational data at that point: no legal joint action can
be supplied and the runner never consults a chooser. -/
private def terminalActive : ExecutionProtocol Unit where
  State := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := True
  step _ joint := False.elim (joint.2.1 trivial)
  progress _ hterm := False.elim (hterm trivial)

private def terminalSignals : InfoSignals terminalActive where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

/-- Menu adequacy constrains the local menu, but does not add a hidden
non-terminal premise.  Both Boolean actions remain locally meaningful. -/
private def terminalModel : InformationModel terminalActive where
  toInfoSignals := terminalSignals
  menu _ _ := Set.range some
  menu_adequate := by
    rintro ⟨⟩ _ _ choice
    constructor
    · rintro ⟨action, rfl⟩
      exact ⟨trivial, Set.mem_univ action⟩
    · intro hlegal
      cases choice with
      | none => exact False.elim (hlegal trivial)
      | some action => exact ⟨action, rfl⟩

example : terminalActive.terminal terminalActive.init := trivial

example : terminalActive.active terminalActive.init () := trivial

/-- This machine-refutes the claim that every terminal local legal-move
type is a singleton.  Terminal execution still stops by construction. -/
theorem terminal_choice_not_subsingleton :
    ¬ Subsingleton (terminalModel.Choice () ()) := by
  intro hsub
  let first : terminalModel.Choice () () :=
    ⟨some false, ⟨false, rfl⟩⟩
  let second : terminalModel.Choice () () :=
    ⟨some true, ⟨true, rfl⟩⟩
  have heq : first = second := Subsingleton.elim _ _
  have hval : (some false : Option Bool) = some true :=
    congrArg Subtype.val heq
  simp at hval

/-- The canonical operation-local replacement remains valid: inactivity, not
terminality, makes the local choice type a singleton. -/
example {E : ExecutionProtocol Unit} (M : InformationModel E)
    {state : E.State} (trace : E.Trace state) (hinactive : ¬ E.active state ()) :
    Subsingleton (M.Choice () (M.infoOf () trace)) :=
  M.subsingleton_choice_of_not_active trace hinactive

/-- Current information states may intentionally forget a player's action.
Thus equality of compressed information cannot support the old raw-view
cancellation lemmas without a separately stated recall hypothesis. -/
example : ¬Randomized.singleSignals.PerfectRecall :=
  Randomized.single_not_perfectRecall


end GameTheory.Experimental.FOSGObservationFacts
