import GameTheory.Languages.FOSG.Compile

/-!
# GameTheory.Languages.FOSG.Examples

Small native FOSG examples that exercise the non-EFG pipeline.
-/

namespace GameTheory

namespace FOSG

namespace Examples

inductive Solo where
  | only
  deriving DecidableEq, Fintype

abbrev SoloAct (_ : Solo) := Bool
abbrev SoloObs (_ : Solo) := Unit
abbrev SoloPub := Unit

inductive SoloState where
  | start
  | done (pick : Bool)
  deriving DecidableEq, Fintype

def binaryChoiceActive : SoloState → Finset Solo
  | .start => {Solo.only}
  | .done _ => ∅

def binaryChoiceAvailable : SoloState → (i : Solo) → Set (SoloAct i)
  | .start, _ => Set.univ
  | .done _, _ => ∅

def binaryChoiceTerminal : SoloState → Prop
  | .start => False
  | .done _ => True

noncomputable def binaryChoiceTransition
    (w : SoloState)
    (a : { a : JointAction SoloAct //
      JointActionLegal SoloAct
        binaryChoiceActive
        binaryChoiceTerminal
        binaryChoiceAvailable
        w a }) :
    PMF SoloState := by
  cases w with
  | start =>
      cases hpick : a.1 Solo.only with
      | none =>
          have hnone : Solo.only ∉ ({Solo.only} : Finset Solo) := by
            simpa [JointActionLegal, binaryChoiceActive, binaryChoiceAvailable,
              binaryChoiceTerminal, hpick] using a.2.2 Solo.only
          exact False.elim (by simp at hnone)
      | some pick =>
          exact PMF.pure (.done pick)
  | done pick =>
      have : False := by
        simpa [binaryChoiceTerminal] using a.2.1
      exact False.elim this

/-- A one-player one-step FOSG. The single player chooses a Boolean at the
initial state and the game terminates immediately. -/
noncomputable def binaryChoice : FOSG Solo SoloState SoloAct SoloObs SoloPub where
  init := .start
  active := binaryChoiceActive
  availableActions := binaryChoiceAvailable
  terminal := binaryChoiceTerminal
  transition := binaryChoiceTransition
  reward _ _ dst _ :=
    match dst with
    | .start => 0
    | .done true => 1
    | .done false => 0
  privObs _ _ _ _ := ()
  pubObs _ _ _ := ()
  terminal_active_eq_empty := by
    intro w hw
    cases w with
    | start => cases hw
    | done pick => simp [binaryChoiceActive]
  terminal_no_legal := by
    intro w a hw
    cases w with
    | start => cases hw
    | done pick =>
        intro hlegal
        exact hlegal.1 (by simp [binaryChoiceTerminal])
  nonterminal_exists_legal := by
    intro w hw
    cases w with
    | start =>
        refine ⟨fun _ => some true, ?_⟩
        simp [JointActionLegal, binaryChoiceActive, binaryChoiceAvailable, binaryChoiceTerminal]
    | done pick =>
        exact False.elim (hw (by simp [binaryChoiceTerminal]))

instance : DecidablePred binaryChoice.terminal := by
  intro w
  cases w with
  | start => exact isFalse (by intro h; cases h)
  | done pick => exact isTrue (by dsimp [binaryChoice, binaryChoiceTerminal])

def startAction (pick : Bool) : JointAction SoloAct :=
  fun _ => some pick

theorem startAction_legal (pick : Bool) :
    binaryChoice.legal .start (startAction pick) := by
  change ¬ binaryChoiceTerminal .start ∧
      ∀ i, match startAction pick i with
        | some ai => i ∈ binaryChoiceActive .start ∧ ai ∈ binaryChoiceAvailable .start i
        | none => i ∉ binaryChoiceActive .start
  constructor
  · intro h
    cases h
  · intro i
    cases i with
    | only =>
        simp [startAction, binaryChoiceActive, binaryChoiceAvailable]

noncomputable def startLegalAction (pick : Bool) : binaryChoice.LegalAction .start :=
  ⟨startAction pick, startAction_legal pick⟩

noncomputable def binaryChoiceKernelAtHorizon : KernelGame Solo :=
  binaryChoice.toKernelGameAtHorizon 1

end Examples

end FOSG

end GameTheory
