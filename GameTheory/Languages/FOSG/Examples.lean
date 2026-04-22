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

namespace MatchingPennies

inductive Player where
  | left
  | right
  deriving DecidableEq, Fintype

abbrev Act (_ : Player) := Bool
abbrev PrivObs (_ : Player) := Unit
abbrev PubObs := Unit

inductive State where
  | start
  | done (left right : Bool)
  deriving DecidableEq, Fintype

def active : State → Finset Player
  | .start => {Player.left, Player.right}
  | .done _ _ => ∅

def availableActions : State → (i : Player) → Set (Act i)
  | .start, _ => Set.univ
  | .done _ _, _ => ∅

def terminal : State → Prop
  | .start => False
  | .done _ _ => True

def payoff (left right : Bool) : Player → ℝ
  | .left => if left = right then 1 else -1
  | .right => if left = right then -1 else 1

noncomputable def leftMove
    (a : { a : JointAction Act //
      JointActionLegal Act active terminal availableActions .start a }) :
    Bool := by
  cases hleft : a.1 Player.left with
  | none =>
      have hnone : Player.left ∉ active .start := by
        simpa [JointActionLegal, active, availableActions, terminal, hleft] using
          a.2.2 Player.left
      exact False.elim (by simp [active] at hnone)
  | some left =>
      exact left

noncomputable def rightMove
    (a : { a : JointAction Act //
      JointActionLegal Act active terminal availableActions .start a }) :
    Bool := by
  cases hright : a.1 Player.right with
  | none =>
      have hnone : Player.right ∉ active .start := by
        simpa [JointActionLegal, active, availableActions, terminal, hright] using
          a.2.2 Player.right
      exact False.elim (by simp [active] at hnone)
  | some right =>
      exact right

noncomputable def transition
    (w : State)
    (a : { a : JointAction Act //
      JointActionLegal Act active terminal availableActions w a }) :
    PMF State := by
  cases w with
  | start =>
      exact PMF.pure (.done (leftMove a) (rightMove a))
  | done left right =>
      have : False := by
        simpa [terminal] using a.2.1
      exact False.elim this

/-- Matching pennies as a native one-step simultaneous FOSG. -/
noncomputable def game : FOSG Player State Act PrivObs PubObs where
  init := .start
  active := active
  availableActions := availableActions
  terminal := terminal
  transition := transition
  reward _ _ dst i :=
    match dst with
    | .start => 0
    | .done left right => payoff left right i
  privObs _ _ _ _ := ()
  pubObs _ _ _ := ()
  terminal_active_eq_empty := by
    intro w hw
    cases w with
    | start => cases hw
    | done left right => simp [active]
  terminal_no_legal := by
    intro w a hw
    cases w with
    | start => cases hw
    | done left right =>
        intro hlegal
        exact hlegal.1 (by simp [terminal])
  nonterminal_exists_legal := by
    intro w hw
    cases w with
    | start =>
        refine ⟨fun i => some (if i = Player.left then true else false), ?_⟩
        constructor
        · intro h
          cases h
        · intro i
          cases i with
          | left => simp [active, availableActions]
          | right => simp [active, availableActions]
    | done left right =>
        exact False.elim (hw (by simp [terminal]))

instance : DecidablePred game.terminal := by
  intro w
  cases w with
  | start => exact isFalse (by intro h; cases h)
  | done left right => exact isTrue (by simp [game, terminal])

theorem step_from_start_isTerminal
    (e : game.Step) (hsrc : e.src = .start) :
    terminal e.dst := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      cases hleft : act.1 Player.left with
      | none =>
          have hnone : Player.left ∉ game.active .start := by
            simpa [game, JointActionLegal, active, availableActions, terminal, hleft] using
              act.2.2 Player.left
          have : False := by
            simp [game, active] at hnone
          exact False.elim this
      | some left =>
          cases hright : act.1 Player.right with
          | none =>
              have hnone : Player.right ∉ game.active .start := by
                simpa [game, JointActionLegal, active, availableActions, terminal, hleft, hright]
                  using
                  act.2.2 Player.right
              have : False := by
                simp [game, active] at hnone
              exact False.elim this
          | some right =>
              cases dst with
              | start =>
                  have hzero : game.transition State.start act State.start = 0 := by
                    change transition State.start act State.start = 0
                    simp [transition, leftMove, rightMove]
                  exact False.elim (support hzero)
              | done left' right' =>
                  simp [terminal]

theorem boundedHorizon : game.BoundedHorizon 1 := by
  intro h hlen
  cases h with
  | mk steps chain =>
      cases steps with
      | nil =>
          simp at hlen
      | cons e es =>
          cases es with
          | nil =>
              have hsrc : e.src = State.start := by
                simpa using chain.1
              have hterm : terminal e.dst := step_from_start_isTerminal e hsrc
              simpa [History.IsTerminal, History.lastState, hterm]
          | cons e' es' =>
              simp at hlen

noncomputable def kernel : KernelGame Player :=
  game.toKernelGameAtHorizon 1

end MatchingPennies

end Examples

end FOSG

end GameTheory
