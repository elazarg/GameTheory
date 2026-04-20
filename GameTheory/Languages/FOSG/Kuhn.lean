import GameTheory.Languages.FOSG.Information
import Mathlib.Probability.Distributions.Uniform

/-!
# GameTheory.Languages.FOSG.Kuhn

A concrete Kuhn poker encoding as a FOSG, with trace lemmas showing the intended
public/private observation split.
-/

namespace GameTheory

namespace FOSG

namespace Kuhn

open Math.Probability

inductive Player where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

inductive Card where
  | jack
  | queen
  | king
  deriving DecidableEq, Fintype, Repr

inductive Deal where
  | jq
  | jk
  | qj
  | qk
  | kj
  | kq
  deriving DecidableEq, Fintype, Repr, Inhabited

inductive Act where
  | check
  | bet
  | call
  | fold
  deriving DecidableEq, Repr

inductive PrivObs where
  | silent
  | card (c : Card)
  deriving DecidableEq, Repr

inductive PubObs where
  | silent
  | check
  | bet
  | call
  | fold
  deriving DecidableEq, Repr

inductive TerminalKind where
  | checkedShowdown
  | calledShowdown
  | oneWinsFold
  | twoWinsFold
  deriving DecidableEq, Repr

inductive State where
  | start
  | p1Turn (d : Deal)
  | p2AfterCheck (d : Deal)
  | p2AfterBet (d : Deal)
  | p1Response (d : Deal)
  | terminal (d : Deal) (tk : TerminalKind)
  deriving DecidableEq, Repr

abbrev ActTy : Player → Type := fun _ => Act
abbrev PrivTy : Player → Type := fun _ => PrivObs

def noop : JointAction ActTy := fun _ => none

def p1Only (a : Act) : JointAction ActTy
  | .one => some a
  | .two => none

def p2Only (a : Act) : JointAction ActTy
  | .one => none
  | .two => some a

@[simp] theorem noop_apply (i : Player) : noop i = none := rfl
@[simp] theorem p1Only_one (a : Act) : p1Only a .one = some a := rfl
@[simp] theorem p1Only_two (a : Act) : p1Only a .two = none := rfl
@[simp] theorem p2Only_one (a : Act) : p2Only a .one = none := rfl
@[simp] theorem p2Only_two (a : Act) : p2Only a .two = some a := rfl

def isNoop (a : JointAction ActTy) : Prop :=
  a .one = none ∧ a .two = none

def isP1Only (x : Act) (a : JointAction ActTy) : Prop :=
  a .one = some x ∧ a .two = none

def isP2Only (x : Act) (a : JointAction ActTy) : Prop :=
  a .one = none ∧ a .two = some x

def cardOf : Deal → Player → Card
  | .jq, .one => .jack
  | .jq, .two => .queen
  | .jk, .one => .jack
  | .jk, .two => .king
  | .qj, .one => .queen
  | .qj, .two => .jack
  | .qk, .one => .queen
  | .qk, .two => .king
  | .kj, .one => .king
  | .kj, .two => .jack
  | .kq, .one => .king
  | .kq, .two => .queen

def cardRank : Card → Nat
  | .jack => 0
  | .queen => 1
  | .king => 2

def winner (d : Deal) : Player :=
  if cardRank (cardOf d .one) < cardRank (cardOf d .two) then .two else .one

def payoff (d : Deal) (tk : TerminalKind) : Player → ℝ
  | .one =>
      match tk with
      | .checkedShowdown =>
          if winner d = .one then 1 else -1
      | .calledShowdown =>
          if winner d = .one then 2 else -2
      | .oneWinsFold => 1
      | .twoWinsFold => -1
  | .two =>
      match tk with
      | .checkedShowdown =>
          if winner d = .two then 1 else -1
      | .calledShowdown =>
          if winner d = .two then 2 else -2
      | .oneWinsFold => -1
      | .twoWinsFold => 1

def dealOf : State → Option Deal
  | .start => none
  | .p1Turn d => some d
  | .p2AfterCheck d => some d
  | .p2AfterBet d => some d
  | .p1Response d => some d
  | .terminal d _ => some d

def terminalKind? : State → Option TerminalKind
  | .terminal _ tk => some tk
  | _ => none

def active : State → Finset Player
  | .start => ∅
  | .p1Turn _ => {.one}
  | .p2AfterCheck _ => {.two}
  | .p2AfterBet _ => {.two}
  | .p1Response _ => {.one}
  | .terminal _ _ => ∅

def terminal : State → Prop
  | .terminal _ _ => True
  | _ => False

def legal : State → JointAction ActTy → Prop
  | .start, a => isNoop a
  | .p1Turn _, a => isP1Only .check a ∨ isP1Only .bet a
  | .p2AfterCheck _, a => isP2Only .check a ∨ isP2Only .bet a
  | .p2AfterBet _, a => isP2Only .call a ∨ isP2Only .fold a
  | .p1Response _, a => isP1Only .call a ∨ isP1Only .fold a
  | .terminal _ _, _ => False

noncomputable def transition :
    (w : State) → {a : JointAction ActTy // legal w a} → PMF State
  | .start, _ =>
      PMF.map State.p1Turn (PMF.uniformOfFintype Deal)
  | .p1Turn d, a =>
      if _h : a.1 .one = some .check then
        PMF.pure (.p2AfterCheck d)
      else
        PMF.pure (.p2AfterBet d)
  | .p2AfterCheck d, a =>
      if _h : a.1 .two = some .check then
        PMF.pure (.terminal d .checkedShowdown)
      else
        PMF.pure (.p1Response d)
  | .p2AfterBet d, a =>
      if _h : a.1 .two = some .call then
        PMF.pure (.terminal d .calledShowdown)
      else
        PMF.pure (.terminal d .oneWinsFold)
  | .p1Response d, a =>
      if _h : a.1 .one = some .call then
        PMF.pure (.terminal d .calledShowdown)
      else
        PMF.pure (.terminal d .twoWinsFold)
  | .terminal _ _, a =>
      False.elim a.2

def reward
    (_w : State) (_a : {a : JointAction ActTy // legal _w a}) (w' : State) (i : Player) : ℝ :=
  match dealOf w', terminalKind? w' with
  | some d, some tk => payoff d tk i
  | _, _ => 0

def privObs (i : Player)
    (_w : State) (_a : {a : JointAction ActTy // legal _w a}) (w' : State) : PrivObs :=
  match w' with
  | .p1Turn d => .card (cardOf d i)
  | _ => .silent

def pubObs
    (_w : State) (_a : {a : JointAction ActTy // legal _w a}) (w' : State) : PubObs :=
  match w' with
  | .p1Turn _ => .silent
  | .p2AfterCheck _ => .check
  | .p2AfterBet _ => .bet
  | .p1Response _ => .bet
  | .terminal _ .checkedShowdown => .check
  | .terminal _ .calledShowdown => .call
  | .terminal _ .oneWinsFold => .fold
  | .terminal _ .twoWinsFold => .fold
  | .start => .silent

noncomputable def game : FOSG Player State ActTy PrivTy PubObs where
  init := .start
  active := active
  init_active_eq_empty := rfl
  terminal := terminal
  legal := legal
  transition := transition
  reward := reward
  privObs := privObs
  pubObs := pubObs
  legal_inactive_none := by
    intro w a i hlegal hi
    cases w with
    | start =>
        cases i with
        | one => exact hlegal.1
        | two => exact hlegal.2
    | p1Turn d =>
        cases i with
        | one =>
            exfalso
            simp [active] at hi
        | two =>
            rcases hlegal with h | h <;> exact h.2
    | p2AfterCheck d =>
        cases i with
        | one =>
            rcases hlegal with h | h <;> exact h.1
        | two =>
            exfalso
            simp [active] at hi
    | p2AfterBet d =>
        cases i with
        | one =>
            rcases hlegal with h | h <;> exact h.1
        | two =>
            exfalso
            simp [active] at hi
    | p1Response d =>
        cases i with
        | one =>
            exfalso
            simp [active] at hi
        | two =>
            rcases hlegal with h | h <;> exact h.2
    | terminal d tk =>
        cases hlegal
  legal_active_some := by
    intro w a i hlegal hi
    cases w with
    | start =>
        exfalso
        simp [active] at hi
    | p1Turn d =>
        cases i with
        | one =>
            rcases hlegal with h | h
            · exact ⟨_, h.1⟩
            · exact ⟨_, h.1⟩
        | two =>
            exfalso
            simp [active] at hi
    | p2AfterCheck d =>
        cases i with
        | one =>
            exfalso
            simp [active] at hi
        | two =>
            rcases hlegal with h | h
            · exact ⟨_, h.2⟩
            · exact ⟨_, h.2⟩
    | p2AfterBet d =>
        cases i with
        | one =>
            exfalso
            simp [active] at hi
        | two =>
            rcases hlegal with h | h
            · exact ⟨_, h.2⟩
            · exact ⟨_, h.2⟩
    | p1Response d =>
        cases i with
        | one =>
            rcases hlegal with h | h
            · exact ⟨_, h.1⟩
            · exact ⟨_, h.1⟩
        | two =>
            exfalso
            simp [active] at hi
    | terminal d tk =>
        exfalso
        simp [active] at hi
  terminal_active_eq_empty := by
    intro w hterm
    cases w <;> simp [terminal, active] at hterm ⊢
  terminal_no_legal := by
    intro w a hterm
    cases w <;> simp [terminal, legal] at hterm ⊢
  nonterminal_exists_legal := by
    intro w hterm
    cases w with
    | start =>
        exact ⟨noop, by simp [legal, isNoop, noop]⟩
    | p1Turn d =>
        exact ⟨p1Only .check, by simp [legal, isP1Only]⟩
    | p2AfterCheck d =>
        exact ⟨p2Only .check, by simp [legal, isP2Only]⟩
    | p2AfterBet d =>
        exact ⟨p2Only .call, by simp [legal, isP2Only]⟩
    | p1Response d =>
        exact ⟨p1Only .call, by simp [legal, isP1Only]⟩
    | terminal d tk =>
        exfalso
        simp [terminal] at hterm

def startAction : game.LegalAction .start :=
  ⟨noop, by simp [game, legal, isNoop, noop]⟩

def p1BetAction (d : Deal) : game.LegalAction (.p1Turn d) :=
  ⟨p1Only .bet, by simp [game, legal, isP1Only]⟩

def p1CheckAction (d : Deal) : game.LegalAction (.p1Turn d) :=
  ⟨p1Only .check, by simp [game, legal, isP1Only]⟩

theorem deal_support (d : Deal) :
    game.transition .start startAction (.p1Turn d) ≠ 0 := by
  apply (PMF.mem_support_iff _ _).1
  exact (PMF.mem_support_map_iff (f := State.p1Turn) (p := PMF.uniformOfFintype Deal)
    (b := State.p1Turn d)).2 ⟨d, PMF.mem_support_uniformOfFintype d, rfl⟩

theorem p1Bet_support (d : Deal) :
    game.transition (.p1Turn d) (p1BetAction d) (.p2AfterBet d) ≠ 0 := by
  simp [game, transition, p1BetAction, p1Only]

theorem p1Check_support (d : Deal) :
    game.transition (.p1Turn d) (p1CheckAction d) (.p2AfterCheck d) ≠ 0 := by
  simp [game, transition, p1CheckAction, p1Only]

noncomputable def dealStep (d : Deal) : game.Step :=
  ⟨.start, startAction, .p1Turn d, deal_support d⟩

noncomputable def p1BetStep (d : Deal) : game.Step :=
  ⟨.p1Turn d, p1BetAction d, .p2AfterBet d, p1Bet_support d⟩

noncomputable def p1CheckStep (d : Deal) : game.Step :=
  ⟨.p1Turn d, p1CheckAction d, .p2AfterCheck d, p1Check_support d⟩

noncomputable def dealt (d : Deal) : game.History :=
  (History.nil game).snoc startAction (.p1Turn d) (deal_support d)

noncomputable def p1BetHistory (d : Deal) : game.History :=
  (dealt d).snoc (p1BetAction d) (.p2AfterBet d) (p1Bet_support d)

noncomputable def p1CheckHistory (d : Deal) : game.History :=
  (dealt d).snoc (p1CheckAction d) (.p2AfterCheck d) (p1Check_support d)

@[simp] theorem publicView_dealt (d : Deal) :
    (dealt d).publicView = [.silent] := by
  rw [dealt, History.publicView_snoc, History.publicView_nil]
  simp [game, pubObs]

@[simp] theorem publicView_p1Bet (d : Deal) :
    (p1BetHistory d).publicView = [.silent, .bet] := by
  rw [p1BetHistory, History.publicView_snoc, publicView_dealt]
  simp [game, pubObs]

@[simp] theorem publicView_p1Check (d : Deal) :
    (p1CheckHistory d).publicView = [.silent, .check] := by
  rw [p1CheckHistory, History.publicView_snoc, publicView_dealt]
  simp [game, pubObs]

@[simp] theorem playerOneView_dealt (d : Deal) :
    (dealt d).playerView .one = [.obs (.card (cardOf d .one)) .silent] := by
  rw [dealt, History.playerView_snoc, History.playerView_nil]
  simp [Step.playerView, Step.ownAction?, Step.privateObs, Step.publicObs,
    startAction, game, privObs, pubObs]
  rfl

@[simp] theorem playerTwoView_dealt (d : Deal) :
    (dealt d).playerView .two = [.obs (.card (cardOf d .two)) .silent] := by
  rw [dealt, History.playerView_snoc, History.playerView_nil]
  simp [Step.playerView, Step.ownAction?, Step.privateObs, Step.publicObs,
    startAction, game, privObs, pubObs]
  rfl

@[simp] theorem playerOneView_p1Bet (d : Deal) :
    (p1BetHistory d).playerView .one =
      [.obs (.card (cardOf d .one)) .silent, .act .bet, .obs .silent .bet] := by
  rw [p1BetHistory, History.playerView_snoc, playerOneView_dealt]
  simp [Step.playerView, Step.ownAction?, Step.privateObs, Step.publicObs,
    p1BetAction, game, privObs, pubObs]
  rfl

@[simp] theorem playerTwoView_p1Bet (d : Deal) :
    (p1BetHistory d).playerView .two =
      [.obs (.card (cardOf d .two)) .silent, .obs .silent .bet] := by
  rw [p1BetHistory, History.playerView_snoc, playerTwoView_dealt]
  simp [Step.playerView, Step.ownAction?, Step.privateObs, Step.publicObs,
    p1BetAction, game, privObs, pubObs]
  rfl

theorem publicView_dealt_same_for_all_deals (d₁ d₂ : Deal) :
    (dealt d₁).publicView = (dealt d₂).publicView := by
  simp

theorem playerOneView_dealt_jk_ne_qk :
    (dealt .jk).playerView .one ≠ (dealt .qk).playerView .one := by
  simp [cardOf]

theorem playerTwoView_dealt_jk_ne_jq :
    (dealt .jk).playerView .two ≠ (dealt .jq).playerView .two := by
  simp [cardOf]

end Kuhn

end FOSG

end GameTheory
