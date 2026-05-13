import GameTheory.Languages.EFG.Syntax

/-!
# EFG Examples

Reader-facing extensive-form examples.

Compilation/SOS validation belongs in `GameTheory.Languages.EFG.Tests`.
-/

namespace GameTheory.EFG.Examples

open _root_.EFG

/-- A one-player information structure with a single binary infoset. -/
def oneInfo : InfoStructure where
  n := 1
  Infoset := fun _ => PUnit
  arity := fun _ _ => 2
  arity_pos := by
    intro _ _
    exact Nat.succ_pos 1

/-- The unique player in `oneInfo`. -/
def p0 : oneInfo.Player := ⟨0, by decide⟩

/-- A minimal binary decision tree. -/
def binaryChoiceTree : GameTree oneInfo Bool :=
  .decision (p := p0) PUnit.unit (fun a =>
    if a.1 = 0 then .terminal false else .terminal true)

/-- A tiny extensive-form game built from `binaryChoiceTree`. -/
def binaryChoiceGame : EFGGame where
  inf := oneInfo
  Outcome := Bool
  tree := binaryChoiceTree
  utility := fun b _ =>
    if b then 1 else 0

/-! ## Centipede game (2-stage)

A small extensive-form game (Rosenthal 1981): two players alternate
choosing to either *take* or *pass*. Each pass increases the total
payoff pool but transfers the move to the opponent, who is then
tempted to take in the next round.

  Player 0 (take)    →  outcome `p0Takes`     payoff (1, 0)
  Player 0 (pass)    →  Player 1 (take)       payoff (0, 2)
                         Player 1 (pass)      payoff (3, 1)

Backward induction: Player 1's best move at stage 2 is *take*
(payoff 2 > 1). Knowing this, Player 0's best move at stage 1 is
*take* (payoff 1 > 0). So the subgame-perfect outcome is
`p0Takes` with payoff vector `(1, 0)` — the social welfare
maximum `(3, 1)` is left on the table, the canonical paradox. -/

/-- The two-player information structure for the centipede: each
player has a single info set, both with binary action arity. -/
def twoPlayerInfo : InfoStructure where
  n := 2
  Infoset := fun _ => PUnit
  arity := fun _ _ => 2
  arity_pos := by intro _ _; exact Nat.succ_pos 1

/-- Player 0 in `twoPlayerInfo`. -/
def cent_p0 : twoPlayerInfo.Player := ⟨0, by decide⟩

/-- Player 1 in `twoPlayerInfo`. -/
def cent_p1 : twoPlayerInfo.Player := ⟨1, by decide⟩

/-- Three terminal outcomes of the centipede. -/
inductive CentipedeOutcome where
  | p0Takes
  | p1Takes
  | p1Passes
deriving DecidableEq, Repr

/-- The centipede tree: Player 0 decides take/pass at the root; on
*pass*, Player 1 then decides take/pass, with a deterministic
terminal at each leaf. Action `0` is *take*, action `1` is *pass*. -/
def centipedeTree : GameTree twoPlayerInfo CentipedeOutcome :=
  .decision (p := cent_p0) PUnit.unit (fun a =>
    if a.1 = 0 then .terminal CentipedeOutcome.p0Takes
    else
      .decision (p := cent_p1) PUnit.unit (fun b =>
        if b.1 = 0 then .terminal CentipedeOutcome.p1Takes
        else .terminal CentipedeOutcome.p1Passes))

/-- The 2-stage centipede game with the classical payoffs. -/
def centipede : EFGGame where
  inf := twoPlayerInfo
  Outcome := CentipedeOutcome
  tree := centipedeTree
  utility := fun o p =>
    match o, p.val with
    | CentipedeOutcome.p0Takes,  0 => 1
    | CentipedeOutcome.p0Takes,  _ => 0
    | CentipedeOutcome.p1Takes,  0 => 0
    | CentipedeOutcome.p1Takes,  _ => 2
    | CentipedeOutcome.p1Passes, 0 => 3
    | CentipedeOutcome.p1Passes, _ => 1

/-- A pure strategy profile in `centipede` is a pair of `PUnit → Fin 2`
choices (one per player). The constructor below picks action `a0` for
player 0 and action `a1` for player 1. Actions follow the convention
`0 = take`, `1 = pass`. -/
def centipedeProfile (a0 a1 : Fin 2) : PureProfile twoPlayerInfo :=
  fun p _ =>
    if p.val = 0 then a0 else a1

/-- If player 0 *takes*, the game ends at `p0Takes` regardless of what
player 1 would have done. -/
theorem centipede_eval_take_take :
    centipedeTree.evalPure (centipedeProfile 0 0) = CentipedeOutcome.p0Takes := rfl

theorem centipede_eval_take_pass :
    centipedeTree.evalPure (centipedeProfile 0 1) = CentipedeOutcome.p0Takes := rfl

/-- If player 0 *passes* and player 1 *takes*, the outcome is `p1Takes`. -/
theorem centipede_eval_pass_take :
    centipedeTree.evalPure (centipedeProfile 1 0) = CentipedeOutcome.p1Takes := rfl

/-- If both players *pass*, the outcome is `p1Passes` and the
welfare-maximum `(3, 1)` is realized. -/
theorem centipede_eval_pass_pass :
    centipedeTree.evalPure (centipedeProfile 1 1) = CentipedeOutcome.p1Passes := rfl

/-- Player 1, faced with the choice at stage 2, strictly prefers `take`
to `pass` (payoff `2` vs `1`); this is the inductive base case for the
backward-induction prediction. -/
theorem centipede_p1_prefers_take :
    centipede.utility CentipedeOutcome.p1Takes cent_p1 >
    centipede.utility CentipedeOutcome.p1Passes cent_p1 := by
  simp [centipede, cent_p1]

/-- Knowing player 1 will take at stage 2, player 0 strictly prefers
taking at stage 1 (payoff `1` for `p0Takes` vs `0` for `p1Takes`). -/
theorem centipede_p0_prefers_take_given_p1_takes :
    centipede.utility CentipedeOutcome.p0Takes cent_p0 >
    centipede.utility CentipedeOutcome.p1Takes cent_p0 := by
  simp [centipede, cent_p0]

/-! ## Ultimatum game (3-action proposer, accept/reject responder)

Güth, Schmittberger & Schwarze (1982): one player (proposer) offers a
split of a fixed pie; the other (responder) either accepts (the split
happens) or rejects (both get 0). Backward induction predicts the
proposer keeps almost everything, since the responder weakly prefers
any non-negative offer to nothing.

We give the proposer three coarse offers — keepAll, half, giveAll —
so the responder has three distinct decision points. Each subtree is a
binary accept/reject choice for the responder. -/

/-- Information structure for the ultimatum game:\ both players use
`Fin 3` as their infoset type (the same shape across players keeps
Fintype synthesis cheap). The proposer's arity is 3 at every infoset
(but only one is actually reached), and the responder's arity is 2
(accept/reject). -/
def ultimatumInfo : InfoStructure where
  n := 2
  Infoset := fun _ => Fin 3
  arity := fun p _ => if p.val = 0 then 3 else 2
  arity_pos := by intro p _; split_ifs <;> decide

def ult_p0 : ultimatumInfo.Player := ⟨0, by decide⟩
def ult_p1 : ultimatumInfo.Player := ⟨1, by decide⟩

/-- Outcomes of the ultimatum game: each of three offers paired with
accept/reject. -/
inductive UltimatumOutcome where
  | keepAllAccept | keepAllReject
  | halfAccept    | halfReject
  | giveAllAccept | giveAllReject
deriving DecidableEq, Repr

/-- The ultimatum tree:\ proposer (at infoset 0) chooses one of three
offers; in each case the responder (at the corresponding infoset)
chooses accept (action 0) or reject (action 1). -/
def ultimatumTree : GameTree ultimatumInfo UltimatumOutcome :=
  .decision (p := ult_p0) (0 : Fin 3)
    (fun a =>
      .decision (p := ult_p1) (a : Fin 3)
        (fun b =>
          match a.val, b.val with
          | 0, 0 => .terminal UltimatumOutcome.keepAllAccept
          | 0, _ => .terminal UltimatumOutcome.keepAllReject
          | 1, 0 => .terminal UltimatumOutcome.halfAccept
          | 1, _ => .terminal UltimatumOutcome.halfReject
          | 2, 0 => .terminal UltimatumOutcome.giveAllAccept
          | 2, _ => .terminal UltimatumOutcome.giveAllReject
          | _, _ => .terminal UltimatumOutcome.keepAllReject))

/-- The ultimatum game: proposer offers, responder accepts/rejects.
Accept payoffs follow the offer; reject gives (0, 0). -/
def ultimatum : EFGGame where
  inf := ultimatumInfo
  Outcome := UltimatumOutcome
  tree := ultimatumTree
  utility := fun o p =>
    match o, p.val with
    -- proposer (p.val = 0):
    | UltimatumOutcome.keepAllAccept,  0 => 10
    | UltimatumOutcome.keepAllReject,  0 => 0
    | UltimatumOutcome.halfAccept,     0 => 5
    | UltimatumOutcome.halfReject,     0 => 0
    | UltimatumOutcome.giveAllAccept,  0 => 0
    | UltimatumOutcome.giveAllReject,  0 => 0
    -- responder (p.val ≠ 0):
    | UltimatumOutcome.keepAllAccept,  _ => 0
    | UltimatumOutcome.keepAllReject,  _ => 0
    | UltimatumOutcome.halfAccept,     _ => 5
    | UltimatumOutcome.halfReject,     _ => 0
    | UltimatumOutcome.giveAllAccept,  _ => 10
    | UltimatumOutcome.giveAllReject,  _ => 0

/-- The responder weakly prefers to accept any non-negative offer.
For the *half* offer this is strict (5 > 0); for `keepAll` the
responder is indifferent (both 0 = 0), illustrating the textbook
subtlety that the SPE relies on tie-breaking. -/
theorem ultimatum_responder_strict_half :
    ultimatum.utility UltimatumOutcome.halfAccept ult_p1 >
    ultimatum.utility UltimatumOutcome.halfReject ult_p1 := by
  simp [ultimatum, ult_p1]

theorem ultimatum_responder_strict_giveAll :
    ultimatum.utility UltimatumOutcome.giveAllAccept ult_p1 >
    ultimatum.utility UltimatumOutcome.giveAllReject ult_p1 := by
  simp [ultimatum, ult_p1]

/-- Conditional on acceptance, the proposer strictly prefers
`keepAll` to `half`, and `half` to `giveAll` — the SPE-driving
backward-induction inequalities. -/
theorem ultimatum_proposer_prefers_keepAll :
    ultimatum.utility UltimatumOutcome.keepAllAccept ult_p0 >
    ultimatum.utility UltimatumOutcome.halfAccept ult_p0 ∧
    ultimatum.utility UltimatumOutcome.halfAccept ult_p0 >
    ultimatum.utility UltimatumOutcome.giveAllAccept ult_p0 := by
  refine ⟨?_, ?_⟩
  · simp [ultimatum, ult_p0]; norm_num
  · simp [ultimatum, ult_p0]

end GameTheory.EFG.Examples
