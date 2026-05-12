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

end GameTheory.EFG.Examples
