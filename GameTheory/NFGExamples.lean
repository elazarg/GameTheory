import GameTheory.NFG
import Mathlib.Tactic.Linarith

/-!
# Normal-Form Game Examples

Prisoner's Dilemma and Matching Pennies with Nash equilibrium proofs.
-/

namespace NFG

/-! ## Prisoner's Dilemma -/

/-- Actions in the Prisoner's Dilemma. -/
inductive PDAction where
  | cooperate
  | defect
deriving DecidableEq, Repr

instance : Fintype PDAction where
  elems := {PDAction.cooperate, PDAction.defect}
  complete x := by cases x <;> simp

open PDAction in
/-- The Prisoner's Dilemma game.
  Payoff matrix:
  - (D,D) = (1,1), (C,D) = (0,3), (D,C) = (3,0), (C,C) = (2,2) -/
def prisonersDilemma : NFGame Bool (fun _ => PDAction) where
  utility s p :=
    match s true, s false, p with
    | defect,    defect,    true  => 1
    | cooperate, defect,    true  => 0
    | defect,    cooperate, true  => 3
    | cooperate, cooperate, true  => 2
    | defect,    defect,    false => 1
    | cooperate, defect,    false => 3
    | defect,    cooperate, false => 0
    | cooperate, cooperate, false => 2

/-- The profile where both players defect. -/
def pd_defect_defect : StrategyProfile (fun _ : Bool => PDAction) :=
  fun _ => PDAction.defect

/-- (Defect, Defect) is a Nash equilibrium of the Prisoner's Dilemma. -/
theorem pd_defect_is_nash : IsNashPure prisonersDilemma pd_defect_defect := by
  intro i a'
  cases i <;> cases a' <;>
    simp [prisonersDilemma, pd_defect_defect, deviate, Function.update]

/-- The profile where both players cooperate. -/
def pd_coop_coop : StrategyProfile (fun _ : Bool => PDAction) :=
  fun _ => PDAction.cooperate

/-- (Cooperate, Cooperate) is NOT a Nash equilibrium. -/
theorem pd_coop_not_nash : ¬ IsNashPure prisonersDilemma pd_coop_coop := by
  intro h
  have h1 := h true PDAction.defect
  unfold IsNashPure prisonersDilemma pd_coop_coop deviate at h1
  simp [Function.update] at h1
  linarith

/-! ## Matching Pennies -/

/-- Actions in Matching Pennies. -/
inductive MPAction where
  | heads
  | tails
deriving DecidableEq, Repr

instance : Fintype MPAction where
  elems := {MPAction.heads, MPAction.tails}
  complete x := by cases x <;> simp

open MPAction in
/-- Matching Pennies game.
  Payoff matrix:
  - (H,H) = (1,-1), (H,T) = (-1,1), (T,H) = (-1,1), (T,T) = (1,-1) -/
def matchingPennies : NFGame Bool (fun _ => MPAction) where
  utility s p :=
    match s true, s false, p with
    | heads, heads, true  =>  1
    | heads, tails, true  => -1
    | tails, heads, true  => -1
    | tails, tails, true  =>  1
    | heads, heads, false => -1
    | heads, tails, false =>  1
    | tails, heads, false =>  1
    | tails, tails, false => -1

/-- Matching Pennies has no pure Nash equilibrium. -/
theorem matchingPennies_no_pure_nash :
    ∀ s : StrategyProfile (fun _ : Bool => MPAction), ¬ IsNashPure matchingPennies s := by
  intro s h
  have e1 : s true = MPAction.heads ∨ s true = MPAction.tails := by cases s true <;> simp
  have e2 : s false = MPAction.heads ∨ s false = MPAction.tails := by cases s false <;> simp
  rcases e1 with hs1 | hs1 <;> rcases e2 with hs2 | hs2
  · have := h false MPAction.tails
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h true MPAction.tails
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h true MPAction.heads
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h false MPAction.heads
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith

end NFG
