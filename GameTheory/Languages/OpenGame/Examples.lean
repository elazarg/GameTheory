/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Theorems

/-!
# Open-Game Examples

Prisoner's Dilemma illustrates context-indexed Nash recovery for the closed
simultaneous shape.  `false` denotes cooperation and `true` defection.
-/

namespace OpenGames.Examples

/-- Standard Prisoner's Dilemma utility pair. -/
def prisonersDilemmaPayoff : Bool × Bool → ℝ × ℝ
  | (false, false) => (3, 3)
  | (false, true) => (0, 5)
  | (true, false) => (5, 0)
  | (true, true) => (1, 1)

/-- Utility profile used as the closing continuation. -/
def prisonersDilemmaUtility (a : Bool → Bool) (i : Bool) : ℝ :=
  if i then (prisonersDilemmaPayoff (a false, a true)).2
  else (prisonersDilemmaPayoff (a false, a true)).1

/-- A closed, two-player simultaneous Prisoner's Dilemma. -/
def prisonersDilemma :
    OpenGame (Bool → Unit) (Bool → Unit) (Bool → Bool) (Bool → ℝ) :=
  ShapeN (fun _i : Bool => Unit) (fun _i : Bool => Bool)

/-- The constant contingent plan selecting action `a`. -/
def constantClosedStrategy (a : Bool) : Bool → Unit → Bool :=
  fun _i _u => a

/-- Mutual defection is selected compositionally. -/
theorem defect_is_equilibrium :
    prisonersDilemma.IsEquilibriumIn (fun _i => ())
      prisonersDilemmaUtility (constantClosedStrategy true) := by
  simp [prisonersDilemma, ShapeN, prisonersDilemmaUtility,
    prisonersDilemmaPayoff, constantClosedStrategy, Function.update]

/-- Mutual cooperation is not an equilibrium: either player can defect. -/
theorem cooperate_not_equilibrium :
    ¬prisonersDilemma.IsEquilibriumIn (fun _i => ())
      prisonersDilemmaUtility (constantClosedStrategy false) := by
  simp [prisonersDilemma, ShapeN, prisonersDilemmaUtility,
    prisonersDilemmaPayoff, constantClosedStrategy, Function.update]
  norm_num

/-- The compositional result is exactly the kernel-level Nash statement. -/
theorem defect_is_kernelNash :
    (ShapeN.compileAction (fun _i : Bool => Bool) prisonersDilemmaUtility).IsNash
      (fun _i => true) := by
  have hn := (ShapeN.closed_isEquilibriumIn_iff_isNash
    prisonersDilemmaUtility (constantClosedStrategy true)).mp
      defect_is_equilibrium
  simpa [ShapeN.closedStrategyEquiv, constantClosedStrategy] using hn

/-! ## Entry deterrence and non-credible threats -/

/-- Entry-deterrence payoffs.  For the leader, `false` is Out and `true` is
Enter.  For the follower, `false` is Accommodate and `true` is Fight. -/
def entryDeterrencePayoff : Bool × Bool → ℝ × ℝ
  | (false, false) => (1, 1)
  | (false, true) => (1, 1)
  | (true, false) => (2, 2)
  | (true, true) => (0, 0)

/-- The non-credible deterrence profile: stay out, with a contingent threat to
fight. -/
def deterrenceThreat : Bool × (Bool → Bool) :=
  (false, fun _entry => true)

/-- The threat is a plain sequential equilibrium. -/
theorem deterrenceThreat_is_plainEquilibrium :
    (ShapeS Bool Bool).IsEquilibriumIn () entryDeterrencePayoff
      deterrenceThreat := by
  simp [ShapeS, entryDeterrencePayoff, deterrenceThreat]

/-- The same profile fails the conditioned predicate because fighting after
entry is not optimal. -/
theorem deterrenceThreat_not_subgamePerfect :
    ¬ShapeS.IsSubgamePerfect entryDeterrencePayoff deterrenceThreat := by
  simp [ShapeS.IsSubgamePerfect, entryDeterrencePayoff, deterrenceThreat]

/-- Enter followed by accommodation is subgame perfect (the off-path Out
subgame leaves the follower indifferent). -/
def entryAccommodation : Bool × (Bool → Bool) :=
  (true, fun _entry => false)

theorem entryAccommodation_is_subgamePerfect :
    ShapeS.IsSubgamePerfect entryDeterrencePayoff entryAccommodation := by
  simp [ShapeS.IsSubgamePerfect, entryDeterrencePayoff, entryAccommodation]

/-- The non-credible threat is nevertheless Nash in the compiled sequential
strategic form. -/
theorem deterrenceThreat_is_kernelNash :
    (ShapeS.compileAction Bool Bool entryDeterrencePayoff).IsNash
      (ShapeS.toProfile deterrenceThreat) :=
  (ShapeS.isEquilibriumIn_iff_isNash entryDeterrencePayoff deterrenceThreat).mp
    deterrenceThreat_is_plainEquilibrium

end OpenGames.Examples
