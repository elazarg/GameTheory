/-
# EXP-042 hostile one-shot witness

Two players move simultaneously. Changing the column player's current action
changes the terminal outcome but cannot change the row player's initial policy
input or action.
-/

import GameTheory.Languages.Bridges.NFGFOSG

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.NFGFOSGTest

open GameTheory GameTheory.Languages GameTheory.Math.Probability
open GameTheory.Languages.NFG.OneShotFOSG

inductive Player
  | row
  | column
  deriving DecidableEq

/-- The outcome records both simultaneous actions, so neither coordinate is
semantically inert. -/
def game : NFG.Game Player where
  Action _ := Bool
  Outcome := Bool × Bool
  outcome profile := (profile .row, profile .column)

local instance gameActionNonempty : ∀ i, Nonempty (game.Action i) :=
  fun _ => ⟨false⟩

def allFalse : Profile game.signature
  | .row => false
  | .column => false

def columnTrue : Profile game.signature
  | .row => false
  | .column => true

/-- Both real source players act at the same initial state. -/
theorem simultaneous_initial :
    (execution game).active .initial .row ∧
      (execution game).active .initial .column :=
  ⟨active_initial game .row, active_initial game .column⟩

/-- The row player receives only the phase-local acting view. -/
theorem row_initial_view :
    (informationModel game).infoOf Player.row
        (execution game).initHistory.trace =
      (.acting : View Player.row) := rfl

/-- Changing the column player's current action does not change what the row
player does at its information state. -/
theorem row_policy_hides_column :
    (policyProfile game allFalse Player.row).act
        (.acting : View Player.row) =
      (policyProfile game columnTrue Player.row).act
        (.acting : View Player.row) := rfl

/-- The hidden current coordinate still changes the realized terminal
outcome, so the locality test is not vacuous. -/
theorem hostile_target_law :
    (toProtocolForm game).play (policyProfile game columnTrue) =
      FinDist.pure (some (false, true)) := by
  rw [toProtocolForm_play_policyProfile]
  simp [NFG.Game.toGameForm, game, columnTrue]

/-- Utility preservation is non-vacuous for both source players. -/
def utility : game.Outcome → Player → ℝ
  | outcome, .row => if outcome.1 then 1 else 0
  | outcome, .column => if outcome.2 then 1 else 0

theorem hostile_utility_law :
    ((toProtocolForm game).play (policyProfile game columnTrue)).map
        (utilityOfOutcome game utility) =
      (game.toGameForm.play columnTrue).map utility :=
  toProtocolForm_utilityLaw_policyProfile game utility columnTrue

end GameTheory.Experimental.PostArchitecture.NFGFOSGTest
