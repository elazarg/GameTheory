/-
# Action-dependent stochastic restart fixture

The first action changes the next state, and the second action depends on the
observed first-stage record.  The test consumes the public-policy compiler and
the generic restart identity; it defines no runner or local payoff semantics.
-/

import GameTheory.Stochastic.History
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Tests.StochasticContinuation

open GameTheory.Math.Probability Stochastic Protocol Protocol.ExecutionProtocol
open Stochastic.Game

/-- Two players, two states, and a transition controlled by player `false`'s
action.  The fixture fails if action data is erased during restart. -/
@[reducible]
def actionGame : Stochastic.Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition _ actions := PMF.pure (actions false)
  stageUtility state actions who :=
    if who then 0 else if state = actions false then 1 else 0

local instance actionNonempty : ∀ i, Nonempty (actionGame.Action i) :=
  fun _ => ⟨false⟩

def firstActions : ∀ i, actionGame.Action i :=
  fun who => if who then false else true

def secondActions : ∀ i, actionGame.Action i := fun _ => false

/-- Changing player `false`'s action changes the next-state law. -/
theorem transition_really_action_dependent :
    actionGame.transition false firstActions ≠
      actionGame.transition false secondActions := by
  intro hequal
  have hprob := congrArg (fun law : PMF Bool => law true) hequal
  norm_num [actionGame, firstActions, secondActions,
    PMF.pure_apply] at hprob

/-- At the empty history player `false` chooses `true`; after any observed
stage both players choose `false`. -/
def publicProfile : PublicProfile actionGame false :=
  fun who history => PMF.pure <|
    if who then false
    else match history with
      | [] => true
      | _ :: _ => false

def canonicalProfile : actionGame.BehaviorProfile false :=
  toBehaviorProfile actionGame false publicProfile

def firstRecord : actionGame.StageRecord where
  source := false
  joint := firstActions
  target := true

def secondRecord : actionGame.StageRecord where
  source := true
  joint := secondActions
  target := false

theorem firstRealized :
    true ∈ (actionGame.transition false firstActions).support := by
  simp [actionGame, firstActions]

/-- The canonical realized history after the action-dependent first step. -/
def firstHistory : (actionGame.toExecution false).History :=
  (actionGame.toExecution false).initHistory.extend
    (canonicalJoint actionGame false false firstActions).2
    (canonicalRealized actionGame false firstRealized)

@[simp]
theorem publicHistoryOfTrace_firstHistory :
    actionGame.publicHistoryOfTrace false firstHistory.trace = [firstRecord] := by
  unfold firstHistory
  simp only [History.extend, Game.publicHistoryOfTrace,
    ExecutionProtocol.initHistory]
  apply congrArg (fun record => [record])
  rfl

theorem publicProfile_after_first (who : Bool) :
    publicProfile who [firstRecord] = PMF.pure (secondActions who) := by
  cases who <;> rfl

theorem publicProfile_initial (who : Bool) :
    publicProfile who [] = PMF.pure (firstActions who) := by
  cases who <;> rfl

/-- Restarting after the first realized record selects the second-stage action
and hence the second target. -/
theorem restart_one_step :
    actionGame.restartHistoryLaw canonicalProfile [firstRecord] true 1 =
      PMF.pure [secondRecord] := by
  unfold canonicalProfile
  rw [actionGame.restartHistoryLaw_succ_toPublicProfile
    publicProfile [firstRecord] true 0]
  simp_rw [publicProfile_after_first]
  rw [independentProduct_pure secondActions, PMF.pure_bind]
  simp [actionGame, Game.restartHistoryLaw_zero, PMF.map,
    secondRecord, secondActions]

/-- The source-facing horizon decomposition computes the full action-dependent
two-stage law without exposing canonical traces. -/
theorem publicHistoryLaw_two_steps :
    actionGame.publicHistoryLaw false canonicalProfile 2 =
      PMF.pure [secondRecord, firstRecord] := by
  have hrestart :
      actionGame.restartHistoryLaw canonicalProfile [] false 2 =
        PMF.pure [secondRecord, firstRecord] := by
    unfold canonicalProfile
    rw [actionGame.restartHistoryLaw_succ_toPublicProfile
      publicProfile [] false 1]
    simp_rw [publicProfile_initial]
    rw [independentProduct_pure firstActions, PMF.pure_bind]
    simp only [actionGame, PMF.pure_bindOnSupport]
    have hrestarted := congrArg
      (PMF.map (fun continuation => continuation ++ [firstRecord]))
      restart_one_step
    simpa [firstActions, firstRecord, canonicalProfile, PMF.map] using hrestarted
  simpa only [Game.restartHistoryLaw, Game.afterPublicHistory_nil] using hrestart

/-- The fixed `Fin 2` chronological law maps back to that exact public law. -/
theorem chronologicalHistoryLaw_two_steps :
    PMF.map actionGame.publicHistoryOfChronological
        (actionGame.chronologicalHistoryLaw false canonicalProfile 2) =
      PMF.pure [secondRecord, firstRecord] := by
  rw [actionGame.map_publicHistoryOfChronological_chronologicalHistoryLaw,
    publicHistoryLaw_two_steps]

set_option backward.isDefEq.respectTransparency false in
/-- The arbitrary-horizon restart theorem reconstructs the complete two-stage
history in the monitoring convention. -/
theorem continuation_from_first_one_step :
    actionGame.publicHistoryLawFrom false canonicalProfile 1 firstHistory =
      PMF.pure [secondRecord, firstRecord] := by
  rw [actionGame.publicHistoryLawFrom_eq_restartedFullHistoryLaw
    canonicalProfile firstHistory 1]
  rw [publicHistoryOfTrace_firstHistory]
  unfold Game.restartedFullHistoryLaw
  have hrestarted := congrArg
    (PMF.map (actionGame.splicePrefix [firstRecord])) restart_one_step
  simpa [firstHistory, Game.splicePrefix, PMF.map] using hrestarted

end GameTheory.Tests.StochasticContinuation
