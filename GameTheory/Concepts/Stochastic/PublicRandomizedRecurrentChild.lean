/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicRecurrentClassTarget
import Math.OutcomeClosure
import Math.OutcomeClosure.TerminalTarget

/-!
# Randomized recurrent children and the deviation interface

A finite stopped process can preserve a whole payoff-vector target in
expectation while selecting among lower-rank terminal children.  The
distributional statement follows directly from `OutcomeClosure.ValueProcess`.

That fact is not, by itself, a recurrent-child constructor for a public
equilibrium recursion.  The selection process must preserve the appropriate
continuation ceiling after every unilateral deviation, not merely its
expectation under prescribed play.  The one-player example below is the
smallest obstruction: prescribed public randomization selects absorbing
payoffs zero and one with mean one half, while the player can select payoff
one with certainty.

Thus randomized target preservation can replace pointwise target
preservation only after a strategic stopped-process lemma supplies:

* prescribed lower and upper continuation martingales;
* a continuation supermartingale under every unilateral deviation;
* public observability of the terminal child; and
* history rebasing of each child's public-phase certificate after the
  stopping history.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- A one-step public state draw whose kernel is independent of the joint
action has the same continuation law under every behavior profile.

Iterating this identity through a finite stopped selection region makes its
terminal public-child law invariant under unilateral deviations.  This is
the concrete public-coin condition missing from the counterexample below. -/
theorem historyContinuationEU_statePotential_eq_of_actionIndependent
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (V : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) (kernel : PMF G.State)
    (actionIndependent :
      ∀ action : G.JointAct,
        G.transition history.2 action = kernel) :
    G.historyContinuationEU σ
        (fun _ next => V next.2) history =
      expect kernel V := by
  unfold historyContinuationEU
  calc
    expect (G.stageActionDist σ history)
        (fun action =>
          expect (G.transition history.2 action) V) =
      expect (G.stageActionDist σ history)
        (fun _ => expect kernel V) := by
          apply congrArg (expect (G.stageActionDist σ history))
          funext action
          rw [actionIndependent action]
    _ = expect kernel V := expect_const _ _

/-- Consequently an action-independent public draw gives identical
state-continuation values under any two profiles, including after a
unilateral deviation. -/
theorem historyContinuationEU_statePotential_profileIndependent
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ τ : G.BehaviorProfile) (V : G.State → ℝ)
    {t : ℕ} (history : G.Hist t) (kernel : PMF G.State)
    (actionIndependent :
      ∀ action : G.JointAct,
        G.transition history.2 action = kernel) :
    G.historyContinuationEU σ
        (fun _ next => V next.2) history =
      G.historyContinuationEU τ
        (fun _ next => V next.2) history := by
  rw [
    G.historyContinuationEU_statePotential_eq_of_actionIndependent
      σ V history kernel actionIndependent,
    G.historyContinuationEU_statePotential_eq_of_actionIndependent
      τ V history kernel actionIndependent
  ]

namespace PlayerControlledPublicMixtureObstruction

abbrev Player := Unit

inductive State
  | start
  | low
  | high
  deriving DecidableEq, Fintype

abbrev Action := Bool

/-- At the initial state the only player publicly selects one of two
absorbing states.  The selected action and the next state both enter the
public history. -/
abbrev game : StochasticGame Player where
  State := State
  Act := fun _ => Action
  stagePayoff := fun state action _ =>
    match state with
    | .start => if action () then 1 else 0
    | .low => 0
    | .high => 1
  transition := fun state action =>
    match state with
    | .start => PMF.pure (if action () then .high else .low)
    | .low => PMF.pure .low
    | .high => PMF.pure .high
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

instance : Fintype game.State :=
  inferInstanceAs (Fintype State)

instance : DecidableEq game.State :=
  inferInstanceAs (DecidableEq State)

instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Action)

instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Action)

/-- Prescribed play uses a fair public selection at every history. -/
def prescribedProfile : game.BehaviorProfile :=
  fun _ _ _ => PMF.uniformOfFintype Bool

/-- The player can instead select the high absorbing child with certainty. -/
def highDeviation : game.BehaviorStrategy () :=
  fun _ _ => PMF.pure true

/-- The terminal continuation payoff, with the prescribed mean assigned to
the initial state. -/
def continuationTarget : State → ℝ
  | .start => 1 / 2
  | .low => 0
  | .high => 1

private theorem expect_jointAction_eq_coord
    (σ : ∀ _ : Player, PMF Action) (f : Action → ℝ) :
    expect (pmfPi σ) (fun action => f (action ())) =
      expect (σ ()) f := by
  calc
    expect (pmfPi σ) (fun action => f (action ())) =
      expect (PMF.map (fun action => action ()) (pmfPi σ)) f := by
        symm
        exact expect_map (fun action => action ()) (pmfPi σ) f
    _ = expect (σ ()) f := by
      have h := pmfPi_push_coord σ ()
      change PMF.map (fun action => action ()) (pmfPi σ) = σ () at h
      rw [h]

/-- The prescribed public selection preserves the parent target in
expectation. -/
theorem prescribed_target_preserved :
    game.historyContinuationEU prescribedProfile
        (fun _ history => continuationTarget history.2)
        (game.emptyHist .start) =
      continuationTarget .start := by
  unfold historyContinuationEU stageActionDist prescribedProfile
  simp only [emptyHist, game, expect_pure]
  rw [show
    (fun action : Player → Action =>
      continuationTarget
        (if action () then State.high else State.low)) =
      (fun action => if action () then 1 else 0) by
        funext action
        cases action () <;> simp [continuationTarget]]
  have hcoord :=
    expect_jointAction_eq_coord
      (fun _ : Player => PMF.uniformOfFintype Bool)
      (fun selected => if selected then 1 else 0)
  rw [hcoord]
  norm_num [expect, PMF.uniformOfFintype_apply, tsum_fintype,
    continuationTarget]

/-- A unilateral deviation changes the public child law and raises the
continuation target from one half to one. -/
theorem deviating_target_strictly_increases :
    game.historyContinuationEU
        (Function.update prescribedProfile () highDeviation)
        (fun _ history => continuationTarget history.2)
        (game.emptyHist .start) =
      1 := by
  unfold historyContinuationEU stageActionDist highDeviation
  simp only [Function.update_self, emptyHist, game, expect_pure]
  rw [show
    (fun action : Player → Action =>
      continuationTarget
        (if action () then State.high else State.low)) =
      (fun action => if action () then 1 else 0) by
        funext action
        cases action () <;> simp [continuationTarget]]
  have hcoord :=
    expect_jointAction_eq_coord
      (fun _ : Player => PMF.pure true)
      (fun selected => if selected then 1 else 0)
  rw [hcoord]
  simp

/-- Expected target preservation under prescribed play does not imply the
deviation-supermartingale inequality needed to splice public-phase
certificates. -/
theorem prescribed_preservation_but_deviation_ceiling_fails :
    game.historyContinuationEU prescribedProfile
        (fun _ history => continuationTarget history.2)
        (game.emptyHist .start) =
        continuationTarget .start ∧
      ¬game.historyContinuationEU
          (Function.update prescribedProfile () highDeviation)
          (fun _ history => continuationTarget history.2)
          (game.emptyHist .start) ≤
        continuationTarget .start := by
  rw [prescribed_target_preserved, deviating_target_strictly_increases]
  norm_num [continuationTarget]

/-- The phase used for the two absorbing child certificates records only the
public current state. -/
def childPhaseProfile : PublicPhaseProfile game where
  Phase := State
  phase := fun _ history => history.2
  play := fun _ _ => PMF.uniformOfFintype Bool

/-- A deviation ceiling that agrees with each absorbing child's target but
dominates the player-controlled selection at the initial state. -/
def deviationCeiling : State → ℝ
  | .start => 1
  | .low => 0
  | .high => 1

private theorem prescribed_stage_eq_target
    (t : ℕ) (history : game.Hist t) :
    game.stageEUAt prescribedProfile history () =
      continuationTarget history.2 := by
  cases hstate : history.2 with
  | start =>
      unfold stageEUAt stageActionDist prescribedProfile
      rw [hstate]
      change
        expect (pmfPi
          (fun _ : Player => PMF.uniformOfFintype Bool))
            (fun action => if action () then 1 else 0) =
          1 / 2
      have hcoord :=
        expect_jointAction_eq_coord
          (fun _ : Player => PMF.uniformOfFintype Bool)
          (fun selected => if selected then 1 else 0)
      rw [hcoord]
      norm_num [expect, PMF.uniformOfFintype_apply, tsum_fintype,
        continuationTarget]
  | low =>
      simp [stageEUAt, stageActionDist, prescribedProfile, game,
        hstate, continuationTarget]
  | high =>
      simp [stageEUAt, stageActionDist, prescribedProfile, game,
        hstate, continuationTarget]

private theorem prescribed_continuation_eq_target
    (t : ℕ) (history : game.Hist t) :
    game.historyContinuationEU prescribedProfile
        (fun _ next => continuationTarget next.2) history =
      continuationTarget history.2 := by
  cases hstate : history.2 with
  | start =>
      unfold historyContinuationEU stageActionDist prescribedProfile
      simp only [game, hstate, expect_pure]
      have hcoord :=
        expect_jointAction_eq_coord
          (fun _ : Player => PMF.uniformOfFintype Bool)
          (fun selected => if selected then 1 else 0)
      rw [show
        (fun action : Player → Action =>
          continuationTarget
            (if action () then State.high else State.low)) =
        (fun action => if action () then 1 else 0) by
          funext action
          cases action () <;> simp [continuationTarget]]
      rw [hcoord]
      norm_num [expect, PMF.uniformOfFintype_apply, tsum_fintype,
        continuationTarget]
  | low =>
      simp [historyContinuationEU, stageActionDist, prescribedProfile,
        game, hstate, continuationTarget]
  | high =>
      simp [historyContinuationEU, stageActionDist, prescribedProfile,
        game, hstate, continuationTarget]

private theorem deviation_stage_le_ceiling
    (dev : game.BehaviorStrategy ()) (t : ℕ)
    (history : game.Hist t) :
    game.stageEUAt
        (Function.update prescribedProfile () dev) history () ≤
      deviationCeiling history.2 := by
  cases hstate : history.2 with
  | start =>
      unfold stageEUAt stageActionDist
      simp only [Function.update_self, game, hstate, deviationCeiling]
      calc
        expect (pmfPi fun _ : Player => dev t history)
            (fun action => if action () then 1 else 0) ≤
          expect (pmfPi fun _ : Player => dev t history)
            (fun _ => 1) := by
              apply expect_mono
              intro action
              cases action () <;> norm_num
        _ = 1 := expect_const _ _
  | low =>
      simp [stageEUAt, stageActionDist, game, hstate,
        deviationCeiling]
  | high =>
      simp [stageEUAt, stageActionDist, game, hstate,
        deviationCeiling]

private theorem deviation_continuation_le_ceiling
    (dev : game.BehaviorStrategy ()) (t : ℕ)
    (history : game.Hist t) :
    game.historyContinuationEU
        (Function.update prescribedProfile () dev)
        (fun _ next => deviationCeiling next.2) history ≤
      deviationCeiling history.2 := by
  cases hstate : history.2 with
  | start =>
      unfold historyContinuationEU stageActionDist
      simp only [Function.update_self, game, hstate, expect_pure,
        deviationCeiling]
      calc
        _ ≤
          expect (pmfPi fun _ : Player => dev t history)
            (fun _ => 1) := by
              apply expect_mono
              intro action
              cases action () <;> simp
        _ = 1 := expect_const _ _
  | low =>
      simp [historyContinuationEU, stageActionDist, game, hstate,
        deviationCeiling]
  | high =>
      simp [historyContinuationEU, stageActionDist, game, hstate,
        deviationCeiling]

/-- Each absorbing terminal child has an exact public-phase punishment
certificate at its own target. -/
def childPublicPhasePunishmentSystem
    (child : State) (hchild : child = .low ∨ child = .high) :
    PublicPhasePunishmentSystemAt game childPhaseProfile child
      (fun _ => continuationTarget child) 0 where
  horizon := 2
  lowerPotential := fun _ => continuationTarget
  upperPotential := fun _ => continuationTarget
  deviationPotential := fun _ => deviationCeiling
  lowerCharge := fun _ _ _ => 0
  upperCharge := fun _ _ _ => 0
  deviationCharge := fun _ _ _ _ => 0
  horizon_ge_two := le_rfl
  lower_initial := by
    intro who
    simp [childPhaseProfile, emptyHist]
  upper_initial := by
    intro who
    simp [childPhaseProfile, emptyHist]
  deviation_initial := by
    intro who
    rcases hchild with rfl | rfl <;>
      simp [childPhaseProfile, emptyHist, continuationTarget,
        deviationCeiling]
  lower_subharmonic := by
    intro who t history
    change continuationTarget history.2 ≤
      game.historyContinuationEU prescribedProfile
        (fun _ next => continuationTarget next.2) history
    exact le_of_eq (prescribed_continuation_eq_target t history).symm
  lower_stage := by
    intro who t history
    change continuationTarget history.2 ≤
      game.stageEUAt prescribedProfile history () + 0
    rw [prescribed_stage_eq_target]
    simp
  upper_superharmonic := by
    intro who t history
    change
      game.historyContinuationEU prescribedProfile
          (fun _ next => continuationTarget next.2) history ≤
        continuationTarget history.2
    exact le_of_eq (prescribed_continuation_eq_target t history)
  upper_stage := by
    intro who t history
    change game.stageEUAt prescribedProfile history () ≤
      continuationTarget history.2 + 0
    rw [prescribed_stage_eq_target]
    simp
  deviation_superharmonic := by
    intro who dev t history
    change
      game.historyContinuationEU
          (Function.update prescribedProfile () dev)
          (fun _ next => deviationCeiling next.2) history ≤
        deviationCeiling history.2
    exact deviation_continuation_le_ceiling dev t history
  deviation_stage := by
    intro who dev t history
    change
      game.stageEUAt
          (Function.update prescribedProfile () dev) history () ≤
        deviationCeiling history.2 + 0
    simpa using deviation_stage_le_ceiling dev t history
  lower_charge_cesaro := by
    intro who T hT
    simp [expectedHistoryValue]
  upper_charge_cesaro := by
    intro who T hT
    simp [expectedHistoryValue]
  deviation_charge_cesaro := by
    intro who dev T hT
    simp [expectedHistoryValue]

/-- Both terminal branches are therefore individually and exactly
certified. -/
theorem both_children_have_publicPhase_certificates :
    game.IsPublicPhasePunishmentSystemAt .low
        (fun _ => continuationTarget .low) 0 ∧
      game.IsPublicPhasePunishmentSystemAt .high
        (fun _ => continuationTarget .high) 0 := by
  constructor
  · exact ⟨childPhaseProfile,
      ⟨childPublicPhasePunishmentSystem .low (Or.inl rfl)⟩⟩
  · exact ⟨childPhaseProfile,
      ⟨childPublicPhasePunishmentSystem .high (Or.inr rfl)⟩⟩

end PlayerControlledPublicMixtureObstruction

end StochasticGame
end GameTheory
