/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFirstStageAdapter
import GameTheory.Concepts.Stochastic.QuittingSimpleBranches

/-!
# An exact local-to-global counterexample for quitting games

This file records a two-player quitting game in which a stationary profile
absorbs surely at the first stage and is exactly indifferent at its finite
root continuation game, but has terminal regret exactly one.  The player who
is prescribed to quit can instead continue forever and prevent absorption.

The example isolates why stagewise (even support-side) perfection does not by
itself imply a global terminal equilibrium: a local-to-global theorem needs a
stationary-equilibrium fallback.  Here that fallback is exact—the
all-continue profile is a terminal zero-equilibrium.

Only the finite root and behavior-profile claims are formalized.  No
absorption-path compactification or discretization theorem is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-! We use `false` for player one and `true` for player two. -/

/-- The payoff table

* `QC ↦ (-1, 0)`,
* `CQ ↦ (0, 0)`, and
* `QQ ↦ (-1, 0)`.
-/
def localGlobalCounterexampleReward
    (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if who = false ∧ false ∈ quitters.1 then -1 else 0

/-- The pure root action `QC`: player one quits and player two continues. -/
def localGlobalCounterexampleAction : Bool → Bool :=
  fun who => !who

/-- The pure mixed root corresponding to `QC`. -/
def localGlobalCounterexampleRoot : Bool → PMF Bool :=
  fun who => PMF.pure (localGlobalCounterexampleAction who)

/-- The continuation vector `(-1, 0)` used by the locally perfect root game. -/
def localGlobalCounterexampleContinuation : Payoff Bool :=
  fun who => if who = false then -1 else 0

/-- The supplied stationary behavior profile: player one always quits and
player two always continues. -/
def localGlobalCounterexampleProfile :
    (quittingGame localGlobalCounterexampleReward).BehaviorProfile :=
  Function.update
    (quittingAlwaysContinueProfile localGlobalCounterexampleReward)
    false
    (quittingAlwaysQuitStrategy localGlobalCounterexampleReward false)

/-- The supplied behavior profile really is the stationary profile generated
by its displayed root. -/
theorem localGlobalCounterexampleProfile_eq_stationary :
    localGlobalCounterexampleProfile =
      (quittingGame localGlobalCounterexampleReward).stationaryBehaviorProfile
        localGlobalCounterexampleRoot := by
  funext who t history
  cases who <;>
    simp [localGlobalCounterexampleProfile,
      localGlobalCounterexampleRoot, localGlobalCounterexampleAction,
      quittingAlwaysContinueProfile, quittingAlwaysQuitStrategy,
      StochasticGame.stationaryBehaviorProfile] <;> rfl

/-- The time-zero root extracted from the supplied stationary profile is the
pure action `QC`. -/
@[simp] theorem quittingProfileRoot_localGlobalCounterexampleProfile :
    quittingProfileRoot localGlobalCounterexampleReward
        localGlobalCounterexampleProfile =
      localGlobalCounterexampleRoot := by
  funext who
  cases who <;>
    simp [quittingProfileRoot, localGlobalCounterexampleProfile,
      localGlobalCounterexampleRoot, localGlobalCounterexampleAction,
      quittingAlwaysContinueProfile,
      quittingAlwaysQuitStrategy,
      StochasticGame.stationaryBehaviorProfile] <;> rfl

/-- The supplied stationary profile absorbs surely at its first stage. -/
theorem localGlobalCounterexampleProfile_absorbsSurelyAtFirstStage :
    QuittingProfileAbsorbsSurelyAtFirstStage
      localGlobalCounterexampleReward localGlobalCounterexampleProfile := by
  rw [quittingProfileAbsorbsSurelyAtFirstStage_iff_rootHasSureQuitter,
    quittingProfileRoot_localGlobalCounterexampleProfile]
  exact ⟨false, by
    simp [localGlobalCounterexampleRoot,
      localGlobalCounterexampleAction]⟩

/-- Every player receives the declared continuation value at the prescribed
pure root. -/
@[simp] theorem quittingRootExpectedPayoff_localGlobalCounterexampleRoot
    (who : Bool) :
    quittingRootExpectedPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleContinuation
        localGlobalCounterexampleRoot who =
      localGlobalCounterexampleContinuation who := by
  unfold quittingRootExpectedPayoff localGlobalCounterexampleRoot
  rw [pmfPi_pure, expect_pure]
  cases who <;>
    simp [quittingRootPayoff, quittingQuitters,
      localGlobalCounterexampleReward,
      localGlobalCounterexampleContinuation,
      localGlobalCounterexampleAction]

/-- At the continuation vector `(-1, 0)`, either pure root action gives every
player exactly its prescribed payoff.  Thus both actions—not merely the
supported one—are exact best replies. -/
theorem quittingRootExpectedPayoff_localGlobalCounterexample_pureDeviation
    (who move : Bool) :
    quittingRootExpectedPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleContinuation
        (Function.update localGlobalCounterexampleRoot who (PMF.pure move))
        who =
      quittingRootExpectedPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleContinuation
        localGlobalCounterexampleRoot who := by
  rw [quittingRootExpectedPayoff_localGlobalCounterexampleRoot]
  have hfamily :
      Function.update localGlobalCounterexampleRoot who (PMF.pure move) =
        fun player => PMF.pure
          (Function.update localGlobalCounterexampleAction who move player) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer,
        localGlobalCounterexampleRoot]
  unfold quittingRootExpectedPayoff
  rw [hfamily, pmfPi_pure, expect_pure]
  cases who <;> cases move <;>
    simp [quittingRootPayoff, quittingQuitters,
      localGlobalCounterexampleReward,
      localGlobalCounterexampleContinuation,
      localGlobalCounterexampleAction]

/-- Arbitrary mixed root deviations are indifferent as well. -/
theorem quittingRootExpectedPayoff_localGlobalCounterexample_deviation
    (who : Bool) (deviation : PMF Bool) :
    quittingRootExpectedPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleContinuation
        (Function.update localGlobalCounterexampleRoot who deviation) who =
      quittingRootExpectedPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleContinuation
        localGlobalCounterexampleRoot who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_update_bind, expect_bind]
  calc
    expect deviation (fun move =>
        expect (pmfPi (Function.update localGlobalCounterexampleRoot who
          (PMF.pure move)))
          (fun action => quittingRootPayoff localGlobalCounterexampleReward
            localGlobalCounterexampleContinuation action who)) =
      expect deviation (fun _ =>
        expect (pmfPi localGlobalCounterexampleRoot)
          (fun action => quittingRootPayoff localGlobalCounterexampleReward
            localGlobalCounterexampleContinuation action who)) := by
        apply congrArg (expect deviation)
        funext move
        exact
          quittingRootExpectedPayoff_localGlobalCounterexample_pureDeviation
            who move
    _ = expect (pmfPi localGlobalCounterexampleRoot)
          (fun action => quittingRootPayoff localGlobalCounterexampleReward
            localGlobalCounterexampleContinuation action who) :=
      expect_const deviation _

/-- The displayed root is an exact root Nash action.  The stronger preceding
pure-deviation equality also supplies both inequalities required by strong
one-stage perfection. -/
theorem isQuittingRootNash_localGlobalCounterexample :
    IsεQuittingRootNash localGlobalCounterexampleReward
      localGlobalCounterexampleContinuation 0
      localGlobalCounterexampleRoot := by
  intro who deviation
  rw [quittingRootExpectedPayoff_localGlobalCounterexample_deviation]
  simp

@[simp] theorem localGlobalCounterexampleReward_singleton_false :
    localGlobalCounterexampleReward
        (quittingSingletonTerminal false) false = -1 := by
  simp [localGlobalCounterexampleReward, quittingSingletonTerminal]

@[simp] theorem localGlobalCounterexampleReward_singleton_true :
    localGlobalCounterexampleReward
        (quittingSingletonTerminal true) true = 0 := by
  simp [localGlobalCounterexampleReward, quittingSingletonTerminal]

/-- The supplied profile has terminal payoff `-1` for player one. -/
@[simp] theorem quittingTerminalPayoff_localGlobalCounterexampleProfile_false :
    quittingTerminalPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleProfile false = -1 := by
  rw [localGlobalCounterexampleProfile,
    quittingTerminalPayoff_update_quittingAlwaysQuitStrategy]
  exact localGlobalCounterexampleReward_singleton_false

/-- Player two's terminal payoff is identically zero. -/
@[simp] theorem quittingTerminalPayoff_localGlobalCounterexampleProfile_true :
    quittingTerminalPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleProfile true = 0 := by
  simp [quittingTerminalPayoff, localGlobalCounterexampleReward]

/-- The profile's terminal payoff vector is exactly the continuation vector
used in the local root calculation. -/
theorem quittingTerminalPayoff_localGlobalCounterexampleProfile_eq :
    (fun who => quittingTerminalPayoff localGlobalCounterexampleReward
      localGlobalCounterexampleProfile who) =
      localGlobalCounterexampleContinuation := by
  funext who
  cases who <;>
    simp [localGlobalCounterexampleContinuation]

/-- Shifting past any completed stage preserves the stationary supplied
profile. -/
@[simp] theorem shiftProfile_localGlobalCounterexampleProfile
    (action : Bool → Bool) :
    (quittingGame localGlobalCounterexampleReward).shiftProfile
        localGlobalCounterexampleProfile (none, action) =
      localGlobalCounterexampleProfile := by
  rw [localGlobalCounterexampleProfile_eq_stationary]
  rfl

/-- Replacing player one's stationary quit strategy by stationary continuation
returns the all-continue profile exactly. -/
theorem update_localGlobalCounterexampleProfile_false_continue :
    Function.update localGlobalCounterexampleProfile false
        (quittingAlwaysContinueStrategy
          localGlobalCounterexampleReward false) =
      quittingAlwaysContinueProfile localGlobalCounterexampleReward := by
  funext who t history
  cases who <;>
    simp [localGlobalCounterexampleProfile,
      quittingAlwaysContinueProfile, quittingAlwaysContinueStrategy,
      StochasticGame.stationaryBehaviorProfile]

/-- Player one's always-continue deviation prevents absorption and therefore
has terminal payoff zero. -/
@[simp] theorem quittingTerminalPayoff_localGlobalCounterexampleDeviation_false :
    quittingTerminalPayoff localGlobalCounterexampleReward
        (Function.update localGlobalCounterexampleProfile false
          (quittingAlwaysContinueStrategy
            localGlobalCounterexampleReward false)) false = 0 := by
  rw [update_localGlobalCounterexampleProfile_false_continue,
    quittingTerminalPayoff_quittingAlwaysContinue]

/-- The supplied profile's exact terminal deviation regret is one. -/
theorem localGlobalCounterexample_terminalRegret_eq_one :
    quittingTerminalPayoff localGlobalCounterexampleReward
        (Function.update localGlobalCounterexampleProfile false
          (quittingAlwaysContinueStrategy
            localGlobalCounterexampleReward false)) false -
      quittingTerminalPayoff localGlobalCounterexampleReward
        localGlobalCounterexampleProfile false = 1 := by
  rw [quittingTerminalPayoff_localGlobalCounterexampleDeviation_false,
    quittingTerminalPayoff_localGlobalCounterexampleProfile_false]
  norm_num

/-- Consequently the supplied profile is not a terminal `ε`-equilibrium for
any error strictly below one. -/
theorem not_isεAsymptoticNash_localGlobalCounterexampleProfile
    {ε : ℝ} (hε : ε < 1) :
    ¬(quittingGame localGlobalCounterexampleReward).IsεAsymptoticNash
      (quittingTerminalPayoff localGlobalCounterexampleReward) ε
      localGlobalCounterexampleProfile := by
  intro hnash
  have hdeviation := hnash false
    (quittingAlwaysContinueStrategy localGlobalCounterexampleReward false)
  rw [quittingTerminalPayoff_localGlobalCounterexampleDeviation_false,
    quittingTerminalPayoff_localGlobalCounterexampleProfile_false] at hdeviation
  linarith

/-- The stationary fallback is an exact terminal equilibrium: both singleton
quitting rewards are nonpositive. -/
theorem isAsymptoticNash_quittingAlwaysContinue_localGlobalCounterexample :
    (quittingGame localGlobalCounterexampleReward).IsεAsymptoticNash
      (quittingTerminalPayoff localGlobalCounterexampleReward) 0
      (quittingAlwaysContinueProfile localGlobalCounterexampleReward) := by
  apply (isεAsymptoticNash_quittingAlwaysContinue_iff
    localGlobalCounterexampleReward le_rfl).2
  intro who
  cases who <;> simp

end GameTheory
