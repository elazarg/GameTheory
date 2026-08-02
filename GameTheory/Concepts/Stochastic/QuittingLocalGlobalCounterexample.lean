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
