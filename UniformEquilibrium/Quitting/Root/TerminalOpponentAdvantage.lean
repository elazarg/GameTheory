/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import GameTheory.Concepts.Potential.MixedPotential

/-!
# Terminal full-set advantage at one quitting root

This file isolates the root-level comparison between continuing with the
singleton terminal option and joining the same realized opponent quitter set.
It contains only one-stage product-root algebra; dynamic debt and path
provenance are downstream consumers.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Against an opponent action, compare continuing with the singleton
terminal option to joining the same simultaneous quitter set.  The action is
sampled with the owner forced to Continue. -/
def quittingTerminalOpponentAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool) : ℝ :=
  quittingRootPayoff reward
      (fun _ ↦ reward (quittingSingletonTerminal owner) owner)
      action owner -
    quittingRootPayoff reward (0 : Payoff ι)
      (Function.update action owner true) owner

/-- The expectation of the full-set advantage is exactly the augmented
Continue endpoint minus the Quit endpoint. -/
theorem expect_terminalOpponentAdvantage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) =
      quittingRootContinuePayoff reward
          (fun _ ↦ reward (quittingSingletonTerminal owner) owner)
          root owner -
        quittingRootQuitPayoff reward (0 : Payoff ι) root owner := by
  unfold quittingTerminalOpponentAdvantage quittingRootContinuePayoff
    quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_sub]
  congr 1
  have hpure := KernelGame.expect_pmfPi_update_pure
    (Function.update root owner (PMF.pure false)) owner true
    (fun action ↦ quittingRootPayoff reward (0 : Payoff ι) action owner)
  simpa using hpure.symm

/-- Updating a forced-continuing owner's action to Quit inserts exactly that
owner into the full simultaneous quitter set. -/
theorem quittingQuitters_update_true_of_apply_false
    (action : ι → Bool) (owner : ι) :
    quittingQuitters (Function.update action owner true) =
      insert owner (quittingQuitters action) := by
  ext player
  by_cases hplayer : player = owner
  · subst player
    simp [quittingQuitters]
  · simp [quittingQuitters, hplayer]

end GameTheory
