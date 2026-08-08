/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Models.Quitting.Asymptotic

/-!
# Solan's three-player absorbing-game theorem: quitting specialization

This module is the sole external-source boundary for the unconditional
three-player quitting-game classification.

## Source statement

Eilon Solan, *Three-Player Absorbing Games*, Mathematics of Operations
Research 24(3) (1999), 669--698, proves that every three-player absorbing game
has an equilibrium payoff.  On p. 669, a vector `g` is an `ε`-equilibrium
payoff when one profile keeps every player's payoff in every sufficiently long
finite game, and the expected liminf average payoff in the infinite game,
above `gᵢ - ε`, while every unilateral deviation has payoff in every
sufficiently long finite game, and expected limsup average payoff in the
infinite game, at most `gᵢ + ε`.  An equilibrium payoff is such a vector for
every positive `ε`.

A finite quitting game is the faithful recursive specialization with three
players, one live state of stage payoff zero, actions Continue/Quit, and one
absorbing state for each nonempty quitting coalition.  In this specialization
the infinite average payoff equals `quittingTerminalPayoff`.  The proposition
`SolanThreePlayerQuittingConclusion` records exactly the part of Solan's
conclusion used downstream: one fixed target, prescribed terminal payoff at
least target minus error, and every unilateral terminal payoff at most target
plus error.

The declaration
`solan1999_threePlayerQuitting_terminalTargetBounds` is intentionally the only
borrowed theorem.  It is fixed to `Fin 3`, arbitrary quitting reward tables,
and the two source inequalities below; it does not assume a repository
uniform-equilibrium payoff, a terminal Nash profile, or any certificate
producer.  All such adapters are proved in subsequent modules.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- The infinite-payoff inequalities contained in Solan's definition of an
`ε`-equilibrium payoff, specialized to a three-player quitting game.

The prescribed profile is only required to attain the fixed target from below;
every unilateral behavior strategy is capped from above.  Their difference is
therefore at most `2 * ε`, which is the terminal-Nash adapter proved in
`SolanTerminalAdapter.lean`. -/
def SolanTerminalTargetBounds
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (target : Payoff (Fin 3)) (ε : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  (∀ who, target who - ε ≤
      quittingTerminalPayoff reward profile who) ∧
    ∀ who (dev : (quittingGame reward).BehaviorStrategy who),
      quittingTerminalPayoff reward
          (Function.update profile who dev) who ≤
        target who + ε

/-- The exact quitting-game specialization of the conclusion borrowed from
Solan's 1999 three-player absorbing-game theorem.

This proposition is kept separate from its source declaration so every
mathematical adapter can instead be stated conditionally and remain
axiom-clean. -/
def SolanThreePlayerQuittingConclusion
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) : Prop :=
  ∃ target : Payoff (Fin 3), ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      SolanTerminalTargetBounds reward target ε profile

/-- **External source theorem (Solan 1999), faithful quitting specialization.**

Every three-player quitting reward table has one target satisfying the
prescribed lower and unilateral-deviation upper terminal bounds at every
positive accuracy.

No broader absorbing-game formalization is postulated here.  Replacing this
single declaration by a formal embedding into a future absorbing-game theorem
is the exact remaining source-formalization task. -/
axiom solan1999_threePlayerQuitting_terminalTargetBounds
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    SolanThreePlayerQuittingConclusion reward

end GameTheory
