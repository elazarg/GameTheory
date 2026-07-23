/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Absorbing

/-!
# Quitting Games

Quitting games presented as stochastic games: every player chooses
`continue`/`quit`; the first nonempty set of quitters ends the game at an
absorbing state that repeats the terminal reward of that quitter set; if
nobody ever quits, the stage payoff is `0` forever.

The construction is general in the player type `ι` and the terminal reward
`r`.  Its role in the uniform-equilibrium program is to localize the
difficulty: absorbed states satisfy the conjecture outright, so for any
quitting game the entire question sits at the active state `none`.

The translation from expected-terminal equilibria to this repository's
finite-horizon-average `IsUniformEquilibriumPayoff` is formalized in
`GameTheory.Concepts.Stochastic.QuittingAsymptotic`.

## Main definitions

* `quittingGame` — quitting games as stochastic games

## Main results

* `isAbsorbingState_quittingGame_some` — absorbed states are absorbing
* `quittingGame_exists_uniformEquilibriumPayoff_of_absorbed` — from any
  absorbed state the conjecture *holds*, so the entire difficulty of any
  quitting-game analysis sits at the active state
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι]

/-- A quitting game as a stochastic game.  The state is `none` while play
is active and `some S` after the nonempty quitter set `S` has ended the
game; each player's action set is `Bool` (`true` = quit).  The absorbing
state `some S` repeats the terminal reward `r S` forever; active play pays
`0`. -/
def quittingGame (r : {S : Finset ι // S.Nonempty} → Payoff ι) :
    StochasticGame ι where
  State := Option {S : Finset ι // S.Nonempty}
  Act := fun _ => Bool
  stagePayoff := fun s _ i =>
    match s with
    | none => 0
    | some S => r S i
  transition := fun s a =>
    match s with
    | none =>
        if h : ({i | a i = true} : Finset ι).Nonempty then
          PMF.pure (some ⟨_, h⟩)
        else
          PMF.pure none
    | some S => PMF.pure (some S)
  discount := 0
  discount_nonneg := le_refl 0
  discount_lt_one := zero_lt_one

/-- Absorbed states of a quitting game are absorbing. -/
theorem isAbsorbingState_quittingGame_some
    (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) :
    (quittingGame r).IsAbsorbingState (some S) :=
  fun _ => rfl

/-- From any absorbed state, a quitting game satisfies the uniform
equilibrium existence conjecture (by the absorbing-state theorem).  The
entire difficulty of any quitting-game refutation candidate therefore
sits at the active state `none`. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_absorbed
    [DecidableEq ι] (r : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) :
    ∃ v : Payoff ι,
      (quittingGame r).IsUniformEquilibriumPayoff (some S) v := by
  haveI : Finite (quittingGame r).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  haveI : ∀ i : ι, Finite ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  haveI : ∀ i : ι, Nonempty ((quittingGame r).Act i) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  exact (quittingGame r).exists_uniformEquilibriumPayoff_of_isAbsorbingState
    (isAbsorbingState_quittingGame_some r S)

end GameTheory
