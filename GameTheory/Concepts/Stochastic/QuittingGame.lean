/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fin.VecNotation
import GameTheory.Concepts.Stochastic.Absorbing

/-!
# Quitting Games and the Altered-Singleton Refutation Candidate

Quitting games presented as stochastic games: every player chooses
`continue`/`quit`; the first nonempty set of quitters ends the game at an
absorbing state that repeats the terminal reward of that quitter set; if
nobody ever quits, the stage payoff is `0` forever.

This file also records the current **refutation candidate** for the uniform
equilibrium existence problem
(`StochasticGame.exists_uniformEquilibriumPayoff`): a four-player quitting
game with exact rational payoffs (the altered-singleton table of the
research notes in `.codex/research-notes.md`).  The refutation target
`alteredSingletonGame_not_exists_uniformEquilibriumPayoff` is stated with
`sorry`.

## Status — read before touching either `sorry`

Exactly one of the following two statements is true, and **both currently
carry a `sorry`**:

* `exists_uniformEquilibriumPayoff` (the conjecture, in `Uniform.lean`),
  instantiated at `alteredSingletonGame` and its active state; and
* `alteredSingletonGame_not_exists_uniformEquilibriumPayoff` (below).

Neither `sorry` may be discharged from the other.  The candidate is **not**
a certified counterexample.  What is known (numerically or by exact but
not yet formalized arguments, see the research notes): no pure absorbing
Nash profile; survives sure-quitter, stationary, period-2–7, random-basin,
and terminal-vertex attacks; the continuous absorption-path viability
kernel is exactly empty (boundary and triple-zero cases still unwritten).
What is open: excluding aperiodic discrete absorption paths
(Solan–Solan, *Absorption Paths and Equilibria in Quitting Games*,
Theorem 4.13 reduces the ε-equilibrium question to such paths given the
first-stage screen), and the translation of that framework's expected-
terminal ε-equilibria into this repository's finite-horizon-average
`IsUniformEquilibriumPayoff`.

## Main definitions

* `quittingGame` — quitting games as stochastic games
* `alteredSingletonGame` — the exact rational refutation candidate

## Main results

* `isAbsorbingState_quittingGame_some` — absorbed states are absorbing
* `quittingGame_exists_uniformEquilibriumPayoff_of_absorbed` — from any
  absorbed state the conjecture *holds* (so the entire difficulty of the
  candidate sits at the active state)
* `alteredSingletonGame_not_exists_uniformEquilibriumPayoff` — the
  refutation target (stated with `sorry`; open)
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

-- ============================================================================
-- The altered-singleton refutation candidate
-- ============================================================================

/-- Bit mask of a quitter set: player `i` contributes `2 ^ i`. -/
def quitMask (S : Finset (Fin 4)) : ℕ :=
  ∑ i ∈ S, 2 ^ (i : ℕ)

/-- The exact terminal payoff table of the altered-singleton candidate,
indexed by quitter-set mask (`never = 0` pays `0`, masks `1`–`15` as in
the research notes; `vary-singleton-survivors.json`, first record). -/
def alteredSingletonTable : ℕ → Fin 4 → ℝ
  | 1 => ![1, 0, 3, 0]
  | 2 => ![5, 1, -1, 0]
  | 3 => ![0, 3, 7 / 4, 3 / 4]
  | 4 => ![-2, 4, 1, 4]
  | 5 => ![1 / 2, 21 / 4, 0, -1 / 2]
  | 6 => ![1, 0, 2, 3 / 2]
  | 7 => ![7 / 4, 1 / 2, -1 / 2, 3 / 2]
  | 8 => ![4, -1, 0, 1]
  | 9 => ![1 / 4, 1 / 4, 13 / 4, 7 / 4]
  | 10 => ![-5 / 2, 9 / 4, -1 / 4, 0]
  | 11 => ![-1, 13 / 4, 1 / 2, -3 / 4]
  | 12 => ![3 / 4, 7 / 4, 0, -5 / 4]
  | 13 => ![-1 / 4, -1 / 2, 0, 3 / 4]
  | 14 => ![3 / 2, 1, 19 / 4, 0]
  | 15 => ![-2, 10, -1 / 4, -2]
  | _ => fun _ => 0

/-- The altered-singleton four-player quitting game: the current strongest
refutation candidate for the uniform equilibrium existence problem. -/
def alteredSingletonGame : StochasticGame (Fin 4) :=
  quittingGame fun S => alteredSingletonTable (quitMask S.1)

/-- **Refutation target** (open).  The altered-singleton candidate has no
uniform equilibrium payoff from its active state.

This `sorry` is the mirror image of the one on
`exists_uniformEquilibriumPayoff`: exactly one of the two is provable,
and neither may be discharged by weakening or by citing the other.  The
certification obligations are listed in the module docstring; until they
are met this statement is a *conjecture of falsity*, not a disproof. -/
theorem alteredSingletonGame_not_exists_uniformEquilibriumPayoff :
    ¬ ∃ v : Payoff (Fin 4),
      alteredSingletonGame.IsUniformEquilibriumPayoff
        (none : alteredSingletonGame.State) v := by
  sorry

end GameTheory
