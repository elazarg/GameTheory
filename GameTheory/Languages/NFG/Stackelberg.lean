/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Stackelberg (Leader-Follower) Games

A Stackelberg game is a two-player sequential game where the leader
commits to a strategy first, and the follower best-responds. The main
result is that the leader's Stackelberg payoff is at least as good as
their Nash payoff in the simultaneous-move game.

## Main definitions

* `StackelbergGame` — a two-player game with leader/follower structure
* `StackelbergGame.followerBR` — follower's best response function
* `StackelbergGame.stackelbergPayoff` — leader's payoff when follower best-responds
* `StackelbergGame.IsStackelbergEq` — Stackelberg equilibrium

## Main results

* `stackelberg_leader_ge_nash` — leader's Stackelberg payoff ≥ Nash payoff
-/

namespace GameTheory

open Math.Probability

/-- A Stackelberg (leader-follower) game. -/
structure StackelbergGame where
  /-- Leader's action set. -/
  L : Type
  /-- Follower's action set. -/
  F : Type
  /-- Leader's utility. -/
  uL : L → F → ℝ
  /-- Follower's utility. -/
  uF : L → F → ℝ

namespace StackelbergGame

variable (G : StackelbergGame)

/-- The follower's best response to a leader action `l`. -/
noncomputable def followerBR (br : G.L → G.F) : Prop :=
  ∀ l f', G.uF l (br l) ≥ G.uF l f'

/-- The leader's Stackelberg payoff given a follower BR function. -/
noncomputable def stackelbergPayoff (br : G.L → G.F) (l : G.L) : ℝ :=
  G.uL l (br l)

/-- A Stackelberg equilibrium. -/
def IsStackelbergEq (l : G.L) (br : G.L → G.F) : Prop :=
  G.followerBR br ∧ ∀ l', G.uL l (br l) ≥ G.uL l' (br l')

/-- A simultaneous Nash equilibrium of the underlying normal-form game. -/
def IsSimNash (l : G.L) (f : G.F) : Prop :=
  (∀ l', G.uL l f ≥ G.uL l' f) ∧ (∀ f', G.uF l f ≥ G.uF l f')

/-- The Stackelberg leader advantage theorem. -/
theorem stackelberg_leader_ge_nash
    (l_S : G.L) (br : G.L → G.F)
    (l_N : G.L) (f_N : G.F)
    (hStack : G.IsStackelbergEq l_S br)
    (_hNash : G.IsSimNash l_N f_N)
    (hbr_nash : br l_N = f_N) :
    G.uL l_S (br l_S) ≥ G.uL l_N f_N := by
  calc G.uL l_S (br l_S) ≥ G.uL l_N (br l_N) := hStack.2 l_N
    _ = G.uL l_N f_N := by rw [hbr_nash]

/-- If the follower has a unique best response at the Nash action,
    then `br l_N = f_N` follows automatically from Nash. -/
theorem followerBR_at_nash_unique
    (br : G.L → G.F) (l_N : G.L) (f_N : G.F)
    (hbr : G.followerBR br)
    (hNash : G.IsSimNash l_N f_N)
    (huniq : ∀ f, G.uF l_N f ≥ G.uF l_N f_N → G.uF l_N f_N ≥ G.uF l_N f → f = f_N) :
    br l_N = f_N := by
  apply huniq
  · exact hbr l_N f_N
  · exact hNash.2 (br l_N)

open Classical in
/-- The simultaneous game as a `KernelGame` over `Fin 2`. -/
noncomputable def toKernelGame (G : StackelbergGame) : KernelGame (Fin 2) :=
  KernelGame.ofEU
    (fun i => if i = 0 then G.L else G.F)
    (fun σ i =>
      let l : G.L := cast (by simp) (σ 0)
      let f : G.F := cast (by simp) (σ 1)
      if i = 0 then G.uL l f else G.uF l f)

end StackelbergGame

/-! ## Entry-deterrence Stackelberg example

Two actions per player. The leader is an incumbent committing publicly
to *fight* or *accommodate*; the follower is a potential entrant
choosing *enter* or *stay out*.

  ╭──────────────╮  enter         stay out
  │ fight        │  (0, -1)       (2,  0)
  │ accommodate  │  (1,  1)       (2,  0)
  ╰──────────────╯

The follower's best response is *stay out* against *fight* (0 > -1)
and *enter* against *accommodate* (1 > 0). The Stackelberg leader
therefore commits to *fight*, forcing the entrant to stay out, and
collects payoff 2. The simultaneous game also has a Nash equilibrium
at *(accommodate, enter)* with leader payoff 1, so the leader strictly
benefits from commitment over that Nash. -/

namespace EntryDeterrence

/-- Leader and follower actions, both binary. We reuse `Bool` so that
the structure remains a plain 2×2 game; `true` is *fight*/*enter* and
`false` is *accommodate*/*stay out*. -/
def fight : Bool := true
def accommodate : Bool := false
def enter : Bool := true
def stayOut : Bool := false

/-- Leader (incumbent) payoff. -/
def uL : Bool → Bool → ℝ
  | true,  true  => 0   -- fight, enter
  | true,  false => 2   -- fight, stay out
  | false, true  => 1   -- accommodate, enter
  | false, false => 2   -- accommodate, stay out

/-- Follower (entrant) payoff. -/
def uF : Bool → Bool → ℝ
  | true,  true  => -1  -- fight, enter
  | true,  false => 0   -- fight, stay out
  | false, true  => 1   -- accommodate, enter
  | false, false => 0   -- accommodate, stay out

/-- The Stackelberg instance. -/
def game : StackelbergGame where
  L := Bool
  F := Bool
  uL := uL
  uF := uF

/-- The follower's best-response function:\ stay out against fight,
enter against accommodate. -/
def br : Bool → Bool
  | true  => false  -- BR(fight) = stay out
  | false => true   -- BR(accommodate) = enter

/-- `br` is indeed a best-response function. -/
theorem br_isBR : game.followerBR br := by
  intro l f'
  cases l <;> cases f' <;> simp [game, br, uF]

/-- *(fight, stay out)* is the Stackelberg outcome: leader's payoff 2
is the maximum over committed-leader payoffs `uL(l, br l)`. -/
theorem game_stackelberg_eq_fight :
    game.IsStackelbergEq fight br := by
  refine ⟨br_isBR, ?_⟩
  intro l'
  cases l' <;> simp [game, fight, br, uL]

/-- The simultaneous *(accommodate, enter)* is a Nash equilibrium of
the underlying 2×2 game. -/
theorem game_simNash_accommodate :
    game.IsSimNash accommodate enter := by
  refine ⟨?_, ?_⟩
  · intro l'
    cases l' <;> simp [game, accommodate, enter, uL]
  · intro f'
    cases f' <;> simp [game, accommodate, enter, uF]

/-- The follower's BR at the *accommodate* Nash matches the Nash
follower action (= enter). -/
theorem game_br_at_accommodate :
    br accommodate = enter := rfl

/-- **Stackelberg leader-advantage on this instance**: the leader's
Stackelberg payoff (`uL(fight, stay out) = 2`) is at least the
simultaneous-Nash payoff at the *(accommodate, enter)* Nash
(`uL(accommodate, enter) = 1`) — strictly larger, in fact. -/
theorem leader_advantage :
    game.uL fight (br fight) ≥ game.uL accommodate enter := by
  have := game.stackelberg_leader_ge_nash fight br accommodate enter
    game_stackelberg_eq_fight game_simNash_accommodate game_br_at_accommodate
  exact this

theorem leader_advantage_strict :
    game.uL fight (br fight) > game.uL accommodate enter := by
  simp [game, fight, accommodate, enter, br, uL]

end EntryDeterrence

end GameTheory
