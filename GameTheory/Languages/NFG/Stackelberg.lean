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

end GameTheory
