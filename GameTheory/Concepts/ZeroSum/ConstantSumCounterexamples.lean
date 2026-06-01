/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.ConstantSumCorrelated
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq

/-!
# Constant-Sum Counterexamples

The two-player hypotheses in the constant/zero-sum value theorems are genuine.
For three or more players, constant-sum does not determine each player's Nash or
correlated-equilibrium payoff: one player can absorb the negative total while
the others play a coordination game with multiple Nash payoff levels.
-/

namespace GameTheory

namespace KernelGame

namespace ThreePlayerZeroSumCoordination

/-- Boolean strategies for three players. -/
abbrev Strategy (_ : Fin 3) : Type := Bool

/-- A three-player zero-sum coordination game.

Players `0` and `1` receive payoff `1` from coordinating on `false`, payoff `2`
from coordinating on `true`, and payoff `0` from failing to coordinate.  Player
`2`'s payoff is the negative sum of the first two players' payoffs and their
own strategy is payoff-irrelevant. -/
def payoff (σ : ∀ i : Fin 3, Strategy i) : Payoff (Fin 3) :=
  if σ 0 = σ 1 then
    if σ 0 = true then
      fun i => if i.val = 0 then (2 : ℝ) else if i.val = 1 then 2 else -4
    else
      fun i => if i.val = 0 then (1 : ℝ) else if i.val = 1 then 1 else -2
  else
    fun _ => 0

/-- The deterministic strategic-form kernel for the counterexample. -/
noncomputable def game : KernelGame (Fin 3) :=
  KernelGame.ofPureEU Strategy payoff

/-- Low-payoff coordination equilibrium: everyone plays `false`. -/
def lowProfile : Profile game :=
  fun _ => false

/-- High-payoff coordination equilibrium: everyone plays `true`. -/
def highProfile : Profile game :=
  fun _ => true

theorem game_isZeroSum : game.IsZeroSum := by
  intro σ
  rw [Fin.sum_univ_three]
  change payoff σ 0 + payoff σ 1 + payoff σ 2 = 0
  have h20 : ¬ (2 : Nat) = 0 := by decide
  have h21 : ¬ (2 : Nat) = 1 := by decide
  cases h0 : σ 0 <;> cases h1 : σ 1 <;>
    simp [payoff, h0, h1, h20, h21] <;> norm_num

theorem lowProfile_isNash : game.IsNash lowProfile := by
  intro who s'
  fin_cases who <;> cases s' <;>
    simp [game, lowProfile, payoff, Function.update]

theorem highProfile_isNash : game.IsNash highProfile := by
  intro who s'
  fin_cases who <;> cases s' <;>
    simp [game, highProfile, payoff, Function.update]

@[simp] theorem eu_low_zero : game.eu lowProfile 0 = 1 := by
  simp [game, lowProfile, payoff]

@[simp] theorem eu_high_zero : game.eu highProfile 0 = 2 := by
  simp [game, highProfile, payoff]

theorem low_high_player_zero_payoffs_ne :
    game.eu lowProfile 0 ≠ game.eu highProfile 0 := by
  norm_num

/-- Three-player zero-sum games need not have a unique Nash payoff for a fixed
player.  This is the obstruction to generalizing the two-player value theorem
to arbitrary finite player sets. -/
theorem exists_threePlayer_zeroSum_nash_payoff_not_unique :
    ∃ (G : KernelGame (Fin 3)) (σ τ : Profile G),
      G.IsZeroSum ∧ G.IsNash σ ∧ G.IsNash τ ∧ G.eu σ 0 ≠ G.eu τ 0 := by
  exact ⟨game, lowProfile, highProfile, game_isZeroSum,
    lowProfile_isNash, highProfile_isNash, low_high_player_zero_payoffs_ne⟩

/-- Three-player zero-sum games can have a correlated equilibrium whose payoff
for a fixed player differs from a Nash equilibrium payoff. -/
theorem exists_threePlayer_zeroSum_correlated_payoff_not_nash_value :
    ∃ (G : KernelGame (Fin 3)) (σ : Profile G) (μ : PMF (Profile G)),
      G.IsZeroSum ∧ G.IsNash σ ∧ G.IsCorrelatedEq μ ∧
        G.correlatedEu μ 0 ≠ G.eu σ 0 := by
  refine ⟨game, lowProfile, PMF.pure highProfile, game_isZeroSum,
    lowProfile_isNash, nash_pure_isCorrelatedEq highProfile_isNash, ?_⟩
  rw [correlatedEu_pure]
  simp

end ThreePlayerZeroSumCoordination

end KernelGame

end GameTheory
