/-
# A nondegenerate stochastic-game bridge witness

Two players act simultaneously in two public states. Disagreement produces a
genuinely stochastic successor and the horizon equilibrium surface is exactly
canonical approximate Nash.
-/

import GameTheory.Stochastic.Uniform
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Examples.StochasticUniform

open Probability Stochastic

namespace Game

def fairState : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

/-- Disagreement randomizes the next state; utility depends on the current
state and the player's simultaneous action. -/
def hostile : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition state action :=
    if action false = action true then FinDist.pure (!state) else fairState
  stageUtility state action who := if action who = state then 1 else 0

local instance hostileActionNonempty :
    ∀ i : Bool, Nonempty (hostile.Action i) :=
  fun _ => ⟨false⟩

theorem false_mem_support_fairState : false ∈ fairState.support := by
  exact FinDist.prob_pos_iff.mp (by norm_num [fairState, FinDist.prob_pure_eq_ite])

theorem true_mem_support_fairState : true ∈ fairState.support := by
  exact FinDist.prob_pos_iff.mp (by norm_num [fairState, FinDist.prob_pure_eq_ite])

/-- The representative joint action reaches both states with positive mass. -/
theorem hostile_transition_nondegenerate (state : Bool) :
    false ∈ (hostile.transition state fun i => i).support ∧
      true ∈ (hostile.transition state fun i => i).support := by
  have htransition : hostile.transition state (fun i => i) = fairState := by
    simp [hostile]
  rw [htransition]
  exact And.intro false_mem_support_fairState true_mem_support_fairState

/-- The stochastic witness reaches the canonical approximate-Nash surface. -/
theorem hostile_horizon_nash_is_canonical (initial : Bool) (horizon : ℕ)
    (epsilon : ℝ) (profile : hostile.BehaviorProfile initial) :
    hostile.IsεHorizonNash initial horizon epsilon profile ↔
      ∀ who (deviation : (hostile.perfectMonitoring initial).BehavioralPolicy who),
        hostile.finiteAveragePayoff initial horizon
              (Profile.update profile who deviation) who ≤
          hostile.finiteAveragePayoff initial horizon profile who + epsilon :=
  hostile.isεHorizonNash_iff initial horizon epsilon profile

end Game

end GameTheory.Examples.StochasticUniform
