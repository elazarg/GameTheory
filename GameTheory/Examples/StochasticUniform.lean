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

/-! The same nondegenerate dynamics with zero stage utility provide an exact
positive and negative check for the payoff-level uniformity definition. -/

def zeroPayoff : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition := hostile.transition
  stageUtility _ _ _ := 0

local instance zeroPayoffActionNonempty :
    ∀ i : Bool, Nonempty (zeroPayoff.Action i) :=
  fun _ => ⟨false⟩

def zeroProfile (initial : Bool) : zeroPayoff.BehaviorProfile initial :=
  fun _ _ => FinDist.pure ⟨some false, ⟨false, rfl⟩⟩

/-- Zero utility does not trivialize the stochastic dynamics. -/
theorem zeroPayoff_transition_nondegenerate (state : Bool) :
    false ∈ (zeroPayoff.transition state fun i => i).support ∧
      true ∈ (zeroPayoff.transition state fun i => i).support := by
  show false ∈ (hostile.transition state fun i => i).support ∧
    true ∈ (hostile.transition state fun i => i).support
  exact hostile_transition_nondegenerate state

@[simp]
theorem zeroPayoff_historyAverageUtility (initial : Bool) (horizon : ℕ)
    (history : (zeroPayoff.toExecution initial).History) (who : Bool) :
    zeroPayoff.historyAverageUtility initial horizon history who = 0 := by
  rcases history with ⟨state, trace⟩
  have hsum :
      trace.valueSum (fun event => zeroPayoff.eventUtility initial event who) = 0 := by
    induction trace with
    | start => rfl
    | extend prior joint isLegal realized ih =>
        rw [Protocol.ExecutionProtocol.Trace.valueSum_extend, ih]
        simp [Game.eventUtility, zeroPayoff]
  show (horizon : ℝ)⁻¹ *
    trace.valueSum (fun event => zeroPayoff.eventUtility initial event who) = 0
  rw [hsum]
  ring

@[simp]
theorem zeroPayoff_finiteAveragePayoff (initial : Bool) (horizon : ℕ)
    (profile : zeroPayoff.BehaviorProfile initial) (who : Bool) :
    zeroPayoff.finiteAveragePayoff initial horizon profile who = 0 := by
  show expectedUtility (zeroPayoff.horizonUtility initial horizon) who
    ((zeroPayoff.horizonForm initial horizon).play profile) = 0
  unfold expectedUtility
  refine Eq.trans (FinDist.expect_congr (v := fun _ => 0) ?_)
    (FinDist.expect_const _ 0)
  intro history _
  exact zeroPayoff_historyAverageUtility initial horizon history who

/-- The zero vector is a uniform equilibrium payoff, witnessed at every
horizon by one fixed behavioral profile. -/
theorem zeroPayoff_isUniformEquilibriumPayoff (initial : Bool) :
    zeroPayoff.IsUniformEquilibriumPayoff initial (fun _ => 0) := by
  intro epsilon hepsilon
  refine ⟨zeroProfile initial, 0, fun horizon _ => ?_⟩
  constructor
  · rw [zeroPayoff.isεHorizonNash_iff]
    intro who deviation
    simp
    exact le_of_lt hepsilon
  · intro who
    simpa using le_of_lt hepsilon

/-- The constant-one vector fails the approximation clause even though the
underlying transition remains genuinely stochastic. -/
theorem one_not_isUniformEquilibriumPayoff (initial : Bool) :
    ¬ zeroPayoff.IsUniformEquilibriumPayoff initial (fun _ => 1) := by
  intro hone
  obtain ⟨profile, threshold, hprofile⟩ := hone (1 / 2) (by norm_num)
  have hclose := (hprofile threshold le_rfl).2 false
  norm_num at hclose

end Game

end GameTheory.Examples.StochasticUniform
