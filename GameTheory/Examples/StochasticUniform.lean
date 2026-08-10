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

open Probability Stochastic Protocol Protocol.ExecutionProtocol

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

/-! ## A reachable, nonconstant transient-payoff certificate -/

/-- The initial state pays one or two (depending on the player), then the game
enters a zero-payoff absorbing state. Payoffs are nonconstant along every
positive-horizon path, and the transient contribution vanishes uniformly. -/
def transientPayoff : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition _state _action := FinDist.pure false
  stageUtility state _action who :=
    if state then if who then 2 else 1 else 0

@[simp]
theorem transientPayoff_stageUtility (state : Bool)
    (action : Bool → Bool) (who : Bool) :
    transientPayoff.stageUtility state action who =
      if state then if who then 2 else 1 else 0 :=
  rfl

local instance transientPayoffActionNonempty :
    ∀ i : Bool, Nonempty (transientPayoff.Action i) :=
  fun _ => ⟨false⟩

def transientProfile : transientPayoff.BehaviorProfile true :=
  fun _ _ => FinDist.pure ⟨some false, ⟨false, rfl⟩⟩

theorem transientPayoff_is_reachable_and_nonconstant :
    transientPayoff.stageUtility true (fun _ => false) false = 1 ∧
      transientPayoff.stageUtility true (fun _ => false) true = 2 ∧
      transientPayoff.stageUtility false (fun _ => false) true = 0 := by
  show (1 : ℝ) = 1 ∧ (2 : ℝ) = 2 ∧ (0 : ℝ) = 0
  norm_num

/-- A realized transition always reaches the absorbing false state. -/
private theorem transientPayoff_target_false
    {source target : Bool}
    (joint : ∀ i, Option ((transientPayoff.toExecution true).Action i))
    (isLegal : (transientPayoff.toExecution true).Legal source joint)
    (realized :
      target ∈
        ((transientPayoff.toExecution true).step source
          ⟨joint, isLegal⟩).support) :
    target = false := by
  have hpure : target ∈ (FinDist.pure false).support := realized
  exact FinDist.mem_support_pure.mp hpure

/-- Every history contains at most the one initial transient reward. -/
private theorem transientPayoff_trace_valueSum_bounds
    (history : (transientPayoff.toExecution true).History)
    (who : Bool) :
    0 ≤ history.valueSum
        (fun event => transientPayoff.eventUtility true event who) ∧
      history.valueSum
        (fun event => transientPayoff.eventUtility true event who) ≤ 2 := by
  show
    0 ≤ history.trace.valueSum
        (fun event => transientPayoff.eventUtility true event who) ∧
      history.trace.valueSum
        (fun event => transientPayoff.eventUtility true event who) ≤ 2
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => norm_num
  | @extend source target prior joint isLegal realized ih =>
      rw [Trace.valueSum_extend]
      cases prior with
      | start =>
          cases who <;>
            norm_num [Game.eventUtility, transientPayoff_stageUtility]
      | @extend previous source earlier earlierJoint earlierLegal earlierRealized =>
        have hsource : source = false :=
          transientPayoff_target_false earlierJoint earlierLegal earlierRealized
        subst source
        simpa [Game.eventUtility, transientPayoff] using ih

/-- At every horizon, every behavioral profile and deviation has payoff in
the interval from zero to the reciprocal horizon, up to the player-two factor
of two. -/
theorem transientPayoff_finiteAveragePayoff_bounds (horizon : ℕ)
    (profile : transientPayoff.BehaviorProfile true) (who : Bool) :
    0 ≤ transientPayoff.finiteAveragePayoff true horizon profile who ∧
      transientPayoff.finiteAveragePayoff true horizon profile who ≤
        2 * (horizon : ℝ)⁻¹ := by
  show
    0 ≤ expectedUtility (transientPayoff.horizonUtility true horizon) who
        ((transientPayoff.horizonForm true horizon).play profile) ∧
      expectedUtility (transientPayoff.horizonUtility true horizon) who
          ((transientPayoff.horizonForm true horizon).play profile) ≤
        2 * (horizon : ℝ)⁻¹
  constructor
  · calc
      0 = FinDist.expect
          ((transientPayoff.horizonForm true horizon).play profile)
          (fun _ => 0) := (FinDist.expect_const _ 0).symm
      _ ≤ _ := FinDist.expect_mono fun history _ => by
        unfold Game.horizonUtility Game.historyAverageUtility
        have hsum :=
          (transientPayoff_trace_valueSum_bounds history who).1
        exact mul_nonneg (by positivity) hsum
  · calc
      _ ≤ FinDist.expect
          ((transientPayoff.horizonForm true horizon).play profile)
          (fun _ => 2 * (horizon : ℝ)⁻¹) :=
        FinDist.expect_mono fun history _ => by
          unfold Game.horizonUtility Game.historyAverageUtility
          have hsum :=
            (transientPayoff_trace_valueSum_bounds history who).2
          have hinv : 0 ≤ (horizon : ℝ)⁻¹ := by positivity
          calc
            (horizon : ℝ)⁻¹ * history.valueSum
                (fun event => transientPayoff.eventUtility true event who) ≤
                (horizon : ℝ)⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hsum hinv
            _ = 2 * (horizon : ℝ)⁻¹ := by ring
      _ = 2 * (horizon : ℝ)⁻¹ := FinDist.expect_const _ _

/-- A nonconstant-payoff uniform deviation-cap constructor. The threshold
makes the one-period transient smaller than the requested accuracy. -/
theorem transientPayoff_hasUniformDeviationCapConstructor :
    transientPayoff.HasUniformDeviationCapConstructor true (fun _ => 0) := by
  intro delta hdelta
  have hdeltaHalf : 0 < delta / 2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdeltaHalf
  let threshold := n + 1
  refine ⟨transientProfile, threshold, fun horizon hhorizon => ?_⟩
  have hthresholdPos : 0 < threshold := by
    simp [threshold]
  have hhorizonPos : 0 < horizon := lt_of_lt_of_le hthresholdPos hhorizon
  have hcast : (threshold : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have hinv : (horizon : ℝ)⁻¹ ≤ (threshold : ℝ)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by exact_mod_cast hthresholdPos) hcast
  have hsmall : 2 * (horizon : ℝ)⁻¹ ≤ delta := by
    have hthresholdSmall : (threshold : ℝ)⁻¹ < delta / 2 := by
      simpa [threshold, one_div] using hn
    nlinarith
  constructor
  · intro who
    have hbounds :=
      transientPayoff_finiteAveragePayoff_bounds horizon transientProfile who
    rw [sub_zero, abs_of_nonneg hbounds.1]
    exact hbounds.2.trans hsmall
  · intro who deviation
    exact
      (transientPayoff_finiteAveragePayoff_bounds horizon
        (Profile.update transientProfile who deviation) who).2.trans
        (by simpa using hsmall)

/-- The public semantic uniform-payoff predicate is reached through the
nonconstant deviation-cap certificate. -/
theorem transientPayoff_isUniformEquilibriumPayoff :
    transientPayoff.IsUniformEquilibriumPayoff true (fun _ => 0) :=
  transientPayoff.isUniformEquilibriumPayoff_of_deviation_caps true
    (fun _ => 0) transientPayoff_hasUniformDeviationCapConstructor

end Game

end GameTheory.Examples.StochasticUniform
