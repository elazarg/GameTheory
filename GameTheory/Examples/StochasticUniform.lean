/-
# A nondegenerate stochastic-game bridge witness

Two players act simultaneously in two public states. Disagreement produces a
genuinely stochastic successor and the horizon equilibrium surface is exactly
canonical approximate Nash.
-/

import GameTheory.Stochastic.Uniform
import GameTheory.Math.Probability.Mixture
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.Examples.StochasticUniform

open GameTheory.Math.Probability Stochastic Protocol Protocol.ExecutionProtocol

namespace Game

/-- The unbiased law on the two states. -/
def fairState : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

/-- Disagreement randomizes the next state; utility depends on the current
state and the player's simultaneous action. -/
def hostile : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition state action :=
    if action false = action true then PMF.pure (!state) else fairState
  stageUtility state action who := if action who = state then 1 else 0

local instance hostileActionNonempty :
    ∀ i : Bool, Nonempty (hostile.Action i) :=
  fun _ => ⟨false⟩

theorem false_mem_support_fairState : false ∈ fairState.support := by
  exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by simp)

theorem true_mem_support_fairState : true ∈ fairState.support := by
  exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by simp)

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
        ∃ hprofile : UtilityIntegrable (hostile.horizonUtility initial horizon) who
            ((hostile.horizonForm initial horizon).play profile),
          ∃ hdeviation : UtilityIntegrable (hostile.horizonUtility initial horizon)
              who ((hostile.horizonForm initial horizon).play
                (Profile.update profile who deviation)),
            hostile.finiteAveragePayoff initial horizon
                (Profile.update profile who deviation) who hdeviation ≤
              hostile.finiteAveragePayoff initial horizon profile who hprofile +
                epsilon :=
  hostile.isεHorizonNash_iff initial horizon epsilon profile

/-! The same nondegenerate dynamics with zero stage utility provide an exact
positive and negative check for the payoff-level uniformity definition. -/

/-- The hostile dynamics with every stage payoff zero, isolating the payoff
level from the dynamics. -/
@[reducible]
def zeroPayoff : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition := hostile.transition
  stageUtility _ _ _ := 0

local instance zeroPayoffActionNonempty :
    ∀ i : Bool, Nonempty (zeroPayoff.Action i) :=
  fun _ => ⟨false⟩

/-- The constant profile in the zero-payoff game. -/
def zeroProfile (initial : Bool) : zeroPayoff.BehaviorProfile initial :=
  fun _ _ => PMF.pure ⟨some false, ⟨false, rfl⟩⟩

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
        simp [Game.eventUtility]
  show (horizon : ℝ)⁻¹ *
    trace.valueSum (fun event => zeroPayoff.eventUtility initial event who) = 0
  rw [hsum]
  ring

/-- The zero stage payoff is integrable at every horizon and behavioral profile. -/
@[simp]
theorem zeroPayoff_horizonIntegrable (initial : Bool) (horizon : ℕ)
    (profile : zeroPayoff.BehaviorProfile initial) (who : Bool) :
    UtilityIntegrable (zeroPayoff.horizonUtility initial horizon) who
      ((zeroPayoff.horizonForm initial horizon).play profile) := by
  apply payoffIntegrable_of_bounded _ _ (C := 0)
  intro history
  simp only [Game.horizonUtility, zeroPayoff_historyAverageUtility,
    abs_zero, le_refl]

@[simp]
theorem zeroPayoff_finiteAveragePayoff (initial : Bool) (horizon : ℕ)
    (profile : zeroPayoff.BehaviorProfile initial) (who : Bool) :
    zeroPayoff.finiteAveragePayoff initial horizon profile who
      (zeroPayoff_horizonIntegrable initial horizon profile who) = 0 := by
  let law := (zeroPayoff.horizonForm initial horizon).play profile
  have hconstant := payoffIntegrable_constant law 0
  have heq := expect_congr_on_support (μ := law)
    (f := fun history => zeroPayoff.horizonUtility initial horizon history who)
    (g := fun _ => 0)
    (fun history _ => zeroPayoff_historyAverageUtility initial horizon history who)
    (zeroPayoff_horizonIntegrable initial horizon profile who) hconstant
  exact heq.trans (expect_constant law 0 hconstant)

/-- The zero vector is a uniform equilibrium payoff, witnessed at every
horizon by one fixed behavioral profile. -/
theorem zeroPayoff_isUniformEquilibriumPayoff (initial : Bool) :
    zeroPayoff.IsUniformEquilibriumPayoff initial (fun _ => 0) := by
  intro epsilon hepsilon
  refine ⟨zeroProfile initial, 0, fun horizon _ => ?_⟩
  constructor
  · rw [zeroPayoff.isεHorizonNash_iff]
    intro who deviation
    refine ⟨zeroPayoff_horizonIntegrable initial horizon (zeroProfile initial) who,
      zeroPayoff_horizonIntegrable initial horizon
        (Profile.update (zeroProfile initial) who deviation) who, ?_⟩
    simp only [zeroPayoff_finiteAveragePayoff, zero_add]
    exact le_of_lt hepsilon
  · intro who
    refine ⟨zeroPayoff_horizonIntegrable initial horizon (zeroProfile initial) who,
      ?_⟩
    simpa only [zeroPayoff_finiteAveragePayoff, sub_zero, abs_zero] using
      (le_of_lt hepsilon)

/-- The constant-one vector fails the approximation clause even though the
underlying transition remains genuinely stochastic. -/
theorem one_not_isUniformEquilibriumPayoff (initial : Bool) :
    ¬ zeroPayoff.IsUniformEquilibriumPayoff initial (fun _ => 1) := by
  intro hone
  obtain ⟨profile, threshold, hprofile⟩ := hone (1 / 2) (by norm_num)
  obtain ⟨hguard, hclose⟩ := (hprofile threshold le_rfl).2 false
  rw [zeroPayoff_finiteAveragePayoff] at hclose
  norm_num at hclose

/-! ## A reachable, nonconstant transient-payoff certificate -/

/-- The initial state pays one or two (depending on the player), then the game
enters a zero-payoff absorbing state. Payoffs are nonconstant along every
positive-horizon path, and the transient contribution vanishes uniformly. -/
@[reducible]
def transientPayoff : Game Bool where
  State := Bool
  Action := fun _ => Bool
  transition _state _action := PMF.pure false
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

/-- The constant profile in the transient-payoff game. -/
def transientProfile : transientPayoff.BehaviorProfile true :=
  fun _ _ => PMF.pure ⟨some false, ⟨false, rfl⟩⟩

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
  have hpure : target ∈ (PMF.pure false).support := realized
  exact (PMF.mem_support_pure_iff _ _).mp hpure

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

/-- The bounded transient payoff is integrable at every horizon and profile. -/
theorem transientPayoff_horizonIntegrable (horizon : ℕ)
    (profile : transientPayoff.BehaviorProfile true) (who : Bool) :
    UtilityIntegrable (transientPayoff.horizonUtility true horizon) who
      ((transientPayoff.horizonForm true horizon).play profile) := by
  apply payoffIntegrable_of_bounded _ _ (C := 2 * (horizon : ℝ)⁻¹)
  intro history
  have hsum := transientPayoff_trace_valueSum_bounds history who
  have hinv : 0 ≤ (horizon : ℝ)⁻¹ := by positivity
  have hnonneg : 0 ≤ (horizon : ℝ)⁻¹ * history.valueSum
      (fun event => transientPayoff.eventUtility true event who) :=
    mul_nonneg hinv hsum.1
  have hupper : (horizon : ℝ)⁻¹ * history.valueSum
      (fun event => transientPayoff.eventUtility true event who) ≤
        2 * (horizon : ℝ)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hsum.2 hinv]
  simpa only [Game.horizonUtility, Game.historyAverageUtility,
    abs_of_nonneg hnonneg] using hupper

/-- At every horizon, every behavioral profile and deviation has payoff in
the interval from zero to twice the reciprocal horizon. -/
theorem transientPayoff_finiteAveragePayoff_bounds (horizon : ℕ)
    (profile : transientPayoff.BehaviorProfile true) (who : Bool) :
    0 ≤ transientPayoff.finiteAveragePayoff true horizon profile who
        (transientPayoff_horizonIntegrable horizon profile who) ∧
      transientPayoff.finiteAveragePayoff true horizon profile who
        (transientPayoff_horizonIntegrable horizon profile who) ≤
        2 * (horizon : ℝ)⁻¹ := by
  let law := (transientPayoff.horizonForm true horizon).play profile
  let hpayoff := transientPayoff_horizonIntegrable horizon profile who
  have hzero := payoffIntegrable_constant law 0
  have hcap := payoffIntegrable_constant law (2 * (horizon : ℝ)⁻¹)
  constructor
  · have hmono := expect_mono (μ := law)
        (f := fun _ => 0)
        (g := fun history => transientPayoff.horizonUtility true horizon
          history who)
        (fun history _ => by
          exact mul_nonneg (by positivity)
            (transientPayoff_trace_valueSum_bounds history who).1)
        hzero hpayoff
    simpa only [expect_constant, Game.finiteAveragePayoff,
      expectedUtility] using hmono
  · have hmono := expect_mono (μ := law)
        (f := fun history => transientPayoff.horizonUtility true horizon
          history who)
        (g := fun _ => 2 * (horizon : ℝ)⁻¹)
        (fun history _ => by
          have hsum :=
            (transientPayoff_trace_valueSum_bounds history who).2
          have hinv : 0 ≤ (horizon : ℝ)⁻¹ := by positivity
          dsimp only [Game.horizonUtility, Game.historyAverageUtility]
          nlinarith [mul_le_mul_of_nonneg_left hsum hinv])
        hpayoff hcap
    simpa only [expect_constant, Game.finiteAveragePayoff,
      expectedUtility] using hmono

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
    refine ⟨transientPayoff_horizonIntegrable horizon transientProfile who, ?_⟩
    simpa only [Pi.zero_apply, sub_zero, abs_of_nonneg hbounds.1] using
      hbounds.2.trans hsmall
  · intro who deviation
    refine ⟨transientPayoff_horizonIntegrable horizon
      (Profile.update transientProfile who deviation) who, ?_⟩
    simpa only [Pi.zero_apply, zero_add] using
      (transientPayoff_finiteAveragePayoff_bounds horizon
        (Profile.update transientProfile who deviation) who).2.trans
        hsmall

/-- The public semantic uniform-payoff predicate is reached through the
nonconstant deviation-cap certificate. -/
theorem transientPayoff_isUniformEquilibriumPayoff :
    transientPayoff.IsUniformEquilibriumPayoff true (fun _ => 0) :=
  transientPayoff.isUniformEquilibriumPayoff_of_deviation_caps true
    (fun _ => 0) transientPayoff_hasUniformDeviationCapConstructor

end Game

end GameTheory.Examples.StochasticUniform
