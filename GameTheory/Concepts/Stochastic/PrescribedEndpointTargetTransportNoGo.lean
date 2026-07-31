/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerOwnedEndpointTargetTransportNoGo

/-!
# Prescribed endpoint target transport need not vanish

This file gives a two-state, two-player analytic Bellman germ whose
prescribed universal-calendar Fink profile leaks from a low state into a
high absorbing state.  The endpoint target of the first player is zero at
the low state and one at the high state.  Although the prescribed mixing
probability tends to zero, its cumulative hazard is infinite, so the
expected endpoint target and the prescribed finite-average payoff both
converge to one.

This is a no-go only for automatic two-sided endpoint-target realization by
an arbitrary analytic Bellman germ under the universal calendar.  It is not
a counterexample to uniform-equilibrium existence: a different profile can
remain at the low state.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace PrescribedEndpointTargetTransportNoGo

open Filter Math Math.OnlineLearning Math.PMFProduct Math.Probability Set

abbrev Player := Bool
abbrev State := Bool
abbrev Act (_ : Player) : Type := Bool

instance (player : Player) : Fintype (Act player) := by
  unfold Act
  infer_instance

instance (player : Player) : DecidableEq (Act player) := by
  unfold Act
  infer_instance

def otherAction (action : ∀ player, Act player) : Bool :=
  action true

/-- `false` is low and `true` is high.  The second player's `true` action
leaks from low to high; high is absorbing.  The first player's own action
has no effect. -/
abbrev game : StochasticGame Player where
  State := State
  Act := Act
  stagePayoff state _ player :=
    if player then 0 else if state then 1 else -1
  transition state action :=
    if state || otherAction action then PMF.pure true else PMF.pure false
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance : Fintype game.State := by
  change Fintype Bool
  infer_instance

instance : DecidableEq game.State := by
  change DecidableEq Bool
  infer_instance

instance (player : Player) : Fintype (game.Act player) := by
  change Fintype Bool
  infer_instance

instance (player : Player) : DecidableEq (game.Act player) := by
  change DecidableEq Bool
  infer_instance

def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  BigMatch.coinPMF p hp0 hp1

@[simp]
theorem coin_true_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 true).toReal = p := by
  exact BigMatch.coinPMF_apply_true_toReal p hp0 hp1

@[simp]
theorem coin_false_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 false).toReal = 1 - p := by
  exact BigMatch.coinPMF_apply_false_toReal p hp0 hp1

theorem expect_coin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (coin p hp0 hp1) f =
      p * f true + (1 - p) * f false := by
  exact BigMatch.expect_coinPMF p hp0 hp1 f

/-- The first player uses an irrelevant pure action.  At low, the second
player leaks with probability `t`; at high, both use the endpoint action. -/
def profile (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    game.StationaryMixedProfile :=
  fun state player =>
    if state then PMF.pure false
    else if player then coin t ht0 ht1
    else PMF.pure false

private theorem profile_eq_of_eq
    {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h : t = u) :
    profile t ht0 ht1 = profile u hu0 hu1 := by
  subst u
  rfl

/-- The discounted low-state value moves just enough to support leak
probability `t`; its endpoint is zero. -/
def value (t : ℝ) (state : State) (player : Player) : ℝ :=
  if player then 0 else if state then 1 else -t / (2 - t)

private theorem expect_pmfPi_bool
    (m : Player → PMF Bool) (f : (Player → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun owner =>
        expect (m true) (fun other =>
          f (fun player => if player then other else owner))) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m false))
  funext owner
  have htrue :
      Function.update (Function.update m false (PMF.pure owner))
          true (m true) =
        Function.update m false (PMF.pure owner) := by
    funext player
    cases player <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m true))
  funext other
  have hpure :
      Function.update
          (Function.update m false (PMF.pure owner))
          true (PMF.pure other) =
        fun player =>
          PMF.pure (if player then other else owner) := by
    funext player
    cases player <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

private theorem pureDeviationAuxEU_eq
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (state : State) (player : Player) (action : game.Act player) :
    game.discountedAuxEU (1 - t) (value t) state
        (Function.update (profile t ht0 ht1 state)
          player (PMF.pure action)) player =
      game.discountedAuxEU (1 - t) (value t) state
        (profile t ht0 ht1 state) player := by
  rw [game.discountedAuxEU_eq, game.discountedAuxEU_eq]
  simp_rw [expect_pmfPi_bool]
  cases state <;> cases player <;> cases action
  all_goals
    simp [profile, value, game, otherAction, expect_coin,
      Function.update]

/-- For `0 ≤ t ≤ 1`, the explicit profile and value solve the discounted
Bellman equations at discount factor `1 - t`. -/
theorem equilibrium
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    game.IsDiscountedStationaryBellmanEq
      (1 - t) (profile t ht0 ht1) (value t) := by
  have denominator_ne : 2 - t ≠ 0 := by linarith
  constructor
  · intro state player deviation
    rw [game.discountedAuxEU_update_eq_expect_pure]
    calc
      expect deviation
          (fun action =>
            game.discountedAuxEU (1 - t) (value t) state
              (Function.update (profile t ht0 ht1 state)
                player (PMF.pure action)) player) =
          expect deviation
            (fun _ =>
              game.discountedAuxEU (1 - t) (value t) state
                (profile t ht0 ht1 state) player) := by
            congr 1
            funext action
            exact pureDeviationAuxEU_eq
              t ht0 ht1 state player action
      _ ≤ game.discountedAuxEU (1 - t) (value t) state
          (profile t ht0 ht1 state) player := by
        exact le_of_eq (expect_const _ _)
  · intro state player
    rw [game.discountedAuxEU_eq]
    simp_rw [expect_pmfPi_bool]
    cases state <;> cases player
    all_goals
      simp [profile, value, game, otherAction, expect_coin]
    field_simp [denominator_ne]
    ring

/-- Analytic Bellman-coordinate weights. -/
def weight
    (t : ℝ) (state : State) (player : Player) (action : Bool) : ℝ :=
  if state then
    if action then 0 else 1
  else if player then
    if action then t else 1 - t
  else if action then
    0
  else
    1

def assignment (t : ℝ) : BellmanVar game → ℝ
  | .mix state player action => weight t state player action
  | .val state player => value t state player
  | .disc => t

private theorem assignment_eq_bellmanAssignment
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    assignment t =
      game.bellmanAssignment (profile t ht0 ht1) (value t) (1 - t) := by
  funext coordinate
  cases coordinate with
  | mix state player action =>
      cases state <;> cases player <;> cases action
      all_goals
        simp [assignment, weight, StochasticGame.bellmanAssignment,
          profile]
  | val state player =>
      rfl
  | disc =>
      simp [assignment, StochasticGame.bellmanAssignment]

/-- A genuine analytic Bellman germ carrying the prescribed leak. -/
def germ : game.AnalyticBellmanGerm where
  ramification := 1
  radius := 1
  assignment := assignment
  ramification_pos := Nat.zero_lt_succ 0
  radius_pos := zero_lt_one
  analytic_assignment := by
    rw [analyticAt_pi_iff]
    intro coordinate
    cases coordinate with
    | mix state player action =>
        cases state <;> cases player <;> cases action <;>
          norm_num [assignment, weight]
        all_goals fun_prop
    | val state player =>
        cases state <;> cases player
        · norm_num [assignment, value]
          exact
            analyticAt_id.neg.div
              (analyticAt_const.sub analyticAt_id)
              (by norm_num)
        all_goals norm_num [assignment, value]
        all_goals exact analyticAt_const
    | disc =>
        exact analyticAt_id
  solution := by
    intro t ht
    rw [assignment_eq_bellmanAssignment t ht.1.le ht.2.le]
    exact game.isPolynomialBellmanSolution_bellmanAssignment
      (equilibrium t ht.1.le ht.2.le)
  discountCoordinate := by
    intro t _
    simp [assignment]

@[simp]
theorem germ_endpointValue (state : State) (player : Player) :
    germ.endpointValue state player =
      (if player then 0 else if state then 1 else 0) := by
  change value 0 state player =
    (if player then 0 else if state then 1 else 0)
  cases state <;> cases player <;> norm_num [value]

theorem finkProfile_finkPointAt
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    game.finkProfile (germ.finkPointAt ht) =
      profile t ht.1.le ht.2.le := by
  rw [germ.finkProfile_finkPointAt]
  funext state player
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  unfold Math.ProbabilityMassFunction.toVector
  rw [game.bellmanDecodeProfile_apply_toReal]
  cases state <;> cases player <;> cases action <;>
    simp [germ, assignment, weight, profile, coin_true_toReal,
      coin_false_toReal]

/-! ## Exact prescribed-calendar realization -/

def calendarHazard (stage : ℕ) : ℝ :=
  PlayerOwnedEndpointTargetTransportNoGo.calendarHazard stage

theorem calendarHazard_mem_Ioo (stage : ℕ) :
    calendarHazard stage ∈ Ioo (0 : ℝ) 1 :=
  PlayerOwnedEndpointTargetTransportNoGo.calendarHazard_mem_Ioo stage

theorem not_summable_calendarHazard :
    ¬ Summable calendarHazard :=
  PlayerOwnedEndpointTargetTransportNoGo.not_summable_calendarHazard

def survivalProbability (stage : ℕ) : ℝ :=
  BigMatch.MarkovScalar.liveProbability calendarHazard stage

theorem tendsto_survivalProbability_zero :
    Tendsto survivalProbability atTop (nhds 0) := by
  have hbranch :=
    BigMatch.MarkovScalar.summable_or_tendsto_liveProbability_zero
      calendarHazard
      (fun stage => (calendarHazard_mem_Ioo stage).1.le)
      (fun stage => (calendarHazard_mem_Ioo stage).2.le)
  exact hbranch.resolve_left not_summable_calendarHazard

def scalarEndpointTarget (stage : ℕ) : ℝ :=
  1 - survivalProbability stage

theorem tendsto_scalarEndpointTarget_one :
    Tendsto scalarEndpointTarget atTop (nhds 1) := by
  change
    Tendsto (fun stage => 1 - survivalProbability stage)
      atTop (nhds 1)
  simpa using tendsto_const_nhds.sub tendsto_survivalProbability_zero

/-- The prescribed universal-calendar Fink profile. -/
def prescribedProfile : game.BehaviorProfile :=
  AnalyticBellmanGerm.LowerValueJet.calendarFinkBehaviorProfile germ

private theorem prescribedMixedProfile_eq
    (stage : ℕ) (state : State) :
    AnalyticBellmanGerm.LowerValueJet.calendarFinkMixedProfile
        germ stage state =
      profile (calendarHazard stage)
        (calendarHazard_mem_Ioo stage).1.le
        (calendarHazard_mem_Ioo stage).2.le state := by
  have valid :
      AnalyticBellmanGerm.LowerValueJet.residualCalendarScale stage ∈
        Ioo (0 : ℝ) germ.radius := by
    change
      AnalyticBellmanGerm.LowerValueJet.residualCalendarScale stage ∈
        Ioo (0 : ℝ) 1
    simpa [AnalyticBellmanGerm.LowerValueJet.residualCalendarScale,
      calendarHazard,
      PlayerOwnedEndpointTargetTransportNoGo.calendarHazard,
      AnalyticBellmanGerm.playerOwnedCalendarScale,
      shiftedUniversalEpochScale]
      using calendarHazard_mem_Ioo stage
  rw [
    AnalyticBellmanGerm.LowerValueJet.calendarFinkMixedProfile_eq_finkPointAt
      germ stage valid state]
  have scale_eq :
      AnalyticBellmanGerm.LowerValueJet.residualCalendarScale stage =
        calendarHazard stage := by
    simp [AnalyticBellmanGerm.LowerValueJet.residualCalendarScale,
      calendarHazard,
      PlayerOwnedEndpointTargetTransportNoGo.calendarHazard,
      AnalyticBellmanGerm.playerOwnedCalendarScale,
      shiftedUniversalEpochScale]
  have hprofile := congrFun (finkProfile_finkPointAt valid) state
  calc
    _ =
        profile
          (AnalyticBellmanGerm.LowerValueJet.residualCalendarScale stage)
          valid.1.le valid.2.le state :=
      hprofile
    _ = _ :=
      congrFun
        (profile_eq_of_eq
          valid.1.le valid.2.le
          (calendarHazard_mem_Ioo stage).1.le
          (calendarHazard_mem_Ioo stage).2.le
          scale_eq)
        state

private theorem historyContinuationEU_prescribed
    {stage : ℕ} (history : game.Hist stage) :
    game.historyContinuationEU
        prescribedProfile
        (fun _ nextHistory =>
          germ.endpointValue nextHistory.2 false)
        history =
      calendarHazard stage +
        (1 - calendarHazard stage) *
          germ.endpointValue history.2 false := by
  unfold StochasticGame.historyContinuationEU prescribedProfile
    AnalyticBellmanGerm.LowerValueJet.calendarFinkBehaviorProfile
  rw [game.stageActionDist_scheduledMarkovBehaviorProfile]
  rw [prescribedMixedProfile_eq stage history.2]
  simp_rw [expect_pmfPi_bool]
  simp_rw [germ_endpointValue]
  cases history.2 <;>
    simp [profile, game, otherAction, expect_coin]

private theorem scalarEndpointTarget_succ (stage : ℕ) :
    scalarEndpointTarget (stage + 1) =
      calendarHazard stage +
        (1 - calendarHazard stage) *
          scalarEndpointTarget stage := by
  unfold scalarEndpointTarget survivalProbability
  rw [BigMatch.MarkovScalar.liveProbability_succ]
  ring

/-- The actual prescribed history law has exactly the scalar endpoint-target
expectation. -/
theorem expected_endpointValue_prescribedProfile
    (stage : ℕ) :
    game.expectedHistoryValue
        prescribedProfile false
        (fun _ history =>
          germ.endpointValue history.2 false)
        stage =
      scalarEndpointTarget stage := by
  induction stage with
  | zero =>
      simp [StochasticGame.expectedHistoryValue,
        StochasticGame.emptyHist, prescribedProfile,
        scalarEndpointTarget, survivalProbability,
        BigMatch.MarkovScalar.liveProbability, germ_endpointValue]
  | succ stage inductionHypothesis =>
      rw [game.expectedHistoryValue_succ]
      simp_rw [historyContinuationEU_prescribed]
      rw [expect_add, expect_const, expect_const_mul]
      change
        calendarHazard stage +
            (1 - calendarHazard stage) *
              game.expectedHistoryValue
                prescribedProfile false
                (fun _ history =>
                  germ.endpointValue history.2 false)
                stage =
          scalarEndpointTarget (stage + 1)
      rw [inductionHypothesis, scalarEndpointTarget_succ]

/-- Hence the prescribed expected endpoint target converges to the high
value one rather than remaining at the entry target zero. -/
theorem tendsto_expected_endpointValue_prescribedProfile_one :
    Tendsto
      (game.expectedHistoryValue
        prescribedProfile false
        (fun _ history =>
          germ.endpointValue history.2 false))
      atTop (nhds 1) := by
  change
    Tendsto
      (fun stage =>
        game.expectedHistoryValue
          prescribedProfile false
          (fun _ history =>
            germ.endpointValue history.2 false)
          stage)
      atTop (nhds 1)
  simpa only [expected_endpointValue_prescribedProfile] using
    tendsto_scalarEndpointTarget_one

private theorem stageEUAt_prescribed_eq
    {stage : ℕ} (history : game.Hist stage) :
    game.stageEUAt prescribedProfile history false =
      2 * germ.endpointValue history.2 false - 1 := by
  unfold StochasticGame.stageEUAt prescribedProfile
    AnalyticBellmanGerm.LowerValueJet.calendarFinkBehaviorProfile
  rw [game.stageActionDist_scheduledMarkovBehaviorProfile]
  rw [prescribedMixedProfile_eq stage history.2]
  simp_rw [expect_pmfPi_bool]
  simp_rw [germ_endpointValue]
  cases history.2 <;>
    simp [profile, game]
  all_goals ring

theorem expectedStagePayoff_prescribed_eq
    (stage : ℕ) :
    game.expectedStagePayoff prescribedProfile false stage false =
      2 * scalarEndpointTarget stage - 1 := by
  unfold StochasticGame.expectedStagePayoff
  simp_rw [stageEUAt_prescribed_eq]
  rw [expect_sub, expect_const, expect_const_mul]
  change
    2 *
        game.expectedHistoryValue prescribedProfile false
          (fun _ history =>
            germ.endpointValue history.2 false) stage -
      1 =
        2 * scalarEndpointTarget stage - 1
  rw [expected_endpointValue_prescribedProfile]

theorem tendsto_expectedStagePayoff_prescribed_one :
    Tendsto
      (game.expectedStagePayoff prescribedProfile false · false)
      atTop (nhds 1) := by
  have hmul :
      Tendsto
        (fun stage => (2 : ℝ) * scalarEndpointTarget stage)
        atTop (nhds (2 * 1)) :=
    tendsto_const_nhds.mul tendsto_scalarEndpointTarget_one
  have hsub :
      Tendsto
        (fun stage => (2 : ℝ) * scalarEndpointTarget stage - 1)
        atTop (nhds (2 * 1 - 1)) :=
    hmul.sub_const 1
  rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num] at hsub
  simpa only [expectedStagePayoff_prescribed_eq] using hsub

/-- The prescribed finite-average payoff converges to one, whereas the
entry endpoint target is zero. -/
theorem tendsto_finiteAveragePayoff_prescribed_one :
    Tendsto
      (fun horizon =>
        game.finiteAveragePayoff false horizon prescribedProfile false)
      atTop (nhds 1) := by
  have hcesaro :
      Tendsto
        (fun horizon : ℕ =>
          (horizon : ℝ)⁻¹ *
            ∑ stage ∈ Finset.range horizon,
              game.expectedStagePayoff
                prescribedProfile false stage false)
        atTop (nhds 1) :=
    tendsto_expectedStagePayoff_prescribed_one.cesaro
  simpa only [
    game.finiteAveragePayoff_eq_sum_expectedStagePayoff] using hcesaro

theorem endpointTarget_at_entry_eq_zero :
    germ.endpointValue false false = 0 := by
  simp

/-- Therefore no eventual two-sided realization estimate with an error
tending to zero can bind this prescribed profile to its entry endpoint
target. -/
theorem no_vanishing_twoSided_entryTarget_realization :
    ¬ ∃ error : ℕ → ℝ,
        Tendsto error atTop (nhds 0) ∧
        ∀ᶠ horizon in atTop,
          |game.finiteAveragePayoff
              false horizon prescribedProfile false -
            germ.endpointValue false false| ≤ error horizon := by
  rintro ⟨error, error_zero, bound⟩
  have payoff_error_one :
      Tendsto
        (fun horizon =>
          |game.finiteAveragePayoff
              false horizon prescribedProfile false -
            germ.endpointValue false false|)
        atTop (nhds 1) := by
    rw [endpointTarget_at_entry_eq_zero]
    simpa using tendsto_finiteAveragePayoff_prescribed_one.abs
  have one_le_zero : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto payoff_error_one error_zero bound
  norm_num at one_le_zero

end PrescribedEndpointTargetTransportNoGo
end StochasticGame
end GameTheory
