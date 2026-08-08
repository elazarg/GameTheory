/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.FiniteBiasPlayerOwnedTargetTransportBoundary
import UniformEquilibrium.Examples.BigMatch.Uniform

/-!
# Endpoint target transport is not an automatic calendar account

This file gives a two-state, two-player analytic Bellman germ for which the
finite-bias forcing and its Poisson correction vanish, while an endpoint-
neutral owner action creates a positive-parameter leak into a higher-value
absorbing state.

The example isolates the target-transport term in
`FiniteBiasPlayerOwnedResidualBridge`.  The leak probability tends to zero
along the universal calendar, but its cumulative hazard is infinite.
Consequently the expected endpoint target converges to the higher absorbing
value and its Cesàro average converges to one.

Thus endpoint harmonicity and the finite-bias Poisson equation do not make
the calendar target-transport term sublinear.  A sufficient extra hypothesis
is superharmonicity of the endpoint target for every actual moving
player-owned action row.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace PlayerOwnedEndpointTargetTransportNoGo

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

def ownerAction (action : ∀ player, Act player) : Bool :=
  action false

def otherAction (action : ∀ player, Act player) : Bool :=
  action true

/-- `false` is the low state and `true` is the high absorbing state.
At the low state, the owner can enable a leak which occurs exactly when the
other player uses their rare action. -/
abbrev game : StochasticGame Player where
  State := State
  Act := Act
  stagePayoff state action player :=
    if player then
      0
    else if state then
      1
    else if ownerAction action then
      if otherAction action then 0 else -1
    else
      0
  transition state action :=
    if state then
      PMF.pure true
    else if ownerAction action && otherAction action then
      PMF.pure true
    else
      PMF.pure false
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

/-- A Boolean coin with true probability `p`. -/
def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  GameTheory.StochasticGame.BigMatch.coinPMF p hp0 hp1

@[simp]
theorem coin_true_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 true).toReal = p := by
  exact GameTheory.StochasticGame.BigMatch.coinPMF_apply_true_toReal
    p hp0 hp1

@[simp]
theorem coin_false_toReal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 false).toReal = 1 - p := by
  exact GameTheory.StochasticGame.BigMatch.coinPMF_apply_false_toReal
    p hp0 hp1

theorem expect_coin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (coin p hp0 hp1) f =
      p * f true + (1 - p) * f false := by
  exact GameTheory.StochasticGame.BigMatch.expect_coinPMF p hp0 hp1 f

/-- At positive parameter `t`, the owner plays safe while the other player
uses the rare action with probability `t` in the low state. -/
def profile (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    game.StationaryMixedProfile :=
  fun state player =>
    if state then PMF.pure false
    else if player then coin t ht0 ht1
    else PMF.pure false

/-- The selected discounted value is constant along the analytic branch. -/
def value (state : State) (player : Player) : ℝ :=
  if player then 0 else if state then 1 else 0

/-- The shared Fubini expansion of a product of two Boolean mixed actions,
specialized to this file's player index. -/
private theorem expect_pmfPi_bool
    (m : Player → PMF Bool) (f : (Player → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun owner =>
        expect (m true) (fun other =>
          f (fun player => if player then other else owner))) :=
  BigMatch.expect_pmfPi_bool m f

private theorem pureDeviationAuxEU_eq
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (state : State) (player : Player) (action : game.Act player) :
    game.discountedAuxEU (1 - t) value state
        (Function.update (profile t ht0 ht1 state)
          player (PMF.pure action)) player =
      game.discountedAuxEU (1 - t) value state
        (profile t ht0 ht1 state) player := by
  rw [game.discountedAuxEU_eq, game.discountedAuxEU_eq]
  simp_rw [expect_pmfPi_bool]
  cases state <;> cases player <;> cases action
  all_goals
    simp [profile, value, game, ownerAction, otherAction,
      expect_coin, Function.update]
  all_goals ring_nf

/-- The parameterized profile and the constant value solve the discounted
Bellman equations at discount factor `1 - t`. -/
theorem equilibrium
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    game.IsDiscountedStationaryBellmanEq
      (1 - t) (profile t ht0 ht1) value := by
  constructor
  · intro state player deviation
    rw [game.discountedAuxEU_update_eq_expect_pure]
    calc
      expect deviation
          (fun action =>
            game.discountedAuxEU (1 - t) value state
              (Function.update (profile t ht0 ht1 state)
                player (PMF.pure action)) player) =
          expect deviation
            (fun _ =>
              game.discountedAuxEU (1 - t) value state
                (profile t ht0 ht1 state) player) := by
            congr 1
            funext action
            exact pureDeviationAuxEU_eq
              t ht0 ht1 state player action
      _ ≤ game.discountedAuxEU (1 - t) value state
          (profile t ht0 ht1 state) player := by
        exact le_of_eq (expect_const _ _)
  · intro state player
    rw [game.discountedAuxEU_eq]
    simp_rw [expect_pmfPi_bool]
    cases state <;> cases player
    all_goals
      simp [profile, value, game, ownerAction, otherAction,
        expect_coin]

/-- Polynomial mixing weights used to extend the Bellman assignment
analytically through the endpoint. -/
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
  | .val state player => value state player
  | .disc => t

private theorem assignment_eq_bellmanAssignment
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    assignment t =
      game.bellmanAssignment (profile t ht0 ht1) value (1 - t) := by
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

/-- A genuine analytic Bellman germ realizing the leaking equilibrium
branch. -/
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
        exact analyticAt_const
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
    germ.endpointValue state player = value state player :=
  rfl

/-- The endpoint decodes to the pure no-leak profile. -/
theorem germ_endpointProfile :
    germ.endpointProfile =
      profile 0 (le_refl 0) zero_le_one := by
  unfold AnalyticBellmanGerm.endpointProfile
  funext state player
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  unfold Math.ProbabilityMassFunction.toVector
  rw [game.bellmanDecodeProfile_apply_toReal]
  cases state <;> cases player <;> cases action <;>
    simp [AnalyticBellmanGerm.endpoint, germ, assignment, weight,
      profile, coin]

/-- The decoded value curve is constant. -/
theorem germ_valueCurve (t : ℝ) :
    germ.valueCurve t = value :=
  rfl

/-- Hence the relative value increment vanishes identically. -/
theorem germ_valueIncrement (t : ℝ) :
    germ.valueIncrement t = 0 := by
  have hendpoint : germ.endpointValue = value := by
    funext state player
    exact germ_endpointValue state player
  change germ.valueCurve t - germ.endpointValue = 0
  rw [germ_valueCurve, hendpoint]
  exact sub_self value

/-- The example lies in the finite-bias branch with the zero factor. -/
def finiteBiasSeed : germ.FiniteBiasSeed where
  factor := 0
  analytic_factor := analyticAt_const
  valueIncrement_eq := by
    filter_upwards [] with t
    simp [germ_valueIncrement]

@[simp]
theorem finiteBiasSeed_H :
    finiteBiasSeed.H = 0 := by
  simp [finiteBiasSeed, AnalyticBellmanGerm.FiniteBiasSeed.H,
    AnalyticBellmanGerm.FiniteBiasSeed.extension]

/-- The endpoint on-profile stage payoff already equals the endpoint value. -/
theorem finkStageEU_endpoint_eq_value
    (state : State) (player : Player) :
    game.finkStageEU germ.endpointFinkPoint state player =
      value state player := by
  unfold StochasticGame.finkStageEU
  rw [germ.finkProfile_endpointFinkPoint, germ_endpointProfile]
  simp_rw [expect_pmfPi_bool]
  cases state <;> cases player <;>
    simp [profile, value, game, ownerAction, otherAction]

/-- In particular the limiting Bellman forcing is exactly zero, so the zero
Poisson correction is valid. -/
theorem finkBellmanForcingVector_endpoint_eq_zero :
    game.finkBellmanForcingVector
        germ.endpointValue finiteBiasSeed.H
        germ.endpointFinkPoint = 0 := by
  ext state player
  unfold StochasticGame.finkBellmanForcingVector
  rw [finiteBiasSeed_H, finkStageEU_endpoint_eq_value]
  simp [germ_endpointValue, StochasticGame.finkContinuationEU]

/-- At every positive parameter, the canonical Fink point decodes to the
explicit leaking profile. -/
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

/-- All raw stage gains are nonpositive on this branch.  The owner is
indifferent in discounted auxiliary payoff only because the negative
current gain pays for the positive continuation leak. -/
theorem finkStageGain_nonpos
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (state : State) (player : Player) (action : game.Act player) :
    game.finkStageGain (germ.finkPointAt ht)
        state player action ≤ 0 := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  unfold StochasticGame.finkStageGain StochasticGame.mixedStageEU
  rw [finkProfile_finkPointAt ht]
  simp_rw [expect_pmfPi_bool]
  cases state <;> cases player <;> cases action <;>
    simp [profile, game, ownerAction, otherAction, expect_coin,
      Function.update]
  all_goals linarith

/-- With zero bias, every player-owned moving charge is nonpositive. -/
theorem rawPlayerOwnedOccupationCharge_zero_nonpos
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (player : Player)
    (index : AnalyticBellmanGerm.OwnerOccupationIndex game player) :
    germ.rawPlayerOwnedOccupationCharge 0 player t index ≤ 0 := by
  rw [germ.rawPlayerOwnedOccupationCharge_eq_finkPointAt 0 ht]
  cases index with
  | inl state =>
      rfl
  | inr response =>
      rcases response with ⟨state, action⟩
      have hstage := finkStageGain_nonpos ht state player action
      have hcontinuation :
          game.finkContinuationGain 0 (germ.finkPointAt ht)
              state player action = 0 := by
        apply game.finkContinuationGain_eq_zero_of_stateConstant
        intro who source destination
        rfl
      simp only [hcontinuation, add_zero]
      exact hstage

/-- The common-potential branch is realized by pole order zero and the zero
state potential for both players. -/
def commonZeroPotential :
    AnalyticOwnerScaledChargedOccupationPotential
      (fun player =>
        AnalyticBellmanGerm.OwnerOccupationIndex game player)
      (fun player => germ.rawOwnerAnalyticOccupationColumn player)
      (fun player => germ.rawPlayerOwnedOccupationCharge 0 player) where
  poleOrder := 0
  potential := fun _ _ _ => 0
  analytic_potential := fun _ => analyticAt_const
  eventual := by
    filter_upwards
        [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    intro player index
    simpa using
      rawPlayerOwnedOccupationCharge_zero_nonpos ht player index

/-! ## The universal calendar accumulates the invisible leak -/

/-- Leak hazard at one absolute calendar stage. -/
def calendarHazard (stage : ℕ) : ℝ :=
  AnalyticBellmanGerm.playerOwnedCalendarScale 0 stage

theorem calendarHazard_pos (stage : ℕ) :
    0 < calendarHazard stage := by
  exact shiftedUniversalEpochScale_pos
    0 (anytimeEpochIndex stage)

private theorem universalEpochScale_lt_one (epoch : ℕ) :
    universalEpochScale epoch < 1 := by
  have harg :
      Real.exp 1 < universalCalendarArgument epoch := by
    rw [universalCalendarArgument]
    have hexp : Real.exp 1 < Real.exp 2 :=
      Real.exp_lt_exp.mpr (by norm_num)
    exact hexp.trans_le (le_add_of_nonneg_left (by positivity))
  have hlog :
      1 < Real.log (universalCalendarArgument epoch) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log
      (Real.exp_pos 1) (universalCalendarArgument_pos epoch) harg
  unfold universalEpochScale
  exact inv_lt_one_of_one_lt₀ hlog

theorem calendarHazard_lt_one (stage : ℕ) :
    calendarHazard stage < 1 := by
  simpa [calendarHazard,
    AnalyticBellmanGerm.playerOwnedCalendarScale,
    AnalyticBellmanGerm.calendarScale,
    shiftedUniversalEpochScale] using
      universalEpochScale_lt_one (anytimeEpochIndex stage)

theorem calendarHazard_mem_Ioo (stage : ℕ) :
    calendarHazard stage ∈ Ioo (0 : ℝ) 1 :=
  ⟨calendarHazard_pos stage, calendarHazard_lt_one stage⟩

private theorem anytimeEpochIndex_le (stage : ℕ) :
    anytimeEpochIndex stage ≤ stage := by
  exact
    (le_anytimeEpochStart (anytimeEpochIndex stage)).trans
      (anytimeEpochStart_index_le stage)

private theorem antitone_universalEpochScale :
    Antitone universalEpochScale := by
  intro earlier later hle
  have harg :
      universalCalendarArgument earlier ≤
        universalCalendarArgument later := by
    unfold universalCalendarArgument
    simpa [add_comm] using
      add_le_add_right (Nat.cast_le.mpr hle) (Real.exp 2)
  have hlog :
      Real.log (universalCalendarArgument earlier) ≤
        Real.log (universalCalendarArgument later) :=
    Real.strictMonoOn_log.monotoneOn
      (universalCalendarArgument_pos earlier)
      (universalCalendarArgument_pos later) harg
  unfold universalEpochScale
  simpa [one_div] using
    one_div_le_one_div_of_le
      (Real.log_pos (one_lt_universalCalendarArgument earlier))
      hlog

/-- The stage hazard dominates a shifted harmonic-order sequence. -/
theorem reciprocalCalendarArgument_le_hazard (stage : ℕ) :
    1 / universalCalendarArgument stage ≤ calendarHazard stage := by
  have hlog :
      Real.log (universalCalendarArgument stage) ≤
        universalCalendarArgument stage :=
    (Real.log_le_sub_one_of_pos
      (universalCalendarArgument_pos stage)).trans
        (sub_le_self _ zero_le_one)
  calc
    1 / universalCalendarArgument stage ≤
        universalEpochScale stage := by
      unfold universalEpochScale
      simpa only [one_div] using
        one_div_le_one_div_of_le
          (Real.log_pos (one_lt_universalCalendarArgument stage))
          hlog
    _ ≤ universalEpochScale (anytimeEpochIndex stage) :=
      antitone_universalEpochScale (anytimeEpochIndex_le stage)
    _ = calendarHazard stage := by
      simp [calendarHazard,
        AnalyticBellmanGerm.playerOwnedCalendarScale,
        AnalyticBellmanGerm.calendarScale,
        shiftedUniversalEpochScale]

private theorem not_summable_reciprocalCalendarArgument :
    ¬ Summable (fun stage : ℕ =>
      1 / universalCalendarArgument stage) := by
  let c : ℝ := 1 / Real.exp 2
  have hexp : 0 < Real.exp 2 := Real.exp_pos 2
  have hexpOne : 1 ≤ Real.exp 2 :=
    Real.one_le_exp (by norm_num)
  have hc : 0 < c := one_div_pos.mpr hexp
  have hminorize :
      ∀ stage : ℕ,
        c * (1 / ((stage : ℝ) + 1)) ≤
          1 / universalCalendarArgument stage := by
    intro stage
    have hden :
        (stage : ℝ) + Real.exp 2 ≤
          Real.exp 2 * ((stage : ℝ) + 1) := by
      have hstage : (0 : ℝ) ≤ stage := by positivity
      nlinarith
    calc
      c * (1 / ((stage : ℝ) + 1)) =
          1 / (Real.exp 2 * ((stage : ℝ) + 1)) := by
        dsimp [c]
        field_simp [hexp.ne']
      _ ≤ 1 / ((stage : ℝ) + Real.exp 2) :=
        one_div_le_one_div_of_le
          (by positivity) hden
      _ = 1 / universalCalendarArgument stage := by
        rw [universalCalendarArgument]
  intro hs
  have hscaled :
      Summable (fun stage : ℕ =>
        c * (1 / ((stage : ℝ) + 1))) :=
    Summable.of_nonneg_of_le
      (fun stage => mul_nonneg hc.le (by positivity))
      hminorize hs
  have hharmonic :
      Summable (fun stage : ℕ => 1 / ((stage : ℝ) + 1)) :=
    (summable_mul_left_iff hc.ne').mp hscaled
  have hnonneg :
      ∀ stage : ℕ, 0 ≤ 1 / ((stage : ℝ) + 1) :=
    fun _ => by positivity
  have hnot :
      ¬ Summable (fun stage : ℕ =>
        1 / ((stage : ℝ) + 1)) :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).2
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact hnot hharmonic

theorem not_summable_calendarHazard :
    ¬ Summable calendarHazard := by
  intro hs
  have hlower :
      Summable (fun stage : ℕ =>
        1 / universalCalendarArgument stage) :=
    Summable.of_nonneg_of_le
      (fun stage =>
        one_div_nonneg.mpr
          (universalCalendarArgument_pos stage).le)
      reciprocalCalendarArgument_le_hazard hs
  exact not_summable_reciprocalCalendarArgument hlower

def survivalProbability (stage : ℕ) : ℝ :=
  BigMatch.MarkovScalar.liveProbability calendarHazard stage

theorem tendsto_survivalProbability_zero :
    Tendsto survivalProbability atTop (nhds 0) := by
  have hbranch :=
    BigMatch.MarkovScalar.summable_or_tendsto_liveProbability_zero
      calendarHazard
      (fun stage => (calendarHazard_pos stage).le)
      (fun stage => (calendarHazard_lt_one stage).le)
  exact hbranch.resolve_left not_summable_calendarHazard

/-- Expected endpoint target in the scalar leaking process at one stage. -/
def scalarEndpointTarget (stage : ℕ) : ℝ :=
  1 - survivalProbability stage

/-- Cumulative endpoint target transport in the scalar leaking process. -/
def scalarEndpointTargetTransport (T : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range T, scalarEndpointTarget stage

theorem tendsto_scalarEndpointTarget_one :
    Tendsto scalarEndpointTarget atTop (nhds 1) := by
  change
    Tendsto (fun stage => 1 - survivalProbability stage)
      atTop (nhds 1)
  simpa using tendsto_const_nhds.sub tendsto_survivalProbability_zero

/-- The normalized target transport converges to one, not zero. -/
theorem tendsto_normalized_scalarEndpointTargetTransport_one :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ)⁻¹ * scalarEndpointTargetTransport T)
      atTop (nhds 1) := by
  unfold scalarEndpointTargetTransport
  exact tendsto_scalarEndpointTarget_one.cesaro

/-- Therefore this endpoint target-transport process is not asymptotically
sublinear. -/
theorem scalarEndpointTargetTransport_not_sublinear :
    ¬ IsAsymptoticallySublinear scalarEndpointTargetTransport := by
  intro hsublinear
  have hzero :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ)⁻¹ * scalarEndpointTargetTransport T)
        atTop (nhds 0) := by
    exact isAsymptoticallySublinear_iff_tendsto.mp hsublinear
  have hfalse : (1 : ℝ) = 0 :=
    tendsto_nhds_unique
      tendsto_normalized_scalarEndpointTargetTransport_one hzero
  norm_num at hfalse

/-! ## Exact finite-state realization of the scalar process -/

def lowIndicator (state : State) : ℝ :=
  if state then 0 else 1

def leakKernel (stage : ℕ) (state : State) : PMF State :=
  if state then
    PMF.pure true
  else
    coin (calendarHazard stage)
      (calendarHazard_pos stage).le
      (calendarHazard_lt_one stage).le

def calendarStateLaw : ℕ → PMF State
  | 0 => PMF.pure false
  | stage + 1 =>
      (calendarStateLaw stage).bind (leakKernel stage)

def calendarLowMass (stage : ℕ) : ℝ :=
  expect (calendarStateLaw stage) lowIndicator

private theorem expect_leakKernel_lowIndicator
    (stage : ℕ) (state : State) :
    expect (leakKernel stage state) lowIndicator =
      (1 - calendarHazard stage) * lowIndicator state := by
  cases state <;>
    simp [leakKernel, lowIndicator, expect_coin]

theorem calendarLowMass_succ (stage : ℕ) :
    calendarLowMass (stage + 1) =
      calendarLowMass stage * (1 - calendarHazard stage) := by
  rw [calendarLowMass, calendarStateLaw, expect_bind]
  simp_rw [expect_leakKernel_lowIndicator]
  rw [expect_const_mul]
  unfold calendarLowMass
  ring

theorem calendarLowMass_eq_survivalProbability (stage : ℕ) :
    calendarLowMass stage = survivalProbability stage := by
  induction stage with
  | zero =>
      simp [calendarLowMass, calendarStateLaw, lowIndicator,
        survivalProbability,
        BigMatch.MarkovScalar.liveProbability]
  | succ stage ih =>
      rw [calendarLowMass_succ, ih]
      simpa [survivalProbability] using
        (BigMatch.MarkovScalar.liveProbability_succ
          calendarHazard stage).symm

/-- The state law's expected owner endpoint value is exactly the scalar
target process. -/
theorem expected_endpointValue_calendarStateLaw
    (stage : ℕ) :
    expect (calendarStateLaw stage)
        (fun state => germ.endpointValue state false) =
      scalarEndpointTarget stage := by
  have hvalue :
      (fun state : State => germ.endpointValue state false) =
        fun state => 1 - lowIndicator state := by
    funext state
    cases state <;> simp [germ_endpointValue, value, lowIndicator]
  rw [hvalue, expect_sub, expect_const]
  change 1 - calendarLowMass stage =
    1 - survivalProbability stage
  rw [calendarLowMass_eq_survivalProbability]

/-! ## The scalar law is the actual scheduled unilateral deviation law -/

/-- The owner always enables the leak. -/
def alwaysEnableDeviation : game.BehaviorStrategy false :=
  fun _ _ => PMF.pure true

/-- Every parameter of the unshifted universal calendar lies in the germ's
punctured validity interval. -/
theorem calendarValid (epoch : ℕ) :
    shiftedUniversalEpochScale 0 epoch ∈ Ioo (0 : ℝ) germ.radius := by
  rw [show germ.radius = 1 by rfl]
  constructor
  · exact shiftedUniversalEpochScale_pos 0 epoch
  · simpa [shiftedUniversalEpochScale] using
      universalEpochScale_lt_one epoch

/-- The generic player-owned scheduled-deviation profile for the owner who
always enables the leak. -/
def scheduledLeakProfile : game.BehaviorProfile :=
  AnalyticBellmanGerm.scheduledPlayerOwnedFinkDeviationProfile
    germ false 0 calendarValid alwaysEnableDeviation

private theorem endpointValue_finkOwnerAlwaysEnable
    (stage : ℕ) (state : State) :
    expect
        (germ.finkOwnerActualOccupationKernelAt
          (calendarValid (anytimeEpochIndex stage))
          false (.inr (state, true)))
        (fun destination => germ.endpointValue destination false) =
      calendarHazard stage +
        (1 - calendarHazard stage) *
          germ.endpointValue state false := by
  unfold AnalyticBellmanGerm.finkOwnerActualOccupationKernelAt
    AnalyticBellmanGerm.ownerOccupationIndexEmbedding
    AnalyticBellmanGerm.finkActualOccupationKernelAt
    occupationKernel
  change
    expect
        (game.finkPureDeviationStateKernel
          (germ.finkPointAt
            (calendarValid (anytimeEpochIndex stage)))
          state false true)
        (fun destination => germ.endpointValue destination false) =
      _
  unfold StochasticGame.finkPureDeviationStateKernel
  rw [finkProfile_finkPointAt
    (calendarValid (anytimeEpochIndex stage))]
  simp_rw [germ_endpointValue]
  rw [expect_bind]
  simp_rw [expect_pmfPi_bool]
  cases state <;>
    simp [profile, game, ownerAction, otherAction, value, calendarHazard,
      AnalyticBellmanGerm.playerOwnedCalendarScale,
      AnalyticBellmanGerm.calendarScale,
      shiftedUniversalEpochScale, Function.update, expect_coin]

private theorem historyContinuationEU_scheduledLeakProfile
    {stage : ℕ} (history : game.Hist stage) :
    game.historyContinuationEU
        scheduledLeakProfile
        (fun _ nextHistory =>
          germ.endpointValue nextHistory.2 false)
        history =
      calendarHazard stage +
        (1 - calendarHazard stage) *
          germ.endpointValue history.2 false := by
  calc
    _ =
        expect
          (AnalyticBellmanGerm.LowerValueJet.behaviorStateStep
            scheduledLeakProfile history)
          (fun destination =>
            germ.endpointValue destination false) :=
      AnalyticBellmanGerm.historyContinuationEU_statePotential_eq_behaviorStateStep
        (G := game) scheduledLeakProfile
        (fun destination => germ.endpointValue destination false)
        history
    _ = _ := by
      unfold scheduledLeakProfile
      rw [
        AnalyticBellmanGerm.behaviorStateStep_scheduledPlayerOwnedFinkDeviationProfile
          germ false 0 calendarValid alwaysEnableDeviation history]
      unfold AnalyticBellmanGerm.playerOwnedCalendarMixedStep
        alwaysEnableDeviation
      rw [PMF.pure_bind]
      exact endpointValue_finkOwnerAlwaysEnable stage history.2

private theorem scalarEndpointTarget_succ (stage : ℕ) :
    scalarEndpointTarget (stage + 1) =
      calendarHazard stage +
        (1 - calendarHazard stage) *
          scalarEndpointTarget stage := by
  unfold scalarEndpointTarget
  rw [show survivalProbability (stage + 1) =
      survivalProbability stage * (1 - calendarHazard stage) by
    exact BigMatch.MarkovScalar.liveProbability_succ
      calendarHazard stage]
  ring

/-- The generic scheduled-deviation history law has exactly the same
expected endpoint target as the explicit scalar leak process. -/
theorem expected_endpointValue_scheduledLeakProfile
    (stage : ℕ) :
    game.expectedHistoryValue
        scheduledLeakProfile false
        (fun _ history =>
          germ.endpointValue history.2 false)
        stage =
      scalarEndpointTarget stage := by
  induction stage with
  | zero =>
      simp [StochasticGame.expectedHistoryValue,
        StochasticGame.emptyHist, scheduledLeakProfile,
        scalarEndpointTarget,
        survivalProbability, BigMatch.MarkovScalar.liveProbability,
        germ_endpointValue, value]
  | succ stage inductionHypothesis =>
      rw [game.expectedHistoryValue_succ]
      simp_rw [historyContinuationEU_scheduledLeakProfile]
      rw [expect_add, expect_const, expect_const_mul]
      change
        calendarHazard stage +
            (1 - calendarHazard stage) *
              game.expectedHistoryValue
                scheduledLeakProfile false
                (fun _ history =>
                  germ.endpointValue history.2 false)
                stage =
          scalarEndpointTarget (stage + 1)
      rw [inductionHypothesis, scalarEndpointTarget_succ]

/-- The target-transport term of the generic player-owned calendar account
is exactly the explicit scalar target transport. -/
theorem expectedPlayerOwnedCalendarEndpointTargetTransport_eq_scalar
    (T : ℕ) :
    AnalyticBellmanGerm.FiniteBiasSeed.expectedPlayerOwnedCalendarEndpointTargetTransport
        germ false false 0 calendarValid alwaysEnableDeviation false T =
      scalarEndpointTargetTransport T := by
  unfold
    AnalyticBellmanGerm.FiniteBiasSeed.expectedPlayerOwnedCalendarEndpointTargetTransport
    scalarEndpointTargetTransport
  apply Finset.sum_congr rfl
  intro stage _
  change
    game.expectedHistoryValue
        scheduledLeakProfile false
        (fun _ history =>
          germ.endpointValue history.2 false -
            germ.endpointValue false false)
        stage =
      scalarEndpointTarget stage
  have hentry : germ.endpointValue false false = 0 := by
    simp [germ_endpointValue, value]
  rw [hentry]
  simp only [sub_zero]
  exact expected_endpointValue_scheduledLeakProfile stage

/-- Therefore no uniformly sublinear target-transport account can cover
all unilateral deviations in this analytic Bellman germ. -/
theorem no_playerOwnedCalendarEndpointTargetTransportAccount :
    ¬ Nonempty
      (AnalyticBellmanGerm.FiniteBiasSeed.PlayerOwnedCalendarEndpointTargetTransportAccount
        germ false 0 calendarValid) := by
  rintro ⟨account⟩
  have hbudget :
      Tendsto
        (fun T : ℕ => (T : ℝ)⁻¹ * account.budget false T)
        atTop (nhds 0) :=
    isAsymptoticallySublinear_iff_tendsto.mp (account.sublinear false)
  have hlimit : (1 : ℝ) ≤ 0 := by
    apply le_of_tendsto_of_tendsto
      tendsto_normalized_scalarEndpointTargetTransport_one
      hbudget
    filter_upwards [] with T
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [
      ← expectedPlayerOwnedCalendarEndpointTargetTransport_eq_scalar T]
    exact
      account.transport_le false alwaysEnableDeviation T
  norm_num at hlimit

end PlayerOwnedEndpointTargetTransportNoGo
end StochasticGame
end GameTheory
