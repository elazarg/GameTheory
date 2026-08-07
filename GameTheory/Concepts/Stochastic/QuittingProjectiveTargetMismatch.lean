/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingProjectiveAnalyticPacket
import GameTheory.Concepts.Stochastic.QuittingExceptionalTailProfileAdapter
import GameTheory.Concepts.Stochastic.QuittingSureExitSet
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection
import GameTheory.Concepts.Stochastic.QuittingStationaryMinMax
import GameTheory.Concepts.Stochastic.AnalyticBellmanHierarchy
import Math.PMFProduct.Bool

/-!
# A projective packet whose analytic endpoint is not a uniform target

This module is a target-selection regression for the projective quitting-game
pipeline.  It exhibits a two-player quitting game with all of the following
features:

* a genuine analytic branch of exact discounted stationary Bellman
  equilibria;
* matching discount and quit orders, producing the normalized singleton
  packet with cemetery and both singleton weights equal to `1 / 3`;
* analytic endpoint value `(1, 1)`;
* a fixed quantitative separation between `(1, 1)` and every sufficiently
  accurate terminal approximate equilibrium;
* elementary exact uniform-equilibrium payoffs `(1, 2)` and `(2, 1)`.

Thus matching-order analytic packet extraction does not by itself preserve
the extracted endpoint through strategic production.  A positive cemetery
coordinate is an affine accounting device, not an executable continuation
contract.  Any producer which is meant to preserve a declared target must
therefore pass through the repository's target-acceptance or target-rejection
gate before invoking chronological realization.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingProjectiveTargetMismatch

open QuittingSureSetOwnerRepair

abbrev Player := Bool
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The owner of a singleton exit receives `1`; every other absorbing
coordinate receives `2`.  Equivalently,
`r({false}) = (1,2)`, `r({true}) = (2,1)`, and `r({false,true}) = (2,2)`. -/
def reward (S : Terminal) : Payoff Player :=
  fun who => if S.1 = {who} then 1 else 2

@[simp] theorem reward_singleton_self (who : Player)
    (h : ({who} : Finset Player).Nonempty) :
    reward ⟨{who}, h⟩ who = 1 := by
  simp [reward]

@[simp] theorem reward_singleton_other {who other : Player}
    (hne : other ≠ who) (h : ({who} : Finset Player).Nonempty) :
    reward ⟨{who}, h⟩ other = 2 := by
  simp [reward, hne.symm]

@[simp] theorem reward_pair (who : Player)
    (h : ({false, true} : Finset Player).Nonempty) :
    reward ⟨{false, true}, h⟩ who = 2 := by
  cases who <;> simp [reward, Finset.ext_iff]

/-- Explicit quitter set for a two-coordinate Boolean action. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool => if who then second else first) =
      (if first then {false} else ∅) ∪ (if second then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

@[simp] theorem quittingQuitters_id :
    quittingQuitters (fun who : Bool => who) = {true} := by
  simpa using quittingQuitters_boolAction false true

@[simp] theorem quittingQuitters_not :
    quittingQuitters (fun who : Bool => !who) = {false} := by
  simpa using quittingQuitters_boolAction true false

@[simp] theorem quittingQuitters_const_true :
    quittingQuitters (fun _ : Bool => true) = {false, true} := by
  simpa using quittingQuitters_boolAction true true

/-- The analytic active-state quit probability. -/
def hazard (t : ℝ) : ℝ := t / (1 - t)

theorem hazard_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ hazard t := by
  exact div_nonneg ht0 (by linarith)

theorem hazard_le_one {t : ℝ} (_ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2) :
    hazard t ≤ 1 := by
  have hden : 0 < 1 - t := by linarith
  rw [hazard, div_le_one hden]
  linarith

/-- Both players use the analytic hazard at the live state.  Actions at an
absorbed state are immaterial and are fixed to Continue. -/
def profile (t : ℝ) (ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2) :
    (quittingGame reward).StationaryMixedProfile :=
  fun state _ =>
    match state with
    | none => quittingHazardCoin (hazard t)
        (hazard_nonneg ht0 (by linarith)) (hazard_le_one ht0 hthalf)
    | some _ => PMF.pure false

/-- The live value is constantly `1`; absorbed-state values are their fixed
terminal rewards. -/
def value (state : (quittingGame reward).State) : Payoff Player :=
  match state with
  | none => fun _ => 1
  | some terminal => reward terminal

private theorem expect_pmfPi_bool
    (m : Player → PMF Bool) (f : (Player → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun first =>
        expect (m true) (fun second =>
          f (fun who => if who then second else first))) :=
  Math.PMFProduct.expect_pmfPi_bool m f

@[simp] theorem expect_hazardCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

private theorem pureDeviationAuxEU_eq
    (t : ℝ) (ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2)
    (state : (quittingGame reward).State) (who : Player)
    (action : (quittingGame reward).Act who) :
    (quittingGame reward).discountedAuxEU (1 - t) value state
        (Function.update (profile t ht0 hthalf state) who (PMF.pure action)) who =
    (quittingGame reward).discountedAuxEU (1 - t) value state
        (profile t ht0 hthalf state) who := by
  have hden : 1 - t ≠ 0 := by linarith
  rcases state with _ | terminal
  · rw [discountedAuxEU_quittingGame_none,
      discountedAuxEU_quittingGame_none]
    unfold quittingRootExpectedPayoff
    rw [expect_pmfPi_bool, expect_pmfPi_bool]
    cases who <;> cases action <;>
      simp [profile, value, quittingGame, quittingRootPayoff, reward,
        hazard, expect_hazardCoin, Function.update, Finset.ext_iff] <;>
      field_simp [hden] <;> ring_nf <;> simp_all
  · rw [discountedAuxEU_quittingGame_some,
      discountedAuxEU_quittingGame_some]

/-- For `0 ≤ t ≤ 1/2`, the explicit stationary profile and value solve
the exact discounted Bellman system at discount factor `1 - t`. -/
theorem equilibrium
    (t : ℝ) (ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2) :
    (quittingGame reward).IsDiscountedStationaryBellmanEq
      (1 - t) (profile t ht0 hthalf) value := by
  constructor
  · intro state who deviation
    rw [(quittingGame reward).discountedAuxEU_update_eq_expect_pure]
    calc
      expect deviation (fun action =>
          (quittingGame reward).discountedAuxEU (1 - t) value state
            (Function.update (profile t ht0 hthalf state) who
              (PMF.pure action)) who) =
        expect deviation (fun _ =>
          (quittingGame reward).discountedAuxEU (1 - t) value state
            (profile t ht0 hthalf state) who) := by
          congr 1
          funext action
          exact pureDeviationAuxEU_eq t ht0 hthalf state who action
      _ ≤ (quittingGame reward).discountedAuxEU (1 - t) value state
          (profile t ht0 hthalf state) who :=
        le_of_eq (expect_const _ _)
  · intro state who
    have hden : 1 - t ≠ 0 := by linarith
    rcases state with _ | terminal
    · rw [discountedAuxEU_quittingGame_none]
      unfold quittingRootExpectedPayoff
      rw [expect_pmfPi_bool]
      cases who <;>
        simp [profile, value, quittingRootPayoff, reward,
          hazard, expect_hazardCoin, Finset.ext_iff] <;>
        field_simp [hden] <;> ring_nf
    · rw [discountedAuxEU_quittingGame_some]
      simp only [value]
      ring

/-- Bellman coordinates written without proof-dependent probability objects. -/
def assignment (t : ℝ) : BellmanVar (quittingGame reward) → ℝ
  | .mix state _ action =>
      match state with
      | none => if (show Bool from action) then hazard t else 1 - hazard t
      | some _ => if (show Bool from action) then 0 else 1
  | .val state who => value state who
  | .disc => t

private theorem assignment_eq_bellmanAssignment
    (t : ℝ) (ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2) :
    assignment t = (quittingGame reward).bellmanAssignment
      (profile t ht0 hthalf) value (1 - t) := by
  funext coordinate
  cases coordinate with
  | mix state who action =>
      rcases state with _ | terminal
      · cases action
        · change 1 - hazard t =
            ((quittingHazardCoin (hazard t)
              (hazard_nonneg ht0 (by linarith))
              (hazard_le_one ht0 hthalf)) false).toReal
          symm
          exact quittingHazardCoin_false_toReal _ _ _
        · change hazard t =
            ((quittingHazardCoin (hazard t)
              (hazard_nonneg ht0 (by linarith))
              (hazard_le_one ht0 hthalf)) true).toReal
          symm
          exact quittingHazardCoin_true_toReal _ _ _
      · cases action <;>
          simp [assignment, StochasticGame.bellmanAssignment, profile]
  | val state who => rfl
  | disc => simp [assignment, StochasticGame.bellmanAssignment]

/-- A genuine matching-order analytic germ of exact discounted stationary
equilibria. -/
def germ : (quittingGame reward).AnalyticBellmanGerm where
  ramification := 1
  radius := 1 / 2
  assignment := assignment
  ramification_pos := Nat.zero_lt_succ 0
  radius_pos := by norm_num
  analytic_assignment := by
    have hHazard : AnalyticAt ℝ hazard 0 := by
      unfold hazard
      exact analyticAt_id.div
        (analyticAt_const.sub analyticAt_id) (by norm_num)
    rw [analyticAt_pi_iff]
    intro coordinate
    cases coordinate with
    | mix state who action =>
        rcases state with _ | terminal <;> cases action
        · change AnalyticAt ℝ (fun t : ℝ => 1 - hazard t) 0
          exact analyticAt_const.sub hHazard
        · change AnalyticAt ℝ hazard 0
          exact hHazard
        all_goals exact analyticAt_const
    | val state who =>
        rcases state with _ | terminal <;> simp only [assignment, value]
        all_goals exact analyticAt_const
    | disc => exact analyticAt_id
  solution := by
    intro t ht
    rw [assignment_eq_bellmanAssignment t ht.1.le ht.2.le]
    exact (quittingGame reward).isPolynomialBellmanSolution_bellmanAssignment
      (equilibrium t ht.1.le ht.2.le)
  discountCoordinate := by
    intro t _
    simp [assignment]

@[simp] theorem germ_quitRate (who : Player) (t : ℝ) :
    quittingGermQuitRate germ who t = hazard t :=
  rfl

@[simp] theorem germ_endpointValue (who : Player) :
    quittingGermValue germ 0 who = 1 :=
  rfl

/-! ## Exact matching-order packet -/

/-- The two identical quit-rate germs have first order, with cofactor
`1 / (1 - t)`. -/
def quitRateJet : Math.LeadingOrderJet (quittingGermQuitRate germ) where
  order := 1
  cofactor := fun _ t => 1 / (1 - t)
  analytic_cofactor := by
    intro who
    exact analyticAt_const.div
      (analyticAt_const.sub analyticAt_id) (by norm_num)
  factor_eq := by
    intro who
    filter_upwards [] with t
    simp [hazard]
    ring
  exists_leading := by
    refine ⟨false, ?_⟩
    norm_num

theorem germ_matchingOrder :
    Math.familyAnalyticOrder (quittingGermQuitRate germ) =
      germ.ramification := by
  simpa [quitRateJet, germ] using quitRateJet.familyAnalyticOrder_eq

private theorem eventually_parameter_lt_one :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < 1 := by
  have h : ∀ᶠ t in nhds (0 : ℝ), t < 1 :=
    eventually_lt_nhds zero_lt_one
  exact h.filter_mono nhdsWithin_le_nhds

private theorem tendsto_hazard_div_two_hazard_half :
    Tendsto
      (fun t : ℝ => hazard t / (hazard t + hazard t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_parameter_lt_one]
      with t ht0 ht1
  have htne : t ≠ 0 := ne_of_gt ht0
  have hden : 1 - t ≠ 0 := by linarith
  unfold hazard
  field_simp [htne, hden]
  norm_num

private theorem tendsto_parameter_div_two_hazard_half :
    Tendsto
      (fun t : ℝ => t / (hazard t + hazard t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  have hcontinuous : ContinuousAt (fun t : ℝ => (1 - t) / 2) 0 := by
    fun_prop
  have htend : Tendsto (fun t : ℝ => (1 - t) / 2)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((1 - 0) / 2)) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  norm_num at htend
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_parameter_lt_one]
      with t ht0 ht1
  have htne : t ≠ 0 := ne_of_gt ht0
  have hden : 1 - t ≠ 0 := by linarith
  unfold hazard
  field_simp [htne, hden]
  norm_num

private theorem germ_absorption_eq (t : ℝ) :
    quittingGermAbsorption germ t = 2 * hazard t - hazard t ^ 2 := by
  simp [quittingGermAbsorption, hazard]
  ring

private theorem tendsto_absorption_div_parameter_two :
    Tendsto
      (fun t : ℝ => quittingGermAbsorption germ t / t)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (2 : ℝ)) := by
  have hcontinuous : ContinuousAt
      (fun t : ℝ => (2 - 3 * t) / (1 - t) ^ 2) 0 := by
    exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
      ((continuousAt_const.sub continuousAt_id).pow 2) (by norm_num)
  have htend : Tendsto
      (fun t : ℝ => (2 - 3 * t) / (1 - t) ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((2 - 3 * 0) / (1 - 0) ^ 2)) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  norm_num at htend
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_parameter_lt_one]
      with t ht0 ht1
  rw [germ_absorption_eq]
  have htne : t ≠ 0 := ne_of_gt ht0
  have hden : 1 - t ≠ 0 := by linarith
  unfold hazard
  field_simp [htne, hden]
  ring

/-- Canonical matching leading data for the analytic branch. -/
def matchingData : QuittingGermMatchingLeadingData reward germ where
  leading := fun _ => 1
  leading_nonneg := by intro; norm_num
  leading_sum_pos := by simp
  order_eq_ramification := germ_matchingOrder
  eventually_total_pos := by
    filter_upwards [self_mem_nhdsWithin, eventually_parameter_lt_one]
        with t ht0 ht1
    rw [Fintype.sum_bool]
    simp only [germ_quitRate]
    have hpositive : 0 < hazard t := div_pos ht0 (by linarith)
    exact add_pos hpositive hpositive
  share_tendsto := by
    intro who
    simp only [Fintype.sum_bool, germ_quitRate]
    norm_num
    exact tendsto_hazard_div_two_hazard_half
  discount_div_total_tendsto := by
    simp only [germ, pow_one, Fintype.sum_bool]
    norm_num
    exact tendsto_parameter_div_two_hazard_half
  absorption_div_discount_tendsto := by
    simpa [germ] using tendsto_absorption_div_parameter_two

/-- The packet extracted from the analytic branch. -/
def packet : QuittingProjectiveSingletonPacket reward :=
  matchingData.toProjectiveSingletonPacket

@[simp] theorem packet_cemetery : packet.cemetery = 1 / 3 := by
  norm_num [packet, matchingData,
    QuittingGermMatchingLeadingData.toProjectiveSingletonPacket]

@[simp] theorem packet_singleton (who : Player) :
    packet.singleton who = 1 / 3 := by
  norm_num [packet, matchingData,
    QuittingGermMatchingLeadingData.toProjectiveSingletonPacket]

@[simp] theorem packet_value (who : Player) : packet.value who = 1 := by
  rfl

/-- The projective packet carries exactly the active analytic endpoint, not a
separately chosen target. -/
theorem packet_value_eq_germ_endpointValue :
    packet.value = germ.endpointValue none :=
  rfl

/-! ## The late-quit target obstruction -/

/-- Against one opponent, forcing `who` to Continue leaves exactly the
opponent's current Continue probability. -/
theorem fixedOpponentsContinueMass_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots who time =
      ((roots time (!who)) false).toReal := by
  cases who <;>
    simp [quittingFixedOpponentsContinueMass,
      quittingStationaryContinueMass_eq_prod]

/-- If `who` continues, an opponent exit pays `2`; otherwise the game remains
live. -/
theorem fixedOpponentsContinueReward_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsContinueReward reward roots who time =
      2 * (1 - quittingFixedOpponentsContinueMass roots who time) := by
  unfold quittingFixedOpponentsContinueReward
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;> simp_rw [expect_eq_sum, Fintype.sum_bool] <;>
    simp [fixedOpponentsContinueMass_eq, quittingRootPayoff, reward,
      Finset.ext_iff, Math.PMFProduct.pmfBool_false_toReal] <;>
    ring

/-- If `who` quits, a simultaneous opponent exit pays `2` and a solo exit
pays `1`. -/
theorem fixedOpponentsQuitValue_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots who time =
      2 - quittingFixedOpponentsContinueMass roots who time := by
  unfold quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;> simp_rw [expect_eq_sum, Fintype.sum_bool] <;>
    simp [fixedOpponentsContinueMass_eq, quittingRootPayoff, reward,
      Finset.ext_iff, Math.PMFProduct.pmfBool_false_toReal] <;>
    ring

/-- The accumulated reward from waiting for the opponent is twice the
opponent absorption probability over the same prefix. -/
theorem liveLedgerAccum_eq_two_mul_one_sub_survival
    (roots : ℕ → Player → PMF Bool) (who : Player)
    (start fuel : ℕ) :
    quittingLiveLedgerAccum reward roots who start fuel =
      2 * (1 - quittingOpponentSurvivalWeight roots who start fuel) := by
  unfold quittingLiveLedgerAccum
  simp_rw [fixedOpponentsContinueReward_eq]
  calc
    ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          (2 * (1 - quittingFixedOpponentsContinueMass roots who
            (start + offset))) =
      2 * ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          (1 - quittingFixedOpponentsContinueMass roots who
            (start + offset)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
    _ = 2 * (1 - quittingOpponentSurvivalWeight roots who start fuel) := by
      rw [sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass]

/-- Quitting at deterministic delay `fuel` pays `2` minus the probability
that the opponent continues through the quitting stage. -/
theorem pureTimeTerminalValue_some_add_eq_two_sub_survival
    (roots : ℕ → Player → PMF Bool) (who : Player)
    (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start =
      2 - quittingOpponentSurvivalWeight roots who start (fuel + 1) := by
  rw [quittingRootSequencePureTimeTerminalValue_some_add,
    liveLedgerAccum_eq_two_mul_one_sub_survival,
    fixedOpponentsQuitValue_eq,
    quittingOpponentSurvivalWeight_succ]
  ring

/-- The payoff from quitting at date `time` against an arbitrary behavior
profile converges to `2` minus the probability that the opponent never
quits. -/
theorem tendsto_terminalPayoff_update_pureTime_two_sub_opponentSurvival
    (profile : (quittingGame reward).BehaviorProfile) (who : Player) :
    Tendsto
      (fun time => quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who)
      atTop
      (nhds (2 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile who))) := by
  have hlive := tendsto_quittingLiveMass reward
    (quittingOpponentOnlyProfile reward profile who)
  have hshift : Tendsto (fun time : ℕ => time + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun time => Nat.le_add_right time 1) tendsto_id
  have hshifted := hlive.comp hshift
  have hsub : Tendsto
      (fun time : ℕ => 2 - quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile who) (time + 1))
      atTop
      (nhds (2 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile who))) := by
    simpa [Function.comp_def] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
        atTop (nhds 2)).sub hshifted)
  apply hsub.congr'
  filter_upwards [] with time
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    show quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) who (some time) 0 =
      2 - quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) who 0 (time + 1) by
      simpa using pureTimeTerminalValue_some_add_eq_two_sub_survival
        (quittingProfileLiveRoot reward profile) who 0 time]
  exact congrArg (fun mass : ℝ => 2 - mass)
    (quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward profile who (time + 1)).symm

/-- Terminal approximate Nash bounds each opponent's eventual-exit
probability by the prescribed payoff above the solo reward, plus the Nash
error. -/
theorem opponentTail_le_terminalPayoff_sub_one_add
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    1 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who) ≤
      quittingTerminalPayoff reward profile who - 1 + ε := by
  have hlimit :=
    tendsto_terminalPayoff_update_pureTime_two_sub_opponentSurvival
      profile who
  have hbound :
      2 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who) ≤
        quittingTerminalPayoff reward profile who + ε := by
    apply le_of_tendsto hlimit
    exact Filter.Eventually.of_forall fun time =>
      hnash who (quittingPureTimeBehaviorStrategy reward who (some time))
  linarith

/-- **Quantitative target gap.**  If a terminal `ε`-Nash payoff is
coordinatewise `δ`-close to the analytic endpoint `(1,1)`, then
`1 - δ ≤ 4(δ + ε)`. -/
theorem one_sub_le_four_mul_add_of_terminalNash_close
    (profile : (quittingGame reward).BehaviorProfile) {ε δ : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (hclose : ∀ who,
      |quittingTerminalPayoff reward profile who - 1| ≤ δ) :
    1 - δ ≤ 4 * (δ + ε) := by
  let firstSurvival := quittingLiveMassLimit reward
    (quittingOpponentOnlyProfile reward profile false)
  let secondSurvival := quittingLiveMassLimit reward
    (quittingOpponentOnlyProfile reward profile true)
  let totalSurvival := quittingLiveMassLimit reward profile
  have hfirstTail : 1 - firstSurvival ≤ δ + ε := by
    have htail := opponentTail_le_terminalPayoff_sub_one_add
      profile false hnash
    have hupper := (abs_le.mp (hclose false)).2
    dsimp only [firstSurvival]
    linarith
  have hsecondTail : 1 - secondSurvival ≤ δ + ε := by
    have htail := opponentTail_le_terminalPayoff_sub_one_add
      profile true hnash
    have hupper := (abs_le.mp (hclose true)).2
    dsimp only [secondSurvival]
    linarith
  have hfirstNonneg : 0 ≤ firstSurvival :=
    quittingLiveMassLimit_nonneg reward _
  have hsecondNonneg : 0 ≤ secondSurvival :=
    quittingLiveMassLimit_nonneg reward _
  have hfirstLe : firstSurvival ≤ 1 := by
    have h := quittingLiveMassLimit_le reward
      (quittingOpponentOnlyProfile reward profile false) 0
    simpa [firstSurvival] using h
  have hsecondLe : secondSurvival ≤ 1 := by
    have h := quittingLiveMassLimit_le reward
      (quittingOpponentOnlyProfile reward profile true) 0
    simpa [secondSurvival] using h
  have hproduct : firstSurvival * secondSurvival ≤ totalSurvival := by
    simpa [firstSurvival, secondSurvival, totalSurvival] using
      (quittingOpponentLiveMassLimit_mul_le_liveMassLimit
        reward profile (by decide : false ≠ true))
  have habsorption :
      1 - totalSurvival ≤
        (1 - firstSurvival) + (1 - secondSurvival) := by
    have hcross : 0 ≤ (1 - firstSurvival) * (1 - secondSurvival) :=
      mul_nonneg (sub_nonneg.mpr hfirstLe) (sub_nonneg.mpr hsecondLe)
    nlinarith
  have hreward : ∀ terminal player, |reward terminal player| ≤ 2 := by
    intro terminal player
    by_cases h : terminal.1 = {player} <;> simp [reward, h]
  have hpayoffBound := abs_quittingTerminalPayoff_le_absorbedMass
    reward profile false hreward
  have hlower := (abs_le.mp (hclose false)).1
  have hpayoffLeAbs := le_abs_self
    (quittingTerminalPayoff reward profile false)
  dsimp only [totalSurvival] at habsorption hpayoffBound
  linarith

/-- At equal target and Nash error, the target gap is at least `1/9`. -/
theorem one_ninth_le_of_terminalNash_close
    (profile : (quittingGame reward).BehaviorProfile) {η : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) η profile)
    (hclose : ∀ who,
      |quittingTerminalPayoff reward profile who - 1| ≤ η) :
    1 / 9 ≤ η := by
  have hgap := one_sub_le_four_mul_add_of_terminalNash_close
    profile hnash hclose
  linarith

/-- The analytic packet value `(1,1)` is not a uniform-equilibrium payoff. -/
theorem packet_value_not_isUniformEquilibriumPayoff :
    ¬ (quittingGame reward).IsUniformEquilibriumPayoff none packet.value := by
  intro huniform
  let η : ℝ := 1 / 10
  have hη : 0 < η := by norm_num [η]
  obtain ⟨profile, threshold, hprofile⟩ := huniform η hη
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none η profile :=
    ⟨threshold, fun horizon hhorizon => (hprofile horizon hhorizon).1⟩
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) η profile :=
    (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
      none (quittingTerminalPayoff reward) huniform
      (fun selectedProfile who =>
        tendsto_finiteAveragePayoff_quittingGame
          reward selectedProfile who)
  have hclose : ∀ who,
      |quittingTerminalPayoff reward profile who - 1| ≤ η := by
    intro who
    have hlimit := tendsto_finiteAveragePayoff_quittingGame
      reward profile who
    have hupperLimit : Tendsto
        (fun horizon =>
          (quittingGame reward).finiteAveragePayoff none horizon profile who - 1)
        atTop
        (nhds (quittingTerminalPayoff reward profile who - 1)) :=
      hlimit.sub tendsto_const_nhds
    have hlowerLimit : Tendsto
        (fun horizon =>
          1 - (quittingGame reward).finiteAveragePayoff none horizon profile who)
        atTop
        (nhds (1 - quittingTerminalPayoff reward profile who)) :=
      tendsto_const_nhds.sub hlimit
    have hupper : quittingTerminalPayoff reward profile who - 1 ≤ η := by
      apply le_of_tendsto hupperLimit
      filter_upwards [eventually_ge_atTop threshold] with horizon hhorizon
      have hdelivery := (hprofile horizon hhorizon).2 who
      simpa [packet_value] using (abs_le.mp hdelivery).2
    have hlower : 1 - quittingTerminalPayoff reward profile who ≤ η := by
      apply le_of_tendsto hlowerLimit
      filter_upwards [eventually_ge_atTop threshold] with horizon hhorizon
      have hdelivery := (hprofile horizon hhorizon).2 who
      have hbound := (abs_le.mp hdelivery).1
      simp only [packet_value] at hbound
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hgap := one_ninth_le_of_terminalNash_close profile hnash hclose
  norm_num [η] at hgap

/-- Equivalently, the active value of the analytic germ itself is rejected by
the semantic uniform-payoff gate. -/
theorem germ_endpointValue_not_isUniformEquilibriumPayoff :
    ¬ (quittingGame reward).IsUniformEquilibriumPayoff none
      (germ.endpointValue none) := by
  rw [← packet_value_eq_germ_endpointValue]
  exact packet_value_not_isUniformEquilibriumPayoff

/-! ## Exact attainable retargets -/

/-- Payoff from the sure exit of player `false`. -/
def firstExitValue : Payoff Player := fun who => if who then 2 else 1

/-- Payoff from the sure exit of player `true`. -/
def secondExitValue : Payoff Player := fun who => if who then 1 else 2

theorem singleton_false_isQuittingSureExitSet :
    IsQuittingSureExitSet reward ({false} : Finset Player) := by
  rw [isQuittingSureExitSet_singleton_iff]
  constructor
  · norm_num [quittingSoloReward, reward]
  · intro other hne
    cases other
    · exact (hne rfl).elim
    · norm_num [quittingSingletonCollisionReward, quittingSoloReward,
        reward, Finset.ext_iff]

theorem singleton_true_isQuittingSureExitSet :
    IsQuittingSureExitSet reward ({true} : Finset Player) := by
  rw [isQuittingSureExitSet_singleton_iff]
  constructor
  · norm_num [quittingSoloReward, reward]
  · intro other hne
    cases other
    · norm_num [quittingSingletonCollisionReward, quittingSoloReward,
        reward, Finset.ext_iff]
    · exact (hne rfl).elim

/-- `(1,2)` is an exact uniform-equilibrium payoff. -/
theorem firstExitValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none firstExitValue := by
  have h := isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward singleton_false_isQuittingSureExitSet
  convert h using 1
  funext who
  cases who <;>
    norm_num [firstExitValue, quittingSetReward, reward, Finset.ext_iff]

/-- `(2,1)` is an exact uniform-equilibrium payoff. -/
theorem secondExitValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none secondExitValue := by
  have h := isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
    reward singleton_true_isQuittingSureExitSet
  convert h using 1
  funext who
  cases who <;>
    norm_num [secondExitValue, quittingSetReward, reward, Finset.ext_iff]

end QuittingProjectiveTargetMismatch
end GameTheory
