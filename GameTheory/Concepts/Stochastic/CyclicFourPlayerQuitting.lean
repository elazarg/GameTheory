/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# An exact stationary equilibrium in a cyclic four-player quitting game

This file formalizes the positive certificate for this game.  The game
has the explicit fifteen-row terminal table below.  A common quit
probability is selected as the unique root of a rational polynomial in a
small rational interval; at that root, Quit and Continue have exactly the
same continuation value for every player.

The algebraic parameter is selected only after proving existence and
uniqueness.  No decimal approximation enters the construction.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace CyclicFourPlayerQuitting

open Filter Math.Probability Math.PMFProduct StochasticGame

/-- The four cyclic players. -/
abbrev Player := Fin 4

/-- A nonempty terminal quitter set. -/
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The complete fifteen-row terminal table for this game. -/
def terminalReward (S : Terminal) : Payoff Player :=
  match decide (0 ∈ S.1), decide (1 ∈ S.1),
      decide (2 ∈ S.1), decide (3 ∈ S.1) with
  | true, false, false, false => ![1, -2, 2, 2]
  | false, true, false, false => ![2, 1, -2, 2]
  | true, true, false, false => ![-1, 0, -1, 3]
  | false, false, true, false => ![2, 2, 1, -2]
  | true, false, true, false => ![-1, -1, -1, -1]
  | false, true, true, false => ![3, -1, 0, -1]
  | true, true, true, false => ![-4, -3, -3, 0]
  | false, false, false, true => ![-2, 2, 2, 1]
  | true, false, false, true => ![0, -1, 3, -1]
  | false, true, false, true => ![-1, -1, -1, -1]
  | true, true, false, true => ![-3, -3, 0, -4]
  | false, false, true, true => ![-1, 3, -1, 0]
  | true, false, true, true => ![-3, 0, -4, -3]
  | false, true, true, true => ![0, -4, -3, -3]
  | true, true, true, true => ![-6, -6, -6, -6]
  | false, false, false, false => ![0, 0, 0, 0]

/-- The concrete quitting game. -/
abbrev game : StochasticGame Player := quittingGame terminalReward

instance : Fintype game.State :=
  inferInstanceAs (Fintype (Option Terminal))

instance : DecidableEq game.State :=
  inferInstanceAs (DecidableEq (Option Terminal))

instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Bool)

instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Bool)

/-- The polynomial selecting the exact symmetric stationary root. -/
def stationaryPolynomial (x : ℝ) : ℝ :=
  x ^ 5 - 6 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 - 15 * x + 1

theorem stationaryPolynomial_one_fifteenth :
    stationaryPolynomial ((1 : ℝ) / 15) = 21736 / 759375 := by
  norm_num [stationaryPolynomial]

theorem stationaryPolynomial_seven_hundredths :
    stationaryPolynomial ((7 : ℝ) / 100) =
      -183413793 / 10000000000 := by
  norm_num [stationaryPolynomial]

/-- The derivative has the displayed polynomial form. -/
theorem deriv_stationaryPolynomial (x : ℝ) :
    deriv stationaryPolynomial x =
      5 * x ^ 4 - 24 * x ^ 3 + 21 * x ^ 2 + 12 * x - 15 := by
  change deriv (fun y : ℝ =>
    y ^ 5 - 6 * y ^ 4 + 7 * y ^ 3 + 6 * y ^ 2 - 15 * y + 1) x = _
  have h := (((((hasDerivAt_pow 5 x).sub
      ((hasDerivAt_pow 4 x).const_mul (6 : ℝ))).add
      ((hasDerivAt_pow 3 x).const_mul (7 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (6 : ℝ))).sub
      ((hasDerivAt_id x).const_mul (15 : ℝ))).add_const (1 : ℝ)
  convert h.deriv using 1
  all_goals norm_num
  all_goals ring

/-- The selecting polynomial is strictly decreasing on the interval needed
for the exact root certificate. -/
theorem stationaryPolynomial_strictAntiOn :
    StrictAntiOn stationaryPolynomial (Set.Icc (0 : ℝ) (1 / 10)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (1 / 10))
    (by unfold stationaryPolynomial; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_stationaryPolynomial]
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : x ≤ (1 : ℝ) / 10 := hx.2.le
  have hx2nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2 : x ^ 2 ≤ ((1 : ℝ) / 10) ^ 2 := by
    nlinarith [sq_nonneg (x - (1 : ℝ) / 10)]
  have hx3nonneg : 0 ≤ x ^ 3 := by positivity
  have hx4 : x ^ 4 ≤ ((1 : ℝ) / 10) ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - ((1 : ℝ) / 10) ^ 2)]
  norm_num at hx2 hx4 ⊢
  nlinarith

/-- There is exactly one selected root in the rational interval
`(1/15, 7/100)`. -/
theorem existsUnique_stationaryParameter :
    ∃! s : ℝ,
      s ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) ∧
        stationaryPolynomial s = 0 := by
  have hleftPos : 0 < stationaryPolynomial ((1 : ℝ) / 15) := by
    rw [stationaryPolynomial_one_fifteenth]
    norm_num
  have hrightNeg : stationaryPolynomial ((7 : ℝ) / 100) < 0 := by
    rw [stationaryPolynomial_seven_hundredths]
    norm_num
  have hcontinuous : ContinuousOn stationaryPolynomial
      (Set.Icc ((1 : ℝ) / 15) (7 / 100)) := by
    unfold stationaryPolynomial
    fun_prop
  obtain ⟨s, hsIcc, hsroot⟩ :=
    (convex_Icc ((1 : ℝ) / 15) (7 / 100)).isPreconnected.intermediate_value
      (Set.right_mem_Icc.mpr (by norm_num : (1 : ℝ) / 15 ≤ 7 / 100))
      (Set.left_mem_Icc.mpr (by norm_num : (1 : ℝ) / 15 ≤ 7 / 100))
      hcontinuous ⟨hrightNeg.le, hleftPos.le⟩
  have hs : s ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) := by
    refine ⟨lt_of_le_of_ne hsIcc.1 ?_, lt_of_le_of_ne hsIcc.2 ?_⟩
    · intro heq
      subst s
      linarith
    · intro heq
      subst s
      linarith
  refine ⟨s, ⟨hs, hsroot⟩, ?_⟩
  intro y hy
  have hsLarge : s ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor <;> norm_num at hs ⊢ <;> linarith
  have hyLarge : y ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor <;> norm_num at hy ⊢ <;> linarith [hy.1.1, hy.1.2]
  exact (stationaryPolynomial_strictAntiOn.injOn hsLarge hyLarge
    (hsroot.trans hy.2.symm)).symm

/-- The exact symmetric quit probability. -/
def stationaryParameter : ℝ :=
  Classical.choose existsUnique_stationaryParameter

theorem stationaryParameter_mem :
    stationaryParameter ∈ Set.Ioo ((1 : ℝ) / 15) (7 / 100) :=
  (Classical.choose_spec existsUnique_stationaryParameter).1.1

theorem stationaryParameter_root :
    stationaryPolynomial stationaryParameter = 0 :=
  (Classical.choose_spec existsUnique_stationaryParameter).1.2

theorem stationaryParameter_pos : 0 < stationaryParameter := by
  have := stationaryParameter_mem.1
  norm_num at this ⊢
  linarith

theorem stationaryParameter_lt_one : stationaryParameter < 1 := by
  have := stationaryParameter_mem.2
  norm_num at this ⊢
  linarith

/-- The exact common continuation payoff. -/
def stationaryPayoff : ℝ :=
  1 - 5 * stationaryParameter - 3 * stationaryParameter ^ 2 +
    stationaryParameter ^ 3

theorem stationaryPayoff_gt_47_hundredths :
    (47 : ℝ) / 100 < stationaryPayoff := by
  have hs0 := stationaryParameter_pos.le
  have hs1 : stationaryParameter < (1 : ℝ) / 10 := by
    have := stationaryParameter_mem.2
    norm_num at this ⊢
    linarith
  unfold stationaryPayoff
  have hs2 : stationaryParameter ^ 2 < ((1 : ℝ) / 10) ^ 2 := by
    nlinarith [sq_nonneg (stationaryParameter - (1 : ℝ) / 10)]
  have hs3 : 0 ≤ stationaryParameter ^ 3 := by positivity
  norm_num at hs2 ⊢
  nlinarith

theorem stationaryPayoff_lt_one : stationaryPayoff < 1 := by
  have hs := stationaryParameter_pos
  have hslt : stationaryParameter < (1 : ℝ) / 10 := by
    have := stationaryParameter_mem.2
    norm_num at this ⊢
    linarith
  unfold stationaryPayoff
  have hfactor : 0 < 5 + 3 * stationaryParameter - stationaryParameter ^ 2 := by
    nlinarith [sq_nonneg (stationaryParameter - (1 : ℝ) / 10)]
  nlinarith

/-! ## The exact product root -/

/-- A Boolean law which quits with probability `p`. -/
def quitCoin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun quit => if quit then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, if_false, Bool.false_eq_true]
      rw [← ENNReal.ofReal_add hp0 (by linarith)]
      norm_num)

@[simp] theorem quitCoin_apply_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quitCoin p hp0 hp1 true).toReal = p := by
  simp [quitCoin, PMF.ofFintype_apply, ENNReal.toReal_ofReal hp0]

@[simp] theorem quitCoin_apply_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quitCoin p hp0 hp1 false).toReal = 1 - p := by
  simp [quitCoin, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]

@[simp] theorem expect_quitCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quitCoin p hp0 hp1) f = (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-- Fubini expansion of a product of four Boolean mixed actions. -/
theorem expect_pmfPi_fin4_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦
            expect (sigma 3) fun d ↦ f ![a, b, c, d] := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a))
      1 (sigma 1) = Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
      Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext c
  have h3 : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (sigma 3) =
      Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c) := by
    funext who
    fin_cases who <;> simp
  rw [← h3, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 3))
  funext d
  have hpure : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (PMF.pure d) =
      fun who ↦ PMF.pure (![a, b, c, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- A concrete four-coordinate Boolean action has a quitter exactly when one
of its four displayed coordinates is true. -/
@[simp] theorem vector4_quitters_nonempty (a b c d : Bool) :
    ({who | ![a, b, c, d] who = true} : Finset Player).Nonempty ↔
      a = true ∨ b = true ∨ c = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all
  · rintro (ha | hb | hc | hd)
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨2, by simp [hc]⟩
    · exact ⟨3, by simp [hd]⟩

/-- The symmetric product action at the selected algebraic parameter. -/
def stationaryRoot : Player → PMF Bool :=
  fun _ => quitCoin stationaryParameter stationaryParameter_pos.le
    stationaryParameter_lt_one.le

/-- The constant tail vector at the selected payoff. -/
def stationaryTail : Payoff Player := fun _ => stationaryPayoff

@[simp] theorem stationaryRoot_true_toReal (who : Player) :
    (stationaryRoot who true).toReal = stationaryParameter := by
  simp [stationaryRoot]

@[simp] theorem stationaryRoot_false_toReal (who : Player) :
    (stationaryRoot who false).toReal = 1 - stationaryParameter := by
  simp [stationaryRoot]

/-- Every player's pure-Quit value at the symmetric root is `ω`. -/
theorem stationaryRoot_quitPayoff (who : Player) :
    quittingRootQuitPayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [stationaryRoot, stationaryTail, quittingRootPayoff,
      quittingQuitters, terminalReward, stationaryPayoff] <;>
    ring

/-- The unconditional absorbing contribution when a player continues. -/
theorem stationaryRoot_continueReward (who : Player) :
    quittingRootAbsorbingContribution terminalReward
        (Function.update stationaryRoot who (PMF.pure false)) who =
      2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
        stationaryParameter ^ 3 := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [stationaryRoot, quittingRootPayoff, quittingQuitters,
      terminalReward] <;>
    ring

/-- The three opponents all continue with probability `(1-s)^3`. -/
theorem stationaryRoot_opponentContinueMass (who : Player) :
    quittingStationaryContinueMass
        (Function.update stationaryRoot who (PMF.pure false)) =
      (1 - stationaryParameter) ^ 3 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  fin_cases who <;>
    simp [stationaryRoot, quittingAllContinueAction, Fin.prod_univ_succ] <;>
    ring

/-- The selected polynomial root is exactly the stationary continuation
balance identity. -/
theorem stationary_continue_balance :
    2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
          stationaryParameter ^ 3 +
        (1 - stationaryParameter) ^ 3 * stationaryPayoff =
      stationaryPayoff := by
  apply sub_eq_zero.mp
  calc
    (2 * stationaryParameter - 3 * stationaryParameter ^ 2 +
          stationaryParameter ^ 3 +
        (1 - stationaryParameter) ^ 3 * stationaryPayoff) -
          stationaryPayoff =
        -stationaryParameter * stationaryPolynomial stationaryParameter := by
          unfold stationaryPayoff stationaryPolynomial
          ring
    _ = 0 := by rw [stationaryParameter_root, mul_zero]

/-- Every player's pure-Continue value at the symmetric root is also `ω`. -/
theorem stationaryRoot_continuePayoff (who : Player) :
    quittingRootContinuePayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    stationaryRoot_continueReward, stationaryRoot_opponentContinueMass]
  exact stationary_continue_balance

/-- The stationary product root is exactly indifferent for every player. -/
theorem stationaryRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference terminalReward stationaryTail
        stationaryRoot who = 0 := by
  rw [quittingRootEndpointDifference, stationaryRoot_quitPayoff,
    stationaryRoot_continuePayoff, sub_self]

/-- The selected root has current payoff equal to its declared tail. -/
theorem stationaryRoot_fixedPoint (who : Player) :
    quittingRootSuccessorPayoff terminalReward stationaryTail stationaryRoot who =
      stationaryPayoff := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    stationaryRoot_quitPayoff, stationaryRoot_continuePayoff]
  have hsum := quittingRoot_continueProbability_add_quitProbability
    stationaryRoot who
  rw [← add_mul, add_comm, hsum, one_mul]

/-! ## Global unilateral credibility -/

/-- The one-stage all-continue mass at the symmetric root. -/
theorem stationaryRoot_continueMass :
    quittingStationaryContinueMass stationaryRoot =
      (1 - stationaryParameter) ^ 4 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [stationaryRoot, quittingAllContinueAction]

theorem stationaryRoot_continueMass_lt_one :
    quittingStationaryContinueMass stationaryRoot < 1 := by
  rw [stationaryRoot_continueMass]
  apply pow_lt_one₀
  · exact sub_nonneg.mpr stationaryParameter_lt_one.le
  · linarith [stationaryParameter_pos]
  · norm_num

/-- The potential used to certify every unilateral behavioral deviation:
`omega` while live and the terminal table after absorption. -/
def deviationPotential (who : Player) :
    game.State → ℝ
  | none => stationaryPayoff
  | some terminal => terminalReward terminal who

/-- Evaluating the potential after a live-state transition is exactly the
finite root payoff with constant tail `omega`. -/
theorem expect_transition_deviationPotential_eq_rootPayoff
    (who : Player) (action : Player → Bool) :
    expect ((quittingGame terminalReward).transition none action)
        (deviationPotential who) =
      quittingRootPayoff terminalReward stationaryTail action who := by
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hraw : ({who | action who = true} : Finset Player).Nonempty := by
      simpa [quittingQuitters] using hquit
    rw [quittingGame_transition_none, dif_pos hraw, expect_pure,
      quittingRootPayoff, dif_pos hquit]
    rfl
  · have hraw : ¬({who | action who = true} : Finset Player).Nonempty := by
      simpa [quittingQuitters] using hquit
    rw [quittingGame_transition_none, dif_neg hraw, expect_pure,
      quittingRootPayoff, dif_neg hquit]
    rfl

/-- Against the three prescribed stationary opponents, the deviation
potential is harmonic after every history, for every behavioral strategy of
the remaining player. -/
theorem deviationPotential_harmonic
    (who : Player)
    (deviation : game.BehaviorStrategy who)
    {time : ℕ} (history : game.Hist time) :
    expect (game.stageActionDist
        (Function.update
          (quittingStationaryProfile terminalReward stationaryRoot)
          who deviation) history) (fun action ↦
      expect (game.transition history.2 action)
        (deviationPotential who)) =
      deviationPotential who history.2 := by
  cases hstate : (show game.State from history.2) with
  | some terminal =>
      simp only [hstate]
      have hinner : ∀ action : game.JointAct,
          expect (game.transition (show game.State from some terminal) action)
              (deviationPotential who) = terminalReward terminal who := by
        intro action
        change expect (PMF.pure (show game.State from some terminal))
          (deviationPotential who) = terminalReward terminal who
        rw [expect_pure]
        rfl
      simp_rw [hinner]
      rw [expect_const]
      rfl
  | none =>
      simp only [hstate]
      change expect (game.stageActionDist
          (Function.update (game.stationaryBehaviorProfile stationaryRoot)
            who deviation) history)
          (fun action ↦ expect (game.transition none action)
            (deviationPotential who)) = deviationPotential who none
      rw [game.stageActionDist_update_stationaryBehaviorProfile]
      rw [deviationPotential]
      simp_rw [expect_transition_deviationPotential_eq_rootPayoff]
      change quittingRootExpectedPayoff terminalReward stationaryTail
          (Function.update stationaryRoot who (deviation time history)) who =
        stationaryPayoff
      rw [quittingRootExpectedPayoff_update_eq_endpointMix,
        stationaryRoot_quitPayoff, stationaryRoot_continuePayoff]
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (Function.update stationaryRoot who (deviation time history)) who
      simp only [Function.update_self] at hsum
      rw [← add_mul, add_comm, hsum, one_mul]

/-- The deviation potential has constant expectation `omega` at every
finite time, even under an arbitrary history-dependent unilateral
deviation. -/
theorem expectedStateValue_deviationPotential
    (who : Player)
    (deviation : game.BehaviorStrategy who) :
    ∀ time : ℕ,
      (quittingGame terminalReward).expectedStateValue
          (Function.update
            (quittingStationaryProfile terminalReward stationaryRoot)
            who deviation) none time (deviationPotential who) =
        stationaryPayoff := by
  intro time
  induction time with
  | zero => simp [deviationPotential]
  | succ time ih =>
      rw [(quittingGame terminalReward).expectedStateValue_succ]
      calc
        expect ((quittingGame terminalReward).histDist
            (Function.update
              (quittingStationaryProfile terminalReward stationaryRoot)
              who deviation) none time) (fun history ↦
          expect ((quittingGame terminalReward).stageActionDist
              (Function.update
                (quittingStationaryProfile terminalReward stationaryRoot)
                who deviation) history) (fun action ↦
            expect ((quittingGame terminalReward).transition history.2 action)
              (deviationPotential who))) =
          expect ((quittingGame terminalReward).histDist
            (Function.update
              (quittingStationaryProfile terminalReward stationaryRoot)
              who deviation) none time) (fun history ↦
                deviationPotential who history.2) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro history _
            exact deviationPotential_harmonic who deviation history
        _ = stationaryPayoff := ih

/-- The potential expectation splits into the ordinary current-state payoff
and `omega` times the residual live probability. -/
theorem expectedStateValue_deviationPotential_eq
    (profile : (quittingGame terminalReward).BehaviorProfile)
    (who : Player) (time : ℕ) :
    (quittingGame terminalReward).expectedStateValue profile none time
        (deviationPotential who) =
      (quittingGame terminalReward).expectedStagePayoff profile none time who +
        stationaryPayoff * quittingLiveMass terminalReward profile time := by
  rw [quittingLiveMass_eq_expectedStateValue]
  unfold StochasticGame.expectedStateValue StochasticGame.expectedStagePayoff
  simp_rw [stageEUAt_quittingGame_eq_stateReward]
  rw [← expect_const_mul, ← expect_add]
  apply congrArg (expect ((quittingGame terminalReward).histDist
    profile none time))
  funext history
  cases history.2 <;>
    simp [deviationPotential, quittingStateReward, quittingLiveIndicator]

/-- Making one player always continue in the stationary profile is itself
the stationary profile with that one root marginal replaced. -/
theorem opponentOnlyProfile_stationary (who : Player) :
    quittingOpponentOnlyProfile terminalReward
        (quittingStationaryProfile terminalReward stationaryRoot) who =
      quittingStationaryProfile terminalReward
        (Function.update stationaryRoot who (PMF.pure false)) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    simp [quittingOpponentOnlyProfile, quittingAlwaysContinueStrategy,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile]
    rfl
  · simp [quittingOpponentOnlyProfile, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, Function.update_of_ne hplayer]

/-- The three stationary opponents absorb almost surely. -/
theorem tendsto_stationaryOpponentLiveMass_zero (who : Player) :
    Tendsto (quittingLiveMass terminalReward
      (quittingOpponentOnlyProfile terminalReward
        (quittingStationaryProfile terminalReward stationaryRoot) who))
      atTop (nhds 0) := by
  rw [opponentOnlyProfile_stationary]
  apply tendsto_quittingLiveMass_stationary_zero
  rw [stationaryRoot_opponentContinueMass]
  apply pow_lt_one₀
  · exact sub_nonneg.mpr stationaryParameter_lt_one.le
  · linarith [stationaryParameter_pos]
  · norm_num

/-- Every unilateral deviation's residual live mass vanishes, because it is
dominated by the three stationary opponents' survival probability. -/
theorem tendsto_deviationLiveMass_zero
    (who : Player)
    (deviation : game.BehaviorStrategy who) :
    Tendsto (quittingLiveMass terminalReward
      (Function.update
        (quittingStationaryProfile terminalReward stationaryRoot)
        who deviation)) atTop (nhds 0) := by
  exact squeeze_zero
    (fun time ↦ quittingLiveMass_nonneg terminalReward _ time)
    (quittingLiveMass_update_le_opponentOnly terminalReward
      (quittingStationaryProfile terminalReward stationaryRoot) who deviation)
    (tendsto_stationaryOpponentLiveMass_zero who)

/-- Every history-dependent unilateral behavioral deviation receives
exactly `omega` in terminal payoff. -/
theorem quittingTerminalPayoff_stationary_update_eq
    (who : Player)
    (deviation : game.BehaviorStrategy who) :
    quittingTerminalPayoff terminalReward
        (Function.update
          (quittingStationaryProfile terminalReward stationaryRoot)
          who deviation) who = stationaryPayoff := by
  let profile := Function.update
    (quittingStationaryProfile terminalReward stationaryRoot) who deviation
  have hformula : ∀ time : ℕ,
      (quittingGame terminalReward).expectedStagePayoff profile none time who =
        stationaryPayoff - stationaryPayoff *
          quittingLiveMass terminalReward profile time := by
    intro time
    have hpotential := expectedStateValue_deviationPotential who deviation time
    have hsplit := expectedStateValue_deviationPotential_eq profile who time
    have hpotential' :
        (quittingGame terminalReward).expectedStateValue profile none time
            (deviationPotential who) = stationaryPayoff := by
      simpa [profile] using hpotential
    linarith [hpotential', hsplit]
  have hlive := tendsto_deviationLiveMass_zero who deviation
  have hright : Tendsto (fun time : ℕ =>
      stationaryPayoff - stationaryPayoff *
        quittingLiveMass terminalReward profile time) atTop
      (nhds stationaryPayoff) := by
    have hlive' : Tendsto
        (quittingLiveMass terminalReward profile) atTop (nhds 0) := by
      simpa [profile] using hlive
    have hconst : Tendsto (fun _ : ℕ => stationaryPayoff) atTop
        (nhds stationaryPayoff) := tendsto_const_nhds
    simpa using hconst.sub
      (Filter.Tendsto.const_mul stationaryPayoff hlive')
  have hstage : Tendsto (fun time : ℕ =>
      (quittingGame terminalReward).expectedStagePayoff profile none time who)
      atTop (nhds stationaryPayoff) :=
    hright.congr' (Filter.Eventually.of_forall fun time => (hformula time).symm)
  exact tendsto_nhds_unique
    (tendsto_expectedStagePayoff_quittingGame terminalReward profile who) hstage

/-- The prescribed stationary terminal payoff is `omega`. -/
theorem quittingTerminalPayoff_stationary (who : Player) :
    quittingTerminalPayoff terminalReward
        (quittingStationaryProfile terminalReward stationaryRoot) who =
      stationaryPayoff := by
  simpa only [Function.update_eq_self] using
    (quittingTerminalPayoff_stationary_update_eq who
      (quittingStationaryProfile terminalReward stationaryRoot who))

/-- The exact stationary profile is a terminal Nash equilibrium. -/
theorem stationaryProfile_isTerminalNash :
    (quittingGame terminalReward).IsεAsymptoticNash
      (quittingTerminalPayoff terminalReward) 0
      (quittingStationaryProfile terminalReward stationaryRoot) := by
  intro who deviation
  rw [quittingTerminalPayoff_stationary,
    quittingTerminalPayoff_stationary_update_eq]
  norm_num

/-- Hence the same stationary profile is a uniform epsilon-equilibrium for
every positive error. -/
theorem stationaryProfile_isUniformεEquilibrium
    {ε : ℝ} (hε : 0 < ε) :
    (quittingGame terminalReward).IsUniformεEquilibrium none ε
      (quittingStationaryProfile terminalReward stationaryRoot) :=
  quittingGame_isUniformεEquilibrium_of_terminalNash_finite
    terminalReward (quittingStationaryProfile terminalReward stationaryRoot)
      hε stationaryProfile_isTerminalNash

/-- The constant vector `omega` is an explicit uniform-equilibrium payoff of
the four-player quitting game. -/
theorem stationaryTail_isUniformEquilibriumPayoff :
    game.IsUniformEquilibriumPayoff none stationaryTail := by
  intro ε hε
  obtain ⟨nashThreshold, hnashThreshold⟩ :=
    stationaryProfile_isUniformεEquilibrium hε
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |game.finiteAveragePayoff none horizon
          (quittingStationaryProfile terminalReward stationaryRoot) who -
        stationaryTail who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame terminalReward
        (quittingStationaryProfile terminalReward stationaryRoot) who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff terminalReward
            (quittingStationaryProfile terminalReward stationaryRoot) who) hε)
    filter_upwards [hball] with horizon hhorizon
    rw [quittingTerminalPayoff_stationary] at hhorizon
    simpa [Metric.mem_ball, Real.dist_eq, stationaryTail] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨quittingStationaryProfile terminalReward stationaryRoot,
    max nashThreshold deliveryThreshold, fun horizon hhorizon => ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

end CyclicFourPlayerQuitting
end GameTheory
