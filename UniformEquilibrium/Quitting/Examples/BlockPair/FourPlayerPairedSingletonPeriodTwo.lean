/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# An exact period-two equilibrium in the paired-singleton family

The table in this file is the period-two completion of the four-player
paired-singleton family.  Payoffs are shifted playerwise so that perpetual
continuation has value zero; equivalently, every displayed absorbing payoff
in the unshifted table is increased by one.  This harmless normalization is
the convention used by the repository's quitting-game model.

An algebraic continuation probability `a` is selected as the unique root of

`44 a^4 - 7 a^3 - 26 a^2 + a + 3`

in `(1/2,1)`, and `b = (4a^2-1)/(3a^2)`.  The two product rows alternate
active pairs `{0,2}` and `{1,3}`, with continuation probabilities `a,b`.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open Filter Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
  StochasticGame

/-- The complete shifted terminal table of the period-two completion. -/
def periodTwoReward
    (S : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  match decide (0 ∈ S.1), decide (1 ∈ S.1),
      decide (2 ∈ S.1), decide (3 ∈ S.1) with
  | true, false, false, false => ![1, 4, 0, 0]
  | false, true, false, false => ![4, 1, 0, 0]
  | false, false, true, false => ![0, 0, 1, 4]
  | false, false, false, true => ![0, 0, 4, 1]
  | true, true, false, false => ![1, 1, 1, 1]
  | true, false, true, false => ![1, 1, 1, 0]
  | true, false, false, true => ![1, 0, 1, 1]
  | false, true, true, false => ![0, 1, 1, 1]
  | false, true, false, true => ![1, 1, 0, 1]
  | false, false, true, true => ![1, 1, 1, 1]
  | true, true, true, false => ![1, 0, 0, 0]
  | true, true, false, true => ![0, 1, 0, 0]
  | true, false, true, true => ![0, 0, 0, 1]
  | false, true, true, true => ![0, 0, 1, 0]
  | true, true, true, true => ![-1, -1, -1, -1]
  | false, false, false, false => ![0, 0, 0, 0]

/-- The normalized singleton rows of the period-two completion have the
paired comparison matrix. -/
theorem periodTwo_singletonMatrix (who owner : Player) :
    Math.LinearProgramming.quittingSingletonMatrix periodTwoReward who owner =
      pairedSingletonMatrix who owner := by
  rw [Math.LinearProgramming.quittingSingletonMatrix]
  fin_cases who <;> fin_cases owner <;>
    simp [periodTwoReward, pairedSingletonMatrix] <;> norm_num

/-- The quartic selecting the exact period-two continuation probability. -/
def periodTwoPolynomial (x : ℝ) : ℝ :=
  44 * x ^ 4 - 7 * x ^ 3 - 26 * x ^ 2 + x + 3

theorem periodTwoPolynomial_thirtySeven_fiftieths :
    periodTwoPolynomial ((37 : ℝ) / 50) = -437733 / 3125000 := by
  norm_num [periodTwoPolynomial]

theorem periodTwoPolynomial_three_quarters :
    periodTwoPolynomial ((3 : ℝ) / 4) = 3 / 32 := by
  norm_num [periodTwoPolynomial]

/-- The derivative has the displayed cubic form. -/
theorem deriv_periodTwoPolynomial (x : ℝ) :
    deriv periodTwoPolynomial x =
      176 * x ^ 3 - 21 * x ^ 2 - 52 * x + 1 := by
  change deriv (fun y : ℝ =>
    44 * y ^ 4 - 7 * y ^ 3 - 26 * y ^ 2 + y + 3) x = _
  have h4 := (hasDerivAt_pow 4 x).const_mul (44 : ℝ)
  have h3 := (hasDerivAt_pow 3 x).const_mul (7 : ℝ)
  have h2 := (hasDerivAt_pow 2 x).const_mul (26 : ℝ)
  have h := (((h4.sub h3).sub h2).add (hasDerivAt_id x)).add_const (3 : ℝ)
  convert h.deriv using 1
  all_goals norm_num
  all_goals ring

/-- Above `7/10`, the selecting quartic is strictly increasing. -/
theorem periodTwoPolynomial_strictMonoOn :
    StrictMonoOn periodTwoPolynomial (Set.Icc ((7 : ℝ) / 10) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ((7 : ℝ) / 10) 1)
    (by unfold periodTwoPolynomial; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_periodTwoPolynomial]
  let t := x - (7 : ℝ) / 10
  have ht : 0 < t := by
    dsimp [t]
    norm_num at hx ⊢
    linarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have hid :
      176 * x ^ 3 - 21 * x ^ 2 - 52 * x + 1 =
        7339 / 500 + (4433 / 25) * t +
          (1743 / 5) * t ^ 2 + 176 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  positivity

/-- The quartic is negative throughout `(1/2,7/10]`.  This exact Bernstein
certificate rules out a second root below the monotonicity interval. -/
theorem periodTwoPolynomial_neg_of_half_lt_of_le_seven_tenths
    {x : ℝ} (hx0 : (1 : ℝ) / 2 < x) (hx1 : x ≤ 7 / 10) :
    periodTwoPolynomial x < 0 := by
  let t := 5 * (x - (1 : ℝ) / 2)
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let w0 := (1 - t) ^ 4
  let w1 := 4 * t * (1 - t) ^ 3
  let w2 := 6 * t ^ 2 * (1 - t) ^ 2
  let w3 := 4 * t ^ 3 * (1 - t)
  let w4 := t ^ 4
  have hw0 : 0 ≤ w0 := by dsimp [w0]; positivity
  have hw1 : 0 ≤ w1 := by dsimp [w1]; positivity
  have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
  have hw3 : 0 ≤ w3 := by dsimp [w3]; positivity
  have hw4 : 0 ≤ w4 := by dsimp [w4]; positivity
  have hsum : w0 + w1 + w2 + w3 + w4 = 1 := by
    dsimp [w0, w1, w2, w3, w4]
    ring
  have hbernstein :
      periodTwoPolynomial x =
        (-9 / 8) * w0 + (-123 / 80) * w1 +
          (-263 / 150) * w2 + (-3221 / 2000) * w3 +
            (-4383 / 5000) * w4 := by
    dsimp [periodTwoPolynomial, t, w0, w1, w2, w3, w4]
    ring
  rw [hbernstein]
  have hbound :
      (-9 / 8 : ℝ) * w0 + (-123 / 80) * w1 +
          (-263 / 150) * w2 + (-3221 / 2000) * w3 +
            (-4383 / 5000) * w4 ≤
        (-4383 / 5000) * (w0 + w1 + w2 + w3 + w4) := by
    nlinarith
  rw [hsum] at hbound
  norm_num at hbound ⊢
  linarith

/-- There is exactly one quartic root in `(1/2,1)`; in fact it lies in the
rational isolating interval `(37/50,3/4)`. -/
theorem existsUnique_periodTwoParameter :
    ∃! a : ℝ,
      a ∈ Set.Ioo ((1 : ℝ) / 2) 1 ∧ periodTwoPolynomial a = 0 := by
  have hleft : periodTwoPolynomial ((37 : ℝ) / 50) < 0 := by
    rw [periodTwoPolynomial_thirtySeven_fiftieths]
    norm_num
  have hright : 0 < periodTwoPolynomial ((3 : ℝ) / 4) := by
    rw [periodTwoPolynomial_three_quarters]
    norm_num
  have hcontinuous : ContinuousOn periodTwoPolynomial
      (Set.Icc ((37 : ℝ) / 50) (3 / 4)) := by
    unfold periodTwoPolynomial
    fun_prop
  obtain ⟨a, haIcc, haroot⟩ :=
    intermediate_value_Icc
      (by norm_num : (37 : ℝ) / 50 ≤ 3 / 4)
      hcontinuous ⟨hleft.le, hright.le⟩
  have haOpen : a ∈ Set.Ioo ((37 : ℝ) / 50) (3 / 4) := by
    constructor
    · exact lt_of_le_of_ne haIcc.1 fun h ↦ by
        subst a
        linarith
    · exact lt_of_le_of_ne haIcc.2 fun h ↦ by
        subst a
        linarith
  refine ⟨a, ⟨⟨by norm_num at haOpen ⊢; linarith,
      by norm_num at haOpen ⊢; linarith⟩, haroot⟩, ?_⟩
  intro y hy
  have hySevenTenths : (7 : ℝ) / 10 < y := by
    by_contra h
    have hle : y ≤ 7 / 10 := le_of_not_gt h
    have hneg := periodTwoPolynomial_neg_of_half_lt_of_le_seven_tenths
      hy.1.1 hle
    linarith
  have haSevenTenths : (7 : ℝ) / 10 < a := by
    norm_num at haOpen ⊢
    linarith
  have haMem : a ∈ Set.Icc ((7 : ℝ) / 10) 1 :=
    ⟨haSevenTenths.le, by norm_num at haOpen ⊢; linarith⟩
  have hyMem : y ∈ Set.Icc ((7 : ℝ) / 10) 1 :=
    ⟨hySevenTenths.le, hy.1.2.le⟩
  exact (periodTwoPolynomial_strictMonoOn.injOn haMem hyMem
    (haroot.trans hy.2.symm)).symm

/-- The exact selected continuation probability. -/
def periodTwoParameter : ℝ :=
  Classical.choose existsUnique_periodTwoParameter

theorem periodTwoParameter_mem :
    periodTwoParameter ∈ Set.Ioo ((1 : ℝ) / 2) 1 :=
  (Classical.choose_spec existsUnique_periodTwoParameter).1.1

theorem periodTwoParameter_root :
    periodTwoPolynomial periodTwoParameter = 0 :=
  (Classical.choose_spec existsUnique_periodTwoParameter).1.2

theorem periodTwoParameter_pos : 0 < periodTwoParameter :=
  lt_trans (by norm_num) periodTwoParameter_mem.1

theorem periodTwoParameter_lt_one : periodTwoParameter < 1 :=
  periodTwoParameter_mem.2

theorem thirtySeven_fiftieths_lt_periodTwoParameter :
    (37 : ℝ) / 50 < periodTwoParameter := by
  have haSeven : (7 : ℝ) / 10 < periodTwoParameter := by
    by_contra h
    have hneg := periodTwoPolynomial_neg_of_half_lt_of_le_seven_tenths
      periodTwoParameter_mem.1 (le_of_not_gt h)
    linarith [periodTwoParameter_root]
  by_contra h
  have haLe : periodTwoParameter ≤ (37 : ℝ) / 50 := le_of_not_gt h
  by_cases heq : periodTwoParameter = (37 : ℝ) / 50
  · have hroot := periodTwoParameter_root
    rw [heq, periodTwoPolynomial_thirtySeven_fiftieths] at hroot
    norm_num at hroot
  · have hlt : periodTwoParameter < (37 : ℝ) / 50 := lt_of_le_of_ne haLe heq
    have hmono := periodTwoPolynomial_strictMonoOn
      ⟨haSeven.le, periodTwoParameter_lt_one.le⟩
      ⟨by norm_num, by norm_num⟩ hlt
    rw [periodTwoParameter_root,
      periodTwoPolynomial_thirtySeven_fiftieths] at hmono
    norm_num at hmono

/-- The second exact continuation probability. -/
def periodTwoSecondary : ℝ :=
  (4 * periodTwoParameter ^ 2 - 1) /
    (3 * periodTwoParameter ^ 2)

theorem periodTwoSecondary_pos : 0 < periodTwoSecondary := by
  have ha := periodTwoParameter_mem.1
  have ha2 : 0 < periodTwoParameter ^ 2 := sq_pos_of_pos periodTwoParameter_pos
  have hquarter : ((1 : ℝ) / 2) ^ 2 < periodTwoParameter ^ 2 :=
    by simpa [pow_two] using mul_self_lt_mul_self (by norm_num) ha
  unfold periodTwoSecondary
  apply div_pos
  · nlinarith
  · positivity

theorem periodTwoSecondary_lt_one : periodTwoSecondary < 1 := by
  have ha2 : 0 < periodTwoParameter ^ 2 := sq_pos_of_pos periodTwoParameter_pos
  have ha1 := periodTwoParameter_lt_one
  have haSq : periodTwoParameter ^ 2 < (1 : ℝ) ^ 2 :=
    by simpa [pow_two] using
      mul_self_lt_mul_self periodTwoParameter_pos.le ha1
  unfold periodTwoSecondary
  rw [div_lt_one (by positivity : 0 < 3 * periodTwoParameter ^ 2)]
  nlinarith

theorem one_half_lt_periodTwoSecondary :
    (1 : ℝ) / 2 < periodTwoSecondary := by
  have ha := thirtySeven_fiftieths_lt_periodTwoParameter
  have hlowerSq : ((37 : ℝ) / 50) ^ 2 < periodTwoParameter ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self (by norm_num) ha
  have hden : 0 < 3 * periodTwoParameter ^ 2 := by positivity
  unfold periodTwoSecondary
  rw [lt_div_iff₀ hden]
  norm_num at hlowerSq ⊢
  nlinarith

theorem periodTwo_active_identity_second :
    periodTwoParameter ^ 2 * (4 - 3 * periodTwoSecondary) = 1 := by
  have hb :
      3 * periodTwoParameter ^ 2 * periodTwoSecondary =
        4 * periodTwoParameter ^ 2 - 1 := by
    unfold periodTwoSecondary
    field_simp [periodTwoParameter_pos.ne']
  nlinarith

theorem periodTwo_active_identity_first :
    periodTwoSecondary *
      (1 - periodTwoParameter + 3 * periodTwoSecondary -
        2 * periodTwoParameter * periodTwoSecondary) = 1 := by
  apply sub_eq_zero.mp
  calc
    periodTwoSecondary *
          (1 - periodTwoParameter + 3 * periodTwoSecondary -
            2 * periodTwoParameter * periodTwoSecondary) - 1 =
        -(periodTwoParameter - 1) *
            periodTwoPolynomial periodTwoParameter /
              (9 * periodTwoParameter ^ 4) := by
      unfold periodTwoSecondary periodTwoPolynomial
      field_simp [periodTwoParameter_pos.ne']
      ring
    _ = 0 := by rw [periodTwoParameter_root]; ring

/-- The Boolean law whose continuation probability is `a`. -/
def primaryCoin : PMF Bool :=
  quittingHazardCoin (1 - periodTwoParameter)
    (sub_nonneg.mpr periodTwoParameter_lt_one.le)
    (by linarith [periodTwoParameter_pos])

/-- The Boolean law whose continuation probability is `b`. -/
def secondaryCoin : PMF Bool :=
  quittingHazardCoin (1 - periodTwoSecondary)
    (sub_nonneg.mpr periodTwoSecondary_lt_one.le)
    (by linarith [periodTwoSecondary_pos])

@[simp] theorem primaryCoin_true_toReal :
    (primaryCoin true).toReal = 1 - periodTwoParameter := by
  simp [primaryCoin]

@[simp] theorem primaryCoin_false_toReal :
    (primaryCoin false).toReal = periodTwoParameter := by
  simp [primaryCoin]

@[simp] theorem secondaryCoin_true_toReal :
    (secondaryCoin true).toReal = 1 - periodTwoSecondary := by
  simp [secondaryCoin]

@[simp] theorem secondaryCoin_false_toReal :
    (secondaryCoin false).toReal = periodTwoSecondary := by
  simp [secondaryCoin]

@[simp] theorem expect_primaryCoin (f : Bool → ℝ) :
    expect primaryCoin f =
      periodTwoParameter * f false +
        (1 - periodTwoParameter) * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

@[simp] theorem expect_secondaryCoin (f : Bool → ℝ) :
    expect secondaryCoin f =
      periodTwoSecondary * f false +
        (1 - periodTwoSecondary) * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-- The odd phase: players `0,2` are active. -/
def oddRoot : Player → PMF Bool := ![
  primaryCoin, PMF.pure false, secondaryCoin, PMF.pure false]

/-- The even phase: players `1,3` are active. -/
def evenRoot : Player → PMF Bool := ![
  PMF.pure false, primaryCoin, PMF.pure false, secondaryCoin]

/-- Conditional payoff at the odd phase. -/
def oddValue : Payoff Player := ![
  1, 1 / periodTwoSecondary, 1, 1 / periodTwoParameter]

/-- Conditional payoff at the even phase. -/
def evenValue : Payoff Player := ![
  1 / periodTwoSecondary, 1, 1 / periodTwoParameter, 1]

/-- Fubini expansion of a product of four Boolean mixed actions. -/
theorem expect_pmfPi_fin4_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a =>
        expect (sigma 1) fun b =>
          expect (sigma 2) fun c =>
            expect (sigma 3) fun d => f ![a, b, c, d] := by
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
      fun who => PMF.pure (![a, b, c, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- A displayed four-coordinate Boolean row has a quitter exactly when at
least one displayed coordinate is true. -/
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

/-- One-stage value recursion at the odd phase. -/
theorem oddRoot_successor :
    quittingRootSuccessorPayoff periodTwoReward evenValue oddRoot = oddValue := by
  funext who
  change quittingRootExpectedPayoff periodTwoReward evenValue oddRoot who = _
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [oddRoot, oddValue, evenValue, quittingRootPayoff, quittingQuitters,
      periodTwoReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- One-stage value recursion at the even phase. -/
theorem evenRoot_successor :
    quittingRootSuccessorPayoff periodTwoReward oddValue evenRoot = evenValue := by
  funext who
  change quittingRootExpectedPayoff periodTwoReward oddValue evenRoot who = _
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [evenRoot, oddValue, evenValue, quittingRootPayoff, quittingQuitters,
      periodTwoReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- Exact endpoint differences at the odd phase. -/
theorem oddRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference periodTwoReward evenValue oddRoot who =
      ![0,
        periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary -
            1 / periodTwoSecondary,
        0,
        1 - 1 / periodTwoParameter] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [oddRoot, evenValue, quittingRootPayoff, quittingQuitters,
      periodTwoReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- Exact endpoint differences at the even phase. -/
theorem evenRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference periodTwoReward oddValue evenRoot who =
      ![periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary -
            1 / periodTwoSecondary,
        0,
        1 - 1 / periodTwoParameter,
        0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4_bool, expect_pmfPi_fin4_bool]
  fin_cases who <;>
    simp [evenRoot, oddValue, quittingRootPayoff, quittingQuitters,
      periodTwoReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

theorem inactivePairGap_neg :
    periodTwoParameter + periodTwoSecondary -
        periodTwoParameter * periodTwoSecondary -
          1 / periodTwoSecondary < 0 := by
  have hab :
      periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary < 1 := by
    nlinarith [mul_pos (sub_pos.mpr periodTwoParameter_lt_one)
      (sub_pos.mpr periodTwoSecondary_lt_one)]
  have hinv : 1 < 1 / periodTwoSecondary := by
    rw [lt_div_iff₀ periodTwoSecondary_pos]
    simpa using periodTwoSecondary_lt_one
  linarith

theorem inactivePrimaryGap_neg :
    1 - 1 / periodTwoParameter < 0 := by
  rw [sub_neg, lt_div_iff₀ periodTwoParameter_pos]
  simpa using periodTwoParameter_lt_one

/-- The odd row is exact endpoint Nash against the even continuation value. -/
theorem oddRoot_isZeroEndpointNash :
    IsεQuittingRootEndpointNash periodTwoReward evenValue 0 oddRoot := by
  intro who
  rw [oddRoot_endpointDifference]
  have hpair :
      periodTwoParameter + periodTwoSecondary ≤
        periodTwoSecondary⁻¹ +
          periodTwoParameter * periodTwoSecondary := by
    have h := inactivePairGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  have hprimary : 1 ≤ periodTwoParameter⁻¹ := by
    have h := inactivePrimaryGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  fin_cases who <;> simp [oddRoot, hpair, hprimary]

/-- The even row is exact endpoint Nash against the odd continuation value. -/
theorem evenRoot_isZeroEndpointNash :
    IsεQuittingRootEndpointNash periodTwoReward oddValue 0 evenRoot := by
  intro who
  rw [evenRoot_endpointDifference]
  have hpair :
      periodTwoParameter + periodTwoSecondary ≤
        periodTwoSecondary⁻¹ +
          periodTwoParameter * periodTwoSecondary := by
    have h := inactivePairGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  have hprimary : 1 ≤ periodTwoParameter⁻¹ := by
    have h := inactivePrimaryGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  fin_cases who <;> simp [evenRoot, hpair, hprimary]

/-! ## The exact cyclic block -/

def oddSimplexRoot : QuittingRootSimplex Player :=
  fun who => stdSimplexEquiv (oddRoot who)

def evenSimplexRoot : QuittingRootSimplex Player :=
  fun who => stdSimplexEquiv (evenRoot who)

@[simp] theorem quittingRootOfSimplex_oddSimplexRoot :
    quittingRootOfSimplex oddSimplexRoot = oddRoot := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (oddRoot who)

@[simp] theorem quittingRootOfSimplex_evenSimplexRoot :
    quittingRootOfSimplex evenSimplexRoot = evenRoot := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (evenRoot who)

def oddPoint : QuittingNashBellmanPoint Player :=
  (oddValue, oddSimplexRoot)

def evenPoint : QuittingNashBellmanPoint Player :=
  (evenValue, evenSimplexRoot)

/-- The two phases followed by the repeated origin. -/
def periodTwoBlock : QuittingFiniteNashBellmanPath Player 2 :=
  ![oddPoint, evenPoint, oddPoint]

theorem four_le_periodTwoRewardBound :
    (4 : ℝ) ≤ quittingRewardBound periodTwoReward := by
  have h := abs_reward_le_quittingRewardBound periodTwoReward
    (quittingSingletonTerminal 0) 1
  simpa [periodTwoReward, quittingSingletonTerminal] using h

theorem oddPoint_mem_box :
    oddPoint ∈ quittingNashBellmanBox
      (quittingRewardBound periodTwoReward) := by
  have hbound := four_le_periodTwoRewardBound
  have haInvPos : 0 < periodTwoParameter⁻¹ :=
    inv_pos.mpr periodTwoParameter_pos
  have hbInvPos : 0 < periodTwoSecondary⁻¹ :=
    inv_pos.mpr periodTwoSecondary_pos
  have haInv : periodTwoParameter⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoParameter < 2 := by
      rw [div_lt_iff₀ periodTwoParameter_pos]
      nlinarith [periodTwoParameter_mem.1]
    simpa [one_div] using hdiv
  have hbInv : periodTwoSecondary⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoSecondary < 2 := by
      rw [div_lt_iff₀ periodTwoSecondary_pos]
      nlinarith [one_half_lt_periodTwoSecondary]
    simpa [one_div] using hdiv
  change oddValue ∈
    Set.Icc (fun _ : Player => -(quittingRewardBound periodTwoReward))
      (fun _ => quittingRewardBound periodTwoReward)
  constructor <;> intro who <;> fin_cases who <;>
    simp [oddValue] <;> linarith

theorem evenPoint_mem_box :
    evenPoint ∈ quittingNashBellmanBox
      (quittingRewardBound periodTwoReward) := by
  have hbound := four_le_periodTwoRewardBound
  have haInvPos : 0 < periodTwoParameter⁻¹ :=
    inv_pos.mpr periodTwoParameter_pos
  have hbInvPos : 0 < periodTwoSecondary⁻¹ :=
    inv_pos.mpr periodTwoSecondary_pos
  have haInv : periodTwoParameter⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoParameter < 2 := by
      rw [div_lt_iff₀ periodTwoParameter_pos]
      nlinarith [periodTwoParameter_mem.1]
    simpa [one_div] using hdiv
  have hbInv : periodTwoSecondary⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoSecondary < 2 := by
      rw [div_lt_iff₀ periodTwoSecondary_pos]
      nlinarith [one_half_lt_periodTwoSecondary]
    simpa [one_div] using hdiv
  change evenValue ∈
    Set.Icc (fun _ : Player => -(quittingRewardBound periodTwoReward))
      (fun _ => quittingRewardBound periodTwoReward)
  constructor <;> intro who <;> fin_cases who <;>
    simp [evenValue] <;> linarith

theorem oddPoint_edge_evenPoint :
    IsQuittingNashBellmanEdge periodTwoReward oddPoint evenPoint := by
  constructor
  · change oddValue =
      quittingRootSuccessorPayoff periodTwoReward evenValue
        (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot, oddRoot_successor]
  · change IsεQuittingRootEndpointNash periodTwoReward evenValue 0
      (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot]
    exact oddRoot_isZeroEndpointNash

theorem evenPoint_edge_oddPoint :
    IsQuittingNashBellmanEdge periodTwoReward evenPoint oddPoint := by
  constructor
  · change evenValue =
      quittingRootSuccessorPayoff periodTwoReward oddValue
        (quittingRootOfSimplex evenSimplexRoot)
    rw [quittingRootOfSimplex_evenSimplexRoot, evenRoot_successor]
  · change IsεQuittingRootEndpointNash periodTwoReward oddValue 0
      (quittingRootOfSimplex evenSimplexRoot)
    rw [quittingRootOfSimplex_evenSimplexRoot]
    exact evenRoot_isZeroEndpointNash

theorem oddRoot_continueMass :
    quittingStationaryContinueMass oddRoot =
      periodTwoParameter * periodTwoSecondary := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [oddRoot, Fin.prod_univ_succ]

theorem evenRoot_continueMass :
    quittingStationaryContinueMass evenRoot =
      periodTwoParameter * periodTwoSecondary := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [evenRoot, Fin.prod_univ_succ]

theorem oddRoot_absorption_pos :
    0 < quittingRootAbsorptionMass oddRoot := by
  rw [quittingRootAbsorptionMass, oddRoot_continueMass]
  have hmul : periodTwoParameter * periodTwoSecondary < 1 := by
    have h := mul_pos periodTwoParameter_pos
      (sub_pos.mpr periodTwoSecondary_lt_one)
    nlinarith [periodTwoParameter_lt_one]
  linarith

/-- The two displayed rows form an absorbing exact Nash--Bellman cycle. -/
theorem periodTwoBlock_isQuittingCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock periodTwoReward oddValue 2
      periodTwoBlock := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ⟨0, ?_⟩⟩
  · intro time
    fin_cases time
    · exact oddPoint_mem_box
    · exact evenPoint_mem_box
    · exact oddPoint_mem_box
  · rfl
  · intro time
    fin_cases time
    · exact oddPoint_edge_evenPoint
    · exact evenPoint_edge_oddPoint
  · change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot]
    exact oddRoot_absorption_pos

@[simp] theorem quittingCyclicContinuationBlockCycle_periodTwoBlock
    (stage : Fin 2) :
    quittingCyclicContinuationBlockCycle 1 periodTwoBlock stage =
      ![oddRoot, evenRoot] stage := by
  fin_cases stage
  · exact quittingRootOfSimplex_oddSimplexRoot
  · exact quittingRootOfSimplex_evenSimplexRoot

/-- Admissibility is automatic: every own-singleton payoff in the shifted
table equals one. -/
theorem periodTwoBlockCycle_isAdmissible :
    IsQuittingCycleAdmissible periodTwoReward
      (quittingCyclicContinuationBlockCycle 1 periodTwoBlock) := by
  intro who
  refine Or.inr ?_
  fin_cases who <;>
    simp [periodTwoReward, quittingSingletonTerminal]

/-- The exact alternating behavioral profile. -/
def periodTwoProfile : (quittingGame periodTwoReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile periodTwoReward 1 periodTwoBlock 0

/-- The alternating profile is exact terminal Nash against every behavioral
deviation. -/
theorem periodTwoProfile_isExactTerminalNash :
    (quittingGame periodTwoReward).IsεAsymptoticNash
      (quittingTerminalPayoff periodTwoReward) 0 periodTwoProfile :=
  isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    periodTwoReward oddValue 1 periodTwoBlock
      periodTwoBlock_isQuittingCyclicContinuationBlock
      periodTwoBlockCycle_isAdmissible 0

theorem periodTwoProfile_terminalPayoff :
    quittingTerminalPayoff periodTwoReward periodTwoProfile = oddValue :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile
    periodTwoReward oddValue 1 periodTwoBlock
      periodTwoBlock_isQuittingCyclicContinuationBlock

/-- The period-two completion has the exact uniform-equilibrium payoff
`(1,1/b,1,1/a)` in the shifted normalization. -/
theorem periodTwo_isUniformEquilibriumPayoff :
    (quittingGame periodTwoReward).IsUniformEquilibriumPayoff none oddValue := by
  have h := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    periodTwoReward periodTwoProfile periodTwoProfile_isExactTerminalNash
  rwa [periodTwoProfile_terminalPayoff] at h

end FourPlayerPairedSingleton
end GameTheory
