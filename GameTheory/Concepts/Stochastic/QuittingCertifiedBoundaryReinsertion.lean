/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtSemantics
import Math.SurvivalProduct

/-!
# Scalar core of certified quitting-boundary reinsertion

A finite quitting prefix sees a changed prescribed boundary through the
probability `P` that every player follows Continue throughout the prefix.  A
unilateral best response sees the same boundary through the larger
opponent-only survival probability `χ`: the deviator may choose Continue at
every prefix date.  This file separates those two weights and proves the exact
finite perturbation formula.

The result is deliberately scalar.  A terminal behavior profile can supply a
prescribed payoff and a relative best-response debt; once those two numbers
are certified, no additional strategy scaffolding is needed inside the
finite prefix.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Full-profile and opponent-only survival -/

/-- One-stage probability that the prescribed player and all opponents
Continue.  The player's own marginal is supplied separately so the same
definition also applies to a candidate unilateral hazard. -/
def quittingFiniteFullContinueMass
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  (hazard time false).toReal *
    quittingFixedOpponentsContinueMass roots who time

/-- Probability that the prescribed player and every opponent Continue for a
finite prefix. -/
def quittingFiniteFullSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) : ℝ :=
  quittingFiniteContinueWeight
    (quittingFiniteFullContinueMass roots who hazard) start fuel

theorem quittingFiniteFullContinueMass_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ quittingFiniteFullContinueMass roots who hazard time := by
  exact mul_nonneg ENNReal.toReal_nonneg
    (quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false)))

/-- With the prescribed player's actual root marginal, the preceding scalar
is exactly the all-Continue mass of the full product root. -/
theorem quittingFiniteFullContinueMass_self_eq_stationaryContinueMass
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingFiniteFullContinueMass roots who
        (fun stage => roots stage who) time =
      quittingStationaryContinueMass (roots time) := by
  classical
  have hproduct := Math.PMFProduct.pmfPi_update_family_mul
    (roots time) who (PMF.pure false)
      (quittingAllContinueAction : ι → Bool)
  have hreal := congrArg ENNReal.toReal hproduct
  unfold quittingFiniteFullContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  simpa [quittingAllContinueAction, ENNReal.toReal_mul, mul_comm] using hreal

theorem quittingFiniteFullContinueMass_le_opponents
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingFiniteFullContinueMass roots who hazard time ≤
      quittingFixedOpponentsContinueMass roots who time := by
  have hprob : (hazard time false).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (hazard time) false)
  exact mul_le_of_le_one_left
    (quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false))) hprob

theorem quittingFiniteFullSurvivalWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (start fuel : ℕ) :
    0 ≤ quittingFiniteFullSurvivalWeight roots who hazard start fuel := by
  exact quittingFiniteContinueWeight_nonneg _
    (quittingFiniteFullContinueMass_nonneg roots who hazard) start fuel

/-- Closed product form of prescribed full-profile survival. -/
theorem quittingFiniteFullSurvivalWeight_self_eq_product
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingFiniteFullSurvivalWeight roots who
        (fun time => roots time who) start fuel =
      ∏ offset ∈ Finset.range fuel,
        quittingStationaryContinueMass (roots (start + offset)) := by
  rw [quittingFiniteFullSurvivalWeight,
    quittingFiniteContinueWeight_eq_product]
  apply Finset.prod_congr rfl
  intro offset _
  exact quittingFiniteFullContinueMass_self_eq_stationaryContinueMass
    roots who (start + offset)

/-- **Bridge to the canonical survival product.**  At the prescribed
player's own root marginal as hazard, `quittingFiniteFullSurvivalWeight`
collapses to `Math.survivalProduct` at the stationary continue mass -- the
same target `quittingJointSurvivalWeight_eq_survivalProduct` and
`quittingSurvivalPrefix_eq_survivalProduct` reach independently.  See the
module docstring of `Math.SurvivalProduct` for the full census this bridges
into. -/
theorem quittingFiniteFullSurvivalWeight_self_eq_survivalProduct
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingFiniteFullSurvivalWeight roots who
        (fun time => roots time who) start fuel =
      Math.survivalProduct (fun t => quittingStationaryContinueMass (roots t))
        start fuel :=
  quittingFiniteFullSurvivalWeight_self_eq_product roots who start fuel

/-- Full-profile survival is bounded by opponent-only survival. -/
theorem quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteFullSurvivalWeight roots who hazard start fuel ≤
        quittingOpponentSurvivalWeight roots who start fuel := by
  intro start fuel
  rw [← quittingFiniteContinueWeight_fixedOpponents_eq_survivalWeight]
  induction fuel generalizing start with
  | zero => simp [quittingFiniteFullSurvivalWeight,
      quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingFiniteFullSurvivalWeight,
        quittingFiniteContinueWeight, quittingFiniteContinueWeight]
      exact mul_le_mul
        (quittingFiniteFullContinueMass_le_opponents roots who hazard start)
        (ih (start + 1))
        (quittingFiniteFullSurvivalWeight_nonneg roots who hazard
          (start + 1) fuel)
        (quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false)))

/-! ## Boundary-value recursions -/

/-- Payoff from committing to Continue at every remaining prefix date and
receiving `terminalValue` if all opponents also Continue. -/
def quittingFiniteContinueToBoundaryValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => terminalValue
  | start, fuel + 1 =>
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingFiniteContinueToBoundaryValue reward roots who
            terminalValue (start + 1) fuel

/-- Best value among deterministic Quit dates strictly before the boundary.
The second natural-number argument counts the number of additional prefix
dates after the current one. -/
def quittingFiniteEarlyBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℕ → ℕ → ℝ
  | start, 0 => quittingFixedOpponentsQuitValue reward roots who start
  | start, fuel + 1 =>
      max (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            quittingFiniteEarlyBestResponseValue reward roots who
              (start + 1) fuel)

private theorem add_mul_max_of_nonneg
    (a c x y : ℝ) (hc : 0 ≤ c) :
    a + c * max x y = max (a + c * x) (a + c * y) := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, max_eq_right]
    simpa [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hxy hc) a
  · rw [max_eq_left hyx, max_eq_left]
    simpa [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hyx hc) a

/-- A finite best response either quits before the boundary or Continues
throughout the prefix and takes the supplied boundary value. -/
theorem quittingFiniteTerminalBestResponseValue_eq_max_early_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue : ℝ) (start fuel : ℕ) :
    quittingFiniteTerminalBestResponseValue reward roots who terminalValue
        start (fuel + 1) =
      max
        (quittingFiniteEarlyBestResponseValue reward roots who start fuel)
        (quittingFiniteContinueToBoundaryValue reward roots who terminalValue
          start (fuel + 1)) := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteTerminalBestResponseValue,
        quittingFiniteEarlyBestResponseValue,
        quittingFiniteContinueToBoundaryValue, ih (start + 1)]
      rw [add_mul_max_of_nonneg]
      · simp only [max_assoc]
      · exact quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))

/-- The Continue-through boundary alternative is affine in the boundary
value, with slope equal to opponent-only survival. -/
theorem quittingFiniteContinueToBoundaryValue_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (terminalValue error : ℝ) (start fuel : ℕ) :
    quittingFiniteContinueToBoundaryValue reward roots who
        (terminalValue + error) start fuel =
      quittingFiniteContinueToBoundaryValue reward roots who terminalValue
          start fuel +
        quittingOpponentSurvivalWeight roots who start fuel * error := by
  rw [← quittingFiniteContinueWeight_fixedOpponents_eq_survivalWeight]
  induction fuel generalizing start with
  | zero => simp [quittingFiniteContinueToBoundaryValue,
      quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingFiniteContinueToBoundaryValue,
        quittingFiniteContinueToBoundaryValue,
        quittingFiniteContinueWeight, ih (start + 1)]
      ring

/-- The prescribed finite payoff is affine in its terminal boundary, with
slope equal to full-profile survival. -/
theorem quittingFiniteTerminalHazardValue_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (terminalValue error : ℝ)
    (start fuel : ℕ) :
    quittingFiniteTerminalHazardValue reward roots who hazard
        (terminalValue + error) start fuel =
      quittingFiniteTerminalHazardValue reward roots who hazard terminalValue
          start fuel +
        quittingFiniteFullSurvivalWeight roots who hazard start fuel *
          error := by
  induction fuel generalizing start with
  | zero => simp [quittingFiniteTerminalHazardValue,
      quittingFiniteFullSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [quittingFiniteTerminalHazardValue,
        quittingFiniteTerminalHazardValue,
        quittingFiniteFullSurvivalWeight,
        quittingFiniteContinueWeight, ih (start + 1)]
      unfold quittingFiniteFullSurvivalWeight
      unfold quittingFiniteFullContinueMass
      ring

/-! ## Exact policy evaluation and relative debt -/

/-- Evaluating the player's prescribed root marginal through a finite prefix
returns the displayed prescribed value when the supplied terminal boundary
matches the displayed endpoint. -/
theorem quittingFiniteTerminalHazardValue_self_eq_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed) :
    ∀ start fuel,
      quittingFiniteTerminalHazardValue reward roots who
          (fun time => roots time who) (prescribed (start + fuel))
          start fuel =
        prescribed start := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp
  | succ fuel ih =>
      rw [show start + (fuel + 1) = start + 1 + fuel by omega]
      rw [quittingFiniteTerminalHazardValue, ih (start + 1)]
      rw [hprescribed start,
        quittingRootSuccessorPayoff_eq_endpointMix,
        quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]

/-- Difference form of the exact dynamic-debt semantics: relative terminal
debt is exactly the finite Bellman exploitability above the displayed
prescribed value. -/
theorem quittingFiniteRelativeBoundaryDebt_eq_dynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    quittingFiniteTerminalBestResponseValue reward roots who
          (prescribed (start + fuel) + terminalDebt) start fuel -
        prescribed start =
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel := by
  rw [← prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse]
  ring

/-- Exploitability of a finite prescribed prefix after changing its delivered
terminal payoff by `error` while keeping the certified relative terminal debt
fixed. -/
def quittingFiniteRelativeBoundaryExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt error : ℝ)
    (start fuel : ℕ) : ℝ :=
  quittingFiniteTerminalBestResponseValue reward roots who
      (prescribed (start + fuel) + terminalDebt + error) start fuel -
    quittingFiniteTerminalHazardValue reward roots who
      (fun time => roots time who) (prescribed (start + fuel) + error)
      start fuel

/-- With exact boundary matching, the scalar reinsertion exploitability is
exactly the propagated dynamic debt. -/
theorem quittingFiniteRelativeBoundaryExploitability_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt : ℝ) (start fuel : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt 0 start fuel =
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel := by
  rw [quittingFiniteRelativeBoundaryExploitability]
  simp only [add_zero]
  rw [quittingFiniteTerminalHazardValue_self_eq_prescribed
    reward roots who prescribed hprescribed]
  exact quittingFiniteRelativeBoundaryDebt_eq_dynamicDebt
    reward roots who prescribed terminalDebt start fuel

/-- **Sharp relative-boundary perturbation formula.**  The prescribed payoff
sees the boundary error with full-profile survival `P`, while a deviator who
Continues throughout the prefix sees it with opponent-only survival `χ`. -/
theorem quittingFiniteRelativeBoundaryExploitability_succ_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt error : ℝ) (start fuel : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start (fuel + 1) =
      max
          (quittingFiniteEarlyBestResponseValue reward roots who start fuel)
          (quittingFiniteContinueToBoundaryValue reward roots who
              (prescribed (start + (fuel + 1)) + terminalDebt)
              start (fuel + 1) +
            quittingOpponentSurvivalWeight roots who start (fuel + 1) *
              error) -
        (prescribed start +
          quittingFiniteFullSurvivalWeight roots who
              (fun time => roots time who) start (fuel + 1) * error) := by
  rw [quittingFiniteRelativeBoundaryExploitability,
    quittingFiniteTerminalBestResponseValue_eq_max_early_boundary]
  rw [show prescribed (start + (fuel + 1)) + terminalDebt + error =
      (prescribed (start + (fuel + 1)) + terminalDebt) + error by ring]
  rw [quittingFiniteContinueToBoundaryValue_add]
  rw [quittingFiniteTerminalHazardValue_add]
  rw [quittingFiniteTerminalHazardValue_self_eq_prescribed
    reward roots who prescribed hprescribed]

/-- A length-zero prefix is insensitive to boundary mismatch: prescribed and
best-response values shift by the same amount. -/
@[simp] theorem quittingFiniteRelativeBoundaryExploitability_zeroFuel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt error : ℝ) (start : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start 0 = terminalDebt := by
  simp [quittingFiniteRelativeBoundaryExploitability,
    quittingFiniteTerminalBestResponseValue,
    quittingFiniteTerminalHazardValue]

/-! ## Sharp survival-weighted error bounds -/

private theorem max_add_mul_sub_max_le_mul_posPart
    (A T χ error : ℝ) (hχ : 0 ≤ χ) :
    max A (T + χ * error) - max A T ≤ χ * max error 0 := by
  by_cases herror : 0 ≤ error
  · rw [max_eq_left herror]
    have hscaled : 0 ≤ χ * error := mul_nonneg hχ herror
    have hmax : max A (T + χ * error) ≤ max A T + χ * error := by
      apply max_le
      · linarith [le_max_left A T]
      · linarith [le_max_right A T]
    linarith
  · have herror' : error ≤ 0 := le_of_not_ge herror
    rw [max_eq_right herror']
    have hscaled : χ * error ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hχ herror'
    have hmax : max A (T + χ * error) ≤ max A T := by
      apply max_le
      · exact le_max_left A T
      · exact (add_le_of_nonpos_right hscaled).trans (le_max_right A T)
    linarith

private theorem mul_posPart_sub_mul_eq_survivalError
    (χ P error : ℝ) :
    χ * max error 0 - P * error =
      (χ - P) * max error 0 + P * max (-error) 0 := by
  rcases le_total 0 error with herror | herror
  · rw [max_eq_left herror, max_eq_right (neg_nonpos.mpr herror)]
    ring
  · rw [max_eq_right herror, max_eq_left (neg_nonneg.mpr herror)]
    ring

/-- Sign-sensitive reinsertion bound.  Favorable boundary error is charged
only to the extra exposure `χ - P` available to a deviator; unfavorable
boundary error is charged to the prescribed full-survival atom `P`. -/
theorem quittingFiniteRelativeBoundaryExploitability_succ_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt error : ℝ) (start fuel : ℕ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start (fuel + 1) ≤
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start (fuel + 1) +
        (quittingOpponentSurvivalWeight roots who start (fuel + 1) -
            quittingFiniteFullSurvivalWeight roots who
              (fun time => roots time who) start (fuel + 1)) *
          max error 0 +
        quittingFiniteFullSurvivalWeight roots who
            (fun time => roots time who) start (fuel + 1) *
          max (-error) 0 := by
  let A := quittingFiniteEarlyBestResponseValue reward roots who start fuel
  let T := quittingFiniteContinueToBoundaryValue reward roots who
    (prescribed (start + (fuel + 1)) + terminalDebt) start (fuel + 1)
  let χ := quittingOpponentSurvivalWeight roots who start (fuel + 1)
  let P := quittingFiniteFullSurvivalWeight roots who
    (fun time => roots time who) start (fuel + 1)
  have hnew :
      quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
          terminalDebt error start (fuel + 1) =
        max A (T + χ * error) - (prescribed start + P * error) := by
    simpa only [A, T, χ, P] using
      quittingFiniteRelativeBoundaryExploitability_succ_eq reward roots who
        prescribed hprescribed terminalDebt error start fuel
  have hbase :
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start (fuel + 1) =
        max A T - prescribed start := by
    rw [← quittingFiniteRelativeBoundaryExploitability_zero reward roots who
      prescribed hprescribed terminalDebt start (fuel + 1)]
    simpa only [A, T, χ, P, mul_zero, add_zero] using
      quittingFiniteRelativeBoundaryExploitability_succ_eq reward roots who
        prescribed hprescribed terminalDebt 0 start fuel
  have hχ : 0 ≤ χ := by
    exact quittingOpponentSurvivalWeight_nonneg roots who start (fuel + 1)
  have hmax := max_add_mul_sub_max_le_mul_posPart A T χ error hχ
  have hsplit := mul_posPart_sub_mul_eq_survivalError χ P error
  rw [hnew, hbase]
  linarith

private theorem survivalError_le_abs_envelope
    (χ P error κ : ℝ) (hP0 : 0 ≤ P) (hPχ : P ≤ χ)
    (herror : |error| ≤ κ) :
    (χ - P) * max error 0 + P * max (-error) 0 ≤
      κ * max P (χ - P) := by
  have hgap0 : 0 ≤ χ - P := sub_nonneg.mpr hPχ
  have hκ0 : 0 ≤ κ := (abs_nonneg error).trans herror
  have hmax0 : 0 ≤ max P (χ - P) := hP0.trans (le_max_left _ _)
  by_cases hsign : 0 ≤ error
  · rw [max_eq_left hsign, max_eq_right (neg_nonpos.mpr hsign),
      mul_zero, add_zero]
    have herrorκ : error ≤ κ := by
      simpa [abs_of_nonneg hsign] using herror
    have hmul := mul_le_mul herrorκ (le_max_right P (χ - P)) hgap0 hκ0
    simpa [mul_comm] using hmul
  · have hsign' : error ≤ 0 := le_of_not_ge hsign
    rw [max_eq_right hsign', max_eq_left (neg_nonneg.mpr hsign'),
      mul_zero, zero_add]
    have herrorκ : -error ≤ κ := by
      simpa [abs_of_nonpos hsign'] using herror
    have hmul := mul_le_mul herrorκ (le_max_left P (χ - P)) hP0 hκ0
    simpa [mul_comm] using hmul

/-- Absolute-error envelope for approximate boundary matching.  There is no
factor proportional to the prefix length. -/
theorem quittingFiniteRelativeBoundaryExploitability_succ_le_abs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (terminalDebt error κ : ℝ) (start fuel : ℕ)
    (herror : |error| ≤ κ) :
    quittingFiniteRelativeBoundaryExploitability reward roots who prescribed
        terminalDebt error start (fuel + 1) ≤
      quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
          start (fuel + 1) +
        κ * max
          (quittingFiniteFullSurvivalWeight roots who
            (fun time => roots time who) start (fuel + 1))
          (quittingOpponentSurvivalWeight roots who start (fuel + 1) -
            quittingFiniteFullSurvivalWeight roots who
              (fun time => roots time who) start (fuel + 1)) := by
  let P := quittingFiniteFullSurvivalWeight roots who
    (fun time => roots time who) start (fuel + 1)
  let χ := quittingOpponentSurvivalWeight roots who start (fuel + 1)
  have hmain := quittingFiniteRelativeBoundaryExploitability_succ_le
    reward roots who prescribed hprescribed terminalDebt error start fuel
  have hP0 : 0 ≤ P := by
    exact quittingFiniteFullSurvivalWeight_nonneg roots who
      (fun time => roots time who) start (fuel + 1)
  have hPχ : P ≤ χ := by
    exact quittingFiniteFullSurvivalWeight_le_opponentSurvivalWeight roots who
      (fun time => roots time who) start (fuel + 1)
  have henvelope := survivalError_le_abs_envelope χ P error κ hP0 hPχ herror
  dsimp only [P, χ] at hmain henvelope ⊢
  linarith

end GameTheory
