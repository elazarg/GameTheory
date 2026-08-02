/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Logic.Equiv.Fin.Rotate
import GameTheory.Concepts.Stochastic.QuittingBehaviorPureTimeExtremality
import GameTheory.Concepts.Stochastic.QuittingStationaryGain

/-!
# Eventually-periodic quitting compiler

This module compiles finite cyclic root/value certificates into infinite
quitting-game statements.  Its algebraic core is quantitative: if one trip
around a cycle contracts by `ρ < 1`, phase errors are amplified by at most
the corresponding weighted cycle charge divided by `1 - ρ`.  Exact cyclic
fixed-point uniqueness is the zero-error special case.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

/-! ## Quantitative cyclic contraction -/

/-- The phase reached after rotating a finite cycle `steps` times. -/
def quittingCyclicOrbit {K : ℕ} (phase : Fin K) (steps : ℕ) : Fin K :=
  ⟨(phase.val + steps) % K, Nat.mod_lt _ phase.pos⟩

@[simp] theorem quittingCyclicOrbit_zero {K : ℕ} (phase : Fin K) :
    quittingCyclicOrbit phase 0 = phase := by
  apply Fin.ext
  simp [quittingCyclicOrbit, Nat.mod_eq_of_lt phase.isLt]

theorem quittingCyclicOrbit_succ {K : ℕ} (phase : Fin K) (steps : ℕ) :
    quittingCyclicOrbit phase (steps + 1) =
      finRotate K (quittingCyclicOrbit phase steps) := by
  haveI := phase.neZero
  rw [finRotate_apply]
  apply Fin.ext
  change (phase.val + (steps + 1)) % K =
    ((phase.val + steps) % K + 1 % K) % K
  rw [← Nat.add_assoc, Nat.add_mod]

/-- Rotating a nonempty `K`-cycle `K` times returns to the initial phase. -/
theorem quittingCyclicOrbit_card {K : ℕ} (phase : Fin K) :
    quittingCyclicOrbit phase K = phase := by
  apply Fin.ext
  simp [quittingCyclicOrbit, Nat.mod_eq_of_lt phase.isLt]

/-- Advancing by two successive offsets agrees with advancing by their
sum. -/
theorem quittingCyclicOrbit_add {K : ℕ} (phase : Fin K)
    (first second : ℕ) :
    quittingCyclicOrbit phase (first + second) =
      quittingCyclicOrbit (quittingCyclicOrbit phase first) second := by
  induction second with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ, quittingCyclicOrbit_succ, ih,
        quittingCyclicOrbit_succ]

/-- Product of contraction coefficients before a supplied cycle offset. -/
def quittingCyclicPrefixWeight {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel,
    coefficient (quittingCyclicOrbit phase offset)

@[simp] theorem quittingCyclicPrefixWeight_zero {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) :
    quittingCyclicPrefixWeight coefficient phase 0 = 1 := by
  simp [quittingCyclicPrefixWeight]

theorem quittingCyclicPrefixWeight_succ {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) :
    quittingCyclicPrefixWeight coefficient phase (fuel + 1) =
      quittingCyclicPrefixWeight coefficient phase fuel *
        coefficient (quittingCyclicOrbit phase fuel) := by
  simp [quittingCyclicPrefixWeight, Finset.prod_range_succ]

theorem quittingCyclicPrefixWeight_nonneg {K : ℕ}
    (coefficient : Fin K → ℝ) (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (phase : Fin K) (fuel : ℕ) :
    0 ≤ quittingCyclicPrefixWeight coefficient phase fuel := by
  exact Finset.prod_nonneg fun offset _ => hcoefficient _

/-- Prefix weights split at an arbitrary cycle offset. -/
theorem quittingCyclicPrefixWeight_add {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) (first second : ℕ) :
    quittingCyclicPrefixWeight coefficient phase (first + second) =
      quittingCyclicPrefixWeight coefficient phase first *
        quittingCyclicPrefixWeight coefficient
          (quittingCyclicOrbit phase first) second := by
  induction second with
  | zero => simp
  | succ second ih =>
      rw [Nat.add_succ, quittingCyclicPrefixWeight_succ, ih,
        quittingCyclicPrefixWeight_succ, quittingCyclicOrbit_add]
      ring

/-- Prefix weights are antitone when every coefficient is at most one. -/
theorem antitone_quittingCyclicPrefixWeight {K : ℕ}
    (coefficient : Fin K → ℝ)
    (hcoefficient0 : ∀ phase, 0 ≤ coefficient phase)
    (hcoefficient1 : ∀ phase, coefficient phase ≤ 1)
    (phase : Fin K) :
    Antitone (quittingCyclicPrefixWeight coefficient phase) := by
  apply antitone_nat_of_succ_le
  intro fuel
  rw [quittingCyclicPrefixWeight_succ]
  exact mul_le_of_le_one_right
    (quittingCyclicPrefixWeight_nonneg
      coefficient hcoefficient0 phase fuel)
    (hcoefficient1 _)

/-- A full turn multiplies by the product of all phase coefficients,
independently of the starting phase. -/
theorem quittingCyclicPrefixWeight_card {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) :
    quittingCyclicPrefixWeight coefficient phase K =
      ∏ cyclePhase : Fin K, coefficient cyclePhase := by
  letI : NeZero K := phase.neZero
  have horbit : ∀ offset : Fin K,
      quittingCyclicOrbit phase offset.val = finCycle phase offset := by
    intro offset
    apply Fin.ext
    simp [quittingCyclicOrbit, finCycle_apply, Fin.add_def, Nat.add_comm]
  rw [quittingCyclicPrefixWeight, Finset.prod_range]
  simp_rw [horbit]
  exact Equiv.prod_comp (finCycle phase) coefficient

/-- Any whole number of turns returns to the same initial phase. -/
theorem quittingCyclicOrbit_mul_card {K : ℕ} (phase : Fin K)
    (turns : ℕ) :
    quittingCyclicOrbit phase (turns * K) = phase := by
  induction turns with
  | zero => simp
  | succ turns ih =>
      rw [Nat.succ_mul, quittingCyclicOrbit_add, ih,
        quittingCyclicOrbit_card]

/-- Survival through whole turns is a power of the one-cycle product. -/
theorem quittingCyclicPrefixWeight_mul_card {K : ℕ}
    (coefficient : Fin K → ℝ) (phase : Fin K) (turns : ℕ) :
    quittingCyclicPrefixWeight coefficient phase (turns * K) =
      (∏ cyclePhase : Fin K, coefficient cyclePhase) ^ turns := by
  induction turns with
  | zero => simp
  | succ turns ih =>
      rw [Nat.succ_mul, quittingCyclicPrefixWeight_add,
        quittingCyclicOrbit_mul_card, ih,
        quittingCyclicPrefixWeight_card, pow_succ]

/-- A contracting one-cycle product forces all cyclic prefix weights, not
only the weights at cycle boundaries, to vanish. -/
theorem tendsto_zero_quittingCyclicPrefixWeight {K : ℕ}
    (coefficient : Fin K → ℝ)
    (hcoefficient0 : ∀ phase, 0 ≤ coefficient phase)
    (hcoefficient1 : ∀ phase, coefficient phase ≤ 1)
    (hcycle : (∏ phase : Fin K, coefficient phase) < 1)
    (phase : Fin K) :
    Tendsto (quittingCyclicPrefixWeight coefficient phase) atTop (nhds 0) := by
  let ρ := ∏ cyclePhase : Fin K, coefficient cyclePhase
  have hρ0 : 0 ≤ ρ := Finset.prod_nonneg fun cyclePhase _ =>
    hcoefficient0 cyclePhase
  have hpow : Tendsto (fun turns : ℕ => ρ ^ turns) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hcycle
  have hdiv : Tendsto (fun fuel : ℕ => fuel / K) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt phase.pos)
  apply squeeze_zero
  · exact quittingCyclicPrefixWeight_nonneg
      coefficient hcoefficient0 phase
  · intro fuel
    have hmono := antitone_quittingCyclicPrefixWeight
      coefficient hcoefficient0 hcoefficient1 phase
    have hbound := hmono (Nat.div_mul_le_self fuel K)
    simpa only [quittingCyclicPrefixWeight_mul_card, ρ] using hbound
  · exact hpow.comp hdiv

/-- Weighted charge of the phase residuals accumulated before a cutoff. -/
def quittingCyclicResidualCharge {K : ℕ}
    (coefficient residual : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    quittingCyclicPrefixWeight coefficient phase offset *
      residual (quittingCyclicOrbit phase offset)

@[simp] theorem quittingCyclicResidualCharge_zero {K : ℕ}
    (coefficient residual : Fin K → ℝ) (phase : Fin K) :
    quittingCyclicResidualCharge coefficient residual phase 0 = 0 := by
  simp [quittingCyclicResidualCharge]

theorem quittingCyclicResidualCharge_succ {K : ℕ}
    (coefficient residual : Fin K → ℝ) (phase : Fin K) (fuel : ℕ) :
    quittingCyclicResidualCharge coefficient residual phase (fuel + 1) =
      quittingCyclicResidualCharge coefficient residual phase fuel +
        quittingCyclicPrefixWeight coefficient phase fuel *
          residual (quittingCyclicOrbit phase fuel) := by
  simp [quittingCyclicResidualCharge, Finset.sum_range_succ]

theorem quittingCyclicResidualCharge_nonneg {K : ℕ}
    (coefficient residual : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hresidual : ∀ phase, 0 ≤ residual phase)
    (phase : Fin K) (fuel : ℕ) :
    0 ≤ quittingCyclicResidualCharge coefficient residual phase fuel := by
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg
    (quittingCyclicPrefixWeight_nonneg coefficient hcoefficient phase offset)
    (hresidual _)

/-- Iterating a one-sided affine error inequality along a finite cycle. -/
theorem cyclicValue_le_residualCharge_add_weight
    {K : ℕ} (coefficient residual value : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hstep : ∀ phase,
      value phase ≤ residual phase +
        coefficient phase * value (finRotate K phase)) :
    ∀ (phase : Fin K) (fuel : ℕ),
      value phase ≤
        quittingCyclicResidualCharge coefficient residual phase fuel +
          quittingCyclicPrefixWeight coefficient phase fuel *
            value (quittingCyclicOrbit phase fuel) := by
  intro phase fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hnext := hstep (quittingCyclicOrbit phase fuel)
      have hweight := quittingCyclicPrefixWeight_nonneg
        coefficient hcoefficient phase fuel
      have hscaled := mul_le_mul_of_nonneg_left hnext hweight
      rw [quittingCyclicResidualCharge_succ,
        quittingCyclicPrefixWeight_succ, quittingCyclicOrbit_succ]
      calc
        value phase ≤
            quittingCyclicResidualCharge coefficient residual phase fuel +
              quittingCyclicPrefixWeight coefficient phase fuel *
                value (quittingCyclicOrbit phase fuel) := ih
        _ ≤ quittingCyclicResidualCharge coefficient residual phase fuel +
            quittingCyclicPrefixWeight coefficient phase fuel *
              (residual (quittingCyclicOrbit phase fuel) +
                coefficient (quittingCyclicOrbit phase fuel) *
                  value (finRotate K
                    (quittingCyclicOrbit phase fuel))) :=
          add_le_add_right hscaled _
        _ = quittingCyclicResidualCharge coefficient residual phase fuel +
              quittingCyclicPrefixWeight coefficient phase fuel *
                residual (quittingCyclicOrbit phase fuel) +
            (quittingCyclicPrefixWeight coefficient phase fuel *
              coefficient (quittingCyclicOrbit phase fuel)) *
                value (finRotate K
                  (quittingCyclicOrbit phase fuel)) := by ring

/-- Quantitative cyclic contraction: one full cycle bounds every phase error
by its weighted residual charge divided by `1 - ρ`. -/
theorem cyclicValue_le_residualCharge_div_one_sub_prod
    {K : ℕ}
    (coefficient residual value : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hcycle : (∏ phase : Fin K, coefficient phase) < 1)
    (hstep : ∀ phase,
      value phase ≤ residual phase +
        coefficient phase * value (finRotate K phase))
    (phase : Fin K) :
    value phase ≤
      quittingCyclicResidualCharge coefficient residual phase K /
        (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
  have hunroll := cyclicValue_le_residualCharge_add_weight
    coefficient residual value hcoefficient hstep phase K
  rw [quittingCyclicPrefixWeight_card,
    quittingCyclicOrbit_card] at hunroll
  have hdenom : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcycle
  apply (le_div_iff₀ hdenom).2
  nlinarith

/-- Absolute-error form of the one-sided cyclic contraction estimate. -/
theorem abs_cyclicValue_le_residualCharge_div_one_sub_prod
    {K : ℕ} (coefficient residual value : Fin K → ℝ)
    (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (hcycle : (∏ phase : Fin K, coefficient phase) < 1)
    (hstep : ∀ phase,
      |value phase| ≤ residual phase +
        coefficient phase * |value (finRotate K phase)|)
    (phase : Fin K) :
    |value phase| ≤
      quittingCyclicResidualCharge coefficient residual phase K /
        (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
  exact cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient residual (fun cyclePhase => |value cyclePhase|)
      hcoefficient hcycle hstep phase

/-! ## Cyclic root sequences -/

/-- A finite cycle of product roots, read forever from an arbitrary initial
phase. -/
def quittingCyclicRootSequence {K : ℕ} {ι : Type}
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (time : ℕ) :
    ι → PMF Bool :=
  cycle (quittingCyclicOrbit phase time)

@[simp] theorem quittingCyclicRootSequence_zero
    {K : ℕ} {ι : Type} (cycle : Fin K → ι → PMF Bool)
    (phase : Fin K) :
    quittingCyclicRootSequence cycle phase 0 = cycle phase := by
  simp [quittingCyclicRootSequence]

/-- Dropping the first root of a cyclic sequence rotates its initial
phase. -/
theorem quittingCyclicRootSequence_succ
    {K : ℕ} {ι : Type} (cycle : Fin K → ι → PMF Bool)
    (phase : Fin K) (time : ℕ) :
    quittingCyclicRootSequence cycle phase (time + 1) =
      quittingCyclicRootSequence cycle (finRotate K phase) time := by
  unfold quittingCyclicRootSequence
  rw [show time + 1 = 1 + time by omega,
    quittingCyclicOrbit_add, quittingCyclicOrbit_succ]
  simp

/-- Starting a cyclic root sequence later is the same as rotating its
initial phase by that many steps. -/
theorem quittingCyclicRootSequence_add
    {K : ℕ} {ι : Type} (cycle : Fin K → ι → PMF Bool)
    (phase : Fin K) (start time : ℕ) :
    quittingCyclicRootSequence cycle phase (start + time) =
      quittingCyclicRootSequence cycle
        (quittingCyclicOrbit phase start) time := by
  simp only [quittingCyclicRootSequence, quittingCyclicOrbit_add]

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At a cyclic live stage, fixed-opponent continuation mass is the
corresponding phase coefficient. -/
@[simp] theorem quittingFixedOpponentsContinueMass_cyclicRootSequence
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingCyclicRootSequence cycle phase) who time =
      quittingStationaryFixedOpponentsContinueMass
        (cycle (quittingCyclicOrbit phase time)) who := by
  rfl

/-- Opponent survival along a cyclic root sequence is exactly the cyclic
prefix product, from the phase reached at the starting time. -/
theorem quittingOpponentSurvivalWeight_cyclicRootSequence
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingCyclicRootSequence cycle phase) who start fuel =
      quittingCyclicPrefixWeight
        (fun cyclePhase =>
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who)
        (quittingCyclicOrbit phase start) fuel := by
  unfold quittingOpponentSurvivalWeight quittingCyclicPrefixWeight
  apply Finset.prod_congr rfl
  intro offset _
  rw [quittingFixedOpponentsContinueMass_cyclicRootSequence]
  congr 2
  exact quittingCyclicOrbit_add phase start offset

/-- Playerwise contraction over one turn makes opponent survival along the
entire cyclic live path converge to zero. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (hcontracts : (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) who) < 1) :
    Tendsto (quittingOpponentSurvivalWeight
      (quittingCyclicRootSequence cycle phase) who 0) atTop (nhds 0) := by
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who
  have hcoefficient0 : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase =>
      quittingStationaryFixedOpponentsContinueMass_nonneg
        (cycle cyclePhase) who
  have hcoefficient1 : ∀ cyclePhase, coefficient cyclePhase ≤ 1 :=
    fun cyclePhase => quittingStationaryContinueMass_le_one
      (Function.update (cycle cyclePhase) who (PMF.pure false))
  have hprefix := tendsto_zero_quittingCyclicPrefixWeight coefficient
    hcoefficient0 hcoefficient1 hcontracts phase
  convert hprefix using 1
  funext fuel
  rw [quittingOpponentSurvivalWeight_cyclicRootSequence]
  simp
  rfl

/-- Terminal payoff vector selected by the infinite cyclic root profile
from a supplied initial phase. -/
def quittingCyclicTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) : Payoff ι :=
  fun who => quittingRootSequenceTerminalValue reward
    (quittingCyclicRootSequence cycle phase) who 0

omit [DecidableEq ι] in
/-- Terminal evaluation after a finite offset selects the terminal value at
the correspondingly rotated phase. -/
theorem quittingRootSequenceTerminalValue_cyclic_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (who : ι) (start : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who start =
      quittingCyclicTerminalValue reward cycle
        (quittingCyclicOrbit phase start) who := by
  unfold quittingRootSequenceTerminalValue quittingCyclicTerminalValue
  congr 1
  funext player time history
  simp only [quittingRootSequenceProfile,
    quittingCyclicRootSequence_add, zero_add]

omit [DecidableEq ι] in
/-- Cyclic terminal values satisfy the exact root policy-evaluation
recursion at every phase. -/
theorem quittingCyclicTerminalValue_eq_rootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) :
    quittingCyclicTerminalValue reward cycle phase =
      quittingRootSuccessorPayoff reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        (cycle phase) := by
  funext who
  unfold quittingCyclicTerminalValue
  rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff]
  simp only [quittingCyclicRootSequence_zero]
  apply quittingRootExpectedPayoff_continuation_congr
  rw [quittingRootSequenceTerminalValue_cyclic_eq]
  simp [quittingCyclicOrbit_succ]
  rfl

/-! ## Quantitative terminal selection -/

omit [DecidableEq ι] in
/-- A root successor is linear in the selected player's tail coordinate. -/
theorem quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward first root who -
        quittingRootSuccessorPayoff reward second root who =
      quittingStationaryContinueMass root * (first who - second who) := by
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

/-- The probability that everyone continues is at most the probability
that all opponents of any fixed player continue. -/
theorem quittingStationaryContinueMass_le_fixedOpponentsContinueMass
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root ≤
      quittingStationaryFixedOpponentsContinueMass root who := by
  have habsorption :=
    quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
  have hfactor : quittingStationaryContinueMass root =
      (root who false).toReal *
        quittingStationaryFixedOpponentsContinueMass root who := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hprobability : (root who false).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one false)
  have hmass := quittingStationaryFixedOpponentsContinueMass_nonneg root who
  rw [hfactor]
  have hprobability0 : 0 ≤ (root who false).toReal :=
    ENNReal.toReal_nonneg
  nlinarith

/-- Changing a player's tail coordinate changes its root successor payoff
by at most opponent survival times the tail-coordinate change. -/
theorem abs_quittingRootSuccessorPayoff_sub_le_fixedOpponentsContinueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    |quittingRootSuccessorPayoff reward first root who -
        quittingRootSuccessorPayoff reward second root who| ≤
      quittingStationaryFixedOpponentsContinueMass root who *
        |first who - second who| := by
  rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul, abs_mul,
    abs_of_nonneg (quittingStationaryContinueMass_nonneg root)]
  exact mul_le_mul_of_nonneg_right
    (quittingStationaryContinueMass_le_fixedOpponentsContinueMass root who)
    (abs_nonneg _)

/-- A certified approximate cyclic policy-evaluation vector is close to the
terminal payoff vector selected by the infinite lasso.  The amplification is
the exact forward weighted cycle charge divided by the playerwise contraction
gap. -/
theorem abs_sub_quittingCyclicTerminalValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (value : Fin K → Payoff ι) (error : Fin K → ι → ℝ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤
        error phase who)
    (who : ι)
    (hcontracts : (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1)
    (phase : Fin K) :
    |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| ≤
      quittingCyclicResidualCharge
          (fun cyclePhase =>
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) who)
          (fun cyclePhase => error cyclePhase who) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who) := by
  let terminal := quittingCyclicTerminalValue reward cycle
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryFixedOpponentsContinueMass (cycle cyclePhase) who
  let difference : Fin K → ℝ := fun cyclePhase =>
    value cyclePhase who - terminal cyclePhase who
  have hcoefficient : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase =>
      quittingStationaryFixedOpponentsContinueMass_nonneg
        (cycle cyclePhase) who
  have hstep : ∀ cyclePhase,
      |difference cyclePhase| ≤ error cyclePhase who +
        coefficient cyclePhase *
          |difference (finRotate K cyclePhase)| := by
    intro cyclePhase
    have hterminal := congrFun
      (quittingCyclicTerminalValue_eq_rootSuccessorPayoff
        reward cycle cyclePhase) who
    have hsplit : difference cyclePhase =
        (value cyclePhase who -
          quittingRootSuccessorPayoff reward
            (value (finRotate K cyclePhase)) (cycle cyclePhase) who) +
        (quittingRootSuccessorPayoff reward
            (value (finRotate K cyclePhase)) (cycle cyclePhase) who -
          quittingRootSuccessorPayoff reward
            (terminal (finRotate K cyclePhase))
            (cycle cyclePhase) who) := by
      dsimp only [difference, terminal]
      rw [hterminal]
      ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add
      (hpolicy cyclePhase who)
      (abs_quittingRootSuccessorPayoff_sub_le_fixedOpponentsContinueMass_mul
        reward (value (finRotate K cyclePhase))
          (terminal (finRotate K cyclePhase)) (cycle cyclePhase) who))
  exact abs_cyclicValue_le_residualCharge_div_one_sub_prod
    coefficient (fun cyclePhase => error cyclePhase who) difference
      hcoefficient hcontracts hstep phase

/-- Exact cyclic policy evaluation is selected uniquely by playerwise
opponent-cycle contraction. -/
theorem eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (hpolicy : ∀ phase,
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate K phase)) (cycle phase))
    (hcontracts : ∀ who,
      (∏ phase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who) < 1) :
    value = quittingCyclicTerminalValue reward cycle := by
  funext phase who
  have hpolicy0 : ∀ cyclePhase player,
      |value cyclePhase player -
        quittingRootSuccessorPayoff reward
          (value (finRotate K cyclePhase))
          (cycle cyclePhase) player| ≤ 0 := by
    intro cyclePhase player
    rw [congrFun (hpolicy cyclePhase) player]
    simp
  have hbound := abs_sub_quittingCyclicTerminalValue_le
    reward cycle value (fun _ _ => 0) hpolicy0 who
      (hcontracts who) phase
  have hcharge : quittingCyclicResidualCharge
      (fun cyclePhase =>
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who)
      (fun _ => 0) phase K = 0 := by
    simp [quittingCyclicResidualCharge]
  rw [hcharge, zero_div] at hbound
  have hzero :
      |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| = 0 :=
    le_antisymm hbound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-! ## Exact cyclic terminal Nash -/

/-- A prescribed policy has zero pure-action Bellman residual whenever its
current root is an exact Nash action against the prescribed next value. -/
theorem quittingPrescribedOneStepResidual_eq_zero_of_isZeroRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    (hnash : ∀ time (deviation : PMF Bool),
      quittingRootExpectedPayoff reward
          (fun _ => prescribed (time + 1))
          (Function.update (roots time) who deviation) who ≤
        quittingRootExpectedPayoff reward
            (fun _ => prescribed (time + 1)) (roots time) who + 0)
    (time : ℕ) :
    quittingPrescribedOneStepResidual
      reward roots who prescribed time = 0 := by
  let tail : Payoff ι := fun _ => prescribed (time + 1)
  have hquit := hnash time (PMF.pure true)
  have hcontinue := hnash time (PMF.pure false)
  have hquit' : quittingFixedOpponentsQuitValue reward roots who time ≤
      quittingRootSuccessorPayoff reward tail (roots time) who := by
    rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots who tail time]
    simpa only [tail, quittingRootQuitPayoff,
      quittingRootSuccessorPayoff, add_zero] using hquit
  have hcontinue' :
      quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            prescribed (time + 1) ≤
        quittingRootSuccessorPayoff reward tail (roots time) who := by
    rw [← quittingRootContinuePayoff_eq_fixedOpponents
      reward roots who tail time]
    simpa only [tail, quittingRootContinuePayoff,
      quittingRootSuccessorPayoff, add_zero] using hcontinue
  have hmax : quittingLiveBellmanValue reward roots who prescribed time ≤
      quittingRootSuccessorPayoff reward tail (roots time) who := by
    unfold quittingLiveBellmanValue
    exact max_le hquit' hcontinue'
  have hpolicy : quittingRootSuccessorPayoff reward tail (roots time) who =
      prescribed time := by
    symm
    exact hprescribed time
  have hreverse :
      quittingRootSuccessorPayoff reward tail (roots time) who ≤
      quittingLiveBellmanValue reward roots who prescribed time := by
    exact quittingRootSuccessorPayoff_le_liveBellmanValue
      reward roots who prescribed time
  unfold quittingPrescribedOneStepResidual
  rw [← hpolicy]
  exact sub_eq_zero.mpr (le_antisymm hmax hreverse)

/-- Exact root Nash at every cyclic terminal phase gives zero prescribed
Bellman residual at every live time. -/
theorem quittingPrescribedOneStepResidual_cyclic_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (time : ℕ) :
    quittingPrescribedOneStepResidual reward
        (quittingCyclicRootSequence cycle phase) who
        (quittingRootSequenceTerminalValue reward
          (quittingCyclicRootSequence cycle phase) who) time = 0 := by
  let roots := quittingCyclicRootSequence cycle phase
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  have htail : ∀ time,
      prescribed (time + 1) =
        quittingCyclicTerminalValue reward cycle
          (finRotate K (quittingCyclicOrbit phase time)) who := by
    intro liveTime
    dsimp only [prescribed, roots]
    rw [quittingRootSequenceTerminalValue_cyclic_eq,
      quittingCyclicOrbit_succ]
  have hrootNash : ∀ time (deviation : PMF Bool),
      quittingRootExpectedPayoff reward
          (fun _ => prescribed (time + 1))
          (Function.update (roots time) who deviation) who ≤
        quittingRootExpectedPayoff reward
            (fun _ => prescribed (time + 1)) (roots time) who + 0 := by
    intro liveTime deviation
    let cyclePhase := quittingCyclicOrbit phase liveTime
    let terminalTail := quittingCyclicTerminalValue reward cycle
      (finRotate K cyclePhase)
    have hdeviationEq := quittingRootExpectedPayoff_continuation_congr
      reward (fun _ : ι => prescribed (liveTime + 1)) terminalTail
        (Function.update (roots liveTime) who deviation) who
        (htail liveTime)
    have hrootEq := quittingRootExpectedPayoff_continuation_congr
      reward (fun _ : ι => prescribed (liveTime + 1)) terminalTail
        (roots liveTime) who (htail liveTime)
    have hlocal := hnash cyclePhase who deviation
    change quittingRootExpectedPayoff reward terminalTail
        (Function.update (roots liveTime) who deviation) who ≤
      quittingRootExpectedPayoff reward terminalTail
        (roots liveTime) who + 0 at hlocal
    rw [hdeviationEq, hrootEq]
    exact hlocal
  exact quittingPrescribedOneStepResidual_eq_zero_of_isZeroRootNash
    reward roots who prescribed
      (isQuittingLivePrescribedValue_quittingRootSequenceTerminalValue
        reward roots who)
      hrootNash time

/-- Against a cyclic profile with exact phasewise root Nash and playerwise
contraction, no time-dependent unilateral hazard improves the terminal
payoff. -/
theorem quittingCyclicHazardTerminalValue_le_of_isZeroRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) (who : ι)
    (deviation : ℕ → PMF Bool) (bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hcontracts : (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) who) < 1) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase who := by
  let roots := quittingCyclicRootSequence cycle phase
  let prescribed := quittingRootSequenceTerminalValue reward roots who
  have hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time =
        0 := by
    intro time
    exact quittingPrescribedOneStepResidual_cyclic_eq_zero
      reward cycle phase who hnash time
  have hsummable : Summable (fun time =>
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) := by
    simpa only [hresidual, mul_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots who 0) atTop (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
      cycle phase who hcontracts
  have hgap :=
    quittingRootSequenceHazardTerminalGap_le_tsum_residual_of_survival_zero
      reward roots who deviation bound hbound0 hreward hsurvival hsummable
  have hsum : (∑' time,
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingPrescribedOneStepResidual reward roots who prescribed time) =
      0 := by
    simp only [hresidual, mul_zero, tsum_zero]
  rw [hsum] at hgap
  have hbase : prescribed 0 =
      quittingCyclicTerminalValue reward cycle phase who := by
    dsimp only [prescribed, roots]
    rw [quittingRootSequenceTerminalValue_cyclic_eq]
    simp
  dsimp only [roots, prescribed] at hgap hbase ⊢
  linarith

/-- A finite exact phase certificate (policy recursion, local root Nash, and
playerwise contraction) compiles to the terminal no-profitable-hazard
inequality at every initial phase. -/
theorem quittingCyclicHazardTerminalValue_le_of_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) (deviation : ℕ → PMF Bool)
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingCyclicRootSequence cycle phase) who deviation 0 ≤
      quittingCyclicTerminalValue reward cycle phase who := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    reward cycle value hpolicy hcontracts
  have hnashTerminal : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase)) 0 (cycle cyclePhase) := by
    rw [← hvalue]
    exact hnash
  exact quittingCyclicHazardTerminalValue_le_of_isZeroRootNash
    reward cycle phase who deviation bound hbound0 hreward hnashTerminal
      (hcontracts who)

/-- History-independent behavior profile generated by an infinite cyclic
root sequence. -/
def quittingCyclicBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingCyclicRootSequence cycle phase) 0

omit [DecidableEq ι] in
/-- The canonical live roots of the cyclic behavior profile recover its
defining cyclic root sequence. -/
@[simp] theorem quittingProfileLiveRoot_cyclicBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) :
    quittingProfileLiveRoot reward
        (quittingCyclicBehaviorProfile reward cycle phase) =
      quittingCyclicRootSequence cycle phase := by
  funext time player
  simp [quittingProfileLiveRoot, quittingCyclicBehaviorProfile,
    quittingRootSequenceProfile]

omit [DecidableEq ι] in
/-- The terminal payoff of the cyclic behavior profile is its selected
cyclic terminal value. -/
@[simp] theorem quittingTerminalPayoff_cyclicBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) :
    quittingTerminalPayoff reward
        (quittingCyclicBehaviorProfile reward cycle phase) =
      quittingCyclicTerminalValue reward cycle phase := by
  rfl

/-- **Exact periodic quitting compiler.**  A finite phase certificate with
exact policy recursion, exact local root Nash, and playerwise opponent-cycle
contraction yields an exact terminal Nash behavior profile. -/
theorem isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate K cyclePhase)) (cycle cyclePhase))
    (hnash : ∀ cyclePhase,
      IsεQuittingRootNash reward
        (value (finRotate K cyclePhase)) 0 (cycle cyclePhase))
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro who deviation
  have hhazard := quittingCyclicHazardTerminalValue_le_of_certificate
    reward cycle value phase who
      (quittingBehaviorLiveHazard reward deviation) bound hbound0 hreward
      hpolicy hnash hcontracts
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile
    reward cycle phase] at hhazard
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase) who deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [hdeviation]
  simpa using hhazard

end GameTheory
