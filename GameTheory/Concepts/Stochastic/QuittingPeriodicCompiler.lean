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

end GameTheory
