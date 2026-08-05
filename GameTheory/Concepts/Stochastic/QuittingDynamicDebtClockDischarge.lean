/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebt
import GameTheory.Concepts.Stochastic.QuittingOpponentClockDichotomy

/-!
# Exact quitting debt discharged by a divergent opponent clock

The finite dynamic debt is bounded by the
terminal debt times the probability that all opponents continue.  Hence a
divergent additive opponent clock discharges that exact debt at every fixed
chronological start, provided the displayed local Bellman residuals vanish.

This is an analytic implication for a supplied policy-value sequence.  It
does not construct that sequence, identify the finite Bellman quantity with
an unrestricted infinite-horizon deviation value, or produce an equilibrium.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A divergent opponent clock on one suffix drives the corresponding exact
finite dynamic debt to zero as the residual horizon tends to infinity. -/
theorem tendsto_zero_quittingFiniteDynamicDebt_of_not_summable_suffixClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (start : ℕ)
    (hclock : ¬Summable (fun offset ↦
      quittingOpponentClockCharge roots who (start + offset))) :
    Tendsto
      (fun fuel ↦ quittingFiniteDynamicDebt reward roots who prescribed
        terminalDebt start fuel)
      atTop (nhds 0) := by
  have hsurvival : Tendsto
      (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
      roots who start hclock
  have hscaled : Tendsto
      (fun fuel ↦
        quittingOpponentSurvivalWeight roots who start fuel * terminalDebt)
      atTop (nhds 0) := by
    simpa using hsurvival.mul_const terminalDebt
  exact squeeze_zero
    (fun fuel ↦ quittingFiniteDynamicDebt_nonneg reward roots who prescribed
      hprescribed hterminalDebt start fuel)
    (fun fuel ↦
      quittingFiniteDynamicDebt_le_survival_mul_terminalDebt
        reward roots who prescribed hprescribed hterminalDebt hresidual
          start fuel)
    hscaled

/-- Nonsummability of the clock from time zero is inherited by every suffix,
so exact finite dynamic debt vanishes from every fixed chronological start. -/
theorem tendsto_zero_quittingFiniteDynamicDebt_of_not_summable_clock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue
      reward roots who prescribed)
    {terminalDebt : ℝ} (hterminalDebt : 0 ≤ terminalDebt)
    (hresidual : ∀ time,
      quittingPrescribedOneStepResidual reward roots who prescribed time = 0)
    (hclock : ¬Summable (quittingOpponentClockCharge roots who)) :
    ∀ start,
      Tendsto
        (fun fuel ↦ quittingFiniteDynamicDebt reward roots who prescribed
          terminalDebt start fuel)
        atTop (nhds 0) := by
  intro start
  apply
    tendsto_zero_quittingFiniteDynamicDebt_of_not_summable_suffixClock
      reward roots who prescribed hprescribed hterminalDebt hresidual start
  intro hsuffix
  have hshift : Summable (fun offset ↦
      quittingOpponentClockCharge roots who (offset + start)) := by
    simpa [Nat.add_comm] using hsuffix
  exact hclock ((summable_nat_add_iff start).1 hshift)

end GameTheory
