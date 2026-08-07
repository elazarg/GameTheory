/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingProjectiveLasso

/-!
# Weighted cyclewise projective-lasso seams

The invariant lasso condition is cyclewise.  If `s_k` is survival before
phase `k`, `e_k` is the Bellman seam and `q_k = 1-c_k` is real absorption,
the exact correction estimate reads

`|value - exactValue| ≤ (∑ k, s_k |e_k|) / (∑ k, s_k q_k)`.

Thus the natural finite certificate is

`∑ k, s_k |e_k| ≤ η * ∑ k, s_k q_k`.

This formulation handles zero-charge phases and unequal phase scales without
omitting any seam.  The pointwise condition used by
`QuittingFiniteChargedProjectiveLasso`, `|e_k| ≤ η q_k`, is a stronger,
easy-to-check sufficient condition: in particular it forces `e_k = 0` when
`q_k = 0`.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Survival-weighted absolute seam around one turn of a cyclic word. -/
def quittingCyclicWeightedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) : ℝ :=
  quittingCyclicResidualCharge
    (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
    (fun cyclePhase =>
      |quittingCyclicPolicyResidual reward cycle value cyclePhase who|)
    phase K

/-- Total survival-weighted real absorption around one turn. -/
def quittingCyclicWeightedAbsorption
    (cycle : Fin K → ι → PMF Bool) : ℝ :=
  1 - ∏ cyclePhase : Fin K,
    quittingStationaryContinueMass (cycle cyclePhase)

/-- The weighted absorption denominator is the sum of preceding survival times
one-stage absorption. -/
theorem quittingCyclicWeightedAbsorption_eq_sum
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K) :
    quittingCyclicWeightedAbsorption cycle =
      ∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight
          (fun cyclePhase =>
            quittingStationaryContinueMass (cycle cyclePhase))
          phase offset *
        quittingRootAbsorptionMass
          (cycle (quittingCyclicOrbit phase offset)) := by
  unfold quittingCyclicWeightedAbsorption
  rw [← quittingCyclicPrefixWeight_card
    (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase)) phase]
  rw [← sum_quittingCyclicPrefixWeight_mul_one_sub]
  apply Finset.sum_congr rfl
  intro offset _
  rw [quittingRootAbsorptionMass]

/-- **Weighted projective-lasso correction.**  A cyclewise seam bound against
the equally weighted absorption charge controls the exact periodic correction
with the same constant. -/
theorem abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {η : ℝ}
    (hweighted : ∀ phase who,
      quittingCyclicWeightedResidual reward cycle value phase who ≤
        η * quittingCyclicWeightedAbsorption cycle)
    (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    ∀ phase who,
      |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| ≤ η := by
  intro phase who
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  let residual : Fin K → ℝ := fun cyclePhase =>
    |quittingCyclicPolicyResidual reward cycle value cyclePhase who|
  let difference : Fin K → ℝ := fun cyclePhase =>
    value cyclePhase who -
      quittingCyclicTerminalValue reward cycle cyclePhase who
  have hcoefficient : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg (cycle cyclePhase)
  have hcontract : (∏ cyclePhase : Fin K, coefficient cyclePhase) < 1 := by
    simpa only [coefficient] using
      prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
        cycle absorbingPhase habsorbing
  have hstep : ∀ cyclePhase,
      |difference cyclePhase| ≤ residual cyclePhase +
        coefficient cyclePhase *
          |difference (finRotate K cyclePhase)| := by
    intro cyclePhase
    have heq :=
      quittingCyclicValue_sub_terminalValue_step_with_residual
        reward cycle value who cyclePhase
    dsimp only [difference, residual, coefficient]
    rw [heq]
    calc
      |quittingCyclicPolicyResidual reward cycle value cyclePhase who +
          quittingStationaryContinueMass (cycle cyclePhase) *
            (value (finRotate K cyclePhase) who -
              quittingCyclicTerminalValue reward cycle
                (finRotate K cyclePhase) who)| ≤
          |quittingCyclicPolicyResidual reward cycle value cyclePhase who| +
            |quittingStationaryContinueMass (cycle cyclePhase) *
              (value (finRotate K cyclePhase) who -
                quittingCyclicTerminalValue reward cycle
                  (finRotate K cyclePhase) who)| := abs_add_le _ _
      _ = |quittingCyclicPolicyResidual reward cycle value cyclePhase who| +
          quittingStationaryContinueMass (cycle cyclePhase) *
            |value (finRotate K cyclePhase) who -
              quittingCyclicTerminalValue reward cycle
                (finRotate K cyclePhase) who| := by
        rw [abs_mul, abs_of_nonneg
          (quittingStationaryContinueMass_nonneg (cycle cyclePhase))]
  have hraw :=
    abs_cyclicValue_le_residualCharge_div_one_sub_prod
      coefficient residual difference hcoefficient hcontract hstep phase
  have hdenom : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcontract
  have hcharge :
      quittingCyclicResidualCharge coefficient residual phase K ≤
        η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
    simpa only [quittingCyclicWeightedResidual,
      quittingCyclicWeightedAbsorption, coefficient, residual] using
      hweighted phase who
  have hquotient :
      quittingCyclicResidualCharge coefficient residual phase K /
          (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) ≤ η := by
    rw [div_le_iff₀ hdenom]
    exact hcharge
  exact hraw.trans hquotient

/-- The stronger pointwise charged-seam condition implies the invariant
weighted condition. -/
theorem quittingCyclicWeightedResidual_le_of_pointwise
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {η : ℝ}
    (hpointwise : ∀ phase who,
      |quittingCyclicPolicyResidual reward cycle value phase who| ≤
        η * quittingRootAbsorptionMass (cycle phase))
    (phase : Fin K) (who : ι) :
    quittingCyclicWeightedResidual reward cycle value phase who ≤
      η * quittingCyclicWeightedAbsorption cycle := by
  unfold quittingCyclicWeightedResidual
  calc
    quittingCyclicResidualCharge
        (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
        (fun cyclePhase =>
          |quittingCyclicPolicyResidual reward cycle value cyclePhase who|)
        phase K ≤
      ∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight
          (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
          phase offset *
        (η * quittingRootAbsorptionMass
          (cycle (quittingCyclicOrbit phase offset))) := by
      apply Finset.sum_le_sum
      intro offset _
      exact mul_le_mul_of_nonneg_left
        (hpointwise (quittingCyclicOrbit phase offset) who)
        (quittingCyclicPrefixWeight_nonneg
          (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
          (fun cyclePhase =>
            quittingStationaryContinueMass_nonneg (cycle cyclePhase))
          phase offset)
    _ = η * quittingCyclicWeightedAbsorption cycle := by
      rw [show
        (∑ offset ∈ Finset.range K,
          quittingCyclicPrefixWeight
            (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
            phase offset *
          (η * quittingRootAbsorptionMass
            (cycle (quittingCyclicOrbit phase offset)))) =
          η * ∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight
              (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
              phase offset *
            quittingRootAbsorptionMass
              (cycle (quittingCyclicOrbit phase offset)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring]
      rw [← quittingCyclicWeightedAbsorption_eq_sum cycle phase]

end GameTheory
