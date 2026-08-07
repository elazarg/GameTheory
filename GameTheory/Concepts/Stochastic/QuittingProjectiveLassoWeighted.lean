/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingProjectiveLasso

/-!
# Signed and absolute cyclewise projective-lasso seams

The exact cyclic policy-evaluation recurrence retains the sign of every
Bellman seam.  If `s_k` is survival before phase `k`, `e_k` is the signed seam,
and `ρ` is survival around one full turn, then

`(1 - ρ) * (value - exactValue) = ∑ k, s_k * e_k`.

Thus the weakest finite correction certificate controls the absolute value of
the **signed monodromy charge** against the weighted absorption `1 - ρ`.
Cancellation within each rotated turn is valid; checking every cyclic entry
phase remains load-bearing.

The older absolute certificate

`∑ k, s_k * |e_k| ≤ η * (1 - ρ)`

is a stronger sufficient condition by the triangle inequality.  The pointwise
condition used by `QuittingFiniteChargedProjectiveLasso`,
`|e_k| ≤ η q_k`, is stronger still.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact finite unrolling of an affine recurrence along a cyclic orbit. -/
theorem quittingCyclicDifference_eq_residualCharge_add_prefixWeight_mul
    (coefficient residual difference : Fin K → ℝ)
    (hstep : ∀ cyclePhase,
      difference cyclePhase =
        residual cyclePhase + coefficient cyclePhase *
          difference (finRotate K cyclePhase))
    (phase : Fin K) :
    ∀ fuel : ℕ,
      difference phase =
        quittingCyclicResidualCharge coefficient residual phase fuel +
          quittingCyclicPrefixWeight coefficient phase fuel *
            difference (quittingCyclicOrbit phase fuel) := by
  intro fuel
  induction fuel with
  | zero => simp [quittingCyclicResidualCharge]
  | succ fuel ih =>
      rw [ih, hstep (quittingCyclicOrbit phase fuel)]
      unfold quittingCyclicResidualCharge
      rw [Finset.sum_range_succ, quittingCyclicPrefixWeight_succ,
        quittingCyclicOrbit_succ]
      ring

/-- Exact one-turn monodromy identity for a cyclic affine recurrence. -/
theorem one_sub_prod_mul_quittingCyclicDifference_eq_residualCharge
    (coefficient residual difference : Fin K → ℝ)
    (hstep : ∀ cyclePhase,
      difference cyclePhase =
        residual cyclePhase + coefficient cyclePhase *
          difference (finRotate K cyclePhase))
    (phase : Fin K) :
    (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) * difference phase =
      quittingCyclicResidualCharge coefficient residual phase K := by
  have hturn :=
    quittingCyclicDifference_eq_residualCharge_add_prefixWeight_mul
      coefficient residual difference hstep phase K
  rw [quittingCyclicPrefixWeight_card, quittingCyclicOrbit_card] at hturn
  calc
    (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) * difference phase =
        difference phase -
          (∏ cyclePhase : Fin K, coefficient cyclePhase) * difference phase := by
      ring
    _ = quittingCyclicResidualCharge coefficient residual phase K := by
      linarith

/-- Survival-weighted signed seam around one turn of a cyclic word. -/
def quittingCyclicSignedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) : ℝ :=
  quittingCyclicResidualCharge
    (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase))
    (fun cyclePhase =>
      quittingCyclicPolicyResidual reward cycle value cyclePhase who)
    phase K

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

omit [DecidableEq ι] in
/-- The exact signed Bellman monodromy is weighted absorption times the
cyclic-value correction. -/
theorem
    quittingCyclicWeightedAbsorption_mul_value_sub_terminalValue_eq_signedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) :
    quittingCyclicWeightedAbsorption cycle *
        (value phase who -
          quittingCyclicTerminalValue reward cycle phase who) =
      quittingCyclicSignedResidual reward cycle value phase who := by
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  let residual : Fin K → ℝ := fun cyclePhase =>
    quittingCyclicPolicyResidual reward cycle value cyclePhase who
  let difference : Fin K → ℝ := fun cyclePhase =>
    value cyclePhase who -
      quittingCyclicTerminalValue reward cycle cyclePhase who
  have hstep : ∀ cyclePhase,
      difference cyclePhase = residual cyclePhase +
        coefficient cyclePhase * difference (finRotate K cyclePhase) := by
    intro cyclePhase
    simpa only [difference, residual, coefficient] using
      quittingCyclicValue_sub_terminalValue_step_with_residual
        reward cycle value who cyclePhase
  simpa only [quittingCyclicWeightedAbsorption,
    quittingCyclicSignedResidual, coefficient, residual, difference] using
    one_sub_prod_mul_quittingCyclicDifference_eq_residualCharge
      coefficient residual difference hstep phase

omit [DecidableEq ι] in
/-- A positive-absorption phase makes the aggregate weighted absorption
strictly positive. -/
theorem quittingCyclicWeightedAbsorption_pos_of_absorbingPhase
    (cycle : Fin K → ι → PMF Bool) (absorbingPhase : Fin K)
    (habsorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)) :
    0 < quittingCyclicWeightedAbsorption cycle := by
  unfold quittingCyclicWeightedAbsorption
  exact sub_pos.mpr
    (prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
      cycle absorbingPhase habsorbing)

omit [DecidableEq ι] in
/-- Under positive aggregate absorption, the exact cyclic correction is the
signed monodromy charge divided by that absorption. -/
theorem quittingCyclicValue_sub_terminalValue_eq_signedResidual_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (habsorption : 0 < quittingCyclicWeightedAbsorption cycle)
    (phase : Fin K) (who : ι) :
    value phase who - quittingCyclicTerminalValue reward cycle phase who =
      quittingCyclicSignedResidual reward cycle value phase who /
        quittingCyclicWeightedAbsorption cycle := by
  apply (eq_div_iff (ne_of_gt habsorption)).2
  simpa only [mul_comm] using
    quittingCyclicWeightedAbsorption_mul_value_sub_terminalValue_eq_signedResidual
      reward cycle value phase who

omit [DecidableEq ι] in
/-- The signed monodromy charge is bounded by the survival-weighted absolute
seam. -/
theorem abs_quittingCyclicSignedResidual_le_weightedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) (who : ι) :
    |quittingCyclicSignedResidual reward cycle value phase who| ≤
      quittingCyclicWeightedResidual reward cycle value phase who := by
  classical
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  let residual : Fin K → ℝ := fun cyclePhase =>
    quittingCyclicPolicyResidual reward cycle value cyclePhase who
  have hcoefficient : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg (cycle cyclePhase)
  change
    |quittingCyclicResidualCharge coefficient residual phase K| ≤
      quittingCyclicResidualCharge coefficient
        (fun cyclePhase => |residual cyclePhase|) phase K
  unfold quittingCyclicResidualCharge
  calc
    |∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          residual (quittingCyclicOrbit phase offset)| ≤
      ∑ offset ∈ Finset.range K,
        |quittingCyclicPrefixWeight coefficient phase offset *
          residual (quittingCyclicOrbit phase offset)| :=
      Finset.abs_sum_le_sum_abs
        (fun offset =>
          quittingCyclicPrefixWeight coefficient phase offset *
            residual (quittingCyclicOrbit phase offset))
        (Finset.range K)
    _ = ∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          |residual (quittingCyclicOrbit phase offset)| := by
      apply Finset.sum_congr rfl
      intro offset _
      rw [abs_mul, abs_of_nonneg
        (quittingCyclicPrefixWeight_nonneg coefficient hcoefficient
          phase offset)]

omit [DecidableEq ι] in
/-- **Signed projective-lasso correction.**  A rotation-uniform bound on the
net signed seam around each turn controls the exact periodic correction with
the same constant. -/
theorem abs_quittingCyclicValue_sub_terminalValue_le_of_signedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {η : ℝ}
    (hsigned : ∀ phase who,
      |quittingCyclicSignedResidual reward cycle value phase who| ≤
        η * quittingCyclicWeightedAbsorption cycle)
    (habsorption : 0 < quittingCyclicWeightedAbsorption cycle) :
    ∀ phase who,
      |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| ≤ η := by
  intro phase who
  rw [quittingCyclicValue_sub_terminalValue_eq_signedResidual_div
    reward cycle value habsorption phase who, abs_div,
    abs_of_pos habsorption]
  exact (div_le_iff₀ habsorption).2 (hsigned phase who)

omit [DecidableEq ι] in
/-- The absolute weighted certificate implies the signed certificate, so it
also controls the cyclic correction under positive aggregate absorption. -/
theorem
    abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual_of_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {η : ℝ}
    (hweighted : ∀ phase who,
      quittingCyclicWeightedResidual reward cycle value phase who ≤
        η * quittingCyclicWeightedAbsorption cycle)
    (habsorption : 0 < quittingCyclicWeightedAbsorption cycle) :
    ∀ phase who,
      |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| ≤ η := by
  apply abs_quittingCyclicValue_sub_terminalValue_le_of_signedResidual
    reward cycle value
  · intro phase who
    exact (abs_quittingCyclicSignedResidual_le_weightedResidual
      reward cycle value phase who).trans (hweighted phase who)
  · exact habsorption

omit [DecidableEq ι] in
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
  classical
  unfold quittingCyclicWeightedAbsorption
  rw [← quittingCyclicPrefixWeight_card
    (fun cyclePhase => quittingStationaryContinueMass (cycle cyclePhase)) phase]
  rw [← sum_quittingCyclicPrefixWeight_mul_one_sub]
  apply Finset.sum_congr rfl
  intro offset _
  rw [quittingRootAbsorptionMass]

omit [DecidableEq ι] in
/-- **Weighted projective-lasso correction.**  A cyclewise absolute seam bound
against the equally weighted absorption charge controls the exact periodic
correction with the same constant. -/
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
  exact
    abs_quittingCyclicValue_sub_terminalValue_le_of_weightedResidual_of_pos
      reward cycle value hweighted
      (quittingCyclicWeightedAbsorption_pos_of_absorbingPhase
        cycle absorbingPhase habsorbing)

omit [DecidableEq ι] in
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
  classical
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
