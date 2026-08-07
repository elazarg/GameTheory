/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCycleMismatchContraction
import GameTheory.Concepts.Stochastic.QuittingSupportWitnessPeriodic
import Math.ProjectiveBellmanPacket

/-!
# Charged projective lassos for quitting games

A vanishing-discount branch need not directly produce an exact finite APS
cycle.  In the matching discount/absorption regime it naturally produces a
*projective* cycle: the Bellman seam is smaller than the real absorption
charge, but need not vanish identically.

For a finite root word `cycle`, an approximate cyclic value `value`, and a
phase `p`, define the policy residual

`e_p = value p - F(cycle p, value (next p))`.

The projective condition is

`|e_p(i)| ≤ η * q_p`,

where `q_p` is the one-stage joint absorption probability.  The same survival
weights telescope both the residuals and the absorption hazards.  The
repository's cyclic contraction theorem therefore gives

`|value p i - exactValue p i| ≤ η`

with no factor depending on the period.  Support-local optimality and
punishment rationality are Lipschitz in the continuation coordinate, so the
exact periodically realized cycle has total error `2η`.  The existing
periodic support-witness compiler then produces a divergently absorbing path
and a uniform-equilibrium payoff.

This file proves the complete lasso consumer.  It does **not** assert that
every quitting game supplies such lassos.  The remaining global theorem is a
finite projective pivot-or-output statement for the resolved complementary
Bellman complex; see `docs/uniform-equilibrium/ProjectiveLassoProducer.md`.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Policy-evaluation seam of a proposed cyclic value. -/
def quittingCyclicPolicyResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (phase : Fin K) : Payoff ι :=
  fun who =>
    value phase who -
      quittingRootSuccessorPayoff reward
        (value (finRotate K phase)) (cycle phase) who

/-- One cyclic difference step with an explicit policy residual. -/
theorem quittingCyclicValue_sub_terminalValue_step_with_residual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (who : ι) (phase : Fin K) :
    value phase who -
        quittingCyclicTerminalValue reward cycle phase who =
      quittingCyclicPolicyResidual reward cycle value phase who +
        quittingStationaryContinueMass (cycle phase) *
          (value (finRotate K phase) who -
            quittingCyclicTerminalValue reward cycle
              (finRotate K phase) who) := by
  have hterminal := congrFun
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward cycle phase) who
  calc
    value phase who -
          quittingCyclicTerminalValue reward cycle phase who =
        (value phase who -
          quittingRootSuccessorPayoff reward
            (value (finRotate K phase)) (cycle phase) who) +
        (quittingRootSuccessorPayoff reward
            (value (finRotate K phase)) (cycle phase) who -
          quittingRootSuccessorPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K phase)) (cycle phase) who) := by
          rw [hterminal]
          ring
    _ = quittingCyclicPolicyResidual reward cycle value phase who +
        quittingStationaryContinueMass (cycle phase) *
          (value (finRotate K phase) who -
            quittingCyclicTerminalValue reward cycle
              (finRotate K phase) who) := by
          rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul]
          rfl

/-- Cyclic survival weights telescope exactly against their stage hazards. -/
theorem sum_quittingCyclicPrefixWeight_mul_one_sub
    (coefficient : Fin K → ℝ) (phase : Fin K) :
    ∀ fuel : ℕ,
      (∑ offset ∈ Finset.range fuel,
        quittingCyclicPrefixWeight coefficient phase offset *
          (1 - coefficient (quittingCyclicOrbit phase offset))) =
        1 - quittingCyclicPrefixWeight coefficient phase fuel := by
  intro fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, quittingCyclicPrefixWeight_succ]
      ring

/-- Endpoint differences are `1`-Lipschitz in the player's continuation
coordinate. -/
theorem abs_quittingRootEndpointDifference_sub_le_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    |quittingRootEndpointDifference reward first root who -
        quittingRootEndpointDifference reward second root who| ≤
      |first who - second who| := by
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootContinuePayoff_eq_deleted,
    quittingRootContinuePayoff_eq_deleted]
  have hmass0 := quittingRootDeletedContinueMass_nonneg root who
  have hmass1 := quittingRootDeletedContinueMass_le_one root who
  rw [show
    (quittingRootDeletedQuitValue reward root who -
          (quittingRootDeletedContinueReward reward root who +
            quittingRootDeletedContinueMass root who * first who)) -
        (quittingRootDeletedQuitValue reward root who -
          (quittingRootDeletedContinueReward reward root who +
            quittingRootDeletedContinueMass root who * second who)) =
      quittingRootDeletedContinueMass root who * (second who - first who) by
        ring,
    abs_mul, abs_of_nonneg hmass0]
  calc
    quittingRootDeletedContinueMass root who * |second who - first who| ≤
        1 * |second who - first who| :=
      mul_le_mul_of_nonneg_right hmass1 (abs_nonneg _)
    _ = |first who - second who| := by rw [one_mul, abs_sub_comm]

/-- Support-local optimality survives a uniformly close continuation, with
an additive error. -/
theorem isQuittingRootSupportApproxNash_of_tail_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (approx exact : Payoff ι)
    {δ η : ℝ}
    (hsupport : IsQuittingRootSupportApproxNash reward approx δ root)
    (hclose : ∀ who, |exact who - approx who| ≤ η) :
    IsQuittingRootSupportApproxNash reward exact (δ + η) root := by
  intro who
  have hgapClose :=
    (abs_quittingRootEndpointDifference_sub_le_tail
      reward exact approx root who).trans (hclose who)
  have hgapBounds := abs_le.mp hgapClose
  constructor
  · intro hquit
    have happrox := (hsupport who).1 hquit
    linarith
  · intro hcontinue
    have happrox := (hsupport who).2 hcontinue
    linarith

/-- **Charged residual correction.**  If every cyclic policy residual is at
most `η` times that stage's real absorption charge, then the displayed values
are uniformly within `η` of the exact values selected by periodic repetition.
The bound is independent of the period. -/
theorem abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    {η : ℝ} (hη : 0 ≤ η)
    (hresidual : ∀ phase who,
      |quittingCyclicPolicyResidual reward cycle value phase who| ≤
        η * quittingRootAbsorptionMass (cycle phase))
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
                  (finRotate K cyclePhase) who)| := abs_add _ _
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
  have hcharge :
      quittingCyclicResidualCharge coefficient residual phase K ≤
        η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
    unfold quittingCyclicResidualCharge
    calc
      (∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          residual (quittingCyclicOrbit phase offset)) ≤
          ∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight coefficient phase offset *
              (η * (1 - coefficient
                (quittingCyclicOrbit phase offset))) := by
        apply Finset.sum_le_sum
        intro offset hoffset
        exact mul_le_mul_of_nonneg_left
          (by
            dsimp only [residual, coefficient]
            simpa only [quittingRootAbsorptionMass] using
              hresidual (quittingCyclicOrbit phase offset) who)
          (quittingCyclicPrefixWeight_nonneg
            coefficient hcoefficient phase offset)
      _ = η * (∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight coefficient phase offset *
              (1 - coefficient (quittingCyclicOrbit phase offset))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset hoffset
        ring
      _ = η * (1 - quittingCyclicPrefixWeight coefficient phase K) := by
        rw [sum_quittingCyclicPrefixWeight_mul_one_sub]
      _ = η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
        rw [quittingCyclicPrefixWeight_card]
  have hdenom : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcontract
  have hquotient :
      quittingCyclicResidualCharge coefficient residual phase K /
          (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) ≤ η := by
    rw [div_le_iff₀ hdenom]
    exact hcharge
  exact hraw.trans hquotient

/-- Finite certificate delivered by the projective pivot/recurrence layer.
The Bellman seam is charged relative to *real* one-stage absorption. -/
structure QuittingFiniteChargedProjectiveLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (error : ℝ) where
  cycle : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  error_nonneg : 0 ≤ error
  residual_bound : ∀ phase who,
    |quittingCyclicPolicyResidual reward cycle value phase who| ≤
      error * quittingRootAbsorptionMass (cycle phase)
  support : ∀ phase,
    IsQuittingRootSupportApproxNash reward
      (value (finRotate K phase)) error (cycle phase)
  rational : ∀ target phase,
    quittingPunishmentValue reward target - error ≤ value phase target
  absorbingPhase : Fin K
  absorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)

namespace QuittingFiniteChargedProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- Exact periodic continuation selected by the lasso's root word. -/
def exactValue
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error) :
    Fin K → Payoff ι :=
  quittingCyclicTerminalValue reward lasso.cycle

/-- The charged seam correction costs at most the lasso error. -/
theorem abs_value_sub_exactValue_le
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error)
    (phase : Fin K) (who : ι) :
    |lasso.value phase who - exactValue lasso phase who| ≤ error := by
  exact abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual
    reward lasso.cycle lasso.value lasso.error_nonneg lasso.residual_bound
      lasso.absorbingPhase lasso.absorbing phase who

/-- **Projective lasso correction.**  Replacing the approximate projective
values by the actual periodic values turns the lasso into an exact finite
support-rational cycle at twice the original error. -/
theorem toFiniteSupportRationalCycle
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error) :
    IsQuittingFiniteSupportRationalCycle reward lasso.cycle
      (exactValue lasso) (2 * error) (2 * error) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward lasso.cycle phase
  · intro phase
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (lasso.cycle phase)
        (lasso.value (finRotate K phase))
        (exactValue lasso (finRotate K phase))
        (lasso.support phase) (fun who => ?_)
    · simpa [two_mul] using htransfer
    · simpa [exactValue, abs_sub_comm] using
        abs_value_sub_exactValue_le lasso (finRotate K phase) who
  · intro target phase
    have hir := lasso.rational target phase
    have hclose := abs_value_sub_exactValue_le lasso phase target
    rw [abs_le] at hclose
    dsimp only [exactValue]
    nlinarith

/-- A charged projective lasso produces the exact divergent path consumed by
the support-witness compiler. -/
theorem exists_supportRationalDivergentPath
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan (2 * error) ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - 2 * error ≤
          quittingRootSequenceTerminalValue reward plan target time := by
  exact exists_supportRationalDivergentPath_of_finiteSupportRationalCycle
    reward lasso.cycle (exactValue lasso)
      (toFiniteSupportRationalCycle lasso)
      lasso.absorbingPhase lasso.absorbing

end QuittingFiniteChargedProjectiveLasso

/-- **Uniform-payoff producer interface.**  Charged projective lassos at every
positive accuracy imply a uniform-equilibrium payoff.  The theorem deliberately
leaves the finite projective pivot-or-output construction as an explicit
producer hypothesis. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_chargedProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteChargedProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    reward
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer (δ / 2) hhalf
  obtain ⟨plan, hsupport, hdiverges, hir⟩ :=
    QuittingFiniteChargedProjectiveLasso.exists_supportRationalDivergentPath
      lasso
  have htwo : (2 : ℝ) * (δ / 2) = δ := by ring
  rw [htwo] at hsupport hir
  exact ⟨plan, hsupport, hdiverges, hir⟩

end GameTheory
