/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

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

where `q_p` is the one-stage joint absorption probability.  The key identity
is that the same survival weights telescope both the residuals and the
absorption hazards.  If `u` is the exact terminal value of the periodically
repeated root word and `C` is its one-period joint survival, then

`(1 - C) * (value p - u p)
  = sum_k precedingSurvival_k * e_k`,

while

`1 - C = sum_k precedingSurvival_k * q_k`.

Consequently `|value p - u p| ≤ η`, with no factor depending on the period.
Support-local optimality and punishment rationality are Lipschitz in the
continuation coordinate, so replacing the approximate values by the exact
periodic values costs only one additional `η`.  A charged lasso at error `η`
therefore becomes an exact finite support-rational cycle at error `2η`; the
existing periodic support-witness compiler then produces a divergent
absorption path and a uniform-equilibrium payoff.

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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- Residual telescope around a cyclic word. -/
theorem quittingCyclicValue_sub_terminalValue_eq_sum_residual_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (who : ι) (phase : Fin K) :
    ∀ fuel : ℕ,
      value phase who -
          quittingCyclicTerminalValue reward cycle phase who =
        (∑ offset in Finset.range fuel,
          quittingCyclicPrefixWeight
              (fun cyclePhase =>
                quittingStationaryContinueMass (cycle cyclePhase))
              phase offset *
            quittingCyclicPolicyResidual reward cycle value
              (quittingCyclicOrbit phase offset) who) +
          quittingCyclicPrefixWeight
              (fun cyclePhase =>
                quittingStationaryContinueMass (cycle cyclePhase))
              phase fuel *
            (value (quittingCyclicOrbit phase fuel) who -
              quittingCyclicTerminalValue reward cycle
                (quittingCyclicOrbit phase fuel) who) := by
  intro fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hstep :=
        quittingCyclicValue_sub_terminalValue_step_with_residual
          reward cycle value who (quittingCyclicOrbit phase fuel)
      calc
        value phase who -
              quittingCyclicTerminalValue reward cycle phase who =
            (∑ offset in Finset.range fuel,
              quittingCyclicPrefixWeight
                  (fun cyclePhase =>
                    quittingStationaryContinueMass (cycle cyclePhase))
                  phase offset *
                quittingCyclicPolicyResidual reward cycle value
                  (quittingCyclicOrbit phase offset) who) +
              quittingCyclicPrefixWeight
                  (fun cyclePhase =>
                    quittingStationaryContinueMass (cycle cyclePhase))
                  phase fuel *
                (value (quittingCyclicOrbit phase fuel) who -
                  quittingCyclicTerminalValue reward cycle
                    (quittingCyclicOrbit phase fuel) who) := ih
        _ = (∑ offset in Finset.range (fuel + 1),
              quittingCyclicPrefixWeight
                  (fun cyclePhase =>
                    quittingStationaryContinueMass (cycle cyclePhase))
                  phase offset *
                quittingCyclicPolicyResidual reward cycle value
                  (quittingCyclicOrbit phase offset) who) +
              quittingCyclicPrefixWeight
                  (fun cyclePhase =>
                    quittingStationaryContinueMass (cycle cyclePhase))
                  phase (fuel + 1) *
                (value (quittingCyclicOrbit phase (fuel + 1)) who -
                  quittingCyclicTerminalValue reward cycle
                    (quittingCyclicOrbit phase (fuel + 1)) who) := by
          rw [Finset.sum_range_succ, quittingCyclicPrefixWeight_succ,
            quittingCyclicOrbit_succ, hstep]
          ring

omit [DecidableEq ι] in
/-- Cyclic survival weights telescope exactly against their stage hazards. -/
theorem sum_quittingCyclicPrefixWeight_mul_one_sub
    (coefficient : Fin K → ℝ) (phase : Fin K) :
    ∀ fuel : ℕ,
      (∑ offset in Finset.range fuel,
        quittingCyclicPrefixWeight coefficient phase offset *
          (1 - coefficient (quittingCyclicOrbit phase offset))) =
        1 - quittingCyclicPrefixWeight coefficient phase fuel := by
  intro fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, quittingCyclicPrefixWeight_succ]
      ring

omit [DecidableEq ι] in
/-- Prefix weights are nonnegative when all one-stage coefficients are. -/
theorem quittingCyclicPrefixWeight_nonneg_of_nonneg
    (coefficient : Fin K → ℝ) (hcoefficient : ∀ phase, 0 ≤ coefficient phase)
    (phase : Fin K) (fuel : ℕ) :
    0 ≤ quittingCyclicPrefixWeight coefficient phase fuel := by
  unfold quittingCyclicPrefixWeight
  exact Finset.prod_nonneg fun offset _ =>
    hcoefficient (quittingCyclicOrbit phase offset)

/-- Triangle inequality for a finite range sum, kept local so the lasso proof
does not depend on a particular `Finset` lemma name. -/
theorem abs_sum_range_le_sum_range_abs (f : ℕ → ℝ) :
    ∀ fuel : ℕ,
      |∑ offset in Finset.range fuel, f offset| ≤
        ∑ offset in Finset.range fuel, |f offset| := by
  intro fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (abs_add _ _).trans (add_le_add ih le_rfl)

omit [DecidableEq ι] in
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
  have hcoefficient : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg (cycle cyclePhase)
  have hcontract : (∏ cyclePhase : Fin K, coefficient cyclePhase) < 1 := by
    simpa only [coefficient] using
      prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
        cycle absorbingPhase habsorbing
  have htel :=
    quittingCyclicValue_sub_terminalValue_eq_sum_residual_add
      reward cycle value who phase K
  rw [quittingCyclicPrefixWeight_card, quittingCyclicOrbit_card] at htel
  change
    value phase who - quittingCyclicTerminalValue reward cycle phase who =
      (∑ offset in Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          quittingCyclicPolicyResidual reward cycle value
            (quittingCyclicOrbit phase offset) who) +
        (∏ cyclePhase : Fin K, coefficient cyclePhase) *
          (value phase who -
            quittingCyclicTerminalValue reward cycle phase who) at htel
  have hweight : ∀ offset,
      0 ≤ quittingCyclicPrefixWeight coefficient phase offset :=
    fun offset => quittingCyclicPrefixWeight_nonneg_of_nonneg
      coefficient hcoefficient phase offset
  have hresidual' : ∀ offset,
      |quittingCyclicPolicyResidual reward cycle value
          (quittingCyclicOrbit phase offset) who| ≤
        η * (1 - coefficient (quittingCyclicOrbit phase offset)) := by
    intro offset
    simpa only [coefficient, quittingRootAbsorptionMass] using
      hresidual (quittingCyclicOrbit phase offset) who
  have hsum :
      |∑ offset in Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          quittingCyclicPolicyResidual reward cycle value
            (quittingCyclicOrbit phase offset) who| ≤
        η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
    calc
      |∑ offset in Finset.range K,
          quittingCyclicPrefixWeight coefficient phase offset *
            quittingCyclicPolicyResidual reward cycle value
              (quittingCyclicOrbit phase offset) who| ≤
          ∑ offset in Finset.range K,
            |quittingCyclicPrefixWeight coefficient phase offset *
              quittingCyclicPolicyResidual reward cycle value
                (quittingCyclicOrbit phase offset) who| :=
        abs_sum_range_le_sum_range_abs _ K
      _ = ∑ offset in Finset.range K,
            quittingCyclicPrefixWeight coefficient phase offset *
              |quittingCyclicPolicyResidual reward cycle value
                (quittingCyclicOrbit phase offset) who| := by
        apply Finset.sum_congr rfl
        intro offset _
        rw [abs_mul, abs_of_nonneg (hweight offset)]
      _ ≤ ∑ offset in Finset.range K,
            quittingCyclicPrefixWeight coefficient phase offset *
              (η * (1 - coefficient
                (quittingCyclicOrbit phase offset))) := by
        apply Finset.sum_le_sum
        intro offset _
        exact mul_le_mul_of_nonneg_left (hresidual' offset) (hweight offset)
      _ = η * (∑ offset in Finset.range K,
            quittingCyclicPrefixWeight coefficient phase offset *
              (1 - coefficient (quittingCyclicOrbit phase offset))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
      _ = η * (1 - quittingCyclicPrefixWeight coefficient phase K) := by
        rw [sum_quittingCyclicPrefixWeight_mul_one_sub]
      _ = η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
        rw [quittingCyclicPrefixWeight_card]
  have hfactor :
      (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) *
          (value phase who -
            quittingCyclicTerminalValue reward cycle phase who) =
        ∑ offset in Finset.range K,
          quittingCyclicPrefixWeight coefficient phase offset *
            quittingCyclicPolicyResidual reward cycle value
              (quittingCyclicOrbit phase offset) who := by
    calc
      (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) *
            (value phase who -
              quittingCyclicTerminalValue reward cycle phase who) =
          (value phase who -
              quittingCyclicTerminalValue reward cycle phase who) -
            (∏ cyclePhase : Fin K, coefficient cyclePhase) *
              (value phase who -
                quittingCyclicTerminalValue reward cycle phase who) := by ring
      _ = ∑ offset in Finset.range K,
          quittingCyclicPrefixWeight coefficient phase offset *
            quittingCyclicPolicyResidual reward cycle value
              (quittingCyclicOrbit phase offset) who := by
        linarith [htel]
  have hmul :
      |(1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) *
          (value phase who -
            quittingCyclicTerminalValue reward cycle phase who)| ≤
        η * (1 - ∏ cyclePhase : Fin K, coefficient cyclePhase) := by
    rw [hfactor]
    exact hsum
  have hpositive : 0 < 1 - ∏ cyclePhase : Fin K, coefficient cyclePhase :=
    sub_pos.mpr hcontract
  rw [abs_mul, abs_of_pos hpositive] at hmul
  nlinarith

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
/-- The charged seam correction costs at most the lasso error. -/
theorem abs_value_sub_exactValue_le
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error)
    (phase : Fin K) (who : ι) :
    |lasso.value phase who - lasso.exactValue phase who| ≤ error := by
  exact abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual
    reward lasso.cycle lasso.value lasso.error_nonneg lasso.residual_bound
      lasso.absorbingPhase lasso.absorbing phase who

omit [DecidableEq ι] in
/-- **Projective lasso correction.**  Replacing the approximate projective
values by the actual periodic values turns the lasso into an exact finite
support-rational cycle at twice the original error. -/
theorem toFiniteSupportRationalCycle
    (lasso : QuittingFiniteChargedProjectiveLasso reward K error) :
    IsQuittingFiniteSupportRationalCycle reward lasso.cycle lasso.exactValue
      (2 * error) (2 * error) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phase
    exact quittingCyclicTerminalValue_eq_rootSuccessorPayoff
      reward lasso.cycle phase
  · intro phase
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (lasso.cycle phase)
        (lasso.value (finRotate K phase))
        (lasso.exactValue (finRotate K phase))
        (lasso.support phase) (fun who => ?_)
    · simpa [two_mul] using htransfer
    · simpa [exactValue, abs_sub_comm] using
        lasso.abs_value_sub_exactValue_le (finRotate K phase) who
  · intro target phase
    have hir := lasso.rational target phase
    have hclose := lasso.abs_value_sub_exactValue_le phase target
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
    reward lasso.cycle lasso.exactValue lasso.toFiniteSupportRationalCycle
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
      ∃ K : ℕ, QuittingFiniteChargedProjectiveLasso reward K error) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    reward
  intro δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨K, lasso⟩ := hproducer (δ / 2) hhalf
  obtain ⟨plan, hsupport, hdiverges, hir⟩ :=
    lasso.exists_supportRationalDivergentPath
  have htwo : (2 : ℝ) * (δ / 2) = δ := by ring
  rw [htwo] at hsupport hir
  exact ⟨plan, hsupport, hdiverges, hir⟩

end GameTheory
