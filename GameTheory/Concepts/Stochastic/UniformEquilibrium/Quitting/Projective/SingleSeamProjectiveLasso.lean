/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Projective.WeightedProjectiveLasso
import Math.DivergentChargeRecurrence

/-!
# Single-seam projective lassos

A finite word obtained by reversing an exact forward Bellman segment has a
particularly simple defect: every internal cyclic seam is zero, and only the
closing seam can be nonzero.  Rotation-uniformity is then automatic.  Every
cyclic entry sees that seam exactly once, with a survival prefix at most one.

This file isolates that bookkeeping independently of how the returned block
is produced.  It provides a smaller certificate than
`QuittingFiniteWeightedProjectiveLasso`: one distinguished seam, exact policy
evaluation elsewhere, and a bound on that seam against the aggregate weighted
absorption of the whole word.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A cyclic word with only one nonzero Bellman seam has rotation-uniform
weighted residual bounded by the size of that seam.

The proof does not select a preferred entry phase.  It bounds every survival
prefix by one and uses that the finite cyclic orbit is a permutation of all
phases. -/
theorem quittingCyclicWeightedResidual_le_of_single_seam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (value : Fin K → Payoff ι)
    (closing : Fin K) (seam : ℝ)
    (hzero : ∀ cyclePhase who, cyclePhase ≠ closing →
      quittingCyclicPolicyResidual reward cycle value cyclePhase who = 0)
    (hclosing : ∀ who,
      |quittingCyclicPolicyResidual reward cycle value closing who| ≤ seam)
    (phase : Fin K) (who : ι) :
    quittingCyclicWeightedResidual reward cycle value phase who ≤ seam := by
  classical
  let coefficient : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  let residual : Fin K → ℝ := fun cyclePhase =>
    |quittingCyclicPolicyResidual reward cycle value cyclePhase who|
  have hcoefficient0 : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg (cycle cyclePhase)
  have hcoefficient1 : ∀ cyclePhase, coefficient cyclePhase ≤ 1 :=
    fun cyclePhase => quittingStationaryContinueMass_le_one (cycle cyclePhase)
  have hprefix_le : ∀ offset : ℕ,
      quittingCyclicPrefixWeight coefficient phase offset ≤ 1 := by
    intro offset
    have hmono := antitone_quittingCyclicPrefixWeight
      coefficient hcoefficient0 hcoefficient1 phase
    simpa only [quittingCyclicPrefixWeight_zero] using
      hmono (Nat.zero_le offset)
  have horbit : ∀ offset : Fin K,
      quittingCyclicOrbit phase offset.val = finCycle phase offset := by
    intro offset
    apply Fin.ext
    simp [quittingCyclicOrbit, finCycle_apply, Fin.add_def, Nat.add_comm]
  have hsum : (∑ cyclePhase : Fin K, residual cyclePhase) =
      residual closing := by
    apply Finset.sum_eq_single closing
    · intro cyclePhase _ hne
      simp [residual, hzero cyclePhase who hne]
    · simp
  unfold quittingCyclicWeightedResidual quittingCyclicResidualCharge
  change (∑ offset ∈ Finset.range K,
      quittingCyclicPrefixWeight coefficient phase offset *
        residual (quittingCyclicOrbit phase offset)) ≤ seam
  calc
    (∑ offset ∈ Finset.range K,
        quittingCyclicPrefixWeight coefficient phase offset *
          residual (quittingCyclicOrbit phase offset)) ≤
      ∑ offset ∈ Finset.range K,
        residual (quittingCyclicOrbit phase offset) := by
      apply Finset.sum_le_sum
      intro offset _
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hprefix_le offset)
          (abs_nonneg
            (quittingCyclicPolicyResidual reward cycle value
              (quittingCyclicOrbit phase offset) who))
    _ = ∑ cyclePhase : Fin K, residual cyclePhase := by
      rw [Finset.sum_range]
      simp_rw [horbit]
      exact Equiv.sum_comp (finCycle phase) residual
    _ = residual closing := hsum
    _ ≤ seam := hclosing who

/-- A finite projective lasso whose Bellman defect is concentrated at one
closing phase.  The seam is measured directly against the aggregate
absorption of the whole cycle, so no rotation-indexed hypothesis is needed. -/
structure QuittingFiniteSingleSeamProjectiveLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (error : ℝ) where
  cycle : Fin K → ι → PMF Bool
  value : Fin K → Payoff ι
  closing : Fin K
  error_nonneg : 0 ≤ error
  exact_away : ∀ phase who, phase ≠ closing →
    quittingCyclicPolicyResidual reward cycle value phase who = 0
  closing_bound : ∀ who,
    |quittingCyclicPolicyResidual reward cycle value closing who| ≤
      error * quittingCyclicWeightedAbsorption cycle
  support : ∀ phase,
    IsQuittingRootSupportApproxNash reward
      (value (finRotate K phase)) error (cycle phase)
  rational : ∀ target phase,
    quittingPunishmentValue reward target - error ≤ value phase target
  absorbingPhase : Fin K
  absorbing : 0 < quittingRootAbsorptionMass (cycle absorbingPhase)

namespace QuittingFiniteSingleSeamProjectiveLasso

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℝ}

/-- A single-seam certificate automatically satisfies the canonical
rotation-uniform weighted residual condition. -/
def toWeighted
    (lasso : QuittingFiniteSingleSeamProjectiveLasso reward K error) :
    QuittingFiniteWeightedProjectiveLasso reward K error where
  cycle := lasso.cycle
  value := lasso.value
  error_nonneg := lasso.error_nonneg
  weightedResidual_bound := by
    intro phase who
    exact quittingCyclicWeightedResidual_le_of_single_seam
      reward lasso.cycle lasso.value lasso.closing
        (error * quittingCyclicWeightedAbsorption lasso.cycle)
        lasso.exact_away lasso.closing_bound phase who
  support := lasso.support
  rational := lasso.rational
  absorbingPhase := lasso.absorbingPhase
  absorbing := lasso.absorbing

/-- A single-seam lasso produces the same divergent support-rational path as
the canonical weighted certificate. -/
theorem exists_supportRationalDivergentPath
    (lasso : QuittingFiniteSingleSeamProjectiveLasso reward K error) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan (2 * error) ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - 2 * error ≤
          quittingRootSequenceTerminalValue reward plan target time :=
  lasso.toWeighted.exists_supportRationalDivergentPath

end QuittingFiniteSingleSeamProjectiveLasso

/-- Single-seam projective lassos at every positive accuracy imply a uniform
quitting-game equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_weightedProjectiveLassos
    reward
  intro error herror
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer error herror
  exact ⟨K, ⟨lasso.toWeighted⟩⟩

end GameTheory
