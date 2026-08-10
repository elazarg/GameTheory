/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Tail stability for a quitting root

The root is kept as one full product profile.  If a source root is endpoint
`ε`-Nash against a declared target and the target is coordinatewise within
`δ` of the actual continuation vector, the same root is endpoint
`(ε + δ)`-Nash against that actual vector.  The associated successor payoff
also moves by at most `δ` in each coordinate.

This is a quantitative state-matching interface for any quitting root.  It
changes all coordinates simultaneously only through the common tail
perturbation; it does not claim that independently selected fixed-tail roots
form a chronological path.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A source-matched approximate one-stage Nash--Bellman certificate.

`current` is the actual source payoff, while `tail` is the actual successor
continuation.  The first conjunct records the approximate Bellman equation;
the second records endpoint complementarity against that same continuation.
-/
def IsδQuittingRootSuccessorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε δ : ℝ) (root : ι → PMF Bool)
    (current tail : Payoff ι) : Prop :=
  (∀ who, |current who -
      quittingRootSuccessorPayoff reward tail root who| ≤ δ) ∧
    IsεQuittingRootEndpointNash reward tail ε root

omit [DecidableEq ι] in
/-- Tail perturbation changes each endpoint payoff by at most the coordinate
perturbation. -/
theorem abs_quittingRootExpectedPayoff_sub_of_tail_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : |first who - second who| ≤ δ) :
    |quittingRootExpectedPayoff reward first root who -
        quittingRootExpectedPayoff reward second root who| ≤ δ := by
  have hfirst : first who ≤ second who + δ := by
    linarith [abs_le.mp hclose]
  have hsecond : second who ≤ first who + δ := by
    linarith [abs_le.mp hclose]
  have hupper := quittingRootExpectedPayoff_continuation_le_add
    reward first second root who hδ hfirst
  have hlower := quittingRootExpectedPayoff_continuation_le_add
    reward second first root who hδ hsecond
  rw [abs_le]
  constructor <;> linarith

/-- Endpoint differences are `1`-Lipschitz in the player's continuation
coordinate. -/
theorem abs_quittingRootEndpointDifference_sub_le_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    |quittingRootEndpointDifference reward first root who -
        quittingRootEndpointDifference reward second root who| ≤
      |first who - second who| := by
  have hquitMass : quittingStationaryContinueMass
      (Function.update root who (PMF.pure true)) = 0 := by
    apply le_antisymm
    · exact (quittingStationaryContinueMass_le_ownContinueProbability
        (Function.update root who (PMF.pure true)) who).trans (by simp)
    · exact quittingStationaryContinueMass_nonneg _
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    hquitMass]
  let mass := quittingStationaryContinueMass
    (Function.update root who (PMF.pure false))
  have hmass0 : 0 ≤ mass :=
    quittingStationaryContinueMass_nonneg _
  have hmass1 : mass ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  simp only [zero_mul, add_zero]
  change
    |(quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure true)) who -
        (quittingRootAbsorbingContribution reward
            (Function.update root who (PMF.pure false)) who +
          mass * first who)) -
      (quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure true)) who -
        (quittingRootAbsorbingContribution reward
            (Function.update root who (PMF.pure false)) who +
          mass * second who))| ≤ |first who - second who|
  rw [show
    (quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure true)) who -
        (quittingRootAbsorbingContribution reward
            (Function.update root who (PMF.pure false)) who +
          mass * first who)) -
      (quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure true)) who -
        (quittingRootAbsorbingContribution reward
            (Function.update root who (PMF.pure false)) who +
          mass * second who)) =
      mass * (second who - first who) by
        ring,
    abs_mul, abs_of_nonneg hmass0]
  calc
    mass * |second who - first who| ≤
        1 * |second who - first who| :=
      mul_le_mul_of_nonneg_right hmass1 (abs_nonneg _)
    _ = |first who - second who| := by rw [one_mul, abs_sub_comm]

/-- A fixed root transfers from a declared target to a nearby actual tail.
The theorem is full-vector: no coordinate is updated independently and no
source marginal is discarded. -/
theorem isεQuittingRootEndpointNash_of_tail_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target tail : Payoff ι) (root : ι → PMF Bool)
    {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hroot : IsεQuittingRootEndpointNash reward target ε root)
    (hclose : ∀ who, |target who - tail who| ≤ δ) :
    IsεQuittingRootEndpointNash reward tail (ε + δ) root := by
  intro who
  have hgap :=
    (abs_quittingRootEndpointDifference_sub_le_tail
      reward tail target root who).trans (by
        simpa [abs_sub_comm] using hclose who)
  have hgapBounds := abs_le.mp hgap
  have hsource := hroot who
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hcontinueLe : (root who false).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one false)
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hquitLe : (root who true).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  constructor
  · nlinarith [hsource.1]
  · nlinarith [hsource.2]

/-- Full-vector source matching is obtained from a target match and the
original successor equation.  The displayed source payoff is allowed to be
an actual conditioned value; the result records exactly the residual
Bellman error and the transferred endpoint tolerance.
-/
theorem isδQuittingRootSuccessorCertificate_of_target_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current target tail : Payoff ι) (root : ι → PMF Bool)
    {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hsource : ∀ who,
      |current who - quittingRootSuccessorPayoff reward target root who| ≤ δ)
    (hroot : IsεQuittingRootEndpointNash reward target ε root)
    (hclose : ∀ who, |target who - tail who| ≤ δ) :
    IsδQuittingRootSuccessorCertificate reward (ε + δ) (2 * δ)
      root current tail := by
  refine ⟨?_, isεQuittingRootEndpointNash_of_tail_close
    reward target tail root hδ hroot hclose⟩
  intro who
  have htail := abs_quittingRootExpectedPayoff_sub_of_tail_close
    reward target tail root who hδ (hclose who)
  have hroot := hsource who
  calc
    |current who - quittingRootSuccessorPayoff reward tail root who| ≤
        |current who - quittingRootSuccessorPayoff reward target root who| +
          |quittingRootSuccessorPayoff reward target root who -
            quittingRootSuccessorPayoff reward tail root who| :=
      abs_sub_le _ _ _
    _ ≤ δ + δ := add_le_add (hroot) htail
    _ = 2 * δ := by ring

end GameTheory
