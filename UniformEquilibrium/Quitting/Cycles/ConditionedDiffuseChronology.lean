/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.EssentialAPS.Basic

/-!
# The diffuse conditioned quitting chronology

Conditioning a positive-survival quitting tail on eventual absorption keeps
the exact order of its states but generally destroys the product form of a
row.  In the diffuse branch the conditioned one-stage absorption weights tend
to zero.  This file records what that hypothesis gives without a strategic
purification assumption.

* physical absorption is bounded by conditioned absorption;
* conditional collision is quadratic in the conditioned mesh;
* the conditioned continuation clock telescopes exactly and is complete when
  the remaining eventual-absorption mass vanishes on late tails;
* active-face errors therefore vanish along every diffuse active subsequence;
* conditioning preserves a payoff floor exactly on tight boundary
  coordinates, while on a strict boundary coordinate it has an explicit
  additional viability inequality.

The last distinction is load-bearing.  Diffuse collision removal and active
pinning do not by themselves produce an essential-APS path: a strict boundary
slack can subsidize a conditionally nonviable coordinate.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [DecidableEq ι] in
/-- Remaining eventual absorption is a probability. -/
theorem quittingTailEventualAbsorption_mem_unitInterval
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    quittingTailEventualAbsorption roots time ∈ Set.Icc 0 1 := by
  have hlimitNonneg := quittingJointSurvivalLimit_nonneg roots time
  have hlimitLe : quittingJointSurvivalLimit roots time ≤ 1 :=
    le_of_tendsto' (tendsto_quittingJointSurvivalLimit roots time)
      (fun fuel ↦ quittingJointSurvivalWeight_le_one roots time fuel)
  exact ⟨by
    unfold quittingTailEventualAbsorption
    linarith, by
    unfold quittingTailEventualAbsorption
    linarith⟩

omit [DecidableEq ι] in
/-- Physical one-stage absorption is no larger than its share of all
eventual absorption still present in the tail. -/
theorem quittingRootAbsorptionMass_le_conditionedAbsorptionWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootAbsorptionMass (roots time) ≤
      quittingTailConditionedAbsorptionWeight roots time := by
  unfold quittingTailConditionedAbsorptionWeight
  have habsorption := quittingRootAbsorptionMass_nonneg (roots time)
  have heventual :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  apply (le_div_iff₀ hpositive).2
  nlinarith

/-- Collision mass at a conditioned row, normalized by the remaining
eventual-absorption scale. -/
def quittingTailConditionedCollisionWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingRootCollisionMass (roots time) /
    quittingTailEventualAbsorption roots time

/-- **Diffuse collision estimate.**  Conditional collision is at most the
number of player pairs times physical absorption times conditioned
absorption.  In particular it is quadratic in the conditioned mesh. -/
theorem quittingTailConditionedCollisionWeight_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedCollisionWeight roots time ≤
      (Fintype.card ι).choose 2 *
        quittingRootAbsorptionMass (roots time) *
          quittingTailConditionedAbsorptionWeight roots time := by
  have hcollision :=
    quittingRootCollisionMass_le_choose_card_mul_absorption_sq
      (roots time)
  unfold quittingTailConditionedCollisionWeight
    quittingTailConditionedAbsorptionWeight
  apply (div_le_iff₀ hpositive).2
  calc
    quittingRootCollisionMass (roots time) ≤
        (Fintype.card ι).choose 2 *
          quittingRootAbsorptionMass (roots time) ^ 2 := hcollision
    _ = ((Fintype.card ι).choose 2 *
          quittingRootAbsorptionMass (roots time) *
            (quittingRootAbsorptionMass (roots time) /
              quittingTailEventualAbsorption roots time)) *
          quittingTailEventualAbsorption roots time := by
      field_simp [hpositive.ne']

/-- The convenient pure-mesh consequence of the diffuse collision estimate. -/
theorem quittingTailConditionedCollisionWeight_le_mesh_sq
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedCollisionWeight roots time ≤
      (Fintype.card ι).choose 2 *
        quittingTailConditionedAbsorptionWeight roots time ^ 2 := by
  have hphysical :=
    quittingRootAbsorptionMass_le_conditionedAbsorptionWeight
      roots time hpositive
  have hweight := quittingTailConditionedAbsorptionWeight_nonneg
    roots time hpositive
  calc
    quittingTailConditionedCollisionWeight roots time ≤
        (Fintype.card ι).choose 2 *
          quittingRootAbsorptionMass (roots time) *
            quittingTailConditionedAbsorptionWeight roots time :=
      quittingTailConditionedCollisionWeight_le roots time hpositive
    _ ≤ (Fintype.card ι).choose 2 *
          quittingTailConditionedAbsorptionWeight roots time *
            quittingTailConditionedAbsorptionWeight roots time := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hphysical (Nat.cast_nonneg _)) hweight
    _ = (Fintype.card ι).choose 2 *
          quittingTailConditionedAbsorptionWeight roots time ^ 2 := by ring_nf

omit [DecidableEq ι] in
/-- The conditioned continuation coefficient is literally one minus the
conditioned absorption coefficient. -/
theorem quittingTailConditionedContinuationWeight_eq_one_sub
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedContinuationWeight roots time =
      1 - quittingTailConditionedAbsorptionWeight roots time := by
  have hsum := quittingTailConditionedWeights_add roots time hpositive
  linarith

omit [DecidableEq ι] in
/-- Exact finite telescope for the conditioned continuation clock.  The
division-free form makes the cancellation of consecutive remaining masses
explicit. -/
theorem quittingTailEventualAbsorption_mul_prod_conditionedContinuation
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time) :
    quittingTailEventualAbsorption roots start *
        ∏ offset ∈ Finset.range fuel,
          quittingTailConditionedContinuationWeight roots (start + offset) =
      quittingJointSurvivalWeight roots start fuel *
        quittingTailEventualAbsorption roots (start + fuel) := by
  induction fuel with
  | zero =>
      simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      rw [Finset.prod_range_succ]
      calc
        quittingTailEventualAbsorption roots start *
              ((∏ offset ∈ Finset.range fuel,
                  quittingTailConditionedContinuationWeight roots
                    (start + offset)) *
                quittingTailConditionedContinuationWeight roots
                  (start + fuel)) =
            (quittingTailEventualAbsorption roots start *
                ∏ offset ∈ Finset.range fuel,
                  quittingTailConditionedContinuationWeight roots
                    (start + offset)) *
              quittingTailConditionedContinuationWeight roots
                (start + fuel) := by ring_nf
        _ = (quittingJointSurvivalWeight roots start fuel *
              quittingTailEventualAbsorption roots (start + fuel)) *
            quittingTailConditionedContinuationWeight roots
              (start + fuel) := by rw [ih]
        _ = quittingJointSurvivalWeight roots start fuel *
            (quittingStationaryContinueMass (roots (start + fuel)) *
              quittingTailEventualAbsorption roots (start + fuel + 1)) := by
          unfold quittingTailConditionedContinuationWeight
          field_simp [ne_of_gt (hpositive (start + fuel))]
        _ = quittingJointSurvivalWeight roots start (fuel + 1) *
            quittingTailEventualAbsorption roots (start + (fuel + 1)) := by
          rw [quittingJointSurvivalWeight_succ]
          ring_nf

omit [DecidableEq ι] in
/-- The conditioned clock is complete whenever late tails have vanishing
remaining eventual-absorption mass. -/
theorem tendsto_prod_quittingTailConditionedContinuationWeight_zero
    (roots : ℕ → ι → PMF Bool) (start : ℕ)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0)) :
    Tendsto (fun fuel ↦
        ∏ offset ∈ Finset.range fuel,
          quittingTailConditionedContinuationWeight roots (start + offset))
      atTop (nhds 0) := by
  have hstart := hpositive start
  have hshift : Tendsto
      (fun fuel ↦ quittingTailEventualAbsorption roots (start + fuel))
      atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      heventualZero.comp (tendsto_add_atTop_nat start)
  apply squeeze_zero (g := fun fuel ↦
    quittingTailEventualAbsorption roots (start + fuel) /
      quittingTailEventualAbsorption roots start)
  · intro fuel
    exact Finset.prod_nonneg fun offset hoffset ↦
      quittingTailConditionedContinuationWeight_nonneg roots
        (start + offset)
        (quittingTailEventualAbsorption_mem_unitInterval
          roots (start + offset + 1)).1
        (hpositive (start + offset))
  · intro fuel
    have htelescope :=
      quittingTailEventualAbsorption_mul_prod_conditionedContinuation
        roots start fuel hpositive
    have hsurvival := quittingJointSurvivalWeight_le_one roots start fuel
    have hlate :=
      (quittingTailEventualAbsorption_mem_unitInterval
        roots (start + fuel)).1
    have hproduct :
        (∏ offset ∈ Finset.range fuel,
            quittingTailConditionedContinuationWeight roots
              (start + offset)) =
          (quittingJointSurvivalWeight roots start fuel *
              quittingTailEventualAbsorption roots (start + fuel)) /
            quittingTailEventualAbsorption roots start := by
      apply (eq_div_iff hstart.ne').2
      simpa [mul_comm] using htelescope
    calc
      (∏ offset ∈ Finset.range fuel,
          quittingTailConditionedContinuationWeight roots
            (start + offset)) =
          (quittingJointSurvivalWeight roots start fuel *
              quittingTailEventualAbsorption roots (start + fuel)) /
            quittingTailEventualAbsorption roots start := hproduct
      _ ≤ quittingTailEventualAbsorption roots (start + fuel) /
            quittingTailEventualAbsorption roots start :=
        div_le_div_of_nonneg_right
          (mul_le_of_le_one_left hlate hsurvival) hstart.le
  · simpa [div_eq_mul_inv, mul_comm] using hshift.const_mul
      (quittingTailEventualAbsorption roots start)⁻¹

omit [DecidableEq ι] in
/-- Exact floor accounting under conditioning. -/
theorem quittingTailConditionedValue_sub_floor
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedValue roots value boundary time who - floor who =
      ((value time who - floor who) -
          quittingJointSurvivalLimit roots time *
            (boundary who - floor who)) /
        quittingTailEventualAbsorption roots time := by
  have hden : 1 - quittingJointSurvivalLimit roots time ≠ 0 := by
    simpa [quittingTailEventualAbsorption] using hpositive.ne'
  unfold quittingTailConditionedValue quittingTailEventualAbsorption
  field_simp [hden]
  ring_nf

omit [DecidableEq ι] in
/-- Conditioning preserves a floor precisely when the live annotation above
that floor pays for the surviving boundary slack. -/
theorem floor_le_quittingTailConditionedValue_iff
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    floor who ≤ quittingTailConditionedValue roots value boundary time who ↔
      quittingJointSurvivalLimit roots time *
          (boundary who - floor who) ≤
        value time who - floor who := by
  rw [← sub_nonneg,
    quittingTailConditionedValue_sub_floor
      roots value boundary floor time who hpositive,
    div_nonneg_iff]
  constructor
  · rintro (h | h)
    · exact sub_nonneg.mp h.1
    · exfalso
      linarith [hpositive]
  · intro h
    exact Or.inl ⟨sub_nonneg.mpr h, hpositive.le⟩

omit [DecidableEq ι] in
/-- Tight boundary coordinates retain every lower floor satisfied by the
original annotation. -/
theorem floor_le_quittingTailConditionedValue_of_boundary_eq_floor
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary who = floor who)
    (hvalue : floor who ≤ value time who) :
    floor who ≤ quittingTailConditionedValue roots value boundary time who := by
  rw [floor_le_quittingTailConditionedValue_iff
    roots value boundary floor time who hpositive, htight, sub_self, mul_zero]
  exact sub_nonneg.mpr hvalue

omit [DecidableEq ι] in
/-- Full essential-APS viability of a conditioned state is exactly the
playerwise source-slack inequality.  This is the sharp viability gate on a
strict phantom-boundary coordinate. -/
theorem quittingTailConditionedValue_viable_iff
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    QuittingEssentialAPSViable reward
        (quittingTailConditionedValue roots value boundary time) ↔
      ∀ who,
        quittingJointSurvivalLimit roots time *
            (boundary who - quittingSoloBaseline reward who) ≤
          value time who - quittingSoloBaseline reward who := by
  constructor
  · intro hviable who
    exact (floor_le_quittingTailConditionedValue_iff roots value boundary
      (quittingSoloBaseline reward) time who hpositive).1 (hviable who)
  · intro hslack who
    exact (floor_le_quittingTailConditionedValue_iff roots value boundary
      (quittingSoloBaseline reward) time who hpositive).2 (hslack who)

omit [DecidableEq ι] in
/-- A boundary coordinate tight at the singleton baseline is viable after
conditioning whenever the source annotation is viable there. -/
theorem quittingSoloBaseline_le_conditionedValue_of_tightBoundary
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary who = quittingSoloBaseline reward who)
    (hvalue : quittingSoloBaseline reward who ≤ value time who) :
    quittingSoloBaseline reward who ≤
      quittingTailConditionedValue roots value boundary time who :=
  floor_le_quittingTailConditionedValue_of_boundary_eq_floor
    roots value boundary (quittingSoloBaseline reward) time who hpositive
      htight hvalue

/-- Along a diffuse active subsequence, the conditioned owner's coordinate
converges to its singleton payoff.  This is the exact asymptotic active-face
input available for a prospective chattering argument. -/
theorem tendsto_quittingTailConditionedValue_activeCoordinate
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (owner : ι) (time : ℕ → ℕ)
    (hpositive : ∀ index,
      0 < quittingTailEventualAbsorption roots (time index))
    (hquit : ∀ index, 0 < (roots (time index) owner true).toReal)
    (hpin : boundary owner =
      reward (quittingSingletonTerminal owner) owner)
    (hdiffuse : Tendsto (fun index ↦
      quittingTailConditionedAbsorptionWeight roots (time index))
      atTop (nhds 0)) :
    Tendsto (fun index ↦
      quittingTailConditionedValue roots value boundary (time index) owner)
      atTop
      (nhds (reward (quittingSingletonTerminal owner) owner)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hbound : Tendsto (fun index ↦
      2 * M * quittingTailConditionedAbsorptionWeight roots (time index))
      atTop (nhds 0) := by
    simpa using hdiffuse.const_mul (2 * M)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hbound) ε hε
  refine ⟨threshold, fun index hindex ↦ ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (abs_quittingTailConditionedValue_sub_singleton_le_weight
      roots value boundary hpolicy hnash hM hreward (time index) owner
        (hpositive index) (hquit index) hpin)
    (by
      have hclose := hthreshold index hindex
      have hmajor : 0 ≤ 2 * M *
          quittingTailConditionedAbsorptionWeight roots (time index) :=
        mul_nonneg (mul_nonneg (by norm_num) hM)
          (quittingTailConditionedAbsorptionWeight_nonneg
            roots (time index) (hpositive index))
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hmajor] at hclose
      exact hclose)

end GameTheory
