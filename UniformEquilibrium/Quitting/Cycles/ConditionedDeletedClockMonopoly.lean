/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.DivergentChargeRecurrence
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseChronology
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling

/-!
# Owner monopoly from a deficient conditioned deleted clock

On a diffuse conditioned tail, summability of one player's deleted clock has
a rigid probabilistic meaning.  After product rescaling, every non-owner
hazard is summable, while completeness of the conditioned joint clock forces
the exceptional owner's hazard to be nonsummable and hence positive
arbitrarily late.

This is the probabilistic producer needed by the approximate solo-cycle lane.
It does not yet prove the endpoint-Nash or punishment inequalities required by
that strategic compiler.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Completeness of the conditioned continuation clock forces the conditioned
absorption weights to have divergent sum. -/
theorem not_summable_quittingTailConditionedAbsorptionWeight_of_tendsto_zero
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0)) :
    ¬Summable (quittingTailConditionedAbsorptionWeight roots) := by
  apply Math.not_summable_of_tendsto_prod_one_sub_zero
  · intro time
    exact quittingTailConditionedAbsorptionWeight_nonneg
      roots time (hpositive time)
  · intro time
    exact (quittingTailConditionedWeights_mem_unitInterval roots time
      (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1
      (hpositive time)).1.2
  · intro start
    have hcomplete :=
      tendsto_prod_quittingTailConditionedContinuationWeight_zero
        roots start hpositive heventualZero
    convert hcomplete using 1
    funext fuel
    apply Finset.prod_congr rfl
    intro offset hoffset
    rw [quittingTailConditionedContinuationWeight_eq_one_sub
      roots (start + offset) (hpositive (start + offset))]

/-- The full rescaled marginal total splits into the owner's hazard and the
sum of all non-owner hazards. -/
theorem quittingTailDiffuseRescaledTotal_eq_owner_add_opponentTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (owner : ι) :
    quittingTailDiffuseRescaledTotal roots time =
      quittingTailDiffuseRescaledHazard roots time owner +
        quittingTailDiffuseRescaledOpponentTotal roots time owner := by
  unfold quittingTailDiffuseRescaledTotal
    quittingTailDiffuseRescaledOpponentTotal
  rw [add_comm]
  exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ owner)).symm

omit [DecidableEq ι] in
/-- Every individual rescaled hazard is bounded by the full rescaled
marginal total. -/
theorem quittingTailDiffuseRescaledHazard_le_total
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledHazard roots time who ≤
      quittingTailDiffuseRescaledTotal roots time := by
  classical
  unfold quittingTailDiffuseRescaledTotal
  exact Finset.single_le_sum
    (fun other _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots time other hpositive)
    (Finset.mem_univ who)

/-- A summable normalized source deleted clock makes the corresponding
rescaled non-owner marginal total summable on the same suffix. -/
theorem summable_quittingTailDiffuseRescaledOpponentTotal
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner)) :
    Summable (fun offset =>
      quittingTailDiffuseRescaledOpponentTotal roots (start + offset) owner) := by
  let opponentTotal : ℕ → ℝ := fun offset =>
    quittingTailDiffuseRescaledOpponentTotal roots (start + offset) owner
  let sourceDeleted : ℕ → ℝ := fun offset =>
    quittingTailConditionedOpponentWeight roots (start + offset) owner
  let alpha : ℕ → ℝ := fun offset =>
    quittingTailConditionedAbsorptionWeight roots (start + offset)
  have halphaZero : Tendsto alpha atTop (nhds 0) := by
    have hshift := hmesh.comp (tendsto_add_atTop_nat start)
    convert hshift using 1
    funext offset
    simp only [alpha, Function.comp_apply, Nat.add_comm]
  have hopponentNonneg : ∀ offset, 0 ≤ opponentTotal offset := by
    intro offset
    unfold opponentTotal quittingTailDiffuseRescaledOpponentTotal
    exact Finset.sum_nonneg fun other _ =>
      quittingTailDiffuseRescaledHazard_nonneg roots (start + offset) other
        (hpositive (start + offset))
  have hopponentLe : ∀ offset,
      opponentTotal offset ≤ Fintype.card ι * alpha offset := by
    intro offset
    exact (quittingTailDiffuseRescaledOpponentTotal_le_total
      roots (start + offset) owner (hpositive (start + offset))).trans
        (quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
          roots (start + offset) (hpositive (start + offset)))
  have hopponentZero : Tendsto opponentTotal atTop (nhds 0) := by
    apply squeeze_zero hopponentNonneg hopponentLe
    simpa using halphaZero.const_mul (Fintype.card ι : ℝ)
  have heventually : ∀ᶠ offset : ℕ in atTop,
      opponentTotal offset < 1 :=
    (tendsto_order.1 hopponentZero).2 1 zero_lt_one
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  have hsourceTail : Summable (fun offset =>
      sourceDeleted (threshold + offset)) := by
    have hshift : Summable (fun offset =>
        sourceDeleted (offset + threshold)) :=
      (summable_nat_add_iff threshold).2 hsummable
    simpa [Nat.add_comm] using hshift
  have hopponentTail : Summable (fun offset =>
      opponentTotal (threshold + offset)) := by
    apply (hsourceTail.mul_left 2).of_nonneg_of_le
    · intro offset
      exact hopponentNonneg (threshold + offset)
    · intro offset
      have htotalOne : opponentTotal (threshold + offset) ≤ 1 :=
        (hthreshold (threshold + offset)
          (Nat.le_add_right threshold offset)).le
      have hbonferroni :=
        quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_conditionedOpponentWeight
          roots (start + (threshold + offset)) owner
            (hpositive (start + (threshold + offset)))
      change opponentTotal (threshold + offset) -
          opponentTotal (threshold + offset) ^ 2 / 2 ≤
        sourceDeleted (threshold + offset) at hbonferroni
      have htotal0 := hopponentNonneg (threshold + offset)
      nlinarith [sq_nonneg (opponentTotal (threshold + offset))]
  have hopponentTail' : Summable (fun offset =>
      opponentTotal (offset + threshold)) := by
    simpa [Nat.add_comm] using hopponentTail
  exact (summable_nat_add_iff threshold).1 hopponentTail'

/-- Summability of the rescaled non-owner marginal total implies summability
of the literal opponent-absorption clock of the rescaled product path. -/
theorem summable_quittingTailDiffuseRescaledRoot_opponentAbsorption
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hsummable : Summable (fun offset =>
      quittingTailDiffuseRescaledOpponentTotal roots (start + offset) owner)) :
    Summable (fun offset => quittingRootOpponentAbsorptionMass
      (quittingTailDiffuseRescaledRoot roots (start + offset)
        (hpositive (start + offset))) owner) := by
  apply hsummable.of_nonneg_of_le
  · intro offset
    exact quittingRootAbsorptionMass_nonneg
      (Function.update
        (quittingTailDiffuseRescaledRoot roots (start + offset)
          (hpositive (start + offset))) owner (PMF.pure false))
  · intro offset
    exact quittingTailDiffuseRescaledRoot_opponentAbsorption_le_opponentTotal
      roots (start + offset) owner (hpositive (start + offset))

omit [DecidableEq ι] in
/-- A nonsummable rescaled owner hazard forces the full rescaled absorption
clock to be nonsummable. -/
theorem not_summable_quittingTailDiffuseRescaledRoot_absorptionMass
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (howner : ¬Summable (fun offset =>
      quittingTailDiffuseRescaledHazard roots (start + offset) owner)) :
    ¬Summable (fun offset => quittingRootAbsorptionMass
      (quittingTailDiffuseRescaledRoot roots (start + offset)
        (hpositive (start + offset)))) := by
  intro habsorption
  apply howner
  apply habsorption.of_nonneg_of_le
  · intro offset
    exact quittingTailDiffuseRescaledHazard_nonneg roots
      (start + offset) owner (hpositive (start + offset))
  · intro offset
    rw [← congrFun (hazardOfRoot_quittingTailDiffuseRescaledRoot
      roots (start + offset) (hpositive (start + offset))) owner]
    exact quittingRoot_quitProbability_le_absorptionMass
      (quittingTailDiffuseRescaledRoot roots (start + offset)
        (hpositive (start + offset))) owner

omit [DecidableEq ι] in
/-- A nonsummable full absorption clock makes every finite joint-survival
product of the rescaled path tend to zero. -/
theorem tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
    (targetRoots : ℕ → ι → PMF Bool) (start : ℕ)
    (hdiverges : ¬Summable (fun offset =>
      quittingRootAbsorptionMass (targetRoots (start + offset)))) :
    Tendsto (quittingJointSurvivalWeight targetRoots start) atTop (nhds 0) := by
  let charge : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (targetRoots time)
  have hcharge0 : ∀ time, 0 ≤ charge time := fun time =>
    quittingRootAbsorptionMass_nonneg (targetRoots time)
  have hcharge1 : ∀ time, charge time ≤ 1 := fun time => by
    unfold charge quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg (targetRoots time)]
  have hglobal : ¬Summable charge := by
    intro hsummable
    have hsuffix : Summable (fun offset => charge (start + offset)) := by
      have hshift : Summable (fun offset => charge (offset + start)) :=
        (summable_nat_add_iff start).2 hsummable
      simpa [Nat.add_comm] using hshift
    exact hdiverges hsuffix
  have hproduct := Math.tendsto_prod_one_sub_zero_of_not_summable
    charge hcharge0 hcharge1 hglobal start
  convert hproduct using 1
  funext fuel
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro offset _
  unfold charge quittingRootAbsorptionMass
  ring

/-- **Conditioned owner-monopoly extraction.**  If one conditioned deleted
clock is summable while the conditioned joint clock is complete and diffuse,
then every non-owner rescaled hazard is summable, the owner's rescaled hazard
is nonsummable, and it is positive arbitrarily late. -/
theorem conditionedDeletedClock_ownerMonopoly
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner)) :
    Summable (fun offset =>
        quittingTailDiffuseRescaledOpponentTotal roots (start + offset) owner) ∧
      (∀ other, other ≠ owner → Summable (fun offset =>
        quittingTailDiffuseRescaledHazard roots (start + offset) other)) ∧
      ¬Summable (fun offset =>
        quittingTailDiffuseRescaledHazard roots (start + offset) owner) ∧
      ∀ threshold, ∃ offset, threshold ≤ offset ∧
        0 < quittingTailDiffuseRescaledHazard roots (start + offset) owner := by
  have hopponent := summable_quittingTailDiffuseRescaledOpponentTotal
    roots owner start hpositive hmesh hsummable
  have hothers : ∀ other, other ≠ owner → Summable (fun offset =>
      quittingTailDiffuseRescaledHazard roots (start + offset) other) := by
    intro other hother
    apply hopponent.of_nonneg_of_le
    · intro offset
      exact quittingTailDiffuseRescaledHazard_nonneg roots
        (start + offset) other (hpositive (start + offset))
    · intro offset
      unfold quittingTailDiffuseRescaledOpponentTotal
      exact Finset.single_le_sum
        (fun player _ => quittingTailDiffuseRescaledHazard_nonneg roots
          (start + offset) player (hpositive (start + offset)))
        (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
  have halphaGlobal :
      ¬Summable (quittingTailConditionedAbsorptionWeight roots) :=
    not_summable_quittingTailConditionedAbsorptionWeight_of_tendsto_zero
      roots hpositive heventualZero
  have halpha : ¬Summable (fun offset =>
      quittingTailConditionedAbsorptionWeight roots (start + offset)) := by
    intro hsuffix
    have hshift : Summable (fun offset =>
        quittingTailConditionedAbsorptionWeight roots (offset + start)) := by
      simpa [Nat.add_comm] using hsuffix
    exact halphaGlobal ((summable_nat_add_iff start).1 hshift)
  have howner : ¬Summable (fun offset =>
      quittingTailDiffuseRescaledHazard roots (start + offset) owner) := by
    intro hownerSummable
    have htotal : Summable (fun offset =>
        quittingTailDiffuseRescaledTotal roots (start + offset)) := by
      have hsum := hownerSummable.add hopponent
      apply hsum.congr
      intro offset
      exact (quittingTailDiffuseRescaledTotal_eq_owner_add_opponentTotal
        roots (start + offset) owner).symm
    apply halpha
    apply htotal.of_nonneg_of_le
    · intro offset
      exact quittingTailConditionedAbsorptionWeight_nonneg roots
        (start + offset) (hpositive (start + offset))
    · intro offset
      exact quittingTailConditionedAbsorptionWeight_le_rescaledTotal
        roots (start + offset) (hpositive (start + offset))
  have hpositiveLate : ∀ threshold, ∃ offset, threshold ≤ offset ∧
      0 < quittingTailDiffuseRescaledHazard roots (start + offset) owner := by
    intro threshold
    by_contra hnone
    push Not at hnone
    have htailZero : ∀ offset,
        quittingTailDiffuseRescaledHazard roots
          (start + (threshold + offset)) owner = 0 := by
      intro offset
      have hnonneg := quittingTailDiffuseRescaledHazard_nonneg roots
        (start + (threshold + offset)) owner
          (hpositive (start + (threshold + offset)))
      have hnotPos := hnone (threshold + offset)
        (Nat.le_add_right threshold offset)
      linarith
    have hsuffix : Summable (fun offset =>
        quittingTailDiffuseRescaledHazard roots
          (start + (threshold + offset)) owner) := by
      simp only [htailZero, summable_zero]
    have hsuffix' : Summable (fun offset =>
        (fun time => quittingTailDiffuseRescaledHazard roots
          (start + time) owner) (offset + threshold)) := by
      simpa [Nat.add_comm, Nat.add_assoc] using hsuffix
    exact howner ((summable_nat_add_iff threshold).1 hsuffix')
  exact ⟨hopponent, hothers, howner, hpositiveLate⟩

end GameTheory
