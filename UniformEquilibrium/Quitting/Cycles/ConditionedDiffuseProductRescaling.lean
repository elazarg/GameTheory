/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseChronology
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationPath
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy

/-!
# Product rescaling of a diffuse conditioned quitting row

At a tail with remaining eventual-absorption mass `a`, rescale every physical
quit marginal `p_i` to `p_i / a`.  Since `p_i ≤ q ≤ a`, these are again
Bernoulli probabilities and define an ordinary independent product root.

The rescaled root need not reproduce the conditioned coalition law exactly.
It does reproduce its first-order clock.  If `alpha = q / a` is the
conditioned absorption weight and `s` is the sum of the rescaled marginals,
then

`alpha ≤ s ≤ card(I) * alpha`.

Bonferroni gives `q' ≥ s - s²/2` for the rescaled product absorption `q'`.
Consequently, once `card(I) * alpha ≤ 1`, one has

`alpha / 2 ≤ q' ≤ card(I) * alpha`.

Thus product rescaling preserves the diffuse complete clock up to fixed
constants.  Strategic residual and exact policy repair are separate; they
are consumed by the separated-error compiler.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every marginal quit probability is bounded by joint absorption. -/
theorem quittingRoot_quitProbability_le_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal ≤ quittingRootAbsorptionMass root := by
  have hcontinue : quittingStationaryContinueMass root ≤
      (root who false).toReal := by
    classical
    rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own
      root who]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg
      (quittingRootDeletedContinueMass_le_one root who)
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

/-- Marginal quit rate after division by remaining eventual absorption. -/
def quittingTailDiffuseRescaledHazard
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) : ℝ :=
  (roots time who true).toReal /
    quittingTailEventualAbsorption roots time

omit [DecidableEq ι] in
theorem quittingTailDiffuseRescaledHazard_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailDiffuseRescaledHazard roots time who :=
  div_nonneg ENNReal.toReal_nonneg hpositive.le

omit [DecidableEq ι] in
/-- Every rescaled marginal is bounded by the conditioned total hazard. -/
theorem quittingTailDiffuseRescaledHazard_le_conditionedWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledHazard roots time who ≤
      quittingTailConditionedAbsorptionWeight roots time := by
  unfold quittingTailDiffuseRescaledHazard
    quittingTailConditionedAbsorptionWeight
  exact div_le_div_of_nonneg_right
    (quittingRoot_quitProbability_le_absorptionMass (roots time) who)
    hpositive.le

omit [DecidableEq ι] in
theorem quittingTailDiffuseRescaledHazard_le_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledHazard roots time who ≤ 1 :=
  (quittingTailDiffuseRescaledHazard_le_conditionedWeight
    roots time who hpositive).trans <|
      (quittingTailConditionedWeights_mem_unitInterval roots time
        (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1
        hpositive).1.2

/-- Ordinary product root obtained by scaling every source marginal by the
remaining eventual-absorption probability. -/
def quittingTailDiffuseRescaledRoot
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    ι → PMF Bool :=
  rootOfHazard (quittingTailDiffuseRescaledHazard roots time)
    (fun who ↦ quittingTailDiffuseRescaledHazard_nonneg
      roots time who hpositive)
    (fun who ↦ quittingTailDiffuseRescaledHazard_le_one
      roots time who hpositive)

omit [DecidableEq ι] in
@[simp] theorem hazardOfRoot_quittingTailDiffuseRescaledRoot
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    hazardOfRoot (quittingTailDiffuseRescaledRoot roots time hpositive) =
      quittingTailDiffuseRescaledHazard roots time :=
  hazardOfRoot_rootOfHazard _ _ _

/-- Sum of rescaled player marginals at one conditioned row. -/
def quittingTailDiffuseRescaledTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  ∑ who, quittingTailDiffuseRescaledHazard roots time who

omit [DecidableEq ι] in
theorem quittingTailConditionedAbsorptionWeight_le_rescaledTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedAbsorptionWeight roots time ≤
      quittingTailDiffuseRescaledTotal roots time := by
  have hunion : quittingRootAbsorptionMass (roots time) ≤
      ∑ who, (roots time who true).toReal := by
    have h := Math.one_sub_prod_one_sub_le_sum
      (hazardOfRoot (roots time)) Finset.univ
        (fun who _ ↦ hazardOfRoot_nonneg (roots time) who)
        (fun who _ ↦ hazardOfRoot_le_one (roots time) who)
    rw [quittingRootAbsorptionMass,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    simpa [hazardOfRoot, pmfBool_false_toReal] using h
  unfold quittingTailConditionedAbsorptionWeight
    quittingTailDiffuseRescaledTotal quittingTailDiffuseRescaledHazard
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hunion hpositive.le

omit [DecidableEq ι] in
/-- The rescaled marginal total is at most `card(I)` times conditioned
absorption. -/
theorem quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledTotal roots time ≤
      Fintype.card ι * quittingTailConditionedAbsorptionWeight roots time := by
  unfold quittingTailDiffuseRescaledTotal
  calc
    (∑ who, quittingTailDiffuseRescaledHazard roots time who) ≤
        ∑ _who : ι,
          quittingTailConditionedAbsorptionWeight roots time := by
      exact Finset.sum_le_sum fun who _ ↦
        quittingTailDiffuseRescaledHazard_le_conditionedWeight
          roots time who hpositive
    _ = Fintype.card ι *
        quittingTailConditionedAbsorptionWeight roots time := by simp

omit [DecidableEq ι] in
/-- Bonferroni lower bound for absorption of the rescaled product root. -/
theorem quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_absorptionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledTotal roots time -
        quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 ≤
      quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) := by
  unfold quittingTailDiffuseRescaledRoot
  rw [quittingRootAbsorptionMass_rootOfHazard]
  exact Math.sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub
    (quittingTailDiffuseRescaledHazard roots time) Finset.univ
      (fun who _ ↦ quittingTailDiffuseRescaledHazard_nonneg
        roots time who hpositive)
      (fun who _ ↦ quittingTailDiffuseRescaledHazard_le_one
        roots time who hpositive)

omit [DecidableEq ι] in
/-- In the late diffuse range, rescaled product absorption is bounded below
by half of conditioned absorption. -/
theorem half_conditionedWeight_le_rescaledRoot_absorptionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    quittingTailConditionedAbsorptionWeight roots time / 2 ≤
      quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) := by
  let alpha := quittingTailConditionedAbsorptionWeight roots time
  let total := quittingTailDiffuseRescaledTotal roots time
  have halphaTotal : alpha ≤ total :=
    quittingTailConditionedAbsorptionWeight_le_rescaledTotal
      roots time hpositive
  have htotalOne : total ≤ 1 :=
    (quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
      roots time hpositive).trans hsmall
  have htotalNonneg : 0 ≤ total := by
    unfold total quittingTailDiffuseRescaledTotal
    exact Finset.sum_nonneg fun who _ ↦
      quittingTailDiffuseRescaledHazard_nonneg roots time who hpositive
  have hbonferroni :=
    quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_absorptionMass
      roots time hpositive
  dsimp only [alpha, total] at halphaTotal htotalOne htotalNonneg hbonferroni ⊢
  nlinarith [sq_nonneg (quittingTailDiffuseRescaledTotal roots time)]

omit [DecidableEq ι] in
/-- Union bound for the rescaled product root. -/
theorem quittingTailDiffuseRescaledRoot_absorptionMass_le_total
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) ≤
      quittingTailDiffuseRescaledTotal roots time := by
  unfold quittingTailDiffuseRescaledRoot
  rw [quittingRootAbsorptionMass_rootOfHazard]
  exact Math.one_sub_prod_one_sub_le_sum
    (quittingTailDiffuseRescaledHazard roots time) Finset.univ
      (fun who _ ↦ quittingTailDiffuseRescaledHazard_nonneg
        roots time who hpositive)
      (fun who _ ↦ quittingTailDiffuseRescaledHazard_le_one
        roots time who hpositive)

omit [DecidableEq ι] in
/-- The normalized source absorption has the same Bonferroni lower bound as
the target rescaled product root. -/
theorem quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_conditionedWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledTotal roots time -
        quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 ≤
      quittingTailConditionedAbsorptionWeight roots time := by
  let eventual := quittingTailEventualAbsorption roots time
  let sourceTotal := ∑ who, (roots time who true).toReal
  let targetTotal := quittingTailDiffuseRescaledTotal roots time
  have heventualOne : eventual ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hsourceTotal : sourceTotal = eventual * targetTotal := by
    unfold sourceTotal targetTotal quittingTailDiffuseRescaledTotal
      quittingTailDiffuseRescaledHazard
    dsimp only [eventual]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro who _
    field_simp [hpositive.ne']
  have hbonferroni := Math.sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub
    (fun who ↦ (roots time who true).toReal) Finset.univ
    (fun who _ ↦ ENNReal.toReal_nonneg)
    (fun who _ ↦ hazardOfRoot_le_one (roots time) who)
  have habsorption : quittingRootAbsorptionMass (roots time) =
      1 - ∏ who, (1 - (roots time who true).toReal) := by
    unfold quittingRootAbsorptionMass
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    congr 1
    apply Finset.prod_congr rfl
    intro who _
    rw [pmfBool_false_toReal]
  rw [← habsorption] at hbonferroni
  change sourceTotal - sourceTotal ^ 2 / 2 ≤
      quittingRootAbsorptionMass (roots time) at hbonferroni
  rw [hsourceTotal] at hbonferroni
  unfold quittingTailConditionedAbsorptionWeight
  dsimp only [eventual, targetTotal] at heventualOne hbonferroni ⊢
  apply (le_div_iff₀ hpositive).2
  nlinarith [sq_nonneg (quittingTailDiffuseRescaledTotal roots time)]

omit [DecidableEq ι] in
/-- **Quadratic full-law absorption comparison.**  Source absorption
conditioned on eventual absorption and target rescaled product absorption
differ only at collision order. -/
theorem abs_conditionedWeight_sub_rescaledRoot_absorptionMass_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingTailConditionedAbsorptionWeight roots time -
        quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive)| ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  have hsourceUpper :=
    quittingTailConditionedAbsorptionWeight_le_rescaledTotal
      roots time hpositive
  have hsourceLower :=
    quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_conditionedWeight
      roots time hpositive
  have htargetUpper :=
    quittingTailDiffuseRescaledRoot_absorptionMass_le_total
      roots time hpositive
  have htargetLower :=
    quittingTailDiffuseRescaledTotal_sub_sq_div_two_le_absorptionMass
      roots time hpositive
  rw [abs_le]
  constructor <;> linarith

/-! ## Deleted-player clocks -/

/-- Joint absorption splits into opponent absorption and the event that all
opponents continue while the selected player quits.  This division-free
identity is the local algebra behind the deleted-clock rescaling seam. -/
theorem quittingRootAbsorptionMass_eq_opponentAbsorption_add
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root =
      quittingRootOpponentAbsorptionMass root who +
        (1 - quittingRootOpponentAbsorptionMass root who) *
          (root who true).toReal := by
  have hjoint :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own root who
  have hprobability :=
    quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [hjoint, hfalse]
  ring

/-- The opponent absorption faced by `who` is the union probability of the
opponents' quit marginals. -/
theorem quittingRootOpponentAbsorptionMass_eq_one_sub_prod
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who =
      1 - ∏ other ∈ Finset.univ.erase who,
        (1 - (root other true).toReal) := by
  classical
  have hproduct :
      (∏ player,
          (Function.update root who (PMF.pure false) player false).toReal) =
        ∏ other ∈ Finset.univ.erase who,
          (root other false).toReal := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun player ↦
        (Function.update root who (PMF.pure false) player false).toReal)
      (Finset.mem_univ who)]
    rw [Function.update_self]
    simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro other hother
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability, hproduct]
  congr 1
  apply Finset.prod_congr rfl
  intro other _
  rw [pmfBool_false_toReal]

/-- Sum of the rescaled opponent marginals faced by one player. -/
def quittingTailDiffuseRescaledOpponentTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) : ℝ :=
  ∑ other ∈ Finset.univ.erase who,
    quittingTailDiffuseRescaledHazard roots time other

/-- Source opponent absorption, normalized by remaining eventual
absorption.  This is the additive deleted-clock charge inherited from the
conditioned chronology. -/
def quittingTailConditionedOpponentWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) : ℝ :=
  quittingRootOpponentAbsorptionMass (roots time) who /
    quittingTailEventualAbsorption roots time

/-- The conditioned source opponent charge is at most the sum of the
rescaled opponent marginals. -/
theorem quittingTailConditionedOpponentWeight_le_rescaledOpponentTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailConditionedOpponentWeight roots time who ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
  have hunion := Math.one_sub_prod_one_sub_le_sum
    (fun other ↦ (roots time other true).toReal)
    (Finset.univ.erase who)
    (fun other _ ↦ ENNReal.toReal_nonneg)
    (fun other _ ↦ hazardOfRoot_le_one (roots time) other)
  rw [← quittingRootOpponentAbsorptionMass_eq_one_sub_prod
    (roots time) who] at hunion
  unfold quittingTailConditionedOpponentWeight
    quittingTailDiffuseRescaledOpponentTotal
    quittingTailDiffuseRescaledHazard
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hunion hpositive.le

/-- The deleted rescaled total is bounded by the full rescaled total. -/
theorem quittingTailDiffuseRescaledOpponentTotal_le_total
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledOpponentTotal roots time who ≤
      quittingTailDiffuseRescaledTotal roots time := by
  unfold quittingTailDiffuseRescaledOpponentTotal
    quittingTailDiffuseRescaledTotal
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    fun other _ _ ↦
      quittingTailDiffuseRescaledHazard_nonneg roots time other hpositive

/-- Bonferroni lower bound for a deleted-player clock after product
rescaling. -/
theorem quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_opponentAbsorption
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledOpponentTotal roots time who -
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 ≤
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  change quittingTailDiffuseRescaledOpponentTotal roots time who -
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 ≤
      1 - ∏ other ∈ Finset.univ.erase who,
        (1 - hazardOfRoot
          (quittingTailDiffuseRescaledRoot roots time hpositive) other)
  rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  unfold quittingTailDiffuseRescaledOpponentTotal
  exact Math.sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub
    (quittingTailDiffuseRescaledHazard roots time)
    (Finset.univ.erase who)
    (fun other _ ↦ quittingTailDiffuseRescaledHazard_nonneg
      roots time other hpositive)
    (fun other _ ↦ quittingTailDiffuseRescaledHazard_le_one
      roots time other hpositive)

/-- Union bound for the rescaled product root after deleting one player. -/
theorem quittingTailDiffuseRescaledRoot_opponentAbsorption_le_opponentTotal
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  change 1 - ∏ other ∈ Finset.univ.erase who,
      (1 - hazardOfRoot
        (quittingTailDiffuseRescaledRoot roots time hpositive) other) ≤
    quittingTailDiffuseRescaledOpponentTotal roots time who
  rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  unfold quittingTailDiffuseRescaledOpponentTotal
  exact Math.one_sub_prod_one_sub_le_sum
    (quittingTailDiffuseRescaledHazard roots time)
    (Finset.univ.erase who)
    (fun other _ ↦ quittingTailDiffuseRescaledHazard_nonneg
      roots time other hpositive)
    (fun other _ ↦ quittingTailDiffuseRescaledHazard_le_one
      roots time other hpositive)

/-- The normalized source opponent absorption has the same Bonferroni lower
bound as the target rescaled product, up to discarding the harmless factor
`a ≤ 1` in the quadratic correction. -/
theorem quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_conditionedOpponentWeight
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailDiffuseRescaledOpponentTotal roots time who -
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 ≤
      quittingTailConditionedOpponentWeight roots time who := by
  let eventual := quittingTailEventualAbsorption roots time
  let sourceTotal := ∑ other ∈ Finset.univ.erase who,
    (roots time other true).toReal
  let targetTotal :=
    quittingTailDiffuseRescaledOpponentTotal roots time who
  have heventualPos : 0 < eventual := by
    simpa [eventual] using hpositive
  have heventualOne : eventual ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hsourceTotal : sourceTotal = eventual * targetTotal := by
    unfold sourceTotal targetTotal
      quittingTailDiffuseRescaledOpponentTotal
      quittingTailDiffuseRescaledHazard
    dsimp only [eventual]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro other _
    field_simp [heventualPos.ne']
  have hbonferroni := Math.sum_sub_sq_sum_div_two_le_one_sub_prod_one_sub
    (fun other ↦ (roots time other true).toReal)
    (Finset.univ.erase who)
    (fun other _ ↦ ENNReal.toReal_nonneg)
    (fun other _ ↦ hazardOfRoot_le_one (roots time) other)
  rw [← quittingRootOpponentAbsorptionMass_eq_one_sub_prod
    (roots time) who] at hbonferroni
  have hdivided :
      sourceTotal / eventual - sourceTotal ^ 2 / (2 * eventual) ≤
        quittingTailConditionedOpponentWeight roots time who := by
    unfold quittingTailConditionedOpponentWeight
    apply (le_div_iff₀ hpositive).2
    calc
      (sourceTotal / eventual - sourceTotal ^ 2 / (2 * eventual)) *
            eventual = sourceTotal - sourceTotal ^ 2 / 2 := by
        field_simp [heventualPos.ne']
      _ ≤ quittingRootOpponentAbsorptionMass (roots time) who := by
        simpa [sourceTotal] using hbonferroni
  have heventual0 : 0 ≤ eventual := hpositive.le
  have htargetSq : 0 ≤ targetTotal ^ 2 := sq_nonneg targetTotal
  rw [hsourceTotal] at hdivided
  have hfirst : (eventual * targetTotal) / eventual = targetTotal := by
    field_simp [heventualPos.ne']
  have hsecond :
      (eventual * targetTotal) ^ 2 / (2 * eventual) =
        eventual * targetTotal ^ 2 / 2 := by
    field_simp [heventualPos.ne']
  rw [hfirst] at hdivided
  rw [hsecond] at hdivided
  dsimp only [eventual, targetTotal] at heventualOne heventual0
  dsimp only [eventual, targetTotal] at htargetSq hdivided ⊢
  nlinarith

/-- **Quadratic deleted-law comparison.**  The target opponent absorption
and the normalized source opponent absorption differ by at most half the
square of their common rescaled marginal total.  This is the exact
collision-order estimate needed by the Continue channel. -/
theorem abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingTailConditionedOpponentWeight roots time who -
        quittingRootOpponentAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) who| ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 := by
  have hsourceUpper :=
    quittingTailConditionedOpponentWeight_le_rescaledOpponentTotal
      roots time who hpositive
  have hsourceLower :=
    quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_conditionedOpponentWeight
      roots time who hpositive
  have htargetUpper :=
    quittingTailDiffuseRescaledRoot_opponentAbsorption_le_opponentTotal
      roots time who hpositive
  have htargetLower :=
    quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_opponentAbsorption
      roots time who hpositive
  rw [abs_le]
  constructor <;> linarith

/-- **Exact deleted-continuation rescaling seam.**  The target opponent
continue mass differs from the normalized source opponent continuation by
two terms and no others:

* the quadratic difference between source and target opponent absorption;
* the selected player's rescaled hazard, multiplied by source opponent
  continuation and the phantom survival still present after this row.

The second term vanishes for an inactive player.  For an active player it
is precisely the term which must be paired with a bound on the next
conditioned boundary gap; dropping it would assert a false cancellation. -/
theorem quittingTailDiffuse_deletedContinuation_rescaling_identity
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (1 - quittingRootOpponentAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) who) -
        (1 - quittingRootOpponentAbsorptionMass (roots time) who) *
          quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time =
      quittingTailConditionedOpponentWeight roots time who -
          quittingRootOpponentAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive) who +
        (1 - quittingRootOpponentAbsorptionMass (roots time) who) *
          quittingTailDiffuseRescaledHazard roots time who *
            quittingJointSurvivalLimit roots (time + 1) := by
  let eventual := quittingTailEventualAbsorption roots time
  let nextEventual := quittingTailEventualAbsorption roots (time + 1)
  let opponent := quittingRootOpponentAbsorptionMass (roots time) who
  let own := (roots time who true).toReal
  have heventual :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  have habsorption :=
    quittingRootAbsorptionMass_eq_opponentAbsorption_add
      (roots time) who
  have hcontinue :=
    quittingStationaryContinueMass_eq_forcedContinue_mul_own
      (roots time) who
  have hforced :
      quittingStationaryContinueMass
          (Function.update (roots time) who (PMF.pure false)) =
        1 - opponent := by
    dsimp only [opponent]
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
    ring
  have hown : (roots time who false).toReal = 1 - own := by
    dsimp only [own]
    have hprobability :=
      quittingRoot_continueProbability_add_quitProbability
        (roots time) who
    linarith
  have hrecurrence :
      eventual = opponent +
          (1 - opponent) * own +
        (1 - opponent) * (1 - own) * nextEventual := by
    dsimp only [eventual, nextEventual, opponent, own]
    rw [heventual, habsorption, hcontinue, hforced, hown]
  have hsurvival :
      quittingJointSurvivalLimit roots (time + 1) = 1 - nextEventual := by
    dsimp only [nextEventual]
    unfold quittingTailEventualAbsorption
    ring
  have hownScaled : own / eventual =
      quittingTailDiffuseRescaledHazard roots time who := by
    rfl
  unfold quittingTailConditionedOpponentWeight
  dsimp only [eventual, nextEventual, opponent] at hrecurrence hownScaled ⊢
  rw [← hownScaled, hsurvival]
  field_simp [hpositive.ne']
  nlinarith

/-- The exact seam has a quadratic collision part and one explicit own-clock
part.  This is the sharp scalar estimate: the latter term cannot in general
be replaced by a quadratic bound unless the next conditioned boundary gap
is known to be small. -/
theorem abs_quittingTailDiffuse_deletedContinuation_rescaling_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |(1 - quittingRootOpponentAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) who) -
        (1 - quittingRootOpponentAbsorptionMass (roots time) who) *
          quittingTailEventualAbsorption roots (time + 1) /
            quittingTailEventualAbsorption roots time| ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 +
        quittingTailDiffuseRescaledHazard roots time who *
          quittingJointSurvivalLimit roots (time + 1) := by
  let sourceContinue :=
    1 - quittingRootOpponentAbsorptionMass (roots time) who
  let own := quittingTailDiffuseRescaledHazard roots time who
  let phantom := quittingJointSurvivalLimit roots (time + 1)
  let mismatch :=
    quittingTailConditionedOpponentWeight roots time who -
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who
  have hidentity :=
    quittingTailDiffuse_deletedContinuation_rescaling_identity
      roots time who hpositive
  have hmismatch :=
    abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
      roots time who hpositive
  have hcontinue0 : 0 ≤ sourceContinue := by
    dsimp only [sourceContinue]
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
    have h := quittingStationaryContinueMass_nonneg
      (Function.update (roots time) who (PMF.pure false))
    linarith
  have hcontinue1 : sourceContinue ≤ 1 := by
    dsimp only [sourceContinue]
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
    have h := quittingStationaryContinueMass_le_one
      (Function.update (roots time) who (PMF.pure false))
    linarith
  have hown0 : 0 ≤ own :=
    quittingTailDiffuseRescaledHazard_nonneg roots time who hpositive
  have hphantom0 : 0 ≤ phantom :=
    quittingJointSurvivalLimit_nonneg roots (time + 1)
  have hterm0 : 0 ≤ sourceContinue * own * phantom :=
    mul_nonneg (mul_nonneg hcontinue0 hown0) hphantom0
  have hterm : sourceContinue * own * phantom ≤ own * phantom := by
    nlinarith [mul_nonneg hown0 hphantom0]
  change |_ - _| ≤ _
  rw [hidentity]
  calc
    |mismatch + sourceContinue * own * phantom| ≤
        |mismatch| + |sourceContinue * own * phantom| := abs_add_le _ _
    _ = |mismatch| + sourceContinue * own * phantom := by
      rw [abs_of_nonneg hterm0]
    _ ≤ quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 +
          own * phantom := add_le_add hmismatch hterm
    _ = _ := rfl

/-- In the diffuse range, product rescaling preserves at least half of each
player's conditioned opponent charge. -/
theorem half_conditionedOpponentWeight_le_rescaledRoot_opponentAbsorption
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1) :
    quittingTailConditionedOpponentWeight roots time who / 2 ≤
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
  let opponent := quittingTailConditionedOpponentWeight roots time who
  let total := quittingTailDiffuseRescaledOpponentTotal roots time who
  have hopponentTotal : opponent ≤ total :=
    quittingTailConditionedOpponentWeight_le_rescaledOpponentTotal
      roots time who hpositive
  have htotalOne : total ≤ 1 :=
    (quittingTailDiffuseRescaledOpponentTotal_le_total
      roots time who hpositive).trans <|
      (quittingTailDiffuseRescaledTotal_le_card_mul_conditionedWeight
        roots time hpositive).trans hsmall
  have htotalNonneg : 0 ≤ total := by
    unfold total quittingTailDiffuseRescaledOpponentTotal
    exact Finset.sum_nonneg fun other _ ↦
      quittingTailDiffuseRescaledHazard_nonneg roots time other hpositive
  have hbonferroni :=
    quittingTailDiffuseRescaledOpponentTotal_sub_sq_div_two_le_opponentAbsorption
      roots time who hpositive
  change opponent / 2 ≤
    quittingRootOpponentAbsorptionMass
      (quittingTailDiffuseRescaledRoot roots time hpositive) who
  nlinarith [sq_nonneg total]

/-- The time-indexed product path obtained by diffuse rescaling. -/
def quittingTailDiffuseRescaledRoots
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time) :
    ℕ → ι → PMF Bool :=
  fun time ↦ quittingTailDiffuseRescaledRoot roots time (hpositive time)

theorem quittingTailConditionedOpponentWeight_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedOpponentWeight roots time who := by
  unfold quittingTailConditionedOpponentWeight
  exact div_nonneg
    (quittingRootAbsorptionMass_nonneg
      (Function.update (roots time) who (PMF.pure false)))
    hpositive.le

/-- **Deleted-clock preservation under diffuse product rescaling.**  If the
conditioned opponent charge of `who` is nonsummable, then the rescaled
product path's opponent survival vanishes.  The only smallness needed is the
late diffuse range `card(I) * alpha ≤ 1`; no summability of the mesh itself
is assumed.

This theorem isolates the genuine occupation requirement.  Completeness of
the joint conditioned clock alone does not imply this playerwise hypothesis:
one owner may carry essentially all of the hazard. -/
theorem tendsto_zero_opponentSurvivalWeight_quittingTailDiffuseRescaledRoots
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (hsmall : ∀ time, Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (who : ι) (start : ℕ)
    (hdiverges : ¬Summable (fun offset ↦
      quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    Filter.Tendsto
      (quittingOpponentSurvivalWeight
        (quittingTailDiffuseRescaledRoots roots hpositive) who start)
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
  intro htarget
  apply hdiverges
  have hmajor : Summable (fun offset ↦
      2 * quittingOpponentClockCharge
        (quittingTailDiffuseRescaledRoots roots hpositive) who
          (start + offset)) :=
    htarget.mul_left 2
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro offset
    exact quittingTailConditionedOpponentWeight_nonneg
      roots (start + offset) who (hpositive (start + offset))
  · intro offset
    have hhalf :=
      half_conditionedOpponentWeight_le_rescaledRoot_opponentAbsorption
        roots (start + offset) who (hpositive (start + offset))
          (hsmall (start + offset))
    have hhalf' : quittingTailConditionedOpponentWeight
          roots (start + offset) who / 2 ≤
        quittingOpponentClockCharge
          (quittingTailDiffuseRescaledRoots roots hpositive) who
            (start + offset) := by
      simpa [quittingOpponentClockCharge,
        quittingTailDiffuseRescaledRoots] using hhalf
    nlinarith

end GameTheory
