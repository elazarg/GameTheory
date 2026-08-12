/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonMixtureCompiler
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling

/-!
# The corrected homogeneous LCP branch: algebra and strategic boundary

This file isolates what the homogeneous branch of the corrected normal-core
gate actually supplies.

A homogeneous simplex solution on the corrected normal core extends by zero
to a homogeneous simplex solution on the full singleton comparison matrix.
The only nontrivial point is an abnormal row: every corrected-normal owner
has a strictly positive entry in such a row.  This follows directly from the
recursive definition, without choosing a stabilization time.

The extended solution gives a complementary singleton mixture.  If it is a
vertex, its owner belongs to the corrected normal core and the landed
two-scale owner/blocker construction applies.  Otherwise small stationary
hazards along the simplex direction give terminal approximate equilibria:
the prescribed value, immediate-Quit value, and refusal value all converge to
the same complementary singleton mixture.  These two cases close the bare
homogeneous matrix branch without a punishment-floor hypothesis.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset Math.LinearProgramming
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSoloReward_eq_singletonTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    quittingSoloReward reward owner who =
      reward (quittingSingletonTerminal owner) who := by
  unfold quittingSoloReward quittingSingletonTerminal
  apply congrArg (fun terminal => reward terminal who)
  apply Subtype.ext
  rfl

/-- Extend a weight on the corrected normal core by zero off the core. -/
def extendNormalWeight (M : ι → ι → ℝ)
    (weight : normalCore M → ℝ) : ι → ℝ :=
  fun who => if hwho : who ∈ normalCore M then weight ⟨who, hwho⟩ else 0

@[simp] theorem extendNormalWeight_of_mem
    (M : ι → ι → ℝ) (weight : normalCore M → ℝ)
    {who : ι} (hwho : who ∈ normalCore M) :
    extendNormalWeight M weight who = weight ⟨who, hwho⟩ := by
  simp [extendNormalWeight, hwho]

@[simp] theorem extendNormalWeight_of_notMem
    (M : ι → ι → ℝ) (weight : normalCore M → ℝ)
    {who : ι} (hwho : who ∉ normalCore M) :
    extendNormalWeight M weight who = 0 := by
  simp [extendNormalWeight, hwho]

/-- Zero extension preserves simplex mass. -/
def extendNormalSimplex (M : ι → ι → ℝ)
    (weight : stdSimplex ℝ (normalCore M)) : stdSimplex ℝ ι := by
  classical
  refine ⟨extendNormalWeight M weight.val, ?_, ?_⟩
  · intro who
    by_cases hwho : who ∈ normalCore M
    · simpa [extendNormalWeight, hwho] using weight.property.1 ⟨who, hwho⟩
    · simp [extendNormalWeight, hwho]
  · calc
      (∑ who, extendNormalWeight M weight.val who) =
          ∑ who ∈ normalCore M, extendNormalWeight M weight.val who := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro who _ hwho
            exact extendNormalWeight_of_notMem M weight.val hwho
      _ = ∑ who : normalCore M, weight.val who := by
        calc
          (∑ who ∈ normalCore M, extendNormalWeight M weight.val who) =
              ∑ who : normalCore M,
                extendNormalWeight M weight.val who.1 :=
            Finset.sum_subtype (normalCore M) (fun _ => Iff.rfl)
              (extendNormalWeight M weight.val)
          _ = ∑ who : normalCore M, weight.val who := by
            apply Finset.sum_congr rfl
            intro who _
            exact extendNormalWeight_of_mem M weight.val who.property
      _ = 1 := weight.property.2

@[simp] theorem extendNormalSimplex_apply_of_mem
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ (normalCore M))
    {who : ι} (hwho : who ∈ normalCore M) :
    (extendNormalSimplex M weight).val who = weight.val ⟨who, hwho⟩ := by
  simp [extendNormalSimplex, hwho]

@[simp] theorem extendNormalSimplex_apply_of_notMem
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ (normalCore M))
    {who : ι} (hwho : who ∉ normalCore M) :
    (extendNormalSimplex M weight).val who = 0 := by
  simp [extendNormalSimplex, hwho]

/-- If a row lies outside the corrected normal core, every column belonging
to the core is strictly positive in that row.  Otherwise that fixed core
column would witness, inductively, that the row survives every layer. -/
theorem normalCore_entry_pos_of_notMem
    (M : ι → ι → ℝ) {who owner : ι}
    (hwho : who ∉ normalCore M) (howner : owner ∈ normalCore M) :
    0 < M who owner := by
  have hne : owner ≠ who := by
    intro heq
    subst owner
    exact hwho howner
  have hnotle : ¬ M who owner ≤ 0 := by
    intro hle
    apply hwho
    rw [mem_normalCore]
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        exact (mem_normalLayer_succ M n who).2
          ⟨ih, owner, (mem_normalCore M owner).1 howner n, hne, hle⟩
  exact lt_of_not_ge hnotle

/-- On a corrected-normal row, zero extension reproduces the principal LCP
residual exactly. -/
theorem singletonLCPResidual_extendNormalSimplex_of_mem
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ (normalCore M))
    (who : normalCore M) :
    singletonLCPResidual M (extendNormalSimplex M weight) who.1 =
      singletonLCPResidual (normalPlayerMatrix M) weight who := by
  classical
  unfold singletonLCPResidual wsum dotProduct normalPlayerMatrix principalMatrix
  calc
    (∑ owner,
        (extendNormalSimplex M weight).val owner * M who.1 owner) =
        ∑ owner ∈ normalCore M,
          (extendNormalSimplex M weight).val owner * M who.1 owner := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro owner _ howner
      rw [extendNormalSimplex_apply_of_notMem M weight howner, zero_mul]
    _ = ∑ owner : normalCore M,
        weight.val owner * M who.1 owner.1 := by
      calc
        (∑ owner ∈ normalCore M,
            (extendNormalSimplex M weight).val owner * M who.1 owner) =
            ∑ owner : normalCore M,
              (extendNormalSimplex M weight).val owner.1 * M who.1 owner.1 :=
          Finset.sum_subtype (normalCore M) (fun _ => Iff.rfl)
            (fun owner => (extendNormalSimplex M weight).val owner * M who.1 owner)
        _ = ∑ owner : normalCore M,
            weight.val owner * M who.1 owner.1 := by
          apply Finset.sum_congr rfl
          intro owner _
          rw [extendNormalSimplex_apply_of_mem M weight owner.property]

/-- Off the corrected normal core, the zero-extended residual is
nonnegative (indeed it is a convex sum of strictly positive core entries). -/
theorem singletonLCPResidual_extendNormalSimplex_nonneg_of_notMem
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ (normalCore M))
    {who : ι} (hwho : who ∉ normalCore M) :
    0 ≤ singletonLCPResidual M (extendNormalSimplex M weight) who := by
  classical
  unfold singletonLCPResidual wsum dotProduct
  apply Finset.sum_nonneg
  intro owner _
  by_cases howner : owner ∈ normalCore M
  · exact mul_nonneg ((extendNormalSimplex M weight).property.1 owner)
      (normalCore_entry_pos_of_notMem M hwho howner).le
  · change 0 ≤ (extendNormalSimplex M weight).val owner * M who owner
    rw [extendNormalSimplex_apply_of_notMem M weight howner, zero_mul]

/-- A homogeneous solution on the corrected normal core extends to a
homogeneous solution of the full singleton comparison matrix. -/
theorem singletonLCPFeasible_of_normalPlayerMatrix
    (M : ι → ι → ℝ)
    (homogeneous : SingletonLCPFeasible (normalPlayerMatrix M)) :
    SingletonLCPFeasible M := by
  classical
  obtain ⟨weight, hresidual, hcomplementary⟩ := homogeneous
  refine ⟨extendNormalSimplex M weight, ?_, ?_⟩
  · intro who
    by_cases hwho : who ∈ normalCore M
    · rw [singletonLCPResidual_extendNormalSimplex_of_mem M weight ⟨who, hwho⟩]
      exact hresidual ⟨who, hwho⟩
    · exact singletonLCPResidual_extendNormalSimplex_nonneg_of_notMem
        M weight hwho
  · intro who
    by_cases hwho : who ∈ normalCore M
    · rw [singletonLCPResidual_extendNormalSimplex_of_mem M weight ⟨who, hwho⟩,
        extendNormalSimplex_apply_of_mem M weight hwho]
      exact hcomplementary ⟨who, hwho⟩
    · rw [extendNormalSimplex_apply_of_notMem M weight hwho, zero_mul]

/-- The full homogeneous witness attached to a corrected homogeneous matrix
branch. -/
theorem HomogeneousMatrixBranch.full_homogeneous
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (branch : HomogeneousMatrixBranch reward) :
    SingletonLCPFeasible (normalizedSoloMatrix reward) := by
  exact singletonLCPFeasible_of_normalPlayerMatrix
    (normalizedSoloMatrix reward) branch.homogeneous

/-- A full homogeneous LCP witness gives exactly the singleton-mixture floor
and pinning facts consumed by the face-circulation compiler. -/
theorem fullHomogeneousWitness_singletonMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι)
    (hresidual : ∀ who,
      0 ≤ singletonLCPResidual (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who,
      weight.val who *
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0) :
    (∀ who, reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward weight.val who) ∧
      (∀ who, 0 < weight.val who →
        quittingSingletonMixture reward weight.val who =
          reward (quittingSingletonTerminal who) who) := by
  classical
  have hbalance : ∀ who,
      singletonLCPResidual (normalizedSoloMatrix reward) weight who =
        quittingSingletonMixture reward weight.val who -
          reward (quittingSingletonTerminal who) who := by
    intro who
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    unfold singletonLCPResidual wsum dotProduct
      quittingProjectiveLCPMatrix quittingSingletonMixture
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    change (∑ owner, weight.val owner *
        reward (quittingSingletonTerminal owner) who) -
      (∑ owner, weight.val owner) *
        reward (quittingSingletonTerminal who) who = _
    rw [weight.property.2, one_mul]
  constructor
  · intro who
    have := hresidual who
    rw [hbalance who] at this
    linarith
  · intro who hpositive
    have hzero : singletonLCPResidual
        (normalizedSoloMatrix reward) weight who = 0 := by
      rcases mul_eq_zero.mp (hcomplementary who) with h | h
      · exact False.elim ((ne_of_gt hpositive) h)
      · exact h
    rw [hbalance who] at hzero
    linarith

/-! ## Small-hazard realization of a non-vertex homogeneous witness -/

/-- Scale a simplex direction into the stationary hazard cube. -/
def homogeneousScaledRoot (weight : stdSimplex ℝ ι)
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    ι → PMF Bool := fun who =>
  quittingHazardCoin (scale * weight.val who)
    (mul_nonneg hscale0 (weight.property.1 who)) (by
      have hweight : weight.val who ≤ 1 := by
        rw [← weight.property.2]
        exact Finset.single_le_sum
          (fun owner _ => weight.property.1 owner) (Finset.mem_univ who)
      nlinarith)

omit [DecidableEq ι] in
@[simp] theorem homogeneousScaledRoot_true_toReal
    (weight : stdSimplex ℝ ι) (scale : ℝ)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (who : ι) :
    ((homogeneousScaledRoot weight scale hscale0 hscale1 who) true).toReal =
      scale * weight.val who := by
  simp [homogeneousScaledRoot]

omit [DecidableEq ι] in
@[simp] theorem homogeneousScaledRoot_false_toReal
    (weight : stdSimplex ℝ ι) (scale : ℝ)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (who : ι) :
    ((homogeneousScaledRoot weight scale hscale0 hscale1 who) false).toReal =
      1 - scale * weight.val who := by
  simp [homogeneousScaledRoot]

omit [DecidableEq ι] in
theorem quittingStationaryTotalHazard_homogeneousScaledRoot
    (weight : stdSimplex ℝ ι) (scale : ℝ)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    quittingStationaryTotalHazard
        (homogeneousScaledRoot weight scale hscale0 hscale1) = scale := by
  unfold quittingStationaryTotalHazard
  simp_rw [homogeneousScaledRoot_true_toReal]
  rw [← Finset.mul_sum, weight.property.2, mul_one]

omit [DecidableEq ι] in
theorem quittingStationarySingletonDirectionBarycenter_homogeneousScaledRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (hscale : scale ≠ 0)
    (who : ι) :
    quittingStationarySingletonDirectionBarycenter reward
        (homogeneousScaledRoot weight scale hscale0 hscale1) who =
      quittingSingletonMixture reward weight.val who := by
  unfold quittingStationarySingletonDirectionBarycenter
    quittingSingletonMixture
  rw [quittingStationaryTotalHazard_homogeneousScaledRoot]
  apply Finset.sum_congr rfl
  intro owner _
  rw [homogeneousScaledRoot_true_toReal]
  field_simp
  rw [quittingSoloReward_eq_singletonTerminal]

/-- Deleting one coordinate from a scaled simplex direction leaves total
hazard `scale * (1 - weight who)`. -/
theorem quittingStationaryTotalHazard_update_homogeneousScaledRoot
    (weight : stdSimplex ℝ ι) (scale : ℝ)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (who : ι) :
    quittingStationaryTotalHazard
        (Function.update (homogeneousScaledRoot weight scale hscale0 hscale1)
          who (PMF.pure false)) = scale * (1 - weight.val who) := by
  classical
  unfold quittingStationaryTotalHazard
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  have herase :
      ∑ owner ∈ Finset.univ.erase who,
          ((Function.update
            (homogeneousScaledRoot weight scale hscale0 hscale1) who
              (PMF.pure false)) owner true).toReal =
        ∑ owner ∈ Finset.univ.erase who, scale * weight.val owner := by
    apply Finset.sum_congr rfl
    intro owner howner
    have hne : owner ≠ who := (Finset.mem_erase.mp howner).1
    simp [Function.update, hne]
  rw [herase]
  simp only [Finset.mem_univ, Finset.sum_erase_eq_sub,
    Function.update_self, PMF.pure_apply, Bool.true_eq_false, reduceIte,
    ENNReal.toReal_zero, add_zero]
  rw [← Finset.mul_sum, weight.property.2]
  ring

/-- The direction barycenter after deleting `who` is the original singleton
mixture whenever `who` has zero weight, or whenever the original mixture is
pinned to `who`'s singleton payoff. -/
theorem quittingStationarySingletonDirectionBarycenter_update_scaled_eq_mixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (hscale : scale ≠ 0)
    (who : ι) (hweight : weight.val who < 1)
    (hpinned : weight.val who = 0 ∨
      quittingSingletonMixture reward weight.val who =
        reward (quittingSingletonTerminal who) who) :
    quittingStationarySingletonDirectionBarycenter reward
        (Function.update (homogeneousScaledRoot weight scale hscale0 hscale1)
          who (PMF.pure false)) who =
      quittingSingletonMixture reward weight.val who := by
  classical
  let mix := quittingSingletonMixture reward weight.val who
  let solo := reward (quittingSingletonTerminal who) who
  have hden : scale * (1 - weight.val who) ≠ 0 :=
    mul_ne_zero hscale (sub_ne_zero.mpr (ne_of_gt hweight))
  unfold quittingStationarySingletonDirectionBarycenter
  rw [quittingStationaryTotalHazard_update_homogeneousScaledRoot]
  have hsumErase :
      ∑ owner ∈ Finset.univ.erase who,
          weight.val owner * quittingSoloReward reward owner who =
        mix - weight.val who * solo := by
    have hsum := Finset.sum_erase_add
      (s := Finset.univ)
      (f := fun owner => weight.val owner * quittingSoloReward reward owner who)
      (Finset.mem_univ who)
    have hsub := eq_sub_of_add_eq hsum
    dsimp only [mix, solo]
    unfold quittingSingletonMixture
    simpa only [quittingSoloReward_eq_singletonTerminal] using hsub
  calc
    (∑ owner,
        (((Function.update
          (homogeneousScaledRoot weight scale hscale0 hscale1) who
            (PMF.pure false)) owner true).toReal /
              (scale * (1 - weight.val who))) *
          quittingSoloReward reward owner who) =
        (mix - weight.val who * solo) / (1 - weight.val who) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
      rw [show
        (((Function.update
          (homogeneousScaledRoot weight scale hscale0 hscale1) who
            (PMF.pure false)) who true).toReal /
              (scale * (1 - weight.val who))) *
            quittingSoloReward reward who who = 0 by simp, add_zero]
      have herase :
          ∑ owner ∈ Finset.univ.erase who,
              (((Function.update
                (homogeneousScaledRoot weight scale hscale0 hscale1) who
                  (PMF.pure false)) owner true).toReal /
                    (scale * (1 - weight.val who))) *
                quittingSoloReward reward owner who =
            ∑ owner ∈ Finset.univ.erase who,
              ((scale * weight.val owner) /
                    (scale * (1 - weight.val who))) *
                quittingSoloReward reward owner who := by
        apply Finset.sum_congr rfl
        intro owner howner
        have hne : owner ≠ who := (Finset.mem_erase.mp howner).1
        simp [Function.update, hne]
      rw [herase]
      calc
        (∑ owner ∈ Finset.univ.erase who,
            scale * weight.val owner / (scale * (1 - weight.val who)) *
              quittingSoloReward reward owner who) =
            (∑ owner ∈ Finset.univ.erase who,
              weight.val owner * quittingSoloReward reward owner who) /
                (1 - weight.val who) := by
                  rw [Finset.sum_div]
                  apply Finset.sum_congr rfl
                  intro owner _
                  field_simp
        _ = (mix - weight.val who * solo) / (1 - weight.val who) := by
          rw [hsumErase]
        _ = (mix - weight.val who * solo) / (1 - weight.val who) := rfl
    _ = mix := by
      rcases hpinned with hzero | hpin
      · rw [hzero]
        simp
      · dsimp only [mix] at hpin ⊢
        dsimp only [solo]
        rw [hpin]
        field_simp [sub_ne_zero.mpr (ne_of_gt hweight)]

omit [DecidableEq ι] in
/-- The one-stage absorption probability of a product root is at most the sum
of its marginal quit hazards. -/
theorem quittingRootAbsorptionMass_le_stationaryTotalHazard
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ quittingStationaryTotalHazard root := by
  rw [← rootOfHazard_hazardOfRoot root,
    quittingRootAbsorptionMass_rootOfHazard]
  simpa [quittingStationaryTotalHazard, rootOfHazard,
    Math.PMFProduct.continueMass] using
      (Math.one_sub_prod_one_sub_le_sum (hazardOfRoot root) Finset.univ
        (fun owner _ => hazardOfRoot_nonneg root owner)
        (fun owner _ => hazardOfRoot_le_one root owner))

omit [DecidableEq ι] in
/-- Positive total stationary hazard forces strict one-stage contraction. -/
theorem quittingStationaryContinueMass_lt_one_of_totalHazard_pos
    (root : ι → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root) :
    quittingStationaryContinueMass root < 1 := by
  unfold quittingStationaryTotalHazard at hpositive
  obtain ⟨owner, _, howner⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun player _ => ENNReal.toReal_nonneg)).mp hpositive
  have hle := quittingStationaryContinueMass_le_ownContinueProbability
    root owner
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  linarith

/-- Every player faces contraction along a non-vertex simplex direction. -/
theorem homogeneousScaledRoot_fixedOpponents_contracts
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hnonvertex : ∀ who, weight.val who < 1) :
    ∀ who, quittingStationaryFixedOpponentsContinueMass
      (homogeneousScaledRoot weight scale hscale.le hscale1) who < 1 := by
  intro who
  apply quittingStationaryContinueMass_lt_one_of_totalHazard_pos
  rw [quittingStationaryTotalHazard_update_homogeneousScaledRoot]
  exact mul_pos hscale (sub_pos.mpr (hnonvertex who))

omit [DecidableEq ι] in
/-- The stationary value of a scaled simplex direction is close to its
singleton mixture. -/
theorem abs_homogeneousScaledRoot_terminalPayoff_sub_mixture_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale : 0 < scale) (hscaleHalf : scale ≤ 1 / 2) (who : ι) :
    let root := homogeneousScaledRoot weight scale hscale.le
      (hscaleHalf.trans (by norm_num))
    |quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who -
      quittingSingletonMixture reward weight.val who| ≤
        6 * quittingRewardBound reward * scale := by
  dsimp only
  let root := homogeneousScaledRoot weight scale hscale.le
    (hscaleHalf.trans (by norm_num))
  have htotal := quittingStationaryTotalHazard_homogeneousScaledRoot
    weight scale hscale.le (hscaleHalf.trans (by norm_num))
  have h := abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
    reward (abs_reward_le_quittingRewardBound reward) root who
      (by rw [htotal]; exact hscale) (by rw [htotal]; exact hscaleHalf)
  rw [quittingStationarySingletonDirectionBarycenter_homogeneousScaledRoot
    reward weight hscale.le (hscaleHalf.trans (by norm_num)) hscale.ne'] at h
  simpa [root, htotal] using h

/-- Immediate quitting against the scaled direction is within the uniform
`8 M scale` envelope of the prescribed stationary payoff. -/
theorem homogeneousScaledRoot_quitValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale : 0 < scale) (hscaleHalf : scale ≤ 1 / 2)
    (hmixFloor : ∀ who,
      reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward weight.val who) (who : ι) :
    let root := homogeneousScaledRoot weight scale hscale.le
      (hscaleHalf.trans (by norm_num))
    quittingStationaryFixedOpponentsQuitValue reward root who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
        8 * quittingRewardBound reward * scale := by
  dsimp only
  let root := homogeneousScaledRoot weight scale hscale.le
    (hscaleHalf.trans (by norm_num))
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hquit := abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
    (reward := reward) root who hM (abs_reward_le_quittingRewardBound reward)
  have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass root who
  have habsorption := quittingRootAbsorptionMass_le_stationaryTotalHazard root
  have htotal := quittingStationaryTotalHazard_homogeneousScaledRoot
    weight scale hscale.le (hscaleHalf.trans (by norm_num))
  rw [htotal] at habsorption
  have hpayoff := abs_homogeneousScaledRoot_terminalPayoff_sub_mixture_le
    reward weight hscale hscaleHalf who
  dsimp only at hpayoff
  have hquitUpper := (abs_le.mp hquit).2
  have hpayoffLower := (abs_le.mp hpayoff).1
  calc
    quittingStationaryFixedOpponentsQuitValue reward root who ≤
        reward (quittingSingletonTerminal who) who +
          2 * M * quittingRootOpponentAbsorptionMass root who := by linarith
    _ ≤ reward (quittingSingletonTerminal who) who + 2 * M * scale := by
      gcongr
      exact hopponent.trans habsorption
    _ ≤ quittingSingletonMixture reward weight.val who + 2 * M * scale := by
      gcongr
      exact hmixFloor who
    _ ≤ quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who + 8 * M * scale := by
      dsimp only [M] at hpayoffLower ⊢
      linarith

/-- Refusing one's prescribed hazard is within the uniform `12 M scale`
envelope when the complementary direction is non-vertex. -/
theorem homogeneousScaledRoot_neverValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale : 0 < scale) (hscaleHalf : scale ≤ 1 / 2)
    (hactivePinned : ∀ who, 0 < weight.val who →
      quittingSingletonMixture reward weight.val who =
        reward (quittingSingletonTerminal who) who)
    (hnonvertex : ∀ who, weight.val who < 1) (who : ι) :
    let root := homogeneousScaledRoot weight scale hscale.le
      (hscaleHalf.trans (by norm_num))
    quittingStationaryNeverValue
        (quittingStationaryFixedOpponentsContinueReward reward root who)
        (quittingStationaryFixedOpponentsContinueMass root who) ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
        12 * quittingRewardBound reward * scale := by
  dsimp only
  let root := homogeneousScaledRoot weight scale hscale.le
    (hscaleHalf.trans (by norm_num))
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hweight0 := weight.property.1 who
  have htotal := quittingStationaryTotalHazard_update_homogeneousScaledRoot
    weight scale hscale.le (hscaleHalf.trans (by norm_num)) who
  have hpos : 0 < quittingStationaryTotalHazard
      (Function.update root who (PMF.pure false)) := by
    rw [htotal]
    exact mul_pos hscale (sub_pos.mpr (hnonvertex who))
  have hhalf : quittingStationaryTotalHazard
      (Function.update root who (PMF.pure false)) ≤ 1 / 2 := by
    rw [htotal]
    calc
      scale * (1 - weight.val who) ≤ scale * 1 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hscale.le
      _ ≤ 1 / 2 := by simpa using hscaleHalf
  have hbary :=
    quittingStationarySingletonDirectionBarycenter_update_scaled_eq_mixture
      reward weight hscale.le (hscaleHalf.trans (by norm_num)) hscale.ne'
        who (hnonvertex who) (by
          by_cases hz : weight.val who = 0
          · exact Or.inl hz
          · exact Or.inr (hactivePinned who
              (lt_of_le_of_ne hweight0 (Ne.symm hz))))
  have hcontinue := abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
    reward (abs_reward_le_quittingRewardBound reward)
      (Function.update root who (PMF.pure false)) who hpos hhalf
  rw [hbary] at hcontinue
  have hpayoff := abs_homogeneousScaledRoot_terminalPayoff_sub_mixture_le
    reward weight hscale hscaleHalf who
  dsimp only at hpayoff
  have hnever :
      quittingStationaryNeverValue
          (quittingStationaryFixedOpponentsContinueReward reward root who)
          (quittingStationaryFixedOpponentsContinueMass root who) =
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (Function.update root who (PMF.pure false))) who := by
    unfold quittingStationaryNeverValue
      quittingStationaryFixedOpponentsContinueReward
      quittingStationaryFixedOpponentsContinueMass
    symm
    exact quittingTerminalPayoff_stationary_eq_absorbingContribution_div
      reward (Function.update root who (PMF.pure false)) who
        (quittingStationaryContinueMass_lt_one_of_totalHazard_pos _ hpos)
  rw [hnever]
  have hcontinueUpper := (abs_le.mp hcontinue).2
  have hpayoffLower := (abs_le.mp hpayoff).1
  rw [htotal] at hcontinueUpper
  have herror : 6 * M * (scale * (1 - weight.val who)) ≤ 6 * M * scale := by
    have hfactor : scale * (1 - weight.val who) ≤ scale := by
      calc
        scale * (1 - weight.val who) ≤ scale * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith) hscale.le
        _ = scale := mul_one scale
    exact mul_le_mul_of_nonneg_left hfactor (by positivity)
  dsimp only [M] at hcontinueUpper hpayoffLower herror ⊢
  linarith

/-- The full stationary behavioral cap is asymptotically realized by every
non-vertex complementary homogeneous direction. -/
theorem isεAsymptoticNash_homogeneousScaledRoot_of_nonvertex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι) {scale : ℝ}
    (hscale : 0 < scale) (hscaleHalf : scale ≤ 1 / 2)
    (hmixFloor : ∀ who,
      reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward weight.val who)
    (hactivePinned : ∀ who, 0 < weight.val who →
      quittingSingletonMixture reward weight.val who =
        reward (quittingSingletonTerminal who) who)
    (hnonvertex : ∀ who, weight.val who < 1) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (12 * quittingRewardBound reward * scale)
        (quittingStationaryProfile reward root) := by
  let root := homogeneousScaledRoot weight scale hscale.le
    (hscaleHalf.trans (by norm_num))
  refine ⟨root, ?_⟩
  have hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 := by
    dsimp only [root]
    exact homogeneousScaledRoot_fixedOpponents_contracts weight hscale
      (hscaleHalf.trans (by norm_num)) hnonvertex
  have hcap : ∀ who, quittingStationaryUnilateralCap reward root who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
        12 * quittingRewardBound reward * scale := by
    intro who
    unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    apply max_le
    · have hquit : quittingStationaryFixedOpponentsQuitValue reward root who ≤
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
            8 * quittingRewardBound reward * scale := by
        dsimp only [root]
        exact homogeneousScaledRoot_quitValue_le reward weight hscale hscaleHalf
          hmixFloor who
      exact hquit.trans (by
        have hM := quittingRewardBound_nonneg reward
        nlinarith)
    · have hnever : quittingStationaryNeverValue
            (quittingStationaryFixedOpponentsContinueReward reward root who)
            (quittingStationaryFixedOpponentsContinueMass root who) ≤
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
            12 * quittingRewardBound reward * scale := by
        dsimp only [root]
        exact homogeneousScaledRoot_neverValue_le reward weight hscale hscaleHalf
          hactivePinned hnonvertex who
      exact hnever
  exact isεAsymptoticNash_stationary_of_unilateralCap_le reward root
    (12 * quittingRewardBound reward * scale) hcontracts hcap

/-- A non-vertex homogeneous witness gives terminal approximate equilibria at
every positive accuracy. -/
theorem terminalNash_all_errors_of_nonvertexHomogeneousWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι)
    (hresidual : ∀ who,
      0 ≤ singletonLCPResidual (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who,
      weight.val who *
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0)
    (hnonvertex : ∀ who, weight.val who < 1) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨hmixFloor, hactivePinned⟩ :=
    fullHomogeneousWitness_singletonMixture reward weight
      hresidual hcomplementary
  intro ε hε
  let M := quittingRewardBound reward
  let scale := ε / (24 * M + 2 * ε)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hden : 0 < 24 * M + 2 * ε := by positivity
  have hscale : 0 < scale := div_pos hε hden
  have hscaleHalf : scale ≤ 1 / 2 := by
    dsimp only [scale]
    rw [div_le_iff₀ hden]
    linarith
  have herror : 12 * M * scale < ε := by
    dsimp only [scale]
    rw [show 12 * M * (ε / (24 * M + 2 * ε)) =
      (12 * M * ε) / (24 * M + 2 * ε) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hε hε]
  obtain ⟨root, hnash⟩ :=
    isεAsymptoticNash_homogeneousScaledRoot_of_nonvertex
      reward weight hscale hscaleHalf hmixFloor hactivePinned hnonvertex
  refine ⟨quittingStationaryProfile reward root, ?_⟩
  exact hnash.mono herror.le

/-- A non-vertex homogeneous witness produces an ordinary uniform-equilibrium
payoff by the terminal approximate-equilibrium consumer. -/
theorem exists_uniformEquilibriumPayoff_of_nonvertexHomogeneousWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : stdSimplex ℝ ι)
    (hresidual : ∀ who,
      0 ≤ singletonLCPResidual (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who,
      weight.val who *
        singletonLCPResidual (normalizedSoloMatrix reward) weight who = 0)
    (hnonvertex : ∀ who, weight.val who < 1) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  exact terminalNash_all_errors_of_nonvertexHomogeneousWitness
    reward weight hresidual hcomplementary hnonvertex

omit [DecidableEq ι] in
/-- A simplex coordinate of mass one turns its homogeneous LCP residual into
the corresponding matrix column. -/
theorem singletonLCPResidual_eq_column_of_weight_eq_one
    (M : ι → ι → ℝ) (weight : stdSimplex ℝ ι)
    {owner : ι} (howner : weight.val owner = 1) (who : ι) :
    singletonLCPResidual M weight who = M who owner := by
  classical
  have hownerVal : weight.val owner = 1 := howner
  change weight owner = 1 at howner
  have hzero : ∀ other, other ≠ owner → weight other = 0 := by
    intro other hne
    have hsumErase : ∑ player ∈ Finset.univ.erase owner,
        weight.val player = 0 := by
      have hsum := Finset.sum_erase_add (s := Finset.univ)
        (f := weight.val) (Finset.mem_univ owner)
      rw [hownerVal, weight.property.2] at hsum
      linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun player _ => weight.property.1 player)).mp hsumErase
    exact hall other (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ other⟩)
  unfold singletonLCPResidual wsum dotProduct
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ owner)]
  rw [howner, one_mul]
  have herase : ∑ other ∈ Finset.univ.erase owner,
      weight other * M who other = 0 := by
    apply Finset.sum_eq_zero
    intro other hother
    rw [hzero other (Finset.mem_erase.mp hother).1, zero_mul]
  rw [herase, zero_add]

/-- **Homogeneous matrix producer.**  The corrected homogeneous branch always
produces an ordinary uniform-equilibrium payoff.  A vertex witness is handled
by the landed two-scale owner/blocker construction; every non-vertex witness
is realized by stationary hazards tending to zero along its simplex
direction. -/
theorem exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (branch : HomogeneousMatrixBranch reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  let matrix := normalizedSoloMatrix reward
  obtain ⟨weight, hresidual, hcomplementary⟩ := branch.homogeneous
  let fullWeight := extendNormalSimplex matrix weight
  have hfullResidual : ∀ who,
      0 ≤ singletonLCPResidual matrix fullWeight who := by
    intro who
    by_cases hwho : who ∈ normalCore matrix
    · rw [singletonLCPResidual_extendNormalSimplex_of_mem
        matrix weight ⟨who, hwho⟩]
      exact hresidual ⟨who, hwho⟩
    · exact singletonLCPResidual_extendNormalSimplex_nonneg_of_notMem
        matrix weight hwho
  have hfullComplementary : ∀ who,
      fullWeight.val who * singletonLCPResidual matrix fullWeight who = 0 := by
    intro who
    by_cases hwho : who ∈ normalCore matrix
    · rw [singletonLCPResidual_extendNormalSimplex_of_mem
        matrix weight ⟨who, hwho⟩,
        extendNormalSimplex_apply_of_mem matrix weight hwho]
      exact hcomplementary ⟨who, hwho⟩
    · rw [extendNormalSimplex_apply_of_notMem matrix weight hwho, zero_mul]
  by_cases hvertex : ∃ owner, fullWeight.val owner = 1
  · obtain ⟨owner, howner⟩ := hvertex
    have hownerCore : owner ∈ normalCore matrix := by
      by_contra hnot
      have hzero := extendNormalSimplex_apply_of_notMem matrix weight hnot
      rw [howner] at hzero
      norm_num at hzero
    obtain ⟨blocker, hne, hblocker⟩ :=
      exists_firstLayer_blocker_of_mem_normalLayer matrix (last := 1)
        (by norm_num) ((mem_normalCore matrix owner).1 hownerCore 1)
    have hcolumn : ∀ who, 0 ≤ matrix who owner := by
      intro who
      rw [← singletonLCPResidual_eq_column_of_weight_eq_one
        matrix fullWeight howner who]
      exact hfullResidual who
    exact exists_uniformEquilibriumPayoff_of_nonnegative_column
      reward hne hcolumn hblocker
  · have hnonvertex : ∀ who, fullWeight.val who < 1 := by
      intro who
      have hle : fullWeight.val who ≤ 1 := by
        rw [← fullWeight.property.2]
        exact Finset.single_le_sum
          (fun owner _ => fullWeight.property.1 owner) (Finset.mem_univ who)
      exact lt_of_le_of_ne hle (fun heq => hvertex ⟨who, heq⟩)
    exact exists_uniformEquilibriumPayoff_of_nonvertexHomogeneousWitness
      reward fullWeight hfullResidual hfullComplementary hnonvertex

end QuittingLCPClassification
end GameTheory
