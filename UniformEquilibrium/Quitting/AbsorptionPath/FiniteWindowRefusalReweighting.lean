/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Cycles.BlockSurvival
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation

/-!
# Finite-window survival reweighting under forced Continue

Forcing player `refusing` to Continue changes two different parts of a finite
window:

* the current root is replaced by its `refusing`-deleted product root; and
* chronological survival changes from joint survival to opponent-only
  survival.

This module keeps those changes separate.  `jointOffPlayerSingletonMass`
uses the deleted current root but the original joint chronology.
`forceContinueWindow` uses the same deleted roots with the opponent-only
chronology.  The comparison is intrinsic to a finite root word: it requires
no periodicity or continuation premise.

The raw comparison is division-free.  Normalized comparisons explicitly
require a lower bound on the joint-weighted deleted absorption denominator;
positive deleted absorption alone is insufficient, because all deleted
absorption may occur only after paths on which the refusing player would
already have quit.  A zero deleted-absorption theorem handles that branch
without forming a conditional quotient.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingFiniteRootWindow

variable {roots : ℕ → ι → PMF Bool}

/-- Root sequence obtained by forcing one player to Continue forever. -/
def forceContinueRoots (roots : ℕ → ι → PMF Bool) (refusing : ι) :
    ℕ → ι → PMF Bool :=
  quittingRootSequenceUpdate roots refusing (quittingPureTimeHazard none)

/-- The same literal window in the root sequence with `refusing` forced to
Continue. -/
def forceContinueWindow (window : QuittingFiniteRootWindow roots)
    (refusing : ι) : QuittingFiniteRootWindow
      (forceContinueRoots roots refusing) where
  start := window.start
  fuel := window.fuel

/-- Deleted current root at a phase, without choosing a chronological
survival weight. -/
def offPlayerRoot (window : QuittingFiniteRootWindow roots)
    (refusing : ι) (phase : Fin window.fuel) : ι → PMF Bool :=
  Function.update (window.rootAt phase) refusing (PMF.pure false)

/-- Singleton mass at a deleted current root, weighted by the original joint
survival chronology. -/
def jointOffPlayerSingletonMass
    (window : QuittingFiniteRootWindow roots)
    (refusing owner : ι) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      quittingRootCoalitionMass (window.offPlayerRoot refusing phase) {owner}

/-- Total deleted-root absorption weighted by the original joint survival
chronology. -/
def jointOffPlayerAbsorptionMass
    (window : QuittingFiniteRootWindow roots) (refusing : ι) : ℝ :=
  ∑ phase : Fin window.fuel,
    window.survivalWeight phase *
      quittingRootAbsorptionMass (window.offPlayerRoot refusing phase)

/-- Owner occupation using joint chronology and deleted current roots. -/
def normalizedJointOffPlayerOccupation
    (window : QuittingFiniteRootWindow roots)
    (refusing owner : ι) : ℝ :=
  window.jointOffPlayerSingletonMass refusing owner /
    window.jointOffPlayerAbsorptionMass refusing

/-- The chronological triangular factor `0 + ... + (fuel - 1)`. -/
def chronologyFactor (window : QuittingFiniteRootWindow roots) : ℝ :=
  ∑ phase : Fin window.fuel, (phase.val : ℝ)

omit [Fintype ι] in
@[simp] theorem forceContinueWindow_rootAt
    (window : QuittingFiniteRootWindow roots) (refusing : ι)
    (phase : Fin window.fuel) :
    (window.forceContinueWindow refusing).rootAt phase =
      window.offPlayerRoot refusing phase := by
  rfl

/-- Joint survival of the forced-Continue word is exactly the original
opponent-only survival clock. -/
theorem forceContinueWindow_survivalWeight
    (window : QuittingFiniteRootWindow roots) (refusing : ι)
    (phase : Fin window.fuel) :
    (window.forceContinueWindow refusing).survivalWeight phase =
      quittingOpponentSurvivalWeight roots refusing window.start phase.val := by
  exact quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
    roots refusing window.start phase.val

/-- Exact refusal reweighting of singleton mass: current-root deletion and
opponent-only chronology are both visible on the right-hand side. -/
theorem forceContinueWindow_singletonMass_eq
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι) :
    (window.forceContinueWindow refusing).singletonMass owner =
      ∑ phase : Fin window.fuel,
        quittingOpponentSurvivalWeight roots refusing window.start phase.val *
          quittingRootCoalitionMass
            (window.offPlayerRoot refusing phase) {owner} := by
  unfold singletonMass
  apply Finset.sum_congr rfl
  intro phase _
  rw [forceContinueWindow_survivalWeight,
    forceContinueWindow_rootAt]

/-- Exact refusal reweighting of total absorption. -/
theorem forceContinueWindow_absorptionMass_eq
    (window : QuittingFiniteRootWindow roots) (refusing : ι) :
    (window.forceContinueWindow refusing).absorptionMass =
      ∑ phase : Fin window.fuel,
        quittingOpponentSurvivalWeight roots refusing window.start phase.val *
          quittingRootAbsorptionMass
            (window.offPlayerRoot refusing phase) := by
  unfold absorptionMass
  apply Finset.sum_congr rfl
  intro phase _
  rw [forceContinueWindow_survivalWeight,
    forceContinueWindow_rootAt]

/-- Joint-weighted deleted singleton mass is nonnegative. -/
theorem jointOffPlayerSingletonMass_nonneg
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι) :
    0 ≤ window.jointOffPlayerSingletonMass refusing owner := by
  exact Finset.sum_nonneg fun phase _ =>
    mul_nonneg (window.survivalWeight_nonneg phase)
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _)

/-- Joint-weighted deleted absorption is nonnegative. -/
theorem jointOffPlayerAbsorptionMass_nonneg
    (window : QuittingFiniteRootWindow roots) (refusing : ι) :
    0 ≤ window.jointOffPlayerAbsorptionMass refusing := by
  exact Finset.sum_nonneg fun phase _ =>
    mul_nonneg (window.survivalWeight_nonneg phase)
      (quittingRootAbsorptionMass_nonneg _)

/-- Joint chronology is pointwise dominated by refusal chronology. -/
theorem survivalWeight_le_opponentSurvivalWeight
    (window : QuittingFiniteRootWindow roots) (refusing : ι)
    (phase : Fin window.fuel) :
    window.survivalWeight phase ≤
      quittingOpponentSurvivalWeight roots refusing window.start phase.val :=
  quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
    roots refusing window.start phase.val

/-- Joint-weighted deleted singleton mass is dominated by the actual
forced-Continue singleton mass. -/
theorem jointOffPlayerSingletonMass_le_forceContinue
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι) :
    window.jointOffPlayerSingletonMass refusing owner ≤
      (window.forceContinueWindow refusing).singletonMass owner := by
  rw [window.forceContinueWindow_singletonMass_eq refusing owner]
  unfold jointOffPlayerSingletonMass
  apply Finset.sum_le_sum
  intro phase _
  exact mul_le_mul_of_nonneg_right
    (window.survivalWeight_le_opponentSurvivalWeight refusing phase)
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _)

/-- Joint-weighted deleted absorption is dominated by actual forced-Continue
absorption. -/
theorem jointOffPlayerAbsorptionMass_le_forceContinue
    (window : QuittingFiniteRootWindow roots) (refusing : ι) :
    window.jointOffPlayerAbsorptionMass refusing ≤
      (window.forceContinueWindow refusing).absorptionMass := by
  rw [window.forceContinueWindow_absorptionMass_eq refusing]
  unfold jointOffPlayerAbsorptionMass
  apply Finset.sum_le_sum
  intro phase _
  exact mul_le_mul_of_nonneg_right
    (window.survivalWeight_le_opponentSurvivalWeight refusing phase)
    (quittingRootAbsorptionMass_nonneg _)

/-- If deleted absorption is zero, both chronologies give zero deleted mass,
and every owner singleton numerator is zero. -/
theorem zero_deletedAbsorption
    (window : QuittingFiniteRootWindow roots) (refusing : ι)
    (hzero : (window.forceContinueWindow refusing).absorptionMass = 0) :
    window.jointOffPlayerAbsorptionMass refusing = 0 ∧
      (∀ owner,
        (window.forceContinueWindow refusing).singletonMass owner = 0 ∧
        window.jointOffPlayerSingletonMass refusing owner = 0) := by
  have hjoint : window.jointOffPlayerAbsorptionMass refusing = 0 := by
    apply le_antisymm
    · have hle := window.jointOffPlayerAbsorptionMass_le_forceContinue refusing
      rw [hzero] at hle
      exact hle
    · exact window.jointOffPlayerAbsorptionMass_nonneg refusing
  refine ⟨hjoint, ?_⟩
  intro owner
  have hforcedDecomposition :=
    (window.forceContinueWindow refusing).zero_or_positive_normalizedMass
  rcases hforcedDecomposition with hforced | hpositive
  · refine ⟨hforced.2.2.2 owner, ?_⟩
    apply le_antisymm
    · have hle :=
        window.jointOffPlayerSingletonMass_le_forceContinue refusing owner
      rw [hforced.2.2.2 owner] at hle
      exact hle
    · exact window.jointOffPlayerSingletonMass_nonneg refusing owner
  · rw [hzero] at hpositive
    exact (lt_irrefl 0 hpositive.1).elim

/-! ## Quantitative chronological reweighting -/

/-- Prefix product of the refusing player's own Continue probabilities. -/
def ownContinueWeight (window : QuittingFiniteRootWindow roots)
    (refusing : ι) (phase : Fin window.fuel) : ℝ :=
  ∏ offset ∈ Finset.range phase.val,
    (roots (window.start + offset) refusing false).toReal

/-- Joint chronology factors into opponent-only chronology and the refusing
player's own Continue prefix. -/
theorem survivalWeight_eq_opponent_mul_own
    (window : QuittingFiniteRootWindow roots) (refusing : ι)
    (phase : Fin window.fuel) :
    window.survivalWeight phase =
      quittingOpponentSurvivalWeight roots refusing window.start phase.val *
        window.ownContinueWeight refusing phase := by
  unfold survivalWeight ownContinueWeight
  rw [quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro offset _
  rw [quittingStationaryContinueMass_eq_deletedContinueMass_mul_own,
    quittingRootDeletedContinueMass_eq_fixedOpponents]

/-- If the refusing player's hazard is at most `rho` on the window, deletion
changes a phase's chronological survival weight by at most `phase * rho`. -/
theorem opponentSurvivalWeight_sub_survivalWeight_le
    (window : QuittingFiniteRootWindow roots) (refusing : ι) (rho : ℝ)
    (_hrho : 0 ≤ rho)
    (hown : ∀ phase : Fin window.fuel,
      (window.rootAt phase refusing true).toReal ≤ rho)
    (phase : Fin window.fuel) :
    quittingOpponentSurvivalWeight roots refusing window.start phase.val -
        window.survivalWeight phase ≤ phase.val * rho := by
  have hprefix :
      1 - window.ownContinueWeight refusing phase ≤ phase.val * rho := by
    let q : ℕ → ℝ := fun offset =>
      (roots (window.start + offset) refusing true).toReal
    have hq0 : ∀ offset ∈ Finset.range phase.val, 0 ≤ q offset :=
      fun _ _ => ENNReal.toReal_nonneg
    have hq1 : ∀ offset ∈ Finset.range phase.val, q offset ≤ 1 := by
      intro offset _
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one _ _)
    have hunion := Math.one_sub_prod_one_sub_le_sum q
      (Finset.range phase.val) hq0 hq1
    have hproduct : window.ownContinueWeight refusing phase =
        ∏ offset ∈ Finset.range phase.val, (1 - q offset) := by
      unfold ownContinueWeight
      apply Finset.prod_congr rfl
      intro offset _
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots (window.start + offset)) refusing
      dsimp only [q]
      linarith
    rw [← hproduct] at hunion
    calc
      1 - window.ownContinueWeight refusing phase ≤
          ∑ offset ∈ Finset.range phase.val, q offset := hunion
      _ ≤ ∑ _offset ∈ Finset.range phase.val, rho := by
        apply Finset.sum_le_sum
        intro offset hoffset
        exact hown ⟨offset, Finset.mem_range.mp hoffset |>.trans phase.isLt⟩
      _ = phase.val * rho := by simp
  have hopponent0 :=
    quittingOpponentSurvivalWeight_nonneg roots refusing window.start phase.val
  have hopponent1 :=
    quittingOpponentSurvivalWeight_le_one roots refusing window.start phase.val
  have hown1 : window.ownContinueWeight refusing phase ≤ 1 := by
    unfold ownContinueWeight
    exact Finset.prod_le_one
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun offset _ => ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one _ _))
  rw [window.survivalWeight_eq_opponent_mul_own refusing phase]
  calc
    quittingOpponentSurvivalWeight roots refusing window.start phase.val -
          quittingOpponentSurvivalWeight roots refusing window.start phase.val *
            window.ownContinueWeight refusing phase =
        quittingOpponentSurvivalWeight roots refusing window.start phase.val *
          (1 - window.ownContinueWeight refusing phase) := by ring
    _ ≤ 1 * (1 - window.ownContinueWeight refusing phase) :=
      mul_le_mul_of_nonneg_right hopponent1 (sub_nonneg.mpr hown1)
    _ ≤ phase.val * rho := by simpa using hprefix

/-- A singleton coalition probability is at most total root absorption. -/
theorem rootSingletonMass_le_absorptionMass
    (root : ι → PMF Bool) (owner : ι) :
    quittingRootCoalitionMass root {owner} ≤
      quittingRootAbsorptionMass root := by
  have hdecomposition :=
    quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass root
  have howner : quittingRootCoalitionMass root {owner} ≤
      ∑ other : ι, quittingRootCoalitionMass root {other} :=
    Finset.single_le_sum (fun other _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {other})
      (Finset.mem_univ owner)
  linarith [quittingRootCollisionMass_nonneg root]

/-- Raw owner-mass reweighting bound.  This is the division-free precursor:
the only loss is chronological, and its exact coefficient is the triangular
factor of the finite word. -/
theorem forceContinue_singletonMass_sub_jointOff_le
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι) (rho : ℝ)
    (hrho : 0 ≤ rho)
    (hown : ∀ phase : Fin window.fuel,
      (window.rootAt phase refusing true).toReal ≤ rho) :
    (window.forceContinueWindow refusing).singletonMass owner -
        window.jointOffPlayerSingletonMass refusing owner ≤
      window.chronologyFactor * rho := by
  rw [window.forceContinueWindow_singletonMass_eq refusing owner]
  unfold jointOffPlayerSingletonMass chronologyFactor
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro phase _
  have hgap := window.opponentSurvivalWeight_sub_survivalWeight_le
    refusing rho hrho hown phase
  have hmass0 := MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
    (window.offPlayerRoot refusing phase) {owner}
  have hmass1 := rootSingletonMass_le_absorptionMass
    (window.offPlayerRoot refusing phase) owner |>.trans
      (sub_le_self 1 (quittingStationaryContinueMass_nonneg _))
  calc
    quittingOpponentSurvivalWeight roots refusing window.start phase.val *
          quittingRootCoalitionMass (window.offPlayerRoot refusing phase) {owner} -
        window.survivalWeight phase *
          quittingRootCoalitionMass (window.offPlayerRoot refusing phase) {owner} =
      (quittingOpponentSurvivalWeight roots refusing window.start phase.val -
        window.survivalWeight phase) *
          quittingRootCoalitionMass (window.offPlayerRoot refusing phase) {owner} := by ring
    _ ≤ (phase.val * rho) *
          quittingRootCoalitionMass (window.offPlayerRoot refusing phase) {owner} :=
      mul_le_mul_of_nonneg_right hgap hmass0
    _ ≤ (phase.val * rho) * 1 :=
      mul_le_mul_of_nonneg_left hmass1
        (mul_nonneg (Nat.cast_nonneg phase.val) hrho)
    _ = phase.val * rho := by ring

/-- Raw total deleted-absorption reweighting bound. -/
theorem forceContinue_absorptionMass_sub_jointOff_le
    (window : QuittingFiniteRootWindow roots) (refusing : ι) (rho : ℝ)
    (hrho : 0 ≤ rho)
    (hown : ∀ phase : Fin window.fuel,
      (window.rootAt phase refusing true).toReal ≤ rho) :
    (window.forceContinueWindow refusing).absorptionMass -
        window.jointOffPlayerAbsorptionMass refusing ≤
      window.chronologyFactor * rho := by
  rw [window.forceContinueWindow_absorptionMass_eq refusing]
  unfold jointOffPlayerAbsorptionMass chronologyFactor
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro phase _
  have hgap := window.opponentSurvivalWeight_sub_survivalWeight_le
    refusing rho hrho hown phase
  have hmass0 := quittingRootAbsorptionMass_nonneg
    (window.offPlayerRoot refusing phase)
  have hmass1 : quittingRootAbsorptionMass
      (window.offPlayerRoot refusing phase) ≤ 1 :=
    sub_le_self 1 (quittingStationaryContinueMass_nonneg _)
  calc
    quittingOpponentSurvivalWeight roots refusing window.start phase.val *
          quittingRootAbsorptionMass (window.offPlayerRoot refusing phase) -
        window.survivalWeight phase *
          quittingRootAbsorptionMass (window.offPlayerRoot refusing phase) =
      (quittingOpponentSurvivalWeight roots refusing window.start phase.val -
        window.survivalWeight phase) *
          quittingRootAbsorptionMass (window.offPlayerRoot refusing phase) := by ring
    _ ≤ (phase.val * rho) *
          quittingRootAbsorptionMass (window.offPlayerRoot refusing phase) :=
      mul_le_mul_of_nonneg_right hgap hmass0
    _ ≤ (phase.val * rho) * 1 :=
      mul_le_mul_of_nonneg_left hmass1
        (mul_nonneg (Nat.cast_nonneg phase.val) hrho)
    _ = phase.val * rho := by ring

/-- Sharp normalized precursor.  The normalized occupation discrepancy is
controlled by the relative change of its absorption denominator. -/
theorem abs_normalized_forceContinue_sub_jointOff_le
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι)
    (hforced : 0 < (window.forceContinueWindow refusing).absorptionMass)
    (hjoint : 0 < window.jointOffPlayerAbsorptionMass refusing) :
    |(window.forceContinueWindow refusing).normalizedSingletonOccupation owner -
        window.normalizedJointOffPlayerOccupation refusing owner| ≤
      2 * ((window.forceContinueWindow refusing).absorptionMass -
          window.jointOffPlayerAbsorptionMass refusing) /
        (window.forceContinueWindow refusing).absorptionMass := by
  let A := (window.forceContinueWindow refusing).absorptionMass
  let S := window.jointOffPlayerAbsorptionMass refusing
  let C := A - S
  let X := window.jointOffPlayerSingletonMass refusing owner
  let b := (window.forceContinueWindow refusing).singletonMass owner - X
  have hC : 0 ≤ C := sub_nonneg.mpr
    (window.jointOffPlayerAbsorptionMass_le_forceContinue refusing)
  have hX0 := window.jointOffPlayerSingletonMass_nonneg refusing owner
  have hXS : X ≤ S := by
    unfold X S jointOffPlayerSingletonMass jointOffPlayerAbsorptionMass
    apply Finset.sum_le_sum
    intro phase _
    exact mul_le_mul_of_nonneg_left
      (rootSingletonMass_le_absorptionMass _ owner)
      (window.survivalWeight_nonneg phase)
  have hb0 : 0 ≤ b := sub_nonneg.mpr
    (window.jointOffPlayerSingletonMass_le_forceContinue refusing owner)
  have hbC : b ≤ C := by
    unfold b C A S X jointOffPlayerSingletonMass
      jointOffPlayerAbsorptionMass
    rw [window.forceContinueWindow_singletonMass_eq refusing owner,
      window.forceContinueWindow_absorptionMass_eq refusing,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro phase _
    have hmass := rootSingletonMass_le_absorptionMass
      (window.offPlayerRoot refusing phase) owner
    have hgap := window.survivalWeight_le_opponentSurvivalWeight refusing phase
    nlinarith [mul_le_mul_of_nonneg_left hmass
      (sub_nonneg.mpr hgap)]
  have hXabs : |X| ≤ S := by
    rw [abs_of_nonneg]
    · exact hXS
    · exact hX0
  have h := abs_conditionalPayoff_sub_singletonMixture_le (M := 1)
    (show A = S + C by simp [C]) hforced hjoint hC (by norm_num)
    (by simpa only [one_mul] using hXabs)
    (by simpa [abs_of_nonneg hb0] using hbC)
    (show (window.forceContinueWindow refusing).normalizedSingletonOccupation owner =
      (X + b) / A by simp [normalizedSingletonOccupation, X, b, A])
    (show window.normalizedJointOffPlayerOccupation refusing owner = X / S by
      rfl)
  simpa [A, S, C, mul_div_assoc] using h

/-- Explicit normalized error bound.  A lower bound on the joint-weighted
deleted absorption denominator is necessary; deleted absorption positivity
alone does not control this comparison. -/
theorem abs_normalized_forceContinue_sub_jointOff_le_of_lowerBound
    (window : QuittingFiniteRootWindow roots) (refusing owner : ι)
    (rho lower : ℝ) (hrho : 0 ≤ rho) (hlower : 0 < lower)
    (hown : ∀ phase : Fin window.fuel,
      (window.rootAt phase refusing true).toReal ≤ rho)
    (hjointLower : lower ≤ window.jointOffPlayerAbsorptionMass refusing) :
    |(window.forceContinueWindow refusing).normalizedSingletonOccupation owner -
        window.normalizedJointOffPlayerOccupation refusing owner| ≤
      2 * window.chronologyFactor * rho / lower := by
  have hjoint : 0 < window.jointOffPlayerAbsorptionMass refusing :=
    lt_of_lt_of_le hlower hjointLower
  have hforced : 0 < (window.forceContinueWindow refusing).absorptionMass :=
    hjoint.trans_le
      (window.jointOffPlayerAbsorptionMass_le_forceContinue refusing)
  have hraw := window.forceContinue_absorptionMass_sub_jointOff_le
    refusing rho hrho hown
  have hsharp := window.abs_normalized_forceContinue_sub_jointOff_le
    refusing owner hforced hjoint
  have hfactor0 : 0 ≤ window.chronologyFactor :=
    Finset.sum_nonneg fun phase _ => Nat.cast_nonneg _
  have hgap0 : 0 ≤ (window.forceContinueWindow refusing).absorptionMass -
      window.jointOffPlayerAbsorptionMass refusing := sub_nonneg.mpr
    (window.jointOffPlayerAbsorptionMass_le_forceContinue refusing)
  have hdenomLower : lower ≤
      (window.forceContinueWindow refusing).absorptionMass :=
    hjointLower.trans
      (window.jointOffPlayerAbsorptionMass_le_forceContinue refusing)
  have hratio :
      ((window.forceContinueWindow refusing).absorptionMass -
          window.jointOffPlayerAbsorptionMass refusing) /
          (window.forceContinueWindow refusing).absorptionMass ≤
        window.chronologyFactor * rho / lower := by
    apply (div_le_div_iff₀ hforced hlower).2
    calc
      ((window.forceContinueWindow refusing).absorptionMass -
            window.jointOffPlayerAbsorptionMass refusing) * lower ≤
          (window.chronologyFactor * rho) * lower :=
        mul_le_mul_of_nonneg_right hraw hlower.le
      _ ≤ (window.chronologyFactor * rho) *
          (window.forceContinueWindow refusing).absorptionMass :=
        mul_le_mul_of_nonneg_left hdenomLower
          (mul_nonneg hfactor0 hrho)
  have hscaled :=
    mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
  exact hsharp.trans (by
    calc
      2 * ((window.forceContinueWindow refusing).absorptionMass -
              window.jointOffPlayerAbsorptionMass refusing) /
            (window.forceContinueWindow refusing).absorptionMass =
        2 *
          (((window.forceContinueWindow refusing).absorptionMass -
              window.jointOffPlayerAbsorptionMass refusing) /
            (window.forceContinueWindow refusing).absorptionMass) := by ring
      _ ≤
        2 * (window.chronologyFactor * rho / lower) := hscaled
      _ = 2 * window.chronologyFactor * rho / lower := by ring)

end QuittingFiniteRootWindow

end GameTheory
