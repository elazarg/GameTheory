/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.MetrizableMarkedAbsorptionPath
import UniformEquilibrium.Quitting.Boundary.Holonomy.WeightedBounds

/-!
# Bounded decoders for completed marked absorption paths

The metrizable marked-path carrier retains its large graph in compact
extended-real coordinates.  Fixed-prefix strategic consumers, however, use
the five real coefficients of `QuittingBoundaryHolonomy`.  This module
provides the bounded-real interface between them.

The decoder is a continuous retraction onto the uniform coefficient box.  On
every finite coherent cylinder it is literally the original holonomy.  Its
early best-response coordinate is therefore the exact finite pure-Quit
obstacle cap.  The behavioral-tail repair value then extends continuously to
the completed carrier and is included in a compact-subsequence capstone.

No ordered history, multiplicity, binary splice operation, or composition
fibre uniqueness is inferred from the semantic graph.
-/

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology

private def clampEReal (lower upper : ℝ) (x : EReal) : ℝ :=
  EReal.toReal (max (lower : EReal) (min (upper : EReal) x))

private theorem continuous_clampEReal (lower upper : ℝ) :
    Continuous (clampEReal lower upper) := by
  apply EReal.continuousOn_toReal.comp_continuous
  · exact continuous_const.max (continuous_const.min continuous_id)
  · intro x
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or]
    constructor
    · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe lower) (le_max_left _ _))
    · exact ne_of_lt (lt_of_le_of_lt
        (max_le
          (EReal.coe_le_coe_iff.mpr (le_max_left lower upper))
          ((min_le_left _ _).trans
            (EReal.coe_le_coe_iff.mpr (le_max_right lower upper))))
        (EReal.coe_lt_top (max lower upper)))

private theorem clampEReal_of_mem {lower upper x : ℝ}
    (hlower : lower ≤ x) (hupper : x ≤ upper) :
    clampEReal lower upper x = x := by
  simp [clampEReal, EReal.coe_le_coe_iff.mpr hlower,
    EReal.coe_le_coe_iff.mpr hupper]

private theorem clampEReal_mem {lower upper : ℝ} (h : lower ≤ upper) (x : EReal) :
    clampEReal lower upper x ∈ Set.Icc lower upper := by
  constructor
  · rw [← EReal.coe_le_coe_iff]
    change (lower : EReal) ≤
      ((max (lower : EReal) (min (upper : EReal) x)).toReal : EReal)
    rw [EReal.coe_toReal]
    · exact le_max_left _ _
    · exact ne_of_lt (lt_of_le_of_lt (max_le (EReal.coe_le_coe_iff.mpr h)
          (min_le_left _ _)) (EReal.coe_lt_top upper))
    · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe lower) (le_max_left _ _))
  · rw [← EReal.coe_le_coe_iff]
    change
      ((max (lower : EReal) (min (upper : EReal) x)).toReal : EReal) ≤
        (upper : EReal)
    rw [EReal.coe_toReal]
    · exact max_le (EReal.coe_le_coe_iff.mpr h) (min_le_left _ _)
    · exact ne_of_lt (lt_of_le_of_lt (max_le (EReal.coe_le_coe_iff.mpr h)
          (min_le_left _ _)) (EReal.coe_lt_top upper))
    · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe lower) (le_max_left _ _))

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private def IsRewardBoundedHolonomy (M : ℝ)
    (holonomy : QuittingBoundaryHolonomy ι) : Prop :=
  ∀ who,
    |(holonomy.prescribed who).intercept| ≤
        M * (1 - (holonomy.prescribed who).survival) ∧
      (holonomy.prescribed who).survival ≤ 1 ∧
      |(holonomy.bestResponse who).early| ≤ M ∧
      |(holonomy.bestResponse who).tail| ≤
        M * (1 - (holonomy.bestResponse who).survival) ∧
      (holonomy.bestResponse who).survival ≤ 1

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
private theorem IsRewardBoundedHolonomy.compose
    {M : ℝ}
    {outer inner : QuittingBoundaryHolonomy ι}
    (houter : IsRewardBoundedHolonomy M outer)
    (hinner : IsRewardBoundedHolonomy M inner) :
    IsRewardBoundedHolonomy M (outer * inner) := by
  intro who
  obtain ⟨hB₁, hP₁, hA₁, hT₁, hχ₁⟩ := houter who
  obtain ⟨hB₂, hP₂, hA₂, hT₂, hχ₂⟩ := hinner who
  have hP₁0 := (outer.prescribed who).survival_nonneg
  have hP₂0 := (inner.prescribed who).survival_nonneg
  have hχ₁0 := (outer.bestResponse who).survival_nonneg
  have hχ₂0 := (inner.bestResponse who).survival_nonneg
  have hB :
      |(outer.prescribed who).intercept +
          (outer.prescribed who).survival *
            (inner.prescribed who).intercept| ≤
        M * (1 - (outer.prescribed who).survival *
          (inner.prescribed who).survival) := by
    calc
      _ ≤ |(outer.prescribed who).intercept| +
          |(outer.prescribed who).survival *
            (inner.prescribed who).intercept| := abs_add_le _ _
      _ = |(outer.prescribed who).intercept| +
          (outer.prescribed who).survival *
            |(inner.prescribed who).intercept| := by
          rw [abs_mul, abs_of_nonneg hP₁0]
      _ ≤ M * (1 - (outer.prescribed who).survival) +
          (outer.prescribed who).survival *
            (M * (1 - (inner.prescribed who).survival)) :=
        add_le_add hB₁ (mul_le_mul_of_nonneg_left hB₂ hP₁0)
      _ = _ := by ring
  have hT :
      |(outer.bestResponse who).tail +
          (outer.bestResponse who).survival *
            (inner.bestResponse who).tail| ≤
        M * (1 - (outer.bestResponse who).survival *
          (inner.bestResponse who).survival) := by
    calc
      _ ≤ |(outer.bestResponse who).tail| +
          |(outer.bestResponse who).survival *
            (inner.bestResponse who).tail| := abs_add_le _ _
      _ = |(outer.bestResponse who).tail| +
          (outer.bestResponse who).survival *
            |(inner.bestResponse who).tail| := by
          rw [abs_mul, abs_of_nonneg hχ₁0]
      _ ≤ M * (1 - (outer.bestResponse who).survival) +
          (outer.bestResponse who).survival *
            (M * (1 - (inner.bestResponse who).survival)) :=
        add_le_add hT₁ (mul_le_mul_of_nonneg_left hT₂ hχ₁0)
      _ = _ := by ring
  have hcontinue :
      |(outer.bestResponse who).tail +
          (outer.bestResponse who).survival *
            (inner.bestResponse who).early| ≤ M := by
    calc
      _ ≤ |(outer.bestResponse who).tail| +
          |(outer.bestResponse who).survival *
            (inner.bestResponse who).early| := abs_add_le _ _
      _ = |(outer.bestResponse who).tail| +
          (outer.bestResponse who).survival *
            |(inner.bestResponse who).early| := by
          rw [abs_mul, abs_of_nonneg hχ₁0]
      _ ≤ M * (1 - (outer.bestResponse who).survival) +
          (outer.bestResponse who).survival * M :=
        add_le_add hT₁ (mul_le_mul_of_nonneg_left hA₂ hχ₁0)
      _ = M := by ring
  have hA :
      |max (outer.bestResponse who).early
        ((outer.bestResponse who).tail +
          (outer.bestResponse who).survival *
            (inner.bestResponse who).early)| ≤ M := by
    rw [abs_le]
    constructor
    · exact (abs_le.mp hA₁).1.trans (le_max_left _ _)
    · exact max_le (abs_le.mp hA₁).2 (abs_le.mp hcontinue).2
  refine ⟨hB, ?_, hA, hT, ?_⟩
  · change (outer.prescribed who).survival *
      (inner.prescribed who).survival ≤ 1
    nlinarith [mul_nonneg hP₁0 hP₂0]
  · change (outer.bestResponse who).survival *
      (inner.bestResponse who).survival ≤ 1
    nlinarith [mul_nonneg hχ₁0 hχ₂0]

private theorem IsRewardBoundedHolonomy.ofRealized
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (source : RealizedMarkedAbsorptionCylinder reward anchor) :
    IsRewardBoundedHolonomy (quittingRewardBound reward)
      (MarkedAbsorptionCylinder.ofRealized source).holonomy := by
  change IsRewardBoundedHolonomy (quittingRewardBound reward)
    source.block.holonomy
  unfold QuittingAnchoredBoundaryBlock.holonomy
  intro who
  have hbox := quittingFiniteBoundaryHolonomy_coordinates_bounded
    reward anchor.roots source.block.start source.block.extra who
  refine ⟨?_, hbox.2.1, hbox.2.2.1, ?_, hbox.2.2.2.2⟩
  · simpa [QuittingAnchoredBoundaryBlock.holonomy] using
      (abs_quittingFiniteBoundaryHolonomy_prescribed_intercept_le
        reward anchor.roots source.block.start source.block.extra who)
  · simpa [QuittingAnchoredBoundaryBlock.holonomy] using
      (abs_quittingFiniteBoundaryHolonomy_bestResponse_tail_le
        reward anchor.roots source.block.start source.block.extra who)

/-- Legal chronological splicing preserves the same coefficient box as a
single realized block.  The proof uses weighted intercept defects; unweighted
coordinate bounds alone are not stable under composition. -/
theorem chronology_holonomy_coordinates_mem_box
    {cylinder : MarkedAbsorptionCylinder ι}
    (h : cylinder.IsChronologicallyGenerated reward) :
    cylinder.holonomy.coordinates ∈
      quittingBoundaryHolonomyCoefficientBox ι (quittingRewardBound reward) := by
  have hbounded :
      IsRewardBoundedHolonomy (quittingRewardBound reward) cylinder.holonomy := by
    induction h with
    | realized source => exact IsRewardBoundedHolonomy.ofRealized source
    | splice houter hinner _ ihouter ihinner =>
        exact IsRewardBoundedHolonomy.compose ihouter ihinner
  rw [quittingBoundaryHolonomyCoefficientBox]
  refine ⟨?_, ?_⟩
  · intro who _
    obtain ⟨hB, hP, _, _, _⟩ := hbounded who
    exact ⟨abs_le.mp (hB.trans (by
      nlinarith [quittingRewardBound_nonneg reward,
        (cylinder.holonomy.prescribed who).survival_nonneg])),
      ⟨(cylinder.holonomy.prescribed who).survival_nonneg, hP⟩⟩
  · intro who _
    obtain ⟨_, _, hA, hT, hχ⟩ := hbounded who
    exact ⟨abs_le.mp hA,
      ⟨abs_le.mp (hT.trans (by
        nlinarith [quittingRewardBound_nonneg reward,
          (cylinder.holonomy.bestResponse who).survival_nonneg])),
        ⟨(cylinder.holonomy.bestResponse who).survival_nonneg, hχ⟩⟩⟩

namespace MetrizableMarkedAbsorptionCompletion

/-- Five real holonomy coordinates in their uniform reward-dependent box. -/
abbrev CompactHolonomyCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {coordinates : QuittingBoundaryHolonomyCoordinates ι //
    coordinates ∈ quittingBoundaryHolonomyCoefficientBox ι
      (quittingRewardBound reward)}

instance : CompactSpace (CompactHolonomyCoordinates reward) :=
  isCompact_iff_compactSpace.mp
    (isCompact_quittingBoundaryHolonomyCoefficientBox ι
      (quittingRewardBound reward))

/-- Continuous bounded-real retraction of the extended holonomy projection. -/
def metrizableBoundedHolonomyCoordinates
    (path : MetrizableMarkedAbsorptionPath reward) :
    CompactHolonomyCoordinates reward := by
  let M := quittingRewardBound reward
  let extended := metrizableHolonomy path
  refine ⟨
    (fun who =>
      (clampEReal (-M) M (extended.1 who).1,
        clampEReal 0 1 (extended.1 who).2),
      fun who =>
      (clampEReal (-M) M (extended.2 who).1,
        (clampEReal (-M) M (extended.2 who).2.1,
          clampEReal 0 1 (extended.2 who).2.2))), ?_⟩
  rw [quittingBoundaryHolonomyCoefficientBox]
  refine ⟨?_, ?_⟩
  · intro who _
    exact ⟨clampEReal_mem (by
        linarith [quittingRewardBound_nonneg reward]) _,
      clampEReal_mem zero_le_one _⟩
  · intro who _
    exact ⟨clampEReal_mem (by
        linarith [quittingRewardBound_nonneg reward]) _,
      ⟨clampEReal_mem (by
          linarith [quittingRewardBound_nonneg reward]) _,
        clampEReal_mem zero_le_one _⟩⟩

/-- The bounded real coordinate decoder is continuous. -/
theorem continuous_metrizableBoundedHolonomyCoordinates :
    Continuous
      (metrizableBoundedHolonomyCoordinates (reward := reward)) := by
  have hholonomy := continuous_metrizableHolonomy (reward := reward)
  have hprescribed : Continuous (fun path : MetrizableMarkedAbsorptionPath reward =>
      (metrizableHolonomy path).1) := continuous_fst.comp hholonomy
  have hbest : Continuous (fun path : MetrizableMarkedAbsorptionPath reward =>
      (metrizableHolonomy path).2) := continuous_snd.comp hholonomy
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    apply Continuous.prodMk
    · exact (continuous_clampEReal _ _).comp
        (continuous_fst.comp ((continuous_apply who).comp hprescribed))
    · exact (continuous_clampEReal _ _).comp
        (continuous_snd.comp ((continuous_apply who).comp hprescribed))
  · apply continuous_pi
    intro who
    apply Continuous.prodMk
    · exact (continuous_clampEReal _ _).comp
        (continuous_fst.comp ((continuous_apply who).comp hbest))
    · apply Continuous.prodMk
      · exact (continuous_clampEReal _ _).comp
          (continuous_fst.comp
            (continuous_snd.comp ((continuous_apply who).comp hbest)))
      · exact (continuous_clampEReal _ _).comp
          (continuous_snd.comp
            (continuous_snd.comp ((continuous_apply who).comp hbest)))

/-- Rebundle boxed real coordinates as the affine/max-affine holonomy used by
fixed-prefix consumers. -/
def CompactHolonomyCoordinates.toHolonomy
    (coordinates : CompactHolonomyCoordinates reward) :
    QuittingBoundaryHolonomy ι where
  prescribed who := {
    intercept := coordinates.1.1 who |>.1
    survival := coordinates.1.1 who |>.2
    survival_nonneg := by
      exact (coordinates.2.1 who (Set.mem_univ who)).2.1 }
  bestResponse who := {
    early := coordinates.1.2 who |>.1
    tail := coordinates.1.2 who |>.2.1
    survival := coordinates.1.2 who |>.2.2
    survival_nonneg := by
      exact (coordinates.2.2 who (Set.mem_univ who)).2.2.1 }

/-- Bounded real holonomy decoded from a completed marked path. -/
def metrizableBoundaryHolonomy
    (path : MetrizableMarkedAbsorptionPath reward) :
    QuittingBoundaryHolonomy ι :=
  (metrizableBoundedHolonomyCoordinates path).toHolonomy

/-- Rebundling the decoded coordinates forgets no scalar data. -/
@[simp] theorem metrizableBoundaryHolonomy_coordinates
    (path : MetrizableMarkedAbsorptionPath reward) :
    (metrizableBoundaryHolonomy path).coordinates =
      (metrizableBoundedHolonomyCoordinates path).1 := rfl

/-- On a finite coherent cylinder, the completed decoder is its literal
finite holonomy. -/
@[simp] theorem metrizableBoundaryHolonomy_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableBoundaryHolonomy (completeMetrizable finite) =
      finite.1.holonomy := by
  have hbox := chronology_holonomy_coordinates_mem_box finite.2.chronology
  rw [quittingBoundaryHolonomyCoefficientBox] at hbox
  apply QuittingBoundaryHolonomy.ext <;> funext who
  · apply QuittingAffineSummary.ext
    · exact clampEReal_of_mem (hbox.1 who (Set.mem_univ who)).1.1
        (hbox.1 who (Set.mem_univ who)).1.2
    · exact clampEReal_of_mem (hbox.1 who (Set.mem_univ who)).2.1
        (hbox.1 who (Set.mem_univ who)).2.2
  · apply QuittingMaxAffineSummary.ext
    · exact clampEReal_of_mem (hbox.2 who (Set.mem_univ who)).1.1
        (hbox.2 who (Set.mem_univ who)).1.2
    · exact clampEReal_of_mem (hbox.2 who (Set.mem_univ who)).2.1.1
        (hbox.2 who (Set.mem_univ who)).2.1.2
    · exact clampEReal_of_mem (hbox.2 who (Set.mem_univ who)).2.2.1
        (hbox.2 who (Set.mem_univ who)).2.2.2

/-- Fixed-prefix behavioral-tail repair value evaluated on the decoded real
holonomy of a completed marked path. -/
def metrizableBehavioralTailRepairValue
    (path : MetrizableMarkedAbsorptionPath reward) : ℝ :=
  QuittingBoundaryHolonomy.behavioralTailRepairValue reward
    (metrizableBoundaryHolonomy path)

/-- The completed repair value specializes to the existing finite-prefix
repair value. -/
@[simp] theorem metrizableBehavioralTailRepairValue_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) :
    metrizableBehavioralTailRepairValue (completeMetrizable finite) =
      QuittingBoundaryHolonomy.behavioralTailRepairValue reward
        finite.1.holonomy := by
  simp [metrizableBehavioralTailRepairValue]

/-- The completed repair value inherits the landed coefficient modulus. -/
theorem metrizableBehavioralTailRepairValue_lipschitz
    (path path' : MetrizableMarkedAbsorptionPath reward) :
    |metrizableBehavioralTailRepairValue path -
        metrizableBehavioralTailRepairValue path'| ≤
      QuittingBoundaryHolonomy.maxCoordinateDistance
        (quittingRewardBound reward)
        (metrizableBoundaryHolonomy path)
        (metrizableBoundaryHolonomy path') := by
  exact QuittingBoundaryHolonomy.behavioralTailRepairValue_lipschitz
    reward (quittingRewardBound reward)
    (metrizableBoundaryHolonomy path) (metrizableBoundaryHolonomy path')
    (quittingRewardBound_nonneg reward)
    (fun terminal player => abs_reward_le_quittingRewardBound reward terminal player)

omit [DecidableEq ι] in
private theorem continuous_maxCoordinateDistance_from_boundedCoordinates
    (center : CompactHolonomyCoordinates reward) :
    Continuous (fun coordinates : CompactHolonomyCoordinates reward =>
      QuittingBoundaryHolonomy.maxCoordinateDistance
        (quittingRewardBound reward) coordinates.toHolonomy center.toHolonomy) := by
  unfold QuittingBoundaryHolonomy.maxCoordinateDistance
    QuittingBoundaryHolonomy.finitePlayerMax
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  unfold QuittingBoundaryHolonomy.coordinateDistance
  dsimp only [CompactHolonomyCoordinates.toHolonomy]
  fun_prop

omit [DecidableEq ι] in
private theorem maxCoordinateDistance_toHolonomy_self
    (coordinates : CompactHolonomyCoordinates reward) :
    QuittingBoundaryHolonomy.maxCoordinateDistance
        (quittingRewardBound reward) coordinates.toHolonomy coordinates.toHolonomy = 0 := by
  unfold QuittingBoundaryHolonomy.maxCoordinateDistance
    QuittingBoundaryHolonomy.finitePlayerMax
    QuittingBoundaryHolonomy.coordinateDistance
  simp

/-- The completed fixed-prefix repair value is continuous in the joint
semantic topology. -/
theorem continuous_metrizableBehavioralTailRepairValue :
    Continuous
      (metrizableBehavioralTailRepairValue (reward := reward)) := by
  rw [continuous_iff_continuousAt]
  intro path
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro path'
    simpa [Real.dist_eq] using
      metrizableBehavioralTailRepairValue_lipschitz path' path
  · have hcontinuous :=
      (continuous_maxCoordinateDistance_from_boundedCoordinates
        (metrizableBoundedHolonomyCoordinates path)).comp
        continuous_metrizableBoundedHolonomyCoordinates
    have htendsto := hcontinuous.tendsto path
    change Tendsto
      (fun path' => QuittingBoundaryHolonomy.maxCoordinateDistance
        (quittingRewardBound reward)
        (metrizableBoundedHolonomyCoordinates path').toHolonomy
        (metrizableBoundedHolonomyCoordinates path).toHolonomy)
      (𝓝 path)
      (𝓝 (QuittingBoundaryHolonomy.maxCoordinateDistance
        (quittingRewardBound reward)
        (metrizableBoundedHolonomyCoordinates path).toHolonomy
        (metrizableBoundedHolonomyCoordinates path).toHolonomy)) at htendsto
    rw [maxCoordinateDistance_toHolonomy_self] at htendsto
    simpa only [metrizableBoundaryHolonomy] using htendsto

/-- Continuous extension of the exact finite pure-Quit obstacle cap, decoded
as the early coordinate of the bounded completed holonomy. -/
def metrizableObstacleCap
    (path : MetrizableMarkedAbsorptionPath reward) (who : ι) : ℝ :=
  (metrizableBoundaryHolonomy path).bestResponse who |>.early

/-- Every player's completed obstacle cap is continuous. -/
theorem continuous_metrizableObstacleCap (who : ι) :
    Continuous (fun path : MetrizableMarkedAbsorptionPath reward =>
      metrizableObstacleCap path who) := by
  exact continuous_fst.comp
    ((continuous_apply who).comp
      (continuous_snd.comp
        (continuous_subtype_val.comp
          continuous_metrizableBoundedHolonomyCoordinates)))

/-- The completed cap specializes to the early finite holonomy coordinate. -/
@[simp] theorem metrizableObstacleCap_completeMetrizable
    (finite : FiniteMarkedAbsorptionPath reward) (who : ι) :
    metrizableObstacleCap (completeMetrizable finite) who =
      (finite.1.holonomy.bestResponse who).early := by
  simp [metrizableObstacleCap]

/-- Every marked finite stage lies below the decoded obstacle cap. -/
theorem finite_pureQuitPayoff_le_metrizableObstacleCap
    (finite : FiniteMarkedAbsorptionPath reward) (who : ι)
    {stage : MarkedCylinderStage ι} (hstage : stage ∈ finite.1.stages) :
    stage.pureQuitPayoff who ≤
      metrizableObstacleCap (completeMetrizable finite) who := by
  rw [metrizableObstacleCap_completeMetrizable]
  exact finite.2.obstacle_cap.upper who stage hstage

/-- A marked finite stage attains the decoded obstacle cap. -/
theorem exists_finite_stage_pureQuitPayoff_eq_metrizableObstacleCap
    (finite : FiniteMarkedAbsorptionPath reward) (who : ι) :
    ∃ stage ∈ finite.1.stages,
      stage.pureQuitPayoff who =
        metrizableObstacleCap (completeMetrizable finite) who := by
  simpa using finite.2.obstacle_cap.attained who

/-- Joint bounded holonomy and fixed-prefix repair data used by the completed
decoder.  The obstacle cap is the early-coordinate projection of this state.
-/
abbrev MetrizableRepairState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  CompactHolonomyCoordinates reward × ℝ

/-- Decoder-facing bounded holonomy and repair value of a completed path. -/
def metrizableRepairState (path : MetrizableMarkedAbsorptionPath reward) :
    MetrizableRepairState reward :=
  (metrizableBoundedHolonomyCoordinates path,
    metrizableBehavioralTailRepairValue path)

/-- The joint repair state is continuous. -/
theorem continuous_metrizableRepairState :
    Continuous (metrizableRepairState (reward := reward)) :=
  continuous_metrizableBoundedHolonomyCoordinates.prodMk
    continuous_metrizableBehavioralTailRepairValue

/-- Every sequence of finite coherent cylinders has a subsequence on which
the completed path and its decoder-facing repair state converge jointly. -/
theorem exists_finite_subsequence_with_repairState_limit
    (sequence : ℕ → FiniteMarkedAbsorptionPath reward) :
    ∃ (limit : MetrizableMarkedAbsorptionPath reward) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto (fun n => completeMetrizable (sequence (subseq n)))
        atTop (𝓝 limit) ∧
      Tendsto (fun n => metrizableRepairState
          (completeMetrizable (sequence (subseq n))))
        atTop (𝓝 (metrizableRepairState limit)) := by
  obtain ⟨limit, subseq, hmono, htendsto⟩ :=
    exists_convergent_subsequence
      (fun n => completeMetrizable (sequence n))
  refine ⟨limit, subseq, hmono, htendsto, ?_⟩
  simpa only [Function.comp_apply, Function.comp_def] using
    (continuous_metrizableRepairState.continuousAt.tendsto.comp htendsto)

end MetrizableMarkedAbsorptionCompletion

end GameTheory
