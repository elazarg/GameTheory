/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SurvivalWeightedObstruction
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation

/-!
# Survival-weighted obstruction carried by a finite quitting window

This file maps a literal `QuittingFiniteRootWindow` into the generic raw
accounting algebra of `Math.SurvivalWeightedObstruction`.  The survival clock
is the joint Continue probability.  The nonnegative charge channels are the
raw singleton-owner masses and one collision mass.  Calendar-indexed value
annotations supply the entry and exit values, so their difference is the
grade-zero endpoint coboundary.

Adjacent source windows concatenate exactly.  Singleton and collision charges
in the later window are transported by the earlier joint survival, while the
endpoint coboundary is not.  The induced tangent is therefore exactly the
literal endpoint displacement divided by window absorption mass.

This is an accounting adapter only.  It does not identify a charge with a
strategically feasible occupation, choose or expose a co-state, realize a
product-root word, compare the surviving boundary remainder, or prove boundary
exhaustion.  Payoff delivery and refusal semantics remain in their existing
game-facing modules.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {roots : ℕ → ι → PMF Bool}

/-- The raw nonnegative charge channels retained from a quitting window. -/
inductive QuittingWindowChargeChannel (ι : Type*) where
  | singleton (owner : ι)
  | collision
  deriving DecidableEq, Fintype

namespace QuittingFiniteRootWindow

/-! ## Literal adjacent-window concatenation -/

/-- Two windows in the same source sequence meet at one chronological cut. -/
def ChronologicallyAdjacent
    (earlier later : QuittingFiniteRootWindow roots) : Prop :=
  earlier.start + earlier.fuel = later.start

/-- The outer window spanning two chronologically adjacent source windows. -/
def concat (earlier later : QuittingFiniteRootWindow roots)
    (_hadjacent : earlier.ChronologicallyAdjacent later) :
    QuittingFiniteRootWindow roots where
  start := earlier.start
  fuel := earlier.fuel + later.fuel

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem concat_start (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).start = earlier.start := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem concat_fuel (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).fuel = earlier.fuel + later.fuel := rfl

private def weightedSourceMass
    (window : QuittingFiniteRootWindow roots) (source : ℕ → ℝ) : ℝ :=
  ∑ offset ∈ Finset.range window.fuel,
    quittingJointSurvivalWeight roots window.start offset *
      source (window.start + offset)

omit [DecidableEq ι] in
private theorem weightedSourceMass_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later)
    (source : ℕ → ℝ) :
    weightedSourceMass (earlier.concat later hadjacent) source =
      weightedSourceMass earlier source +
        quittingJointSurvivalWeight roots earlier.start earlier.fuel *
          weightedSourceMass later source := by
  unfold weightedSourceMass
  simp only [concat_start, concat_fuel]
  rw [Finset.sum_range_add, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro offset _
  rw [← hadjacent, quittingJointSurvivalWeight_add]
  simp only [Nat.add_assoc]
  ring

private theorem singletonMass_eq_weightedSourceMass
    (window : QuittingFiniteRootWindow roots) (owner : ι) :
    window.singletonMass owner =
      weightedSourceMass window
        (fun time ↦ quittingRootCoalitionMass (roots time) {owner}) := by
  unfold singletonMass weightedSourceMass survivalWeight rootAt
  rw [Fin.sum_univ_eq_sum_range
    (fun offset : ℕ ↦
      quittingJointSurvivalWeight roots window.start offset *
        quittingRootCoalitionMass (roots (window.start + offset)) {owner})
    window.fuel]

private theorem collisionMass_eq_weightedSourceMass
    (window : QuittingFiniteRootWindow roots) :
    window.collisionMass =
      weightedSourceMass window
        (fun time ↦ quittingRootCollisionMass (roots time)) := by
  unfold collisionMass weightedSourceMass survivalWeight rootAt
  rw [Fin.sum_univ_eq_sum_range
    (fun offset : ℕ ↦
      quittingJointSurvivalWeight roots window.start offset *
        quittingRootCollisionMass (roots (window.start + offset)))
    window.fuel]

omit [DecidableEq ι] in
private theorem absorptionMass_eq_weightedSourceMass
    (window : QuittingFiniteRootWindow roots) :
    window.absorptionMass =
      weightedSourceMass window
        (fun time ↦ quittingRootAbsorptionMass (roots time)) := by
  unfold absorptionMass weightedSourceMass survivalWeight rootAt
  rw [Fin.sum_univ_eq_sum_range
    (fun offset : ℕ ↦
      quittingJointSurvivalWeight roots window.start offset *
        quittingRootAbsorptionMass (roots (window.start + offset)))
    window.fuel]

omit [DecidableEq ι] in
/-- Joint survival through adjacent windows multiplies. -/
theorem jointSurvival_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    quittingJointSurvivalWeight roots
        (earlier.concat later hadjacent).start
        (earlier.concat later hadjacent).fuel =
      quittingJointSurvivalWeight roots earlier.start earlier.fuel *
        quittingJointSurvivalWeight roots later.start later.fuel := by
  rw [concat_start, concat_fuel, quittingJointSurvivalWeight_add, hadjacent]

/-- Raw singleton-owner charge splits with survival transport at an adjacent
chronological cut. -/
theorem singletonMass_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) (owner : ι) :
    (earlier.concat later hadjacent).singletonMass owner =
      earlier.singletonMass owner +
        quittingJointSurvivalWeight roots earlier.start earlier.fuel *
          later.singletonMass owner := by
  rw [singletonMass_eq_weightedSourceMass,
    singletonMass_eq_weightedSourceMass,
    singletonMass_eq_weightedSourceMass]
  exact weightedSourceMass_concat earlier later hadjacent _

/-- Raw collision charge splits with survival transport at an adjacent
chronological cut. -/
theorem collisionMass_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).collisionMass =
      earlier.collisionMass +
        quittingJointSurvivalWeight roots earlier.start earlier.fuel *
          later.collisionMass := by
  rw [collisionMass_eq_weightedSourceMass,
    collisionMass_eq_weightedSourceMass,
    collisionMass_eq_weightedSourceMass]
  exact weightedSourceMass_concat earlier later hadjacent _

omit [DecidableEq ι] in
/-- Total raw absorption splits with the same survival transport. -/
theorem absorptionMass_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).absorptionMass =
      earlier.absorptionMass +
        quittingJointSurvivalWeight roots earlier.start earlier.fuel *
          later.absorptionMass := by
  rw [absorptionMass_eq_weightedSourceMass,
    absorptionMass_eq_weightedSourceMass,
    absorptionMass_eq_weightedSourceMass]
  exact weightedSourceMass_concat earlier later hadjacent _

/-! ## The generic nonnegative block -/

/-- Raw singleton and collision charges of a literal finite window. -/
def rawCharge (window : QuittingFiniteRootWindow roots) :
    Math.SurvivalWeightedObstruction.NonnegativeCharge
      (QuittingWindowChargeChannel ι) where
  value
    | .singleton owner => window.singletonMass owner
    | .collision => window.collisionMass
  nonneg
    | .singleton owner => window.singletonMass_nonneg owner
    | .collision => window.collisionMass_nonneg

@[simp]
theorem rawCharge_singleton_value
    (window : QuittingFiniteRootWindow roots) (owner : ι) :
    window.rawCharge.value (.singleton owner) = window.singletonMass owner := rfl

@[simp]
theorem rawCharge_collision_value
    (window : QuittingFiniteRootWindow roots) :
    window.rawCharge.value (.collision : QuittingWindowChargeChannel ι) =
      window.collisionMass := rfl

/-- A literal finite quitting window as a generic survival-weighted block. -/
def toSurvivalBlock (window : QuittingFiniteRootWindow roots) :
    Math.SurvivalWeightedObstruction.Block
      (QuittingWindowChargeChannel ι) where
  survival := quittingJointSurvivalWeight roots window.start window.fuel
  survival_nonneg :=
    quittingJointSurvivalWeight_nonneg roots window.start window.fuel
  survival_le_one :=
    quittingJointSurvivalWeight_le_one roots window.start window.fuel
  charge := window.rawCharge

@[simp]
theorem toSurvivalBlock_survival
    (window : QuittingFiniteRootWindow roots) :
    window.toSurvivalBlock.survival =
      quittingJointSurvivalWeight roots window.start window.fuel := rfl

@[simp]
theorem toSurvivalBlock_singletonCharge
    (window : QuittingFiniteRootWindow roots) (owner : ι) :
    window.toSurvivalBlock.charge.value (.singleton owner) =
      window.singletonMass owner := rfl

@[simp]
theorem toSurvivalBlock_collisionCharge
    (window : QuittingFiniteRootWindow roots) :
    window.toSurvivalBlock.charge.value
        (.collision : QuittingWindowChargeChannel ι) =
      window.collisionMass := rfl

/-- The generic block's killed mass is the window's literal absorption mass. -/
@[simp]
theorem toSurvivalBlock_absorbedMass
    (window : QuittingFiniteRootWindow roots) :
    window.toSurvivalBlock.absorbedMass = window.absorptionMass := by
  rw [Math.SurvivalWeightedObstruction.Block.absorbedMass, toSurvivalBlock,
    window.absorptionMass_eq_one_sub_survivalWeight]

/-- The window adapter preserves chronological concatenation exactly. -/
theorem toSurvivalBlock_concat
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).toSurvivalBlock =
      Math.SurvivalWeightedObstruction.Block.concat
        earlier.toSurvivalBlock later.toSurvivalBlock := by
  apply Math.SurvivalWeightedObstruction.Block.ext
  · exact jointSurvival_concat earlier later hadjacent
  · ext channel
    cases channel with
    | singleton owner =>
        exact singletonMass_concat earlier later hadjacent owner
    | collision =>
        exact collisionMass_concat earlier later hadjacent

/-! ## Calendar annotations, coboundary, and tangent -/

/-- A calendar-indexed annotation turns a finite source window into a generic
annotated survival block. -/
def toAnnotatedSurvivalBlock {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots) :
    Math.SurvivalWeightedObstruction.AnnotatedBlock
      (QuittingWindowChargeChannel ι) ν where
  block := window.toSurvivalBlock
  entryValue := annotation window.start
  exitValue := annotation (window.start + window.fuel)

@[simp]
theorem toAnnotatedSurvivalBlock_entryValue {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots)
    (coordinate : ν) :
    (window.toAnnotatedSurvivalBlock annotation).entryValue coordinate =
      annotation window.start coordinate := rfl

@[simp]
theorem toAnnotatedSurvivalBlock_exitValue {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots)
    (coordinate : ν) :
    (window.toAnnotatedSurvivalBlock annotation).exitValue coordinate =
      annotation (window.start + window.fuel) coordinate := rfl

@[simp]
theorem toAnnotatedSurvivalBlock_absorbedMass {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots) :
    (window.toAnnotatedSurvivalBlock annotation).block.absorbedMass =
      window.absorptionMass :=
  window.toSurvivalBlock_absorbedMass

@[simp]
theorem toAnnotatedSurvivalBlock_endpointDisplacement {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots)
    (coordinate : ν) :
    (window.toAnnotatedSurvivalBlock annotation).endpointDisplacement coordinate =
      annotation window.start coordinate -
        annotation (window.start + window.fuel) coordinate := rfl

/-- Adjacent calendar windows have compatible endpoint annotations. -/
theorem toAnnotatedSurvivalBlock_compatible {ν : Type*}
    (annotation : ℕ → ν → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    Math.SurvivalWeightedObstruction.AnnotatedBlock.Compatible
      (earlier.toAnnotatedSurvivalBlock annotation)
      (later.toAnnotatedSurvivalBlock annotation) := by
  unfold Math.SurvivalWeightedObstruction.AnnotatedBlock.Compatible
  exact congrArg annotation hadjacent

/-- The annotated adapter preserves chronological concatenation, including
the outer calendar endpoints. -/
theorem toAnnotatedSurvivalBlock_concat {ν : Type*}
    (annotation : ℕ → ν → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).toAnnotatedSurvivalBlock annotation =
      Math.SurvivalWeightedObstruction.AnnotatedBlock.concat
        (earlier.toAnnotatedSurvivalBlock annotation)
        (later.toAnnotatedSurvivalBlock annotation) := by
  apply Math.SurvivalWeightedObstruction.AnnotatedBlock.ext
  · exact toSurvivalBlock_concat earlier later hadjacent
  · rfl
  · funext coordinate
    change annotation (earlier.start + (earlier.fuel + later.fuel)) coordinate =
      annotation (later.start + later.fuel) coordinate
    rw [← hadjacent]
    simp only [Nat.add_assoc]

/-- Literal endpoint displacement is an unweighted coboundary across an
adjacent chronological cut. -/
theorem endpointDisplacement_concat {ν : Type*}
    (annotation : ℕ → ν → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) (coordinate : ν) :
    ((earlier.concat later hadjacent).toAnnotatedSurvivalBlock annotation).endpointDisplacement
        coordinate =
      (earlier.toAnnotatedSurvivalBlock annotation).endpointDisplacement coordinate +
        (later.toAnnotatedSurvivalBlock annotation).endpointDisplacement coordinate := by
  rw [toAnnotatedSurvivalBlock_concat]
  exact Math.SurvivalWeightedObstruction.AnnotatedBlock.endpointDisplacement_concat _ _
    (toAnnotatedSurvivalBlock_compatible annotation earlier later hadjacent)
    coordinate

/-- Coordinatewise endpoint displacement divided by literal window
absorption.  At zero absorption this is totalized to zero by real division. -/
def normalizedEndpointTangent {ν : Type*}
    (window : QuittingFiniteRootWindow roots)
    (annotation : ℕ → ν → ℝ) (coordinate : ν) : ℝ :=
  (annotation window.start coordinate -
      annotation (window.start + window.fuel) coordinate) /
    window.absorptionMass

/-- The generic annotated-block tangent is the literal normalized endpoint
tangent of the source window. -/
@[simp]
theorem toAnnotatedSurvivalBlock_tangent {ν : Type*}
    (annotation : ℕ → ν → ℝ) (window : QuittingFiniteRootWindow roots)
    (coordinate : ν) :
    (window.toAnnotatedSurvivalBlock annotation).tangent coordinate =
      window.normalizedEndpointTangent annotation coordinate := by
  rw [Math.SurvivalWeightedObstruction.AnnotatedBlock.tangent,
    toAnnotatedSurvivalBlock_endpointDisplacement,
    toAnnotatedSurvivalBlock_absorbedMass]
  rfl

omit [DecidableEq ι] in
/-- Grading-correct tangent numerator across an adjacent cut.  Later absorbed
mass is survival-weighted in the denominator clock, but its endpoint
coboundary contribution on the right is not. -/
theorem absorptionMass_mul_normalizedEndpointTangent_concat {ν : Type*}
    (annotation : ℕ → ν → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) (coordinate : ν)
    (htotal : (earlier.concat later hadjacent).absorptionMass ≠ 0)
    (hearlier : earlier.absorptionMass ≠ 0)
    (hlater : later.absorptionMass ≠ 0) :
    (earlier.concat later hadjacent).absorptionMass *
        (earlier.concat later hadjacent).normalizedEndpointTangent
          annotation coordinate =
      earlier.absorptionMass *
          earlier.normalizedEndpointTangent annotation coordinate +
        later.absorptionMass *
          later.normalizedEndpointTangent annotation coordinate := by
  classical
  let earlierBlock := earlier.toAnnotatedSurvivalBlock annotation
  let laterBlock := later.toAnnotatedSurvivalBlock annotation
  have hcompatible :
      Math.SurvivalWeightedObstruction.AnnotatedBlock.Compatible
        earlierBlock laterBlock :=
    toAnnotatedSurvivalBlock_compatible annotation earlier later hadjacent
  have hgeneric :=
    Math.SurvivalWeightedObstruction.AnnotatedBlock.absorbedMass_mul_tangent_concat
    earlierBlock laterBlock hcompatible coordinate
    (by
      rw [← toAnnotatedSurvivalBlock_concat annotation earlier later hadjacent,
        toAnnotatedSurvivalBlock_absorbedMass]
      exact htotal)
    (by simpa only [earlierBlock, toAnnotatedSurvivalBlock_absorbedMass] using hearlier)
    (by simpa only [laterBlock, toAnnotatedSurvivalBlock_absorbedMass] using hlater)
  rw [← toAnnotatedSurvivalBlock_concat annotation earlier later hadjacent] at hgeneric
  simpa only [earlierBlock, laterBlock,
    toAnnotatedSurvivalBlock_absorbedMass,
    toAnnotatedSurvivalBlock_tangent] using hgeneric

end QuittingFiniteRootWindow

end GameTheory
