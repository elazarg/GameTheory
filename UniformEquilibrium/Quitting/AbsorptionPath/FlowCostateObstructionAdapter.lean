/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.FlowCostateDuality
import UniformEquilibrium.Quitting.AbsorptionPath.SurvivalWeightedObstructionAdapter

/-!
# Two-grade flow/co-state form of a finite quitting obstruction

This file embeds the annotated survival block of a literal finite quitting
window into `Math.LinearProgramming.FlowCostateDuality`.  There are exactly
two grades:

* `charge`, of survival degree one, contains the raw singleton and collision
  charges;
* `coboundary`, of survival degree zero, contains the signed playerwise
  endpoint displacement.

The common finite coordinate carrier is the sum of raw charge channels and
players.  Coordinates outside the indicated grade are zero.  With the
identity graded operator, adjacent source-window concatenation is exactly
`survivalTransport`: later raw charges are multiplied by earlier survival,
while later endpoint displacement is not.

The final theorems expose the resulting decomposition against an arbitrary
finite co-state.  They do not assert that the raw flow belongs to a strategic
feasible set, select a co-state, establish boundary exhaustion, expose a face,
or decode a strategic repair or return.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {roots : ℕ → ι → PMF Bool}

/-- The two survival grades of a quitting-window obstruction. -/
inductive QuittingObstructionGrade where
  | charge
  | coboundary
  deriving DecidableEq, Fintype

/-- A finite carrier shared by the charge and endpoint grades. -/
abbrev QuittingObstructionCoordinate (ι : Type*) :=
  Sum (QuittingWindowChargeChannel ι) ι

/-- Raw charge has survival degree one; endpoint coboundary has degree zero. -/
def quittingObstructionSurvivalDegree : QuittingObstructionGrade → ℕ
  | .charge => 1
  | .coboundary => 0

@[simp]
theorem quittingObstructionSurvivalDegree_charge :
    quittingObstructionSurvivalDegree .charge = 1 := rfl

@[simp]
theorem quittingObstructionSurvivalDegree_coboundary :
    quittingObstructionSurvivalDegree .coboundary = 0 := rfl

/-- Identity transport on every grade and coordinate. -/
def quittingObstructionIdentityOperator :
    GradedOperator QuittingObstructionGrade
      (QuittingObstructionCoordinate ι) (QuittingObstructionCoordinate ι) :=
  fun _ output input ↦ if output = input then 1 else 0

@[simp]
theorem push_quittingObstructionIdentityOperator
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    push (quittingObstructionIdentityOperator (ι := ι)) flow = flow := by
  funext grade output
  simp [push, quittingObstructionIdentityOperator]

@[simp]
theorem adjoint_quittingObstructionIdentityOperator
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    adjoint (quittingObstructionIdentityOperator (ι := ι)) costate = costate := by
  funext grade input
  simp [adjoint, quittingObstructionIdentityOperator]

/-- Across the identity operator, the later co-state is just reweighted by
the survival degree. -/
theorem survivalAdjointUpdate_quittingObstructionIdentityOperator
    (survival : ℝ)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    survivalAdjointUpdate quittingObstructionSurvivalDegree survival
        (quittingObstructionIdentityOperator (ι := ι)) costate =
      reweight
        (survivalWeight quittingObstructionSurvivalDegree survival) costate := by
  unfold survivalAdjointUpdate adjointUpdate
  exact adjoint_quittingObstructionIdentityOperator _

@[simp]
theorem survivalAdjointUpdate_identity_charge
    (survival : ℝ)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι))
    (coordinate : QuittingObstructionCoordinate ι) :
    survivalAdjointUpdate quittingObstructionSurvivalDegree survival
        (quittingObstructionIdentityOperator (ι := ι)) costate
        .charge coordinate =
      survival * costate .charge coordinate := by
  rw [survivalAdjointUpdate_quittingObstructionIdentityOperator]
  simp [reweight, survivalWeight]

@[simp]
theorem survivalAdjointUpdate_identity_coboundary
    (survival : ℝ)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι))
    (coordinate : QuittingObstructionCoordinate ι) :
    survivalAdjointUpdate quittingObstructionSurvivalDegree survival
        (quittingObstructionIdentityOperator (ι := ι)) costate
        .coboundary coordinate =
      costate .coboundary coordinate := by
  rw [survivalAdjointUpdate_quittingObstructionIdentityOperator]
  simp [reweight, survivalWeight]

namespace QuittingFiniteRootWindow

/-! ## The sparse two-grade flow -/

/-- The signed two-grade raw flow carried by an annotated quitting window.
Only charge coordinates in grade one and player coordinates in grade zero are
populated. -/
def toObstructionRawGradedFlow
    (annotation : ℕ → ι → ℝ) (window : QuittingFiniteRootWindow roots) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingObstructionCoordinate ι) :=
  fun grade coordinate ↦
    match grade, coordinate with
    | .charge, Sum.inl channel =>
        (window.toAnnotatedSurvivalBlock annotation).block.charge.value channel
    | .coboundary, Sum.inr player =>
        (window.toAnnotatedSurvivalBlock annotation).endpointDisplacement player
    | _, _ => 0

@[simp]
theorem toObstructionRawGradedFlow_charge
    (annotation : ℕ → ι → ℝ) (window : QuittingFiniteRootWindow roots)
    (channel : QuittingWindowChargeChannel ι) :
    window.toObstructionRawGradedFlow annotation
        .charge (Sum.inl channel) =
      window.rawCharge.value channel := rfl

@[simp]
theorem toObstructionRawGradedFlow_coboundary
    (annotation : ℕ → ι → ℝ) (window : QuittingFiniteRootWindow roots)
    (player : ι) :
    window.toObstructionRawGradedFlow annotation
        .coboundary (Sum.inr player) =
      (window.toAnnotatedSurvivalBlock annotation).endpointDisplacement player := rfl

@[simp]
theorem toObstructionRawGradedFlow_charge_player
    (annotation : ℕ → ι → ℝ) (window : QuittingFiniteRootWindow roots)
    (player : ι) :
    window.toObstructionRawGradedFlow annotation
        .charge (Sum.inr player) = 0 := rfl

@[simp]
theorem toObstructionRawGradedFlow_coboundary_charge
    (annotation : ℕ → ι → ℝ) (window : QuittingFiniteRootWindow roots)
    (channel : QuittingWindowChargeChannel ι) :
    window.toObstructionRawGradedFlow annotation
        .coboundary (Sum.inl channel) = 0 := rfl

/-- Identity-operator survival transport is pointwise addition with the later
coordinate multiplied by its grade's survival weight. -/
theorem survivalTransport_identity_apply
    (survival : ℝ)
    (earlier later : RawGradedFlow QuittingObstructionGrade
      (QuittingObstructionCoordinate ι))
    (grade : QuittingObstructionGrade)
    (coordinate : QuittingObstructionCoordinate ι) :
    survivalTransport quittingObstructionSurvivalDegree survival
        (quittingObstructionIdentityOperator (ι := ι)) earlier later
        grade coordinate =
      earlier grade coordinate +
        survival ^ quittingObstructionSurvivalDegree grade *
          later grade coordinate := by
  simp only [survivalTransport, chronologicalTransport, flowAdd, reweight,
    push_quittingObstructionIdentityOperator]
  rfl

/-- **Exact two-grade chronological law.**  Adjacent annotated quitting
windows concatenate as identity-operator survival transport. -/
theorem toObstructionRawGradedFlow_concat
    (annotation : ℕ → ι → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later) :
    (earlier.concat later hadjacent).toObstructionRawGradedFlow annotation =
      survivalTransport quittingObstructionSurvivalDegree
        (quittingJointSurvivalWeight roots earlier.start earlier.fuel)
        (quittingObstructionIdentityOperator (ι := ι))
        (earlier.toObstructionRawGradedFlow annotation)
        (later.toObstructionRawGradedFlow annotation) := by
  funext grade coordinate
  rw [survivalTransport_identity_apply]
  cases grade with
  | charge =>
      cases coordinate with
      | inl channel =>
          cases channel with
          | singleton owner =>
              simpa only [toObstructionRawGradedFlow_charge,
                rawCharge_singleton_value,
                quittingObstructionSurvivalDegree_charge, pow_one] using
                singletonMass_concat earlier later hadjacent owner
          | collision =>
              simpa only [toObstructionRawGradedFlow_charge,
                rawCharge_collision_value,
                quittingObstructionSurvivalDegree_charge, pow_one] using
                collisionMass_concat earlier later hadjacent
      | inr player =>
          simp only [toObstructionRawGradedFlow_charge_player,
            quittingObstructionSurvivalDegree_charge, pow_one, mul_zero,
            add_zero]
  | coboundary =>
      cases coordinate with
      | inl channel =>
          simp only [toObstructionRawGradedFlow_coboundary_charge,
            quittingObstructionSurvivalDegree_coboundary, pow_zero, mul_zero,
            add_zero]
      | inr player =>
          simpa only [toObstructionRawGradedFlow_coboundary,
            quittingObstructionSurvivalDegree_coboundary, pow_zero, one_mul] using
            endpointDisplacement_concat
            annotation earlier later hadjacent player

/-! ## Arbitrary co-state pairing -/

/-- Pairing with a window flow separates into its charge and endpoint
coboundary diagonals. -/
theorem pair_toObstructionRawGradedFlow
    (annotation : ℕ → ι → ℝ)
    (window : QuittingFiniteRootWindow roots)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    pair costate (window.toObstructionRawGradedFlow annotation) =
      (∑ channel : QuittingWindowChargeChannel ι,
        costate .charge (Sum.inl channel) * window.rawCharge.value channel) +
      ∑ player : ι,
        costate .coboundary (Sum.inr player) *
          (window.toAnnotatedSurvivalBlock annotation).endpointDisplacement player := by
  classical
  unfold pair
  have huniv : (Finset.univ : Finset QuittingObstructionGrade) =
      {.charge, .coboundary} := by decide
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [toObstructionRawGradedFlow]
  rfl

/-- Pairing decomposition at an adjacent chronological cut.  The later flow
is priced by the survival-reweighted adjoint co-state. -/
theorem pair_toObstructionRawGradedFlow_concat
    (annotation : ℕ → ι → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    pair costate
        ((earlier.concat later hadjacent).toObstructionRawGradedFlow annotation) =
      pair costate (earlier.toObstructionRawGradedFlow annotation) +
        pair
          (survivalAdjointUpdate quittingObstructionSurvivalDegree
            (quittingJointSurvivalWeight roots earlier.start earlier.fuel)
            (quittingObstructionIdentityOperator (ι := ι)) costate)
          (later.toObstructionRawGradedFlow annotation) := by
  rw [toObstructionRawGradedFlow_concat,
    pair_survivalTransport]

/-- Equivalent explicit form: across the identity operator, the later
co-state is reweighted by survival degree and is not otherwise transformed. -/
theorem pair_toObstructionRawGradedFlow_concat_reweight
    (annotation : ℕ → ι → ℝ)
    (earlier later : QuittingFiniteRootWindow roots)
    (hadjacent : earlier.ChronologicallyAdjacent later)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    pair costate
        ((earlier.concat later hadjacent).toObstructionRawGradedFlow annotation) =
      pair costate (earlier.toObstructionRawGradedFlow annotation) +
        pair
          (reweight
            (Math.LinearProgramming.FlowCostateDuality.survivalWeight
              quittingObstructionSurvivalDegree
              (quittingJointSurvivalWeight roots earlier.start earlier.fuel))
            costate)
          (later.toObstructionRawGradedFlow annotation) := by
  rw [pair_toObstructionRawGradedFlow_concat annotation earlier later
    hadjacent costate,
    survivalAdjointUpdate_quittingObstructionIdentityOperator]

end QuittingFiniteRootWindow

end GameTheory
