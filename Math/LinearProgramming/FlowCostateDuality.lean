/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.Basic

/-!
# Finite graded-flow and co-state duality

This file supplies the small algebraic layer needed to treat a finite raw
occupation flow and a dual co-state without normalizing the flow first.
Coordinates are split into finitely many grades.  A grade can, for example,
record whether a coordinate is transported with survival degree zero or one.

The central identity is

```
pair k (earlier + w * T later)
  = pair k earlier + pair (T.adjoint (w * k)) later.
```

Thus a co-state used after a chronological cut is not generally the original
co-state: it is reweighted and pulled back by the adjoint transport.  The
support-value and exposed-face results below are elementary consequences of
this identity.  They deliberately use attained upper bounds rather than a
topological `sSup`, so no compactness or closedness assumptions enter this
module.

The carriers are signed.  Positivity, mass balance, flow conservation, and
the production of a feasible set belong to downstream adapters.  In
particular, this module does not assert that a strategically defined packet
or occupation realizes any prescribed boundary annotation.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace LinearProgramming
namespace FlowCostateDuality

open Set

/-! ## Raw graded flows and their pairing -/

/-- A finite raw flow, separated into `Grade` channels.  No normalization or
sign condition is built into the carrier. -/
abbrev RawGradedFlow (Grade Coord : Type*) := Grade → Coord → ℝ

/-- A co-state pricing every coordinate of a raw graded flow. -/
abbrev Costate (Grade Coord : Type*) := Grade → Coord → ℝ

/-- A grade-preserving finite linear transport from `In` to `Out`. -/
abbrev GradedOperator (Grade In Out : Type*) := Grade → Out → In → ℝ

variable {Grade In Out : Type*}
  [Fintype Grade] [Fintype In] [Fintype Out]

/-- The finite primal/co-state pairing. -/
def pair (costate : Costate Grade Out) (flow : RawGradedFlow Grade Out) : ℝ :=
  ∑ grade, ∑ coordinate, costate grade coordinate * flow grade coordinate

/-- Pointwise addition of raw flows. -/
def flowAdd (x y : RawGradedFlow Grade Out) : RawGradedFlow Grade Out :=
  fun grade coordinate ↦ x grade coordinate + y grade coordinate

/-- Reweight every coordinate in a grade by the same scalar. -/
def reweight (weight : Grade → ℝ)
    (x : RawGradedFlow Grade Out) : RawGradedFlow Grade Out :=
  fun grade coordinate ↦ weight grade * x grade coordinate

theorem pair_flowAdd (costate : Costate Grade Out)
    (x y : RawGradedFlow Grade Out) :
    pair costate (flowAdd x y) = pair costate x + pair costate y := by
  simp [pair, flowAdd, mul_add, Finset.sum_add_distrib]

theorem pair_reweight_right (costate : Costate Grade Out)
    (weight : Grade → ℝ) (flow : RawGradedFlow Grade Out) :
    pair costate (reweight weight flow) =
      pair (reweight weight costate) flow := by
  unfold pair reweight
  apply Finset.sum_congr rfl
  intro grade _
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-! ## Linear transport and the adjoint update -/

/-- Push a raw graded flow through a grade-preserving finite operator. -/
def push (operator : GradedOperator Grade In Out)
    (flow : RawGradedFlow Grade In) : RawGradedFlow Grade Out :=
  fun grade output ↦
    ∑ input, operator grade output input * flow grade input

/-- Pull a co-state backward through the transpose of a finite operator. -/
def adjoint (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out) : Costate Grade In :=
  fun grade input ↦
    ∑ output, costate grade output * operator grade output input

/-- Finite matrix transpose is adjoint for the raw-flow pairing. -/
theorem pair_push_eq_pair_adjoint
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out) (flow : RawGradedFlow Grade In) :
    pair costate (push operator flow) = pair (adjoint operator costate) flow := by
  unfold pair push adjoint
  apply Finset.sum_congr rfl
  intro grade _
  calc
    (∑ output, costate grade output *
        ∑ input, operator grade output input * flow grade input) =
        ∑ output, ∑ input,
          costate grade output *
            (operator grade output input * flow grade input) := by
      apply Finset.sum_congr rfl
      intro output _
      rw [Finset.mul_sum]
    _ = ∑ input, ∑ output,
          costate grade output *
            (operator grade output input * flow grade input) :=
      Finset.sum_comm
    _ = ∑ input,
          (∑ output,
            costate grade output * operator grade output input) *
              flow grade input := by
      apply Finset.sum_congr rfl
      intro input _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro output _
      ring

/-- Chronological composition of an earlier raw flow with a transported later
flow.  `weight` is allowed to depend on the grade. -/
def chronologicalTransport (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (earlier : RawGradedFlow Grade Out)
    (later : RawGradedFlow Grade In) : RawGradedFlow Grade Out :=
  flowAdd earlier (reweight weight (push operator later))

/-- The co-state seen by a later block across a chronological cut. -/
def adjointUpdate (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out) : Costate Grade In :=
  adjoint operator (reweight weight costate)

/-- **Flow/co-state transport identity.**  A later raw flow is priced by the
reweighted adjoint co-state. -/
theorem pair_chronologicalTransport
    (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : RawGradedFlow Grade Out)
    (later : RawGradedFlow Grade In) :
    pair costate (chronologicalTransport weight operator earlier later) =
      pair costate earlier + pair (adjointUpdate weight operator costate) later := by
  rw [chronologicalTransport, pair_flowAdd, pair_reweight_right,
    pair_push_eq_pair_adjoint]
  rfl

/-! ## Survival grading -/

/-- The weight of a grade transported across a block with the given survival.
Degree zero is unweighted; degree one is the usual killed-flow transport. -/
def survivalWeight (degree : Grade → ℕ) (survival : ℝ) : Grade → ℝ :=
  fun grade ↦ survival ^ degree grade

/-- Survival-weighted chronological transport. -/
def survivalTransport (degree : Grade → ℕ) (survival : ℝ)
    (operator : GradedOperator Grade In Out)
    (earlier : RawGradedFlow Grade Out)
    (later : RawGradedFlow Grade In) : RawGradedFlow Grade Out :=
  chronologicalTransport (survivalWeight degree survival) operator earlier later

/-- The adjoint co-state update associated to survival transport. -/
def survivalAdjointUpdate (degree : Grade → ℕ) (survival : ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out) : Costate Grade In :=
  adjointUpdate (survivalWeight degree survival) operator costate

theorem pair_survivalTransport
    (degree : Grade → ℕ) (survival : ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : RawGradedFlow Grade Out)
    (later : RawGradedFlow Grade In) :
    pair costate (survivalTransport degree survival operator earlier later) =
      pair costate earlier +
        pair (survivalAdjointUpdate degree survival operator costate) later := by
  exact pair_chronologicalTransport
    (survivalWeight degree survival) operator costate earlier later

omit [Fintype Grade] in
/-- Multiplying survival factors multiplies their weights grade by grade. -/
theorem survivalWeight_mul (degree : Grade → ℕ) (s t : ℝ) (grade : Grade) :
    survivalWeight degree (s * t) grade =
      survivalWeight degree s grade * survivalWeight degree t grade := by
  simp [survivalWeight, mul_pow]

/-! ## Feasible-set transport and support values -/

/-- Image of two feasible raw-flow sets under chronological transport. -/
def transportSet (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (earlier : Set (RawGradedFlow Grade Out))
    (later : Set (RawGradedFlow Grade In)) :
    Set (RawGradedFlow Grade Out) :=
  {flow | ∃ x ∈ earlier, ∃ y ∈ later,
    flow = chronologicalTransport weight operator x y}

/-- `value` is an upper bound for the pairing on a feasible set. -/
def IsPairUpperBound (costate : Costate Grade Out)
    (feasible : Set (RawGradedFlow Grade Out)) (value : ℝ) : Prop :=
  ∀ flow ∈ feasible, pair costate flow ≤ value

/-- A support value packaged as an upper bound together with an attaining raw
flow.  This is the finite algebraic content of a support function equality. -/
structure HasSupportValue (costate : Costate Grade Out)
    (feasible : Set (RawGradedFlow Grade Out)) (value : ℝ) : Prop where
  upperBound : IsPairUpperBound costate feasible value
  attained : ∃ flow ∈ feasible, pair costate flow = value

/-- Support-function subadditivity for chronological feasible-set transport.
The later bound is evaluated at the adjoint-updated co-state. -/
theorem isPairUpperBound_transportSet
    (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : Set (RawGradedFlow Grade Out))
    (later : Set (RawGradedFlow Grade In))
    (earlierValue laterValue : ℝ)
    (hearlier : IsPairUpperBound costate earlier earlierValue)
    (hlater : IsPairUpperBound (adjointUpdate weight operator costate)
      later laterValue) :
    IsPairUpperBound costate (transportSet weight operator earlier later)
      (earlierValue + laterValue) := by
  intro flow hflow
  obtain ⟨x, hx, y, hy, rfl⟩ := hflow
  rw [pair_chronologicalTransport]
  exact add_le_add (hearlier x hx) (hlater y hy)

/-- When both component upper bounds are attained, the transported support
bound is attained as well; hence the support value is exactly additive. -/
theorem hasSupportValue_transportSet
    (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : Set (RawGradedFlow Grade Out))
    (later : Set (RawGradedFlow Grade In))
    (earlierValue laterValue : ℝ)
    (hearlier : HasSupportValue costate earlier earlierValue)
    (hlater : HasSupportValue (adjointUpdate weight operator costate)
      later laterValue) :
    HasSupportValue costate (transportSet weight operator earlier later)
      (earlierValue + laterValue) := by
  constructor
  · exact isPairUpperBound_transportSet weight operator costate earlier later
      earlierValue laterValue hearlier.upperBound hlater.upperBound
  · obtain ⟨x, hx, hxvalue⟩ := hearlier.attained
    obtain ⟨y, hy, hyvalue⟩ := hlater.attained
    refine ⟨chronologicalTransport weight operator x y, ?_, ?_⟩
    · exact ⟨x, hx, y, hy, rfl⟩
    · rw [pair_chronologicalTransport, hxvalue, hyvalue]

/-! ## Exposed active faces -/

/-- A chosen feasible raw flow maximizes the co-state pairing. -/
def Exposes (costate : Costate Grade Out)
    (feasible : Set (RawGradedFlow Grade Out))
    (chosen : RawGradedFlow Grade Out) : Prop :=
  chosen ∈ feasible ∧
    ∀ candidate ∈ feasible,
      pair costate candidate ≤ pair costate chosen

/-- The active face exposed by a co-state, represented without choosing a
numeric support value. -/
def exposedFace (costate : Costate Grade Out)
    (feasible : Set (RawGradedFlow Grade Out)) :
    Set (RawGradedFlow Grade Out) :=
  {chosen | Exposes costate feasible chosen}

/-- Exposed maximizers transport across a chronological cut.  The active face
on the later side is selected by the adjoint-updated co-state. -/
theorem exposes_transportSet
    (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : Set (RawGradedFlow Grade Out))
    (later : Set (RawGradedFlow Grade In))
    (x : RawGradedFlow Grade Out) (y : RawGradedFlow Grade In)
    (hx : Exposes costate earlier x)
    (hy : Exposes (adjointUpdate weight operator costate) later y) :
    Exposes costate (transportSet weight operator earlier later)
      (chronologicalTransport weight operator x y) := by
  constructor
  · exact ⟨x, hx.1, y, hy.1, rfl⟩
  · intro candidate hcandidate
    obtain ⟨x', hx', y', hy', rfl⟩ := hcandidate
    rw [pair_chronologicalTransport, pair_chronologicalTransport]
    exact add_le_add (hx.2 x' hx') (hy.2 y' hy')

/-- Set-level form of exposed active-face transport. -/
theorem transportSet_exposedFace_subset
    (weight : Grade → ℝ)
    (operator : GradedOperator Grade In Out)
    (costate : Costate Grade Out)
    (earlier : Set (RawGradedFlow Grade Out))
    (later : Set (RawGradedFlow Grade In)) :
    transportSet weight operator
        (exposedFace costate earlier)
        (exposedFace (adjointUpdate weight operator costate) later) ⊆
      exposedFace costate (transportSet weight operator earlier later) := by
  intro flow hflow
  obtain ⟨x, hx, y, hy, rfl⟩ := hflow
  exact exposes_transportSet weight operator costate earlier later x y hx hy

end FlowCostateDuality
end LinearProgramming
end Math
