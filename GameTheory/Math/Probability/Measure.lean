/-
# Finite laws as probability measures

This is the narrow bridge from the executable finite-support `FinDist` core to
Mathlib's measure theory.  It introduces no probability abstraction: the
target is the ordinary `Measure` type.
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure

noncomputable section

namespace GameTheory.Math.Probability.FinDist

open MeasureTheory ProbabilityTheory

universe u v w

/-- Regard a finite law as its canonical Mathlib probability measure. -/
def toMeasure {α : Type u} [MeasurableSpace α] (law : FinDist α) : Measure α :=
  law.toPMF.toMeasure

instance toMeasure_isProbability {α : Type u} [MeasurableSpace α]
    (law : FinDist α) : IsProbabilityMeasure law.toMeasure :=
  PMF.toMeasure.isProbabilityMeasure law.toPMF

@[simp]
theorem toMeasure_pure {α : Type u} [MeasurableSpace α] (a : α) :
    (FinDist.pure a).toMeasure = Measure.dirac a :=
  PMF.toMeasure_pure a

theorem toMeasure_map {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (law : FinDist α) (f : α → β) (hf : Measurable f) :
    law.toMeasure.map f = (law.map f).toMeasure := by
  exact PMF.toMeasure_map (p := law.toPMF) (f := f) hf

/-- Measure bind agrees with finite-law bind on a countable discrete source. -/
theorem toMeasure_bind {α : Type u} {β : Type v}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (law : FinDist α) (next : α → FinDist β) :
    Measure.bind law.toMeasure (fun a => (next a).toMeasure) =
      (law.bind next).toMeasure := by
  ext s hs
  unfold toMeasure
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_countable']
  simp only [FinDist.toPMF_bind]
  rw [PMF.toMeasure_bind_apply
    (p := law.toPMF) (f := fun a => (next a).toPMF) (s := s) hs]
  refine tsum_congr fun a => ?_
  rw [PMF.toMeasure_apply_singleton (p := law.toPMF) a
    (measurableSet_singleton a), mul_comm]

/-- The finite independent product bridge agrees with Mathlib's product
measure. -/
theorem toMeasure_pi {ι : Type u} [Fintype ι]
    {A : ι → Type v} [∀ i, Fintype (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)]
    (laws : ∀ i, FinDist (A i)) :
    (FinDist.pi laws).toMeasure =
      Measure.pi fun i => (laws i).toMeasure := by
  apply Measure.ext_of_singleton
  intro assignment
  rw [toMeasure, PMF.toMeasure_apply_singleton
    (p := (FinDist.pi laws).toPMF) assignment
    (measurableSet_singleton assignment)]
  rw [show ({assignment} : Set (∀ i, A i)) =
      Set.pi Set.univ (fun i => {assignment i}) by
        ext candidate
        constructor
        · intro h
          subst candidate
          intro i _
          rfl
        · intro h
          apply Set.mem_singleton_iff.mpr
          funext i
          exact Set.mem_singleton_iff.mp (h i (Set.mem_univ i))]
  rw [Measure.pi_pi]
  have hfactor (i : ι) :
      (laws i).toMeasure {assignment i} =
        (laws i).toPMF (assignment i) :=
    PMF.toMeasure_apply_singleton (p := (laws i).toPMF)
      (assignment i) (measurableSet_singleton (assignment i))
  simp_rw [hfactor]
  rfl

end GameTheory.Math.Probability.FinDist
