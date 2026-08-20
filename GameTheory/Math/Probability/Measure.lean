/-
# Finite laws as probability measures

This is the narrow bridge from the executable finite-support `FinDist` core to
Mathlib's measure theory.  It introduces no probability abstraction: the
target is the ordinary `Measure` type.
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Probability.ConditionalProbability
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
theorem toMeasure_real_singleton {α : Type u} [MeasurableSpace α]
    [MeasurableSingletonClass α] (law : FinDist α) (a : α) :
    law.toMeasure.real {a} = law.prob a := by
  rw [measureReal_def, toMeasure,
    PMF.toMeasure_apply_singleton law.toPMF a (measurableSet_singleton a)]
  rfl

/-- The real mass assigned by the measure bridge is the finite law's event
probability. -/
theorem toMeasure_real_apply {α : Type u} [MeasurableSpace α]
    (law : FinDist α) {s : Set α} (hs : MeasurableSet s) :
    law.toMeasure.real s = law.probOf s := by
  rw [measureReal_def, toMeasure, law.toPMF.toMeasure_apply hs]
  rfl

/-- A measurable event has zero mass under the measure bridge exactly when it
is disjoint from the finite law's support. -/
theorem toMeasure_apply_eq_zero_iff {α : Type u} [MeasurableSpace α]
    (law : FinDist α) {s : Set α} (hs : MeasurableSet s) :
    law.toMeasure s = 0 ↔ Disjoint law.support s := by
  exact law.toPMF.toMeasure_apply_eq_zero_iff hs

@[simp]
theorem toMeasure_pure {α : Type u} [MeasurableSpace α] (a : α) :
    (FinDist.pure a).toMeasure = Measure.dirac a :=
  PMF.toMeasure_pure a

theorem toMeasure_map {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    (law : FinDist α) (f : α → β) (hf : Measurable f) :
    law.toMeasure.map f = (law.map f).toMeasure := by
  exact PMF.toMeasure_map (p := law.toPMF) (f := f) hf

/-! ## Finite discrete probability measures -/

/-- Read an ordinary probability measure on a finite discrete carrier as the
canonical executable finite law. -/
def ofMeasure {α : Type u} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (law : Measure α)
    [IsProbabilityMeasure law] : FinDist α :=
  FinDist.ofWeights (fun a => law.real {a})
    (fun _ => measureReal_nonneg)
    (by simp)

@[simp]
theorem prob_ofMeasure {α : Type u} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (law : Measure α)
    [IsProbabilityMeasure law] (a : α) :
    (ofMeasure law).prob a = law.real {a} :=
  FinDist.prob_ofWeights ..

/-- On a finite discrete carrier, conversion from an ordinary probability
measure to `FinDist` and back loses no information. -/
@[simp]
theorem toMeasure_ofMeasure {α : Type u} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : Measure α) [IsProbabilityMeasure law] :
    (ofMeasure law).toMeasure = law := by
  apply Measure.ext_of_measureReal_singleton
  intro a
  rw [toMeasure_real_singleton, prob_ofMeasure]

/-- The discrete measure bridge is a retraction of finite-law conversion. -/
@[simp]
theorem ofMeasure_toMeasure {α : Type u} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : FinDist α) : ofMeasure law.toMeasure = law := by
  apply FinDist.ext_of_prob
  intro a
  rw [prob_ofMeasure, toMeasure_real_singleton]

/-- Conditioning a finite-support law through the ordinary measure API and
then converting the finite output back to `FinDist` agrees with executable
finite-law conditioning. The source carrier itself need not be finite. -/
theorem ofMeasure_map_cond_toMeasure {α : Type u} {β : Type v}
    [MeasurableSpace α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (law : FinDist α) (event : Set α) (hevent : MeasurableSet event)
    (hmeet : ∃ a ∈ event, a ∈ law.support)
    (hmass : law.toMeasure event ≠ 0) (f : α → β) (hf : Measurable f) :
    let conditioned := ProbabilityTheory.cond law.toMeasure event
    letI : IsProbabilityMeasure conditioned :=
      ProbabilityTheory.cond_isProbabilityMeasure hmass
    let pushed := conditioned.map f
    letI : IsProbabilityMeasure pushed :=
      Measure.isProbabilityMeasure_map hf.aemeasurable
    FinDist.ofMeasure pushed = FinDist.map f (law.condOn event hmeet) := by
  classical
  let conditioned := ProbabilityTheory.cond law.toMeasure event
  letI : IsProbabilityMeasure conditioned :=
    ProbabilityTheory.cond_isProbabilityMeasure hmass
  let pushed := conditioned.map f
  letI : IsProbabilityMeasure pushed :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  apply FinDist.ext_of_prob
  intro b
  have hpreimage : MeasurableSet (f ⁻¹' ({b} : Set β)) :=
    hf (measurableSet_singleton b)
  have hinter : MeasurableSet (event ∩ f ⁻¹' ({b} : Set β)) :=
    hevent.inter hpreimage
  rw [prob_ofMeasure, measureReal_def,
    Measure.map_apply hf (measurableSet_singleton b),
    ProbabilityTheory.cond_apply hevent,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    FinDist.prob_map_eq_probOf_preimage_singleton,
    FinDist.probOf_condOn_eq_inter hmeet,
    ← toMeasure_real_apply law hinter,
    ← toMeasure_real_apply law hevent]
  exact mul_comm _ _

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
