/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Divisible.DubinsSpanier
import GameTheory.Mechanism.FairDivision.Divisible.Stromquist
import Math.Fintype.Transport
import Mathlib.Data.Fintype.Pi

/-!
# Divisible Fair-Division Existence Theorems

Public existence wrappers built from the constructive theorem packages.
-/

open MeasureTheory Set
open scoped unitInterval

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Divisible

/-- Envy-free allocations exist for two agents on `[0,1]`. This is the
cut-and-choose theorem in existential form. -/
theorem ef_exists_two_agents
    (μ : Fin 2 → Measure I)
    [IsFiniteMeasure (μ 0)] [NullSingletonClass (μ 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A :=
  cutAndChoose_ef_exists μ

/-- Proportional allocations exist for any nonempty finite agent type with finite
non-atomic measures on `[0,1]`. -/
theorem proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  let n := Fintype.card N
  let e := Fintype.equivFin N
  have hn : 0 < n := Fintype.card_pos
  let μ' : Fin n → Measure I := Math.Fintype.toFin μ
  haveI hfin' : ∀ j : Fin n, IsFiniteMeasure (μ' j) := fun j =>
    show IsFiniteMeasure (μ (e.symm j)) from inferInstance
  haveI hnoatoms' : ∀ j : Fin n, NullSingletonClass (μ' j) := fun j =>
    show NullSingletonClass (μ (e.symm j)) from inferInstance
  obtain ⟨A', hA', hprop'⟩ := dubinsSpanierProportional n hn μ'
  refine ⟨Math.Fintype.fromFin A', ?_, ?_⟩
  · refine ⟨fun i => hA'.measurable (e i), fun i j hij => ?_, ?_⟩
    · exact hA'.disjoint (e i) (e j) (fun h => hij (e.injective h))
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hA'.cover ▸ Set.mem_univ x)
      refine ⟨e.symm j, ?_⟩
      change x ∈ A' (_root_.Fintype.equivFin N (e.symm j))
      rwa [show _root_.Fintype.equivFin N (e.symm j) = j by simp [e]]
  · intro i
    have hμ_eq : μ' (e i) = μ i := by simp [μ', e]
    calc
      μ i Set.univ = μ' (e i) Set.univ := by rw [hμ_eq]
      _ ≤ ↑n * μ' (e i) (A' (e i)) := hprop' (e i)
      _ = ↑n * μ i (A' (e i)) := by rw [hμ_eq]

/-- Envy-free allocations exist for any nonempty finite agent type with finite
non-atomic measures on `[0,1]`. -/
theorem ef_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  let n := Fintype.card N
  let e := Fintype.equivFin N
  have hn : 0 < n := Fintype.card_pos
  let μ' : Fin n → Measure ℝ := fun j => (Math.Fintype.toFin μ j).map Subtype.val
  haveI hfin' : ∀ j : Fin n, IsFiniteMeasure (μ' j) := fun j =>
    show IsFiniteMeasure ((μ (e.symm j)).map Subtype.val) from inferInstance
  haveI hnoatoms' : ∀ j : Fin n, NullSingletonClass (μ' j) := fun j =>
    show NullSingletonClass ((μ (e.symm j)).map Subtype.val) from
      Math.MeasureTheory.nullSingletonMapSubtypeVal (μ (e.symm j))
  have hsupp' : ∀ j : Fin n, μ' j = (μ' j).restrict (Set.Ico 0 1) := fun j => by
    exact Math.MeasureTheory.mapSubtypeVal_eq_restrict_Ico (μ (e.symm j))
  obtain ⟨A', hA', hef'⟩ := stromquist_envyFree_exists n μ' hn hsupp'
  refine ⟨fun i => Subtype.val ⁻¹' Math.Fintype.fromFin A' i, ?_, ?_⟩
  · refine ⟨fun i => (hA'.measurable (e i)).preimage measurable_subtype_coe, ?_, ?_⟩
    · intro i j hij
      exact (hA'.disjoint (e i) (e j) (fun h => hij (e.injective h))).preimage Subtype.val
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hA'.cover ▸ Set.mem_univ (x : ℝ))
      refine ⟨e.symm j, ?_⟩
      change (x : ℝ) ∈ A' (_root_.Fintype.equivFin N (e.symm j))
      rwa [show _root_.Fintype.equivFin N (e.symm j) = j by simp [e]]
  · intro i j
    have hle := hef' (e i) (e j)
    simp only [MeasureValuation] at hle ⊢
    have hμ_eq : μ' (e i) = (μ i).map Subtype.val := by
      simp [μ', e]
    rw [hμ_eq, Measure.map_apply measurable_subtype_coe (hA'.measurable (e j)),
      Measure.map_apply measurable_subtype_coe (hA'.measurable (e i))] at hle
    exact hle

/-- Envy-free allocations on `[0,1]` are also proportional. -/
theorem ef_and_proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A ∧
      IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  obtain ⟨A, hA, hef⟩ := ef_exists μ
  exact ⟨A, hA, hef, hef.isProportional μ A hA⟩

/-- Proportional existence for bundled measure instances on `[0,1]`. -/
theorem MeasureInstance.proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NullSingletonClass (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      M.IsProportional (Fintype.card N) A :=
  Divisible.proportional_exists M.measure

/-- Envy-free existence for bundled finite non-atomic measure instances on
`[0,1]`. -/
theorem MeasureInstance.envyFree_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NullSingletonClass (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ M.IsEnvyFree A :=
  Divisible.ef_exists M.measure

/-- Envy-free and proportional existence for bundled finite non-atomic measure
instances on `[0,1]`. -/
theorem MeasureInstance.envyFree_and_proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NullSingletonClass (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ M.IsEnvyFree A ∧ M.IsProportional (Fintype.card N) A :=
  Divisible.ef_and_proportional_exists M.measure

end Divisible
end FairDivision
end SocialChoice
end GameTheory
