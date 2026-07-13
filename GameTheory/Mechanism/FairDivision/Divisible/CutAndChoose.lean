/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Divisible.Basic
import Math.MeasureTheory.UnitInterval
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Cut and Choose

The two-agent cut-and-choose protocol on the unit interval. The chooser receives
their preferred side of a cut, and the cutter receives the other side.
-/

open MeasureTheory Set
open scoped unitInterval

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Divisible

/-- The cut-and-choose allocation at cut point `t`. Agent `1` chooses their
weakly preferred side; ties go to the left piece. -/
noncomputable def cutAndChooseAlloc (μ : Fin 2 → Measure I) (t : I) :
    Allocation (Fin 2) I :=
  fun i =>
    if μ 1 (Iic t) ≥ μ 1 (Ioi t) then
      if i = 0 then Ioi t else Iic t
    else
      if i = 0 then Iic t else Ioi t

/-- A fair cut for the cutter splits the cutter's measure equally. -/
def IsFairCutPoint (μ : Fin 2 → Measure I) (t : I) : Prop :=
  μ 0 (Iic t) = μ 0 (Ioi t)

@[simp] theorem cutAndChooseAlloc_zero (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 0 =
      if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t :=
  rfl

@[simp] theorem cutAndChooseAlloc_one (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 1 =
      if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t := by
  simp [cutAndChooseAlloc]

/-- For any cut point, cut-and-choose produces a complete measurable partition
of the unit interval. -/
theorem cutAndChooseAlloc_isAllocation (μ : Fin 2 → Measure I) (t : I) :
    IsAllocation (cutAndChooseAlloc μ t) := by
  have hmeasL : MeasurableSet (Iic t : Set I) := measurableSet_Iic
  have hmeasR : MeasurableSet (Ioi t : Set I) := measurableSet_Ioi
  have hdisjLR : Disjoint (Iic t : Set I) (Ioi t) := Iic_disjoint_Ioi le_rfl
  have hcover : (Iic t : Set I) ∪ Ioi t = univ := Iic_union_Ioi
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · fin_cases i
    · change MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs <;> assumption
    · change MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs <;> assumption
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
          (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs
      · exact hdisjLR.symm
      · exact hdisjLR
    · change Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
          (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs
      · exact hdisjLR
      · exact hdisjLR.symm
    · exact absurd rfl hij
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x ∈ Iic t ∨ x ∈ Ioi t :=
      (mem_union x (Iic t) (Ioi t)).mp (hcover ▸ mem_univ x)
    by_cases hchoose : μ 1 (Iic t) ≥ μ 1 (Ioi t)
    · rcases hx with hx | hx
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_pos hchoose]; exact hx⟩
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_pos hchoose]; exact hx⟩
    · rcases hx with hx | hx
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_neg hchoose]; exact hx⟩
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_neg hchoose]; exact hx⟩

/-- The chooser never envies the cutter, independently of the cut point. -/
theorem chooser_isEnvyFree (μ : Fin 2 → Measure I) (t : I) :
    (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 0) ≤
      (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 1) := by
  change μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t) ≤
    μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
  split_ifs with h
  · exact h
  · exact le_of_lt (lt_of_not_ge h)

/-- At a fair cut, the cutter does not envy the chooser. -/
theorem cutter_isEnvyFree_of_fair (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 1) ≤
      (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 0) := by
  change μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t) ≤
    μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
  split_ifs
  · exact le_of_eq hfair
  · exact le_of_eq hfair.symm

/-- Cut-and-choose is envy-free at any fair cut point. -/
theorem cutAndChoose_isEnvyFree (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    IsEnvyFree (MeasureValuation μ) (cutAndChooseAlloc μ t) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact le_refl _
  · exact cutter_isEnvyFree_of_fair μ t hfair
  · exact chooser_isEnvyFree μ t
  · exact le_refl _

/-- If a fair cut exists, cut-and-choose gives an envy-free allocation. -/
theorem cutAndChoose_ef_exists_of_fairCutPoint_exists
    (μ : Fin 2 → Measure I) (hfair : ∃ t : I, IsFairCutPoint μ t) :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  rcases hfair with ⟨t, ht⟩
  exact ⟨cutAndChooseAlloc μ t, cutAndChooseAlloc_isAllocation μ t,
    cutAndChoose_isEnvyFree μ t ht⟩

/-- A fair cut exists for finite non-atomic cutter measure. -/
theorem fairCutPoint_exists
    (μ : Fin 2 → Measure I) [IsFiniteMeasure (μ 0)] [NullSingletonClass (μ 0)] :
    ∃ t : I, IsFairCutPoint μ t := by
  set M := (μ 0 univ).toReal with hM_def
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hM_nonneg with hM_zero | hM_pos
  · refine ⟨0, ?_⟩
    unfold IsFairCutPoint
    have hM_eq : M = 0 := hM_zero.symm
    have h_toReal_zero : (μ 0 Set.univ).toReal = 0 := by
      simpa [hM_def] using hM_eq
    have hμ_univ : μ 0 Set.univ = 0 := by
      have hfin : μ 0 Set.univ ≠ ⊤ := measure_ne_top _ _
      rcases (ENNReal.toReal_eq_zero_iff (μ 0 Set.univ)).mp h_toReal_zero with hzero | htop
      · exact hzero
      · exact (hfin htop).elim
    have hleft : μ 0 (Iic (0 : I)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc
        μ 0 (Iic (0 : I)) ≤ μ 0 Set.univ := measure_mono (Set.subset_univ _)
        _ = 0 := hμ_univ
    have hright : μ 0 (Ioi (0 : I)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc
        μ 0 (Ioi (0 : I)) ≤ μ 0 Set.univ := measure_mono (Set.subset_univ _)
        _ = 0 := hμ_univ
    rw [hleft, hright]
  · obtain ⟨t, ht⟩ :=
      Math.MeasureTheory.unitInterval_cut_exists (μ 0) (M / 2) (half_pos hM_pos)
        (half_lt_self hM_pos)
    refine ⟨t, ?_⟩
    unfold IsFairCutPoint
    have hsplit : μ 0 (Iic t) + μ 0 (Ioi t) = μ 0 univ := by
      have h := measure_union (Iic_disjoint_Ioi (le_refl t)) measurableSet_Ioi (μ := μ 0)
      rw [Iic_union_Ioi] at h
      exact h.symm
    have hIic : (μ 0 (Iic t)).toReal = M / 2 := ht
    have hIoi : (μ 0 (Ioi t)).toReal = M / 2 := by
      have h_add :
          (μ 0 (Iic t)).toReal + (μ 0 (Ioi t)).toReal = M := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsplit]
      linarith
    apply le_antisymm
    · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (by linarith)
    · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (by linarith)

/-- Cut-and-choose gives an envy-free allocation for two finite non-atomic
measure agents. -/
theorem cutAndChoose_ef_exists
    (μ : Fin 2 → Measure I) [IsFiniteMeasure (μ 0)] [NullSingletonClass (μ 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A :=
  cutAndChoose_ef_exists_of_fairCutPoint_exists μ (fairCutPoint_exists μ)

/-- Bundled-instance form of cut-and-choose envy-free existence. -/
theorem cutAndChoose_exists_envyFree_allocation
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NullSingletonClass (M.measure 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ M.IsEnvyFree A :=
  cutAndChoose_ef_exists M.measure

/-- Cut-and-choose as a feasible rule on bundled two-agent measure instances. -/
noncomputable def cutAndChooseRule
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NullSingletonClass (M.measure 0)] :
    {A : Allocation (Fin 2) I // M.feasible A} :=
  let t := Classical.choose (fairCutPoint_exists M.measure)
  ⟨cutAndChooseAlloc M.measure t, cutAndChooseAlloc_isAllocation M.measure t⟩

/-- The bundled cut-and-choose rule is envy-free. -/
theorem cutAndChooseRule_isEnvyFree
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NullSingletonClass (M.measure 0)] :
    M.IsEnvyFree (cutAndChooseRule M).1 := by
  unfold cutAndChooseRule
  exact cutAndChoose_isEnvyFree M.measure
    (Classical.choose (fairCutPoint_exists M.measure))
    (Classical.choose_spec (fairCutPoint_exists M.measure))

end Divisible
end FairDivision
end SocialChoice
end GameTheory
