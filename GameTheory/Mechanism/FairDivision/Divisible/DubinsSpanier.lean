/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Divisible.CutAndChoose
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Dubins-Spanier Proportional Allocation

The Dubins-Spanier moving-knife argument for proportional divisible allocation
on the unit interval.
-/

open MeasureTheory Set
open scoped unitInterval

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Divisible

/-! ## ENNReal proportionality arithmetic -/

private theorem ennreal_prop_step (n : ℕ) (hn : 0 < n)
    (P Q X M : ENNReal)
    (hM : P + Q = M)
    (hP_fin : P ≠ ⊤)
    (hPQ : (↑(n + 1) : ENNReal) * P ≤ M)
    (hIH : Q ≤ ↑n * X) :
    M ≤ (↑(n + 1) : ENNReal) * X := by
  rw [← hM]
  have hPQ' : (↑(n + 1) : ENNReal) * P ≤ P + Q := by
    simpa [hM] using hPQ
  have h_expand : (↑(n + 1) : ENNReal) * P = P + ↑n * P := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
  have h_nP_le_Q : ↑n * P ≤ Q := by
    have h := hPQ'
    rw [h_expand] at h
    exact ENNReal.le_of_add_le_add_left hP_fin h
  have hn_ne_zero : (↑n : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hn_ne_top : (↑n : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top n
  have h_nP_le_nX : P * ↑n ≤ X * ↑n := by
    simpa [mul_comm] using le_trans h_nP_le_Q hIH
  have hP_le_X : P ≤ X := by
    rwa [ENNReal.mul_le_mul_iff_left hn_ne_zero hn_ne_top] at h_nP_le_nX
  have hsum : P + Q ≤ X + ↑n * X := add_le_add hP_le_X hIH
  have h_rhs : X + ↑n * X = (↑(n + 1) : ENNReal) * X := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
  exact le_trans hsum (le_of_eq h_rhs)

/-! ## Inductive proportional existence for `Fin n` agents -/

private def DubinsSpanierProp (n : ℕ) : Prop :=
  ∀ (μ : Fin n → Measure I),
    (∀ i, IsFiniteMeasure (μ i)) →
    (∀ i, NullSingletonClass (μ i)) →
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ IsProportional n (MeasureValuation μ) A

private theorem ds_one : DubinsSpanierProp 1 := by
  intro μ _ _
  refine ⟨fun _ => Set.univ, ⟨fun i => ?_, fun i j hij => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i
    exact MeasurableSet.univ
  · fin_cases i
    fin_cases j
    exact absurd rfl hij
  · simp [Set.iUnion_const]
  · fin_cases i
    simp [MeasureValuation]

private theorem ds_step (n : ℕ) (hn : 0 < n) (ih : DubinsSpanierProp n) :
    DubinsSpanierProp (n + 1) := by
  intro μ hfin hnoatoms
  have hn1_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hn1_gt1 : (1 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ hn
  have hthresh : ∀ i : Fin (n + 1), ∃ t : I,
      (↑(n + 1) : ENNReal) * μ i (Set.Iic t) = μ i Set.univ := by
    intro i
    rcases eq_or_ne (μ i Set.univ) 0 with h0 | hpos
    · exact ⟨0, by
        have hle : μ i (Set.Iic 0) ≤ μ i Set.univ := measure_mono (Set.subset_univ _)
        rw [h0] at hle
        rw [h0, le_antisymm hle zero_le, mul_zero]⟩
    · haveI := hfin i
      haveI := hnoatoms i
      have hM_fin : μ i Set.univ ≠ ⊤ := measure_ne_top _ _
      have hM_pos : 0 < (μ i Set.univ).toReal := ENNReal.toReal_pos hpos hM_fin
      have hc_pos : 0 < (μ i Set.univ).toReal / (↑(n + 1) : ℝ) :=
        div_pos hM_pos hn1_pos
      have hc_lt : (μ i Set.univ).toReal / (↑(n + 1) : ℝ) < (μ i Set.univ).toReal :=
        div_lt_self hM_pos hn1_gt1
      obtain ⟨ti, hti⟩ :=
        Math.MeasureTheory.unitInterval_cut_exists (μ i) _ hc_pos hc_lt
      refine ⟨ti, ?_⟩
      have hIic_fin : μ i (Set.Iic ti) ≠ ⊤ := measure_ne_top _ _
      have hLHS_fin : (↑(n + 1) : ENNReal) * μ i (Set.Iic ti) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hIic_fin
      have h_toReal :
          ((↑(n + 1) : ENNReal) * μ i (Set.Iic ti)).toReal =
            (μ i Set.univ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hti]
        have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
        field_simp [hn1_ne]
      rw [← ENNReal.ofReal_toReal hLHS_fin, h_toReal, ENNReal.ofReal_toReal hM_fin]
  let t : Fin (n + 1) → I := fun i => (hthresh i).choose
  have ht_prop : ∀ i, (↑(n + 1) : ENNReal) * μ i (Set.Iic (t i)) = μ i Set.univ :=
    fun i => (hthresh i).choose_spec
  obtain ⟨i_star, _, hi_star⟩ :=
    Finset.exists_min_image Finset.univ t Finset.univ_nonempty
  have ht_min : ∀ j : Fin (n + 1), t i_star ≤ t j := fun j =>
    hi_star j (Finset.mem_univ j)
  have ht_mono : ∀ j : Fin (n + 1),
      (↑(n + 1) : ENNReal) * μ j (Set.Iic (t i_star)) ≤ μ j Set.univ :=
    fun j => le_trans
      (mul_le_mul_of_nonneg_left
        (measure_mono (Set.Iic_subset_Iic.mpr (ht_min j))) zero_le)
      (ht_prop j).le
  let μ_rem : Fin n → Measure I :=
    fun j => (μ (i_star.succAbove j)).restrict (Set.Ioi (t i_star))
  haveI hfin_rem : ∀ j : Fin n, IsFiniteMeasure (μ_rem j) := fun _ => inferInstance
  haveI hnoatoms_rem : ∀ j : Fin n, NullSingletonClass (μ_rem j) := fun _ => inferInstance
  obtain ⟨A_rem, hA_rem, hprop_rem⟩ :=
    ih μ_rem (fun j => hfin_rem j) (fun j => hnoatoms_rem j)
  let A : Allocation (Fin (n + 1)) I :=
    Fin.insertNth i_star (Set.Iic (t i_star)) (fun j => A_rem j ∩ Set.Ioi (t i_star))
  have hA_star : A i_star = Set.Iic (t i_star) := Fin.insertNth_apply_same _ _ _
  have hA_other : ∀ j : Fin n, A (i_star.succAbove j) = A_rem j ∩ Set.Ioi (t i_star) :=
    fun j => Fin.insertNth_apply_succAbove _ _ _ j
  refine ⟨A, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i = i_star
    · rw [hi, hA_star]
      exact measurableSet_Iic
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [hA_other]
      exact (hA_rem.measurable j).inter measurableSet_Ioi
  · intro i₁ i₂ hi₁₂
    by_cases h₁ : i₁ = i_star <;> by_cases h₂ : i₂ = i_star
    · exact absurd (h₁.trans h₂.symm) hi₁₂
    · obtain ⟨j₂, rfl⟩ := Fin.exists_succAbove_eq h₂
      rw [h₁, hA_star, hA_other]
      exact Set.disjoint_of_subset_right Set.inter_subset_right (Set.Iic_disjoint_Ioi le_rfl)
    · obtain ⟨j₁, rfl⟩ := Fin.exists_succAbove_eq h₁
      rw [h₂, hA_star, hA_other]
      exact (Set.disjoint_of_subset_right Set.inter_subset_right
        (Set.Iic_disjoint_Ioi le_rfl)).symm
    · obtain ⟨j₁, rfl⟩ := Fin.exists_succAbove_eq h₁
      obtain ⟨j₂, rfl⟩ := Fin.exists_succAbove_eq h₂
      rw [hA_other, hA_other]
      have hj₁₂ : j₁ ≠ j₂ := fun h => hi₁₂ (congrArg _ h)
      exact Set.disjoint_of_subset_left Set.inter_subset_left
        (Set.disjoint_of_subset_right Set.inter_subset_left (hA_rem.disjoint _ _ hj₁₂))
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ≤ t i_star
    · exact ⟨_, by rw [hA_star]; exact hx⟩
    · push Not at hx
      have hx_ioi : x ∈ Set.Ioi (t i_star) := hx
      obtain ⟨j, hj⟩ := hA_rem.mem_iUnion x
      exact ⟨i_star.succAbove j, (hA_other j).symm ▸ ⟨hj, hx_ioi⟩⟩
  · intro i
    simp only [MeasureValuation]
    by_cases hi : i = i_star
    · subst hi
      rw [hA_star]
      exact (ht_prop i).ge
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [hA_other]
      apply ennreal_prop_step n hn
        (μ (i_star.succAbove j) (Set.Iic (t i_star)))
        (μ (i_star.succAbove j) (Set.Ioi (t i_star)))
        (μ (i_star.succAbove j) (A_rem j ∩ Set.Ioi (t i_star)))
      · rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
          Set.Iic_union_Ioi]
      · exact measure_ne_top _ _
      · exact ht_mono (i_star.succAbove j)
      · have hpj := hprop_rem j
        simp only [MeasureValuation] at hpj
        rw [show μ_rem j Set.univ = μ (i_star.succAbove j) (Set.Ioi (t i_star)) from
          Measure.restrict_apply_univ _] at hpj
        rw [show μ_rem j (A_rem j) =
            μ (i_star.succAbove j) (A_rem j ∩ Set.Ioi (t i_star)) from
          Measure.restrict_apply (hA_rem.measurable j)] at hpj
        exact hpj

private theorem dubinsSpanierFin : ∀ (n : ℕ), 0 < n → DubinsSpanierProp n := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact absurd hn (Nat.lt_irrefl 0)
  | succ n ih =>
      intro _hn
      by_cases hn' : n = 0
      · subst hn'
        exact ds_one
      · exact ds_step n (Nat.pos_of_ne_zero hn') (ih (Nat.pos_of_ne_zero hn'))

/-- Dubins-Spanier proportional existence for `n ≥ 1` agents indexed by `Fin n`. -/
theorem dubinsSpanierProportional (n : ℕ) (hn : 0 < n)
    (μ : Fin n → Measure I) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] :
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ IsProportional n (MeasureValuation μ) A :=
  dubinsSpanierFin n hn μ (fun _ => inferInstance) (fun _ => inferInstance)

/-- Bundled-instance form of Dubins-Spanier proportional existence. -/
theorem dubinsSpanier_exists_proportional_allocation (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NullSingletonClass (M.measure i)] :
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ M.IsProportional n A :=
  dubinsSpanierProportional n hn M.measure

/-- The Dubins-Spanier rule chooses a proportional allocation from the existence theorem. -/
noncomputable def dubinsSpanierRule (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NullSingletonClass (M.measure i)] :
    {A : Allocation (Fin n) I // IsAllocation A} :=
  let A := Classical.choose (dubinsSpanier_exists_proportional_allocation n hn M)
  ⟨A, (Classical.choose_spec (dubinsSpanier_exists_proportional_allocation n hn M)).1⟩

/-- The bundled Dubins-Spanier rule is proportional. -/
theorem dubinsSpanierRule_isProportional (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NullSingletonClass (M.measure i)] :
    M.IsProportional n (dubinsSpanierRule n hn M).1 := by
  unfold dubinsSpanierRule
  exact (Classical.choose_spec (dubinsSpanier_exists_proportional_allocation n hn M)).2

end Divisible
end FairDivision
end SocialChoice
end GameTheory
