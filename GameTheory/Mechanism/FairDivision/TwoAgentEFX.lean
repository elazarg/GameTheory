/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Two-agent EFX for finite indivisible goods

Every finite two-agent instance with nonnegative additive item values admits an
EFX allocation.  The proof uses the classical cut-and-choose construction:
agent zero chooses a partition maximizing the value of its worse side, then
agent one selects its preferred side. The constructor returns the canonical
disjoint `Allocation`; completeness remains a separate certificate.

For the two-agent cut-and-choose construction, see G. Plaut and T. Roughgarden,
“Almost Envy-Freeness with General Valuations,” SODA 2018.
-/

namespace GameTheory.Mechanism.FairDivision

open Finset

variable {G : Type}

/-- The canonical two-agent allocation with agent zero receiving `S` and
agent one receiving the disjoint bundle `T`. -/
def twoAgentAllocation (S T : Bundle G) (hdisj : Disjoint S T) :
    Allocation (Fin 2) G where
  bundle i := if i = 0 then S else T
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa using hdisj
    · simpa [disjoint_comm] using hdisj
    · exact (hij rfl).elim

@[simp]
theorem twoAgentAllocation_zero (S T : Bundle G) (hdisj : Disjoint S T) :
    twoAgentAllocation S T hdisj (0 : Fin 2) = S := by
  simp [twoAgentAllocation]

@[simp]
theorem twoAgentAllocation_one (S T : Bundle G) (hdisj : Disjoint S T) :
    twoAgentAllocation S T hdisj (1 : Fin 2) = T := by
  simp [twoAgentAllocation]

/-- A canonical two-agent allocation is complete when its two bundles cover
the finite goods universe. -/
theorem twoAgentAllocation_isComplete [Fintype G] [DecidableEq G]
    (S T : Bundle G) (hdisj : Disjoint S T)
    (hcover : S ∪ T = Finset.univ) :
    IsComplete (twoAgentAllocation S T hdisj) := by
  intro g
  have hg : g ∈ S ∪ T := by simp [hcover]
  rcases Finset.mem_union.mp hg with hgS | hgT
  · exact ⟨0, by simpa using hgS⟩
  · exact ⟨1, by simpa using hgT⟩

/-- Two agents who both value one good positively need not admit an envy-free
complete allocation. -/
theorem ef_impossible_two_agents_one_good :
    ∃ v : AdditiveValuation (Fin 2) (Fin 1), Nonnegative v ∧
      ¬ ∃ A : Allocation (Fin 2) (Fin 1), IsComplete A ∧ IsEnvyFree v A := by
  classical
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro _ _
    norm_num
  · rintro ⟨A, hcomplete, hef⟩
    rcases hcomplete 0 with ⟨owner, howner⟩
    fin_cases owner
    · have hnot : (0 : Fin 1) ∉ A (1 : Fin 2) := by
        intro hmem
        exact Finset.disjoint_left.mp
          (A.pairwise_disjoint (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide))
          howner hmem
      have howner0 : (0 : Fin 1) ∈ A (0 : Fin 2) := by simpa using howner
      have hown : A (0 : Fin 2) = Finset.univ := by
        ext g
        fin_cases g
        simp [howner0]
      have hother : A (1 : Fin 2) = ∅ := by
        ext g
        fin_cases g
        simp [hnot]
      have hle := hef (1 : Fin 2) (0 : Fin 2)
      have hself :
          value (fun _ _ => (1 : ℝ)) (1 : Fin 2) (A (1 : Fin 2)) = 0 := by
        simp [hother]
      have henvied :
          value (fun _ _ => (1 : ℝ)) (1 : Fin 2) (A (0 : Fin 2)) = 1 := by
        simp [hown, value]
      linarith
    · have hnot : (0 : Fin 1) ∉ A (0 : Fin 2) := by
        intro hmem
        exact Finset.disjoint_left.mp
          (A.pairwise_disjoint (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide))
          howner hmem
      have howner1 : (0 : Fin 1) ∈ A (1 : Fin 2) := by simpa using howner
      have hown : A (1 : Fin 2) = Finset.univ := by
        ext g
        fin_cases g
        simp [howner1]
      have hother : A (0 : Fin 2) = ∅ := by
        ext g
        fin_cases g
        simp [hnot]
      have hle := hef (0 : Fin 2) (1 : Fin 2)
      have hself :
          value (fun _ _ => (1 : ℝ)) (0 : Fin 2) (A (0 : Fin 2)) = 0 := by
        simp [hother]
      have henvied :
          value (fun _ _ => (1 : ℝ)) (0 : Fin 2) (A (1 : Fin 2)) = 1 := by
        simp [hown, value]
      linarith

section TwoAgents

variable [Fintype G] [DecidableEq G]

private noncomputable def cutScore (v : AdditiveValuation (Fin 2) G)
    (S : Bundle G) : ℝ :=
  min (value v (0 : Fin 2) S)
    (value v (0 : Fin 2) (Finset.univ \ S))

private theorem cutScore_compl (v : AdditiveValuation (Fin 2) G)
    (S : Bundle G) :
    cutScore v (Finset.univ \ S) = cutScore v S := by
  unfold cutScore
  rw [Finset.sdiff_sdiff_eq_self
    (s := (Finset.univ : Finset G)) (t := S) (Finset.subset_univ S)]
  exact min_comm _ _

private theorem maximin_cut_no_envy_after_erase_right
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    {g : G} (hg : g ∈ Finset.univ \ S) (hpos : 0 < v (0 : Fin 2) g) :
    value v (0 : Fin 2) S ≥
      value v (0 : Fin 2) ((Finset.univ \ S).erase g) := by
  by_contra hnot
  have hlt : value v (0 : Fin 2) S <
      value v (0 : Fin 2) ((Finset.univ \ S).erase g) := lt_of_not_ge hnot
  have hgS : g ∉ S := (Finset.mem_sdiff.mp hg).2
  have hcomp : Finset.univ \ insert g S = (Finset.univ \ S).erase g := by
    ext x
    by_cases hxg : x = g
    · subst x
      simp [hgS]
    · simp [hxg]
  have hnewS :
      value v (0 : Fin 2) (insert g S) =
        v (0 : Fin 2) g + value v (0 : Fin 2) S :=
    value_insert_of_notMem v (0 : Fin 2) hgS
  have hnewScore : cutScore v (insert g S) > cutScore v S := by
    unfold cutScore
    rw [hcomp, hnewS]
    have hminOld : min (value v (0 : Fin 2) S)
        (value v (0 : Fin 2) (Finset.univ \ S)) =
        value v (0 : Fin 2) S := by
      exact min_eq_left (le_trans (le_of_lt hlt)
        (value_erase_le hnonneg (0 : Fin 2) (Finset.univ \ S) g))
    rw [hminOld]
    exact lt_min (by linarith [hpos]) hlt
  have hle := hmax (insert g S) (by simp)
  exact not_lt_of_ge hle hnewScore

private theorem maximin_cut_no_envy_after_erase_left
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    {g : G} (hg : g ∈ S) (hpos : 0 < v (0 : Fin 2) g) :
    value v (0 : Fin 2) (Finset.univ \ S) ≥
      value v (0 : Fin 2) (S.erase g) := by
  have hmaxCompl : ∀ R ∈ Finset.univ.powerset,
      cutScore v R ≤ cutScore v (Finset.univ \ S) := by
    intro R hR
    simpa [cutScore_compl v S] using hmax R hR
  have hgcomp : g ∈ Finset.univ \ (Finset.univ \ S) := by simp [hg]
  have h := maximin_cut_no_envy_after_erase_right
    (v := v) hnonneg (S := Finset.univ \ S) hmaxCompl hgcomp hpos
  rwa [Finset.sdiff_sdiff_eq_self
    (s := (Finset.univ : Finset G)) (t := S) (Finset.subset_univ S)] at h

private theorem maximin_cut_partition_efx_for_zero
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    (hchoose : value v (1 : Fin 2) S ≤
      value v (1 : Fin 2) (Finset.univ \ S)) :
    IsEFX v (twoAgentAllocation S (Finset.univ \ S)
      Finset.disjoint_sdiff) := by
  intro i j g hg hpos
  fin_cases i <;> fin_cases j
  · exact value_erase_le hnonneg (0 : Fin 2) S g
  · simpa using maximin_cut_no_envy_after_erase_right hnonneg hmax
      (by simpa using hg) hpos
  · exact le_trans (value_erase_le hnonneg (1 : Fin 2) S g) hchoose
  · exact value_erase_le hnonneg (1 : Fin 2) (Finset.univ \ S) g

private theorem maximin_cut_partition_efx_for_zero_swapped
    {v : AdditiveValuation (Fin 2) G} (hnonneg : Nonnegative v)
    {S : Bundle G}
    (hmax : ∀ R ∈ Finset.univ.powerset, cutScore v R ≤ cutScore v S)
    (hchoose : value v (1 : Fin 2) (Finset.univ \ S) ≤
      value v (1 : Fin 2) S) :
    IsEFX v (twoAgentAllocation (Finset.univ \ S) S
      Finset.sdiff_disjoint) := by
  intro i j g hg hpos
  fin_cases i <;> fin_cases j
  · exact value_erase_le hnonneg (0 : Fin 2) (Finset.univ \ S) g
  · simpa using maximin_cut_no_envy_after_erase_left hnonneg hmax
      (by simpa using hg) hpos
  · exact le_trans
      (value_erase_le hnonneg (1 : Fin 2) (Finset.univ \ S) g) hchoose
  · exact value_erase_le hnonneg (1 : Fin 2) S g

/-- Every finite two-agent additive instance with nonnegative item values has
a complete EFX allocation. -/
theorem exists_efx_two_agents (v : AdditiveValuation (Fin 2) G)
    (hnonneg : Nonnegative v) :
    ∃ A : Allocation (Fin 2) G, IsComplete A ∧ IsEFX v A := by
  classical
  let cuts : Finset (Bundle G) := Finset.univ.powerset
  have hcutsNonempty : cuts.Nonempty := ⟨∅, by simp [cuts]⟩
  obtain ⟨S, _hS, hmax⟩ :=
    Finset.exists_max_image cuts (cutScore v) hcutsNonempty
  have hmax' : ∀ R ∈ Finset.univ.powerset,
      cutScore v R ≤ cutScore v S := by
    intro R hR
    exact hmax R hR
  by_cases hchoose : value v (1 : Fin 2) S ≤
      value v (1 : Fin 2) (Finset.univ \ S)
  · refine ⟨twoAgentAllocation S (Finset.univ \ S) Finset.disjoint_sdiff,
      ?_, maximin_cut_partition_efx_for_zero hnonneg hmax' hchoose⟩
    exact twoAgentAllocation_isComplete S (Finset.univ \ S)
      Finset.disjoint_sdiff (by ext g; simp)
  · refine ⟨twoAgentAllocation (Finset.univ \ S) S Finset.sdiff_disjoint,
      ?_, maximin_cut_partition_efx_for_zero_swapped hnonneg hmax'
        (le_of_lt (lt_of_not_ge hchoose))⟩
    exact twoAgentAllocation_isComplete (Finset.univ \ S) S
      Finset.sdiff_disjoint (by ext g; simp)

/-- Textbook specialization: two agents and two goods admit a complete EFX
allocation. -/
theorem efx_two_agents_two_goods (v : AdditiveValuation (Fin 2) (Fin 2))
    (hnonneg : Nonnegative v) :
    ∃ A : Allocation (Fin 2) (Fin 2), IsComplete A ∧ IsEFX v A :=
  exists_efx_two_agents v hnonneg

end TwoAgents

end GameTheory.Mechanism.FairDivision
