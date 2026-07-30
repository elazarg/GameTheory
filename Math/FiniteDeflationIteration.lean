/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Order.WellFounded

/-!
# Well-founded iteration of finite deflations

Repeated zero-drift restriction is most conveniently organized inside one
fixed finite ambient type.  A node records the currently active indices.
A child is a proper subset of its parent, while every deleted index is
remembered by the complementary exceptional set.

This formulation avoids iterated subtype towers.  It also gives the support
calculus needed by exceptional accounts: an old exceptional cost remains
exceptional after a deflation, a new cost supported on the freshly removed
set is exceptional at the child, and their sum is again exceptional.

The module is purely finite and algebraic.  It does not construct a
deflation step or attach any stochastic or strategic meaning to one.
-/

set_option autoImplicit false

noncomputable section

namespace Math

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- One node in a finite deflation process, represented in a fixed ambient
finite index type. -/
structure FiniteDeflationState (I : Type*) where
  active : Finset I

namespace FiniteDeflationState

/-- Indices deleted before reaching this node. -/
def exceptional (state : FiniteDeflationState I) : Finset I :=
  Finset.univ \ state.active

/-- Natural-number rank of a deflation node. -/
def rank (state : FiniteDeflationState I) : ℕ :=
  state.active.card

/-- A child is a genuine deflation when it retains a proper subset of the
parent's active indices. -/
def Deflates
    (child parent : FiniteDeflationState I) : Prop :=
  child.active ⊂ parent.active

/-- Rank order used for recursive finite deflation. -/
def RankLt
    (child parent : FiniteDeflationState I) : Prop :=
  child.rank < parent.rank

omit [Fintype I] [DecidableEq I] in
theorem rankLt_of_deflates
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    RankLt child parent :=
  Finset.card_lt_card step

omit [Fintype I] [DecidableEq I] in
/-- The finite deflation rank is well founded. -/
theorem rankLt_wellFounded :
    WellFounded
      (RankLt :
        FiniteDeflationState I → FiniteDeflationState I → Prop) :=
  wellFounded_lt.onFun

omit [Fintype I] [DecidableEq I] in
/-- Proper active-set inclusion itself is well founded. -/
theorem deflates_wellFounded :
    WellFounded
      (Deflates :
        FiniteDeflationState I → FiniteDeflationState I → Prop) := by
  apply rankLt_wellFounded.mono
  intro child parent step
  exact rankLt_of_deflates step

omit [Fintype I] [DecidableEq I] in
/-- Well-founded induction principle for arbitrary data carried by a finite
deflation node. -/
theorem deflation_induction
    {motive : FiniteDeflationState I → Prop}
    (step :
      ∀ parent,
        (∀ child, Deflates child parent → motive child) →
          motive parent) :
    ∀ state, motive state := by
  intro state
  exact deflates_wellFounded.induction state fun parent recurse =>
    step parent fun child child_lt => recurse child child_lt

/-- Delete a specified finite subset of the active indices. -/
def delete
    (parent : FiniteDeflationState I) (removed : Finset I) :
    FiniteDeflationState I where
  active := parent.active \ removed

omit [Fintype I] in
/-- Deleting a nonempty subset of the active set is a genuine deflation. -/
theorem delete_deflates
    (parent : FiniteDeflationState I) (removed : Finset I)
    (removed_subset : removed ⊆ parent.active)
    (removed_nonempty : removed.Nonempty) :
    Deflates (parent.delete removed) parent := by
  exact Finset.sdiff_ssubset removed_subset removed_nonempty

omit [Fintype I] in
/-- The explicit deletion constructor strictly lowers rank. -/
theorem rank_delete_lt
    (parent : FiniteDeflationState I) (removed : Finset I)
    (removed_subset : removed ⊆ parent.active)
    (removed_nonempty : removed.Nonempty) :
    (parent.delete removed).rank < parent.rank :=
  rankLt_of_deflates
    (parent.delete_deflates removed removed_subset removed_nonempty)

/-- The indices removed in one abstract proper-subset step. -/
def removed
    {child parent : FiniteDeflationState I}
    (_step : Deflates child parent) : Finset I :=
  parent.active \ child.active

omit [Fintype I] in
theorem removed_subset_parent
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    removed step ⊆ parent.active :=
  Finset.sdiff_subset

omit [Fintype I] in
theorem removed_nonempty
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    (removed step).Nonempty := by
  exact Finset.sdiff_nonempty.mpr step.not_subset

omit [Fintype I] in
/-- One proper-subset step is exactly deletion of its removed set. -/
theorem delete_removed
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    parent.delete (removed step) = child := by
  cases parent with
  | mk parentActive =>
      cases child with
      | mk childActive =>
          simp only [delete, removed] at step ⊢
          congr
          exact Finset.sdiff_sdiff_eq_self step.le

/-- Exceptional sets grow monotonically under deflation. -/
theorem exceptional_subset
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    parent.exceptional ⊆ child.exceptional := by
  intro index index_exceptional
  simp only [exceptional, Finset.mem_sdiff,
    Finset.mem_univ, true_and] at index_exceptional ⊢
  exact fun index_child => index_exceptional (step.le index_child)

/-- The child's exceptional set is the old exceptional set together with
exactly the indices removed in this step. -/
theorem exceptional_eq_union_removed
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent) :
    child.exceptional = parent.exceptional ∪ removed step := by
  ext index
  simp only [exceptional, removed, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro index_not_child
    by_cases index_parent : index ∈ parent.active
    · exact Or.inr ⟨index_parent, index_not_child⟩
    · exact Or.inl index_parent
  · rintro (index_not_parent | ⟨_, index_not_child⟩)
    · exact fun index_child => index_not_parent (step.le index_child)
    · exact index_not_child

/-- A scalar transition cost is exceptional at a node when it vanishes on
every still-active index. -/
def SupportsExceptional
    (state : FiniteDeflationState I) (cost : I → ℝ) : Prop :=
  ∀ index, index ∈ state.active → cost index = 0

omit [Fintype I] [DecidableEq I] in
theorem supportsExceptional_zero
    (state : FiniteDeflationState I) :
    state.SupportsExceptional (fun _ => 0) := by
  intro index _
  rfl

omit [Fintype I] [DecidableEq I] in
theorem SupportsExceptional.add
    {state : FiniteDeflationState I}
    {left right : I → ℝ}
    (hleft : state.SupportsExceptional left)
    (hright : state.SupportsExceptional right) :
    state.SupportsExceptional (fun index => left index + right index) := by
  intro index index_active
  change left index + right index = 0
  rw [hleft index index_active, hright index index_active, zero_add]

omit [Fintype I] [DecidableEq I] in
/-- An old exceptional cost remains exceptional after further deflation. -/
theorem SupportsExceptional.of_deflates
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent)
    {cost : I → ℝ}
    (hcost : parent.SupportsExceptional cost) :
    child.SupportsExceptional cost := by
  intro index index_child
  exact hcost index (step.le index_child)

omit [Fintype I] in
/-- A new cost supported on the freshly removed set is exceptional at the
child node. -/
theorem supportsExceptional_of_supportedOn_removed
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent)
    {cost : I → ℝ}
    (cost_zero :
      ∀ index, index ∉ removed step → cost index = 0) :
    child.SupportsExceptional cost := by
  intro index index_child
  apply cost_zero
  simp only [removed, Finset.mem_sdiff, not_and]
  intro _
  exact fun index_not_child => index_not_child index_child

omit [Fintype I] in
/-- Accumulate an old exceptional cost with a cost introduced on the
freshly removed set. -/
theorem supportsExceptional_accumulate
    {child parent : FiniteDeflationState I}
    (step : Deflates child parent)
    {oldCost newCost : I → ℝ}
    (old_exceptional : parent.SupportsExceptional oldCost)
    (new_supported :
      ∀ index, index ∉ removed step → newCost index = 0) :
    child.SupportsExceptional
      (fun index => oldCost index + newCost index) :=
  (old_exceptional.of_deflates step).add
    (supportsExceptional_of_supportedOn_removed step new_supported)

/-- The dependent finite type of indices active at one ambient node. -/
abbrev ActiveIndex (state : FiniteDeflationState I) :=
  {index : I // index ∈ state.active}

noncomputable instance instFintypeActiveIndex
    (state : FiniteDeflationState I) :
    Fintype state.ActiveIndex :=
  Fintype.ofFinite _

/-- Active indices on which a scalar score is strictly positive. -/
def strictActiveSet
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    Finset state.ActiveIndex :=
  Finset.univ.filter fun index => 0 < score index

omit [DecidableEq I] in
theorem mem_strictActiveSet_iff
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ)
    (index : state.ActiveIndex) :
    index ∈ state.strictActiveSet score ↔ 0 < score index := by
  simp [strictActiveSet]

/-- Flatten a strict set of active subtype indices back into the fixed
ambient type. -/
def strictAmbientSet
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) : Finset I :=
  (state.strictActiveSet score).image Subtype.val

theorem strictAmbientSet_subset_active
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    state.strictAmbientSet score ⊆ state.active := by
  intro index index_strict
  simp only [strictAmbientSet, Finset.mem_image] at index_strict
  obtain ⟨activeIndex, _, rfl⟩ := index_strict
  exact activeIndex.2

theorem strictAmbientSet_nonempty_iff
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    (state.strictAmbientSet score).Nonempty ↔
      ∃ index, 0 < score index := by
  constructor
  · rintro ⟨index, index_strict⟩
    simp only [strictAmbientSet, Finset.mem_image] at index_strict
    obtain ⟨activeIndex, activeIndex_strict, _⟩ := index_strict
    exact ⟨activeIndex,
      (state.mem_strictActiveSet_iff score activeIndex).mp
        activeIndex_strict⟩
  · rintro ⟨activeIndex, score_pos⟩
    refine ⟨activeIndex.1, ?_⟩
    simp only [strictAmbientSet, Finset.mem_image]
    exact ⟨activeIndex,
      (state.mem_strictActiveSet_iff score activeIndex).mpr score_pos,
      rfl⟩

/-- Delete every currently active index with positive score. -/
def deleteStrict
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    FiniteDeflationState I :=
  state.delete (state.strictAmbientSet score)

/-- A positive active score makes strict deletion a genuine ambient
deflation. -/
theorem deleteStrict_deflates
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ)
    (strict_nonempty : ∃ index, 0 < score index) :
    (state.deleteStrict score).Deflates state := by
  apply state.delete_deflates
  · exact state.strictAmbientSet_subset_active score
  · exact
      (state.strictAmbientSet_nonempty_iff score).mpr
        strict_nonempty

/-- Strict active deletion lowers the ambient active-set rank. -/
theorem rank_deleteStrict_lt
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ)
    (strict_nonempty : ∃ index, 0 < score index) :
    (state.deleteStrict score).rank < state.rank :=
  rankLt_of_deflates
    (state.deleteStrict_deflates score strict_nonempty)

/-- For nonnegative scores, either all active scores vanish or deleting the
positive-score set is a genuine finite deflation. -/
theorem all_score_zero_or_deleteStrict_deflates
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ)
    (score_nonneg : ∀ index, 0 ≤ score index) :
    (∀ index, score index = 0) ∨
      (state.deleteStrict score).Deflates state := by
  by_cases strict_nonempty : ∃ index, 0 < score index
  · exact Or.inr (state.deleteStrict_deflates score strict_nonempty)
  · left
    intro index
    apply le_antisymm
    · exact le_of_not_gt fun score_pos =>
        strict_nonempty ⟨index, score_pos⟩
    · exact score_nonneg index

/-- The exceptional set after strict active deletion is the old exceptional
set together with the newly positive-score indices. -/
theorem exceptional_deleteStrict_eq
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    (state.deleteStrict score).exceptional =
      state.exceptional ∪ state.strictAmbientSet score := by
  ext index
  by_cases index_active : index ∈ state.active <;>
    by_cases index_strict :
      index ∈ state.strictAmbientSet score <;>
    simp [exceptional, deleteStrict, delete,
      index_active, index_strict]

/-- Active indices after strict deletion are equivalent to the old active
indices outside the strict active set.  This equivalence flattens the
otherwise nested residual subtype. -/
def deleteStrictActiveEquivRetained
    (state : FiniteDeflationState I)
    (score : state.ActiveIndex → ℝ) :
    (state.deleteStrict score).ActiveIndex ≃
      {index : state.ActiveIndex //
        index ∉ state.strictActiveSet score} where
  toFun index := by
    have retained :
        index.1 ∈ state.active ∧
          index.1 ∉ state.strictAmbientSet score :=
      Finset.mem_sdiff.mp index.2
    refine ⟨⟨index.1, retained.1⟩, ?_⟩
    intro index_strict
    apply retained.2
    simp only [strictAmbientSet, Finset.mem_image]
    exact ⟨⟨index.1, retained.1⟩, index_strict, rfl⟩
  invFun index := by
    refine ⟨index.1.1, Finset.mem_sdiff.mpr ⟨index.1.2, ?_⟩⟩
    intro index_ambient_strict
    simp only [strictAmbientSet, Finset.mem_image] at index_ambient_strict
    obtain ⟨strictIndex, strictIndex_mem, value_eq⟩ :=
      index_ambient_strict
    apply index.2
    have strictIndex_eq : strictIndex = index.1 := by
      apply Subtype.ext
      exact value_eq
    simpa only [strictIndex_eq] using strictIndex_mem
  left_inv index := by
    apply Subtype.ext
    rfl
  right_inv index := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

end FiniteDeflationState
end Math
