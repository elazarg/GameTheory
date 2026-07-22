/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.GaleShapley

/-!
# Stable-matching order with outside options

This file defines the general stable-matching order without assuming balanced
markets or complete acceptability.  Partners are optional: an unmatched agent is
evaluated at its reservation value.

The main result here is the part of the Conway-Knuth picture that follows
directly from the deferred-acceptance optimality theorem: men-proposing deferred
acceptance is the greatest stable matching in the `α`-side order.  The full
optional-market lattice is built in `GaleShapley.OptionalLattice`.
-/

namespace GameTheory

namespace MatchingMarket

variable {α β : Type} (M : MatchingMarket α β)

/-- The `α`-side value of an optional partner.  Being unmatched is worth the
reservation value. -/
def prefAOption (a : α) : Option β → ℤ
  | none => M.reserveA a
  | some b => M.prefA a b

/-- The `β`-side value of an optional partner.  Being unmatched is worth the
reservation value. -/
def prefBOption (b : β) : Option α → ℤ
  | none => M.reserveB b
  | some a => M.prefB b a

@[simp] theorem prefAOption_none (a : α) :
    M.prefAOption a none = M.reserveA a :=
  rfl

@[simp] theorem prefAOption_some (a : α) (b : β) :
    M.prefAOption a (some b) = M.prefA a b :=
  rfl

@[simp] theorem prefBOption_none (b : β) :
    M.prefBOption b none = M.reserveB b :=
  rfl

@[simp] theorem prefBOption_some (b : β) (a : α) :
    M.prefBOption b (some a) = M.prefB b a :=
  rfl

/-- Under strict preferences and no equality with the outside option, equal
`α`-side optional-partner values identify the optional partner. -/
theorem prefAOption_injective
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b) (a : α) :
    Function.Injective (M.prefAOption a) := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b =>
          exact False.elim ((hAne a b) hxy)
  | some b₁ =>
      cases y with
      | none =>
          exact False.elim ((hAne a b₁) hxy.symm)
      | some b₂ =>
          exact congrArg some ((hAinj a) hxy)

/-- Under strict preferences and no equality with the outside option, equal
`β`-side optional-partner values identify the optional partner. -/
theorem prefBOption_injective
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hBne : ∀ b a, M.reserveB b ≠ M.prefB b a) (b : β) :
    Function.Injective (M.prefBOption b) := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some a =>
          exact False.elim ((hBne b a) hxy)
  | some a₁ =>
      cases y with
      | none =>
          exact False.elim ((hBne b a₁) hxy.symm)
      | some a₂ =>
          exact congrArg some ((hBinj b) hxy)

namespace OptionalOrder

/-- The `α`-side order on stable matchings in markets with outside options:
`μ ≤ ν` if every `α`-agent weakly prefers its optional partner in `ν` to its
optional partner in `μ`. -/
def menLe (μ ν : M.StableMatching) : Prop :=
  ∀ a : α, M.prefAOption a (μ a) ≤ M.prefAOption a (ν a)

theorem menLe_refl (μ : M.StableMatching) : menLe M μ μ := by
  intro a
  rfl

theorem menLe_trans {μ ν η : M.StableMatching}
    (hμν : menLe M μ ν) (hνη : menLe M ν η) :
    menLe M μ η := by
  intro a
  exact _root_.le_trans (hμν a) (hνη a)

theorem menLe_antisymm
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    {μ ν : M.StableMatching}
    (hμν : menLe M μ ν) (hνμ : menLe M ν μ) :
    μ = ν := by
  apply StableMatching.ext
  intro a
  exact M.prefAOption_injective hAinj hAne a (_root_.le_antisymm (hμν a) (hνμ a))

variable [Fintype α] [Fintype β]

/-- The stable matching produced by men-proposing deferred acceptance. -/
noncomputable def gsStable
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b)) : M.StableMatching :=
  ⟨M.daMatching, M.daMatching_isStable hAinj hBinj⟩

/-- Men-proposing deferred acceptance is greatest for the `α`-side optional-partner
order.  This does not assume balanced sides or complete acceptability. -/
theorem gsStable_greatest
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    (μ : M.StableMatching) :
    menLe M μ (gsStable M hAinj hBinj) := by
  intro a
  cases hμa : μ a with
  | none =>
      cases hda : M.daMatching a with
      | none =>
          simp [prefAOption, gsStable, hda]
      | some b =>
          have hir := (M.daMatching_isStable hAinj hBinj).2.1 a b hda
          simp [prefAOption, gsStable, hda, hir.1]
  | some b' =>
      obtain ⟨b, hda, hle⟩ := M.daMatching_man_optimal hAinj hBinj hAne μ.2 hμa
      simp [prefAOption, gsStable, hda, hle]

/-- Compatibility/order-style name for `gsStable_greatest`: deferred acceptance
is greatest among stable matchings under the generalized `α`-side order. This
avoids installing a global `LE` instance, since the complete-market lattice
uses a stronger specialized order. -/
theorem le_gsStable
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b) (μ : M.StableMatching) :
    menLe M μ (gsStable M hAinj hBinj) :=
  gsStable_greatest M hAinj hBinj hAne μ

end OptionalOrder

end MatchingMarket

end GameTheory
