/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.EquivFin

/-!
# Finite-Type Transport

Small helpers for transporting functions along finite-type equivalences. These
are useful when a theorem is proved for `Fin (Fintype.card α)` and then applied
to an arbitrary finite type.
-/

namespace Math
namespace Fintype

/-- Reindex a family on `α` as a family on `β` along an equivalence
`e : α ≃ β`. -/
def reindex {α β γ : Type*} (e : α ≃ β) (f : α → γ) : β → γ :=
  fun b => f (e.symm b)

/-- Pull a family on `β` back to `α` along an equivalence `e : α ≃ β`. -/
def pullback {α β γ : Type*} (e : α ≃ β) (f : β → γ) : α → γ :=
  fun a => f (e a)

@[simp] theorem reindex_apply {α β γ : Type*} (e : α ≃ β) (f : α → γ) (b : β) :
    reindex e f b = f (e.symm b) :=
  rfl

@[simp] theorem pullback_apply {α β γ : Type*} (e : α ≃ β) (f : β → γ) (a : α) :
    pullback e f a = f (e a) :=
  rfl

@[simp] theorem reindex_apply_apply {α β γ : Type*} (e : α ≃ β) (f : α → γ)
    (a : α) :
    reindex e f (e a) = f a := by
  simp [reindex]

@[simp] theorem pullback_symm_apply {α β γ : Type*} (e : α ≃ β) (f : β → γ)
    (b : β) :
    pullback e f (e.symm b) = f b := by
  simp [pullback]

/-- Reindex a finite family by the canonical equivalence with `Fin`. -/
noncomputable def toFin {α γ : Type*} [Fintype α] (f : α → γ) :
    Fin (Fintype.card α) → γ :=
  fun j => f ((_root_.Fintype.equivFin α).symm j)

/-- Pull a `Fin (card α)` family back to the finite type `α`. -/
noncomputable def fromFin {α γ : Type*} [Fintype α] (f : Fin (Fintype.card α) → γ) :
    α → γ :=
  fun a => f (_root_.Fintype.equivFin α a)

@[simp] theorem toFin_apply {α γ : Type*} [Fintype α] (f : α → γ)
    (j : Fin (Fintype.card α)) :
    toFin f j = f ((_root_.Fintype.equivFin α).symm j) :=
  rfl

@[simp] theorem fromFin_apply {α γ : Type*} [Fintype α]
    (f : Fin (Fintype.card α) → γ) (a : α) :
    fromFin f a = f (_root_.Fintype.equivFin α a) :=
  rfl

@[simp] theorem toFin_equivFin {α γ : Type*} [Fintype α] (f : α → γ) (a : α) :
    toFin f (_root_.Fintype.equivFin α a) = f a := by
  simp [toFin]

@[simp] theorem fromFin_equivFin_symm {α γ : Type*} [Fintype α]
    (f : Fin (Fintype.card α) → γ) (j : Fin (Fintype.card α)) :
    fromFin f ((_root_.Fintype.equivFin α).symm j) = f j := by
  simp [fromFin]

end Fintype
end Math
