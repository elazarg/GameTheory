/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Basic

/-!
# Generic joint actions

This module contains the optional joint-action vocabulary shared by native
machine game forms and factored-observation stochastic games.  It deliberately
does not depend on any game-language presentation.
-/

namespace GameTheory

/-- Joint action profile with optional participation for each player. -/
abbrev JointAction {ι : Type} (Act : ι → Type) : Type :=
  ∀ i, Option (Act i)

/-- Factorized legality of a joint action: every active player chooses an
available action, and inactive players choose `none`. -/
def JointActionLegal {ι W : Type}
    (Act : ι → Type)
    (active : W → Finset ι)
    (terminal : W → Prop)
    (availableActions : W → (i : ι) → Set (Act i))
    (w : W) (a : JointAction Act) : Prop :=
  ¬ terminal w ∧
    ∀ i, match a i with
      | some ai => i ∈ active w ∧ ai ∈ availableActions w i
      | none => i ∉ active w

theorem JointActionLegal.not_terminal {ι W : Type}
    {Act : ι → Type}
    {active : W → Finset ι}
    {terminal : W → Prop}
    {availableActions : W → (i : ι) → Set (Act i)}
    {w : W} {a : JointAction Act}
    (h : JointActionLegal Act active terminal availableActions w a) :
    ¬ terminal w :=
  h.1

theorem JointActionLegal.some {ι W : Type}
    {Act : ι → Type}
    {active : W → Finset ι}
    {terminal : W → Prop}
    {availableActions : W → (i : ι) → Set (Act i)}
    {w : W} {a : JointAction Act} {i : ι} {ai : Act i}
    (h : JointActionLegal Act active terminal availableActions w a)
    (hai : a i = some ai) :
    i ∈ active w ∧ ai ∈ availableActions w i := by
  simpa [hai] using h.2 i

theorem JointActionLegal.none {ι W : Type}
    {Act : ι → Type}
    {active : W → Finset ι}
    {terminal : W → Prop}
    {availableActions : W → (i : ι) → Set (Act i)}
    {w : W} {a : JointAction Act} {i : ι}
    (h : JointActionLegal Act active terminal availableActions w a)
    (hai : a i = none) :
    i ∉ active w := by
  simpa [hai] using h.2 i

/-- The all-`none` joint action. -/
def noopAction {ι : Type} (Act : ι → Type) : JointAction Act :=
  fun _ => none

@[simp] theorem noopAction_apply {ι : Type} (Act : ι → Type) (i : ι) :
    noopAction Act i = none := rfl

theorem eq_noopAction_iff {ι : Type} {Act : ι → Type}
    {a : JointAction Act} :
    a = noopAction Act ↔ ∀ i, a i = none := by
  constructor
  · intro h i
    rw [h]
    rfl
  · intro h
    funext i
    exact h i

end GameTheory
