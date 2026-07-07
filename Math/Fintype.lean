/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Preorder.Finite

/-!
# Finite subtype cardinality helpers

Small generic consequences of mathlib's finite-cardinality API.
-/

namespace Math

universe u

noncomputable local instance {α : Type} [Fintype α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofFinite _

/-- If `p` implies `q` and the two finite subtypes have the same cardinality,
then `q` implies `p`. -/
theorem subtype_of_card_eq_of_imp {α : Type} [Fintype α] {p q : α → Prop}
    (hpq : ∀ x, p x → q x)
    (hcard : Fintype.card {x : α // p x} = Fintype.card {x : α // q x})
    {x : α} (hx : q x) : p x := by
  classical
  by_contra hnot
  let f : {x : α // p x} → {x : α // q x} := fun y => ⟨y.1, hpq y.1 y.2⟩
  have hfinj : Function.Injective f := by
    intro y z hyz
    exact Subtype.ext (congrArg (fun w : {x : α // q x} => w.1) hyz)
  have hnotSurj : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
    have hyval : y.1 = x := congrArg Subtype.val hy
    exact hnot (hyval ▸ y.2)
  have hlt := Fintype.card_lt_of_injective_not_surjective f hfinj hnotSurj
  rw [hcard] at hlt
  exact (lt_irrefl _ hlt)

/-- For a finite transitive irreflexive relation, every point is either already
maximal or lies below a maximal point. Here `r x y` means that `x` is above
`y`; maximality is therefore `∀ b, ¬ r b m`. -/
theorem exists_maximal_or_rel_of_finite_trans_irrefl {α : Type u} [Finite α]
    (r : α → α → Prop)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hirrefl : ∀ a, ¬ r a a) (a : α) :
    ∃ m : α, (∀ b : α, ¬ r b m) ∧ (m = a ∨ r m a) := by
  classical
  haveI : IsTrans α r := ⟨htrans⟩
  haveI : Std.Irrefl r := ⟨hirrefl⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  let P : α → Prop := fun a =>
    ∃ m : α, (∀ b : α, ¬ r b m) ∧ (m = a ∨ r m a)
  change P a
  exact hwf.induction (C := P) a fun x ih => by
    by_cases hdominated : ∃ b : α, r b x
    · obtain ⟨b, hbx⟩ := hdominated
      obtain ⟨m, hmmax, hmcand⟩ := ih b hbx
      refine ⟨m, hmmax, ?_⟩
      rcases hmcand with rfl | hmb
      · exact Or.inr hbx
      · exact Or.inr (htrans m b x hmb hbx)
    · refine ⟨x, ?_, Or.inl rfl⟩
      intro b hbx
      exact hdominated ⟨b, hbx⟩

/-- If a point in a finite transitive irreflexive relation is dominated, then it
is dominated by a maximal point. -/
theorem exists_maximal_rel_of_finite_trans_irrefl {α : Type u} [Finite α]
    (r : α → α → Prop)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hirrefl : ∀ a, ¬ r a a) {a : α}
    (hdominated : ∃ b : α, r b a) :
    ∃ m : α, (∀ b : α, ¬ r b m) ∧ r m a := by
  obtain ⟨m, hmmax, hmcand⟩ :=
    exists_maximal_or_rel_of_finite_trans_irrefl r htrans hirrefl a
  refine ⟨m, hmmax, ?_⟩
  rcases hmcand with rfl | hma
  · obtain ⟨b, hba⟩ := hdominated
    exact False.elim (hmmax b hba)
  · exact hma

/-- A complete transitive relation on a nonempty finite type has a greatest
element. -/
theorem exists_greatest_of_complete_transitive {α : Type u} [Finite α] [Nonempty α]
    (r : α → α → Prop)
    (hcomplete : ∀ a b, r a b ∨ r b a)
    (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∃ a, ∀ b, r a b := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let le : LE α := ⟨fun x y => r y x⟩
  letI : LE α := le
  have hIsTrans : IsTrans α (· ≤ ·) := ⟨by
    intro a b c hab hbc
    exact htrans c b a hbc hab⟩
  letI : IsTrans α (· ≤ ·) := hIsTrans
  obtain ⟨a, hmax⟩ :=
    Finset.exists_maximal (s := (Finset.univ : Finset α)) Finset.univ_nonempty
  refine ⟨a, ?_⟩
  intro b
  rcases hcomplete a b with hab | hba
  · exact hab
  · exact hmax.2 (by simp) hba

/-- A complete transitive relation on a nonempty finite type has a least
element. -/
theorem exists_least_of_complete_transitive {α : Type u} [Finite α] [Nonempty α]
    (r : α → α → Prop)
    (hcomplete : ∀ a b, r a b ∨ r b a)
    (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∃ a, ∀ b, r b a := by
  simpa using
    (exists_greatest_of_complete_transitive (fun a b => r b a)
      (fun a b => (hcomplete a b).symm)
      (fun a b c hab hbc => htrans c b a hbc hab))

end Math
