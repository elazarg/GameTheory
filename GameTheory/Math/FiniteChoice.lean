module

/-
# Finite-menu choice and revealed preference

A correspondence returns alternatives, including every tie, rather than a
bundle of simultaneously accepted items. Feasibility, nonempty choice and
revealed-preference consistency are independent hypotheses on an ordinary
function. They rationalize choice on all finite menus by a total transitive
relation, even when the ambient alternative type is infinite.

This representation describes observed choice. It need not recover a latent
incomplete preference, and it does not apply to a restricted menu domain without
the binary and triple menus used in the proof. Rejection of every option must
be modeled by an explicit outside alternative if nonempty choice is required.
-/

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Finset.Insert

@[expose] public section

namespace GameTheory.Math.FiniteChoice

universe u

variable {α : Type u}

/-- All feasible alternatives weakly preferred to every member of a menu.
The preferred alternative is the first argument of the relation. -/
def best (prefers : α → α → Prop) (menu : Finset α) : Set α :=
  {chosen | chosen ∈ menu ∧ ∀ alternative ∈ menu, prefers chosen alternative}

/-- Every selected alternative is offered. -/
def Feasible (choose : Finset α → Set α) : Prop :=
  ∀ menu, choose menu ⊆ (menu : Set α)

/-- A nonempty finite menu has at least one selected alternative. -/
def Nonempty (choose : Finset α → Set α) : Prop :=
  ∀ menu, menu.Nonempty → (choose menu).Nonempty

/-- The weak axiom of revealed preference, retaining all ties: if `chosen`
is selected while `other` is available, any menu selecting `other` and offering
`chosen` also selects `chosen`. -/
def WeakAxiom (choose : Finset α → Set α) : Prop :=
  ∀ first second chosen other,
    chosen ∈ choose first → other ∈ first → other ∈ choose second →
      chosen ∈ second → chosen ∈ choose second

/-- Choice of an alternative from its binary menu reveals a weak preference. -/
noncomputable def revealed (choose : Finset α → Set α) (chosen other : α) : Prop := by
  classical
  exact chosen ∈ choose {chosen, other}

theorem best_feasible (prefers : α → α → Prop) : Feasible (best prefers) :=
  fun _ _ chosen => chosen.1

/-- Restricting a menu preserves a selected alternative if it remains offered.
This uses no consistency law on the preference. -/
theorem best_of_subset {prefers : α → α → Prop} {small large : Finset α}
    {chosen : α} (selected : chosen ∈ best prefers large)
    (subset : small ⊆ large) (member : chosen ∈ small) :
    chosen ∈ best prefers small :=
  ⟨member, fun other offered => selected.2 other (subset offered)⟩

/-- Finite existence reuses Mathlib's maximal-element theorem; totality turns
the resulting maximal alternative into a greatest one. -/
theorem best_nonempty {prefers : α → α → Prop}
    (transitive : ∀ a b c, prefers a b → prefers b c → prefers a c)
    (total : ∀ a b, prefers a b ∨ prefers b a) : Nonempty (best prefers) := by
  let : LE α := ⟨fun a b => prefers b a⟩
  let : IsTrans α (· ≤ ·) := ⟨fun a b c hab hbc => transitive c b a hbc hab⟩
  intro menu nonempty
  obtain ⟨chosen, member, maximal⟩ := Finset.exists_maximal nonempty
  refine ⟨chosen, member, fun other offered => ?_⟩
  exact (total chosen other).elim id (maximal offered)

theorem best_weakAxiom {prefers : α → α → Prop}
    (transitive : ∀ a b c, prefers a b → prefers b c → prefers a c) :
    WeakAxiom (best prefers) := by
  intro first second chosen other selected offered accepted available
  exact ⟨available, fun alternative member =>
    transitive chosen other alternative (selected.2 other offered)
      (accepted.2 alternative member)⟩

@[simp]
theorem revealed_best {prefers : α → α → Prop}
    (reflexive : ∀ a, prefers a a) (chosen other : α) :
    revealed (best prefers) chosen other ↔ prefers chosen other := by
  classical
  simp [revealed, best, reflexive]

theorem Feasible.empty {choose : Finset α → Set α} (feasible : Feasible choose) :
    choose ∅ = ∅ := by
  ext chosen
  exact ⟨fun selected => by simpa using feasible ∅ selected, False.elim⟩

/-- A selected alternative remains selected on its binary submenus. -/
theorem WeakAxiom.revealed_of_selected {choose : Finset α → Set α}
    (feasible : Feasible choose) (nonempty : Nonempty choose) (consistent : WeakAxiom choose)
    {menu : Finset α} {chosen other : α}
    (selected : chosen ∈ choose menu) (offered : other ∈ menu) :
    revealed choose chosen other := by
  classical
  obtain ⟨accepted, haccepted⟩ := nonempty {chosen, other} (by simp)
  rcases Finset.mem_insert.mp (feasible _ haccepted) with equal | member
  · simpa [revealed, ← equal] using haccepted
  · have equal : accepted = other := Finset.mem_singleton.mp member
    subst accepted
    exact consistent menu {chosen, other} chosen other selected offered haccepted (by simp)

/-- Binary choices rationalize the entire correspondence; no order laws need
be assumed in addition to feasibility, nonemptiness and the weak axiom. -/
theorem eq_best_revealed {choose : Finset α → Set α}
    (feasible : Feasible choose) (nonempty : Nonempty choose) (consistent : WeakAxiom choose)
    (menu : Finset α) : choose menu = best (revealed choose) menu := by
  classical
  ext chosen
  constructor
  · intro selected
    exact ⟨feasible menu selected, fun other offered =>
      consistent.revealed_of_selected feasible nonempty selected offered⟩
  · rintro ⟨member, greatest⟩
    obtain ⟨other, selected⟩ := nonempty menu ⟨chosen, member⟩
    exact consistent {chosen, other} menu chosen other (greatest other (feasible menu selected))
      (by simp) selected member

theorem revealed_total {choose : Finset α → Set α}
    (feasible : Feasible choose) (nonempty : Nonempty choose) :
    ∀ chosen other, revealed choose chosen other ∨ revealed choose other chosen := by
  classical
  intro chosen other
  obtain ⟨accepted, selected⟩ := nonempty {chosen, other} (by simp)
  rcases Finset.mem_insert.mp (feasible _ selected) with equal | member
  · exact Or.inl (by simpa [revealed, ← equal] using selected)
  · have equal : accepted = other := Finset.mem_singleton.mp member
    exact Or.inr (by simpa [revealed, Finset.pair_comm, ← equal] using selected)

theorem revealed_transitive {choose : Finset α → Set α}
    (feasible : Feasible choose) (nonempty : Nonempty choose) (consistent : WeakAxiom choose) :
    ∀ a b c, revealed choose a b → revealed choose b c → revealed choose a c := by
  classical
  intro a b c hab hbc
  obtain ⟨selected, hselected⟩ := nonempty {a, b, c} (by simp)
  have a_selected : a ∈ choose {a, b, c} := by
    rcases Finset.mem_insert.mp (feasible _ hselected) with equal | member
    · simpa [← equal] using hselected
    · have b_selected : b ∈ choose {a, b, c} := by
        rcases Finset.mem_insert.mp member with equal | member
        · simpa [← equal] using hselected
        · have equal : selected = c := Finset.mem_singleton.mp member
          subst selected
          exact consistent {b, c} {a, b, c} b c hbc (by simp) hselected (by simp)
      exact consistent {a, b} {a, b, c} a b hab (by simp) b_selected (by simp)
  exact consistent.revealed_of_selected feasible nonempty a_selected (by simp)

/-- Finite-menu choice is rationalizable by a complete preorder exactly when
it is feasible, nonempty on nonempty menus, and satisfies the weak axiom. -/
theorem rationalizable_iff (choose : Finset α → Set α) :
    (∃ prefers : α → α → Prop,
      (∀ a b, prefers a b ∨ prefers b a) ∧
      (∀ a b c, prefers a b → prefers b c → prefers a c) ∧
      ∀ menu, choose menu = best prefers menu) ↔
    Feasible choose ∧ Nonempty choose ∧ WeakAxiom choose := by
  constructor
  · rintro ⟨prefers, total, transitive, represents⟩
    have equal : choose = best prefers := funext represents
    rw [equal]
    exact ⟨best_feasible prefers, best_nonempty transitive total, best_weakAxiom transitive⟩
  · rintro ⟨feasible, nonempty, consistent⟩
    exact ⟨revealed choose, revealed_total feasible nonempty,
      revealed_transitive feasible nonempty consistent,
      eq_best_revealed feasible nonempty consistent⟩

end GameTheory.Math.FiniteChoice
