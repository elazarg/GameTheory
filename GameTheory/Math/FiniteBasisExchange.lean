import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.BooleanAlgebra

/-! Exchange of finite basis labels with canonical sorted enumeration.

A basis is represented by its label set, so column permutations do not create
different vertices. Mathlib's `Finset.orderEmbOfFin` supplies its sorted columns.
-/

namespace GameTheory.Math.FiniteBasisExchange

variable {α : Type*} [DecidableEq α]

/-- Replace a leaving label by an entering label. -/
def exchange (s : Finset α) (leaving entering : α) : Finset α :=
  insert entering (s.erase leaving)

@[simp] theorem mem_exchange {s : Finset α} {leaving entering x : α} :
    x ∈ exchange s leaving entering ↔ x = entering ∨ (x ≠ leaving ∧ x ∈ s) := by
  simp [exchange]

/-- Replacing a member by a nonmember preserves the number of basis labels. -/
theorem card_exchange {s : Finset α} {leaving entering : α}
    (hl : leaving ∈ s) (he : entering ∉ s) :
    (exchange s leaving entering).card = s.card := by
  rw [exchange, Finset.card_insert_of_notMem (fun h => he (Finset.mem_of_mem_erase h)),
    Finset.card_erase_add_one hl]

theorem entering_mem (s : Finset α) (leaving entering : α) :
    entering ∈ exchange s leaving entering := by
  simp

/-- The old label disappears in a valid exchange. -/
theorem leaving_not_mem {s : Finset α} {leaving entering : α}
    (hl : leaving ∈ s) (he : entering ∉ s) : leaving ∉ exchange s leaving entering := by
  have hne : leaving ≠ entering := by
    intro h
    apply he
    rw [← h]
    exact hl
  simp [hne]

/-- Exchanging back recovers the same label set, regardless of column order. -/
theorem reverse_exchange {s : Finset α} {leaving entering : α}
    (hl : leaving ∈ s) (he : entering ∉ s) :
    exchange (exchange s leaving entering) entering leaving = s := by
  rw [exchange, exchange,
    Finset.erase_insert (fun h => he (Finset.mem_of_mem_erase h)), Finset.insert_erase hl]

/-- The complementary label set exchanges the same labels in reverse order. -/
theorem compl_exchange [Fintype α] {s : Finset α} {leaving entering : α}
    (hl : leaving ∈ s) (he : entering ∉ s) :
    (exchange s leaving entering)ᶜ = exchange sᶜ entering leaving := by
  have hne : leaving ≠ entering := by
    intro h
    apply he
    rw [← h]
    exact hl
  rw [exchange, exchange, Finset.compl_insert, Finset.compl_erase,
    Finset.erase_insert_of_ne hne]

/-- An injective relabeling commutes with basis exchange. -/
theorem map_exchange {β : Type*} [DecidableEq β] (f : α ↪ β)
    (s : Finset α) (leaving entering : α) :
    (exchange s leaving entering).map f = exchange (s.map f) (f leaving) (f entering) := by
  rw [exchange, exchange, Finset.map_insert, Finset.map_erase]

/-- With the leaving label fixed, an exchange identifies its entering label. -/
theorem exchange_eq_iff {s : Finset α} {leaving a b : α}
    (ha : a ∉ s) (hb : b ∉ s) :
    exchange s leaving a = exchange s leaving b ↔ a = b := by
  constructor
  · intro h
    have hm : a ∈ exchange s leaving b := by
      rw [← h]
      exact entering_mem s leaving a
    exact (mem_exchange.mp hm).resolve_right (fun h => ha h.2)
  · rintro rfl
    rfl

section Canonical

variable [LinearOrder α] {n : ℕ}

omit [DecidableEq α] in
/-- Canonically sorted basis columns agree exactly when their label sets agree. -/
theorem canonical_eq_iff {s t : Finset α} (hs : s.card = n) (ht : t.card = n) :
    s.orderEmbOfFin hs = t.orderEmbOfFin ht ↔ s = t := by
  constructor
  · intro h
    have hr := congrArg (fun f : Fin n ↪o α => Set.range f) h
    simpa only [Finset.range_orderEmbOfFin, Finset.coe_inj] using hr
  · rintro rfl
    rfl

omit [DecidableEq α] in
/-- Any increasing enumeration of a basis has the canonical sorted columns. -/
theorem canonical_unique {s : Finset α} (hs : s.card = n) {f : Fin n → α}
    (hmem : ∀ i, f i ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin hs :=
  Finset.orderEmbOfFin_unique hs hmem hmono

/-- The raw column enumeration after replacing one column, before sorting. -/
def exchangeEnumeration (s : Finset α) (hs : s.card = n) (l : Fin n)
    (entering : α) (i : Fin n) : α :=
  if i = l then entering else s.orderEmbOfFin hs i

theorem exchangeEnumeration_mem (s : Finset α) (hs : s.card = n) (l : Fin n)
    (entering : α) (i : Fin n) :
    exchangeEnumeration s hs l entering i ∈ exchange s (s.orderEmbOfFin hs l) entering := by
  by_cases hi : i = l
  · simp [exchangeEnumeration, hi]
  · simp only [exchangeEnumeration, hi, ↓reduceIte, mem_exchange]
    exact Or.inr ⟨fun h => hi ((s.orderEmbOfFin hs).injective h),
      Finset.orderEmbOfFin_mem s hs i⟩

omit [DecidableEq α] in
theorem exchangeEnumeration_injective (s : Finset α) (hs : s.card = n) (l : Fin n)
    (entering : α) (he : entering ∉ s) :
    Function.Injective (exchangeEnumeration s hs l entering) := by
  intro i j hij
  by_cases hi : i = l <;> by_cases hj : j = l
  · exact hi.trans hj.symm
  · simp only [exchangeEnumeration, hi, hj, ↓reduceIte] at hij
    apply False.elim
    apply he
    rw [hij]
    exact Finset.orderEmbOfFin_mem s hs j
  · simp only [exchangeEnumeration, hi, hj, ↓reduceIte] at hij
    apply False.elim
    apply he
    rw [← hij]
    exact Finset.orderEmbOfFin_mem s hs i
  · simp only [exchangeEnumeration, hi, hj, ↓reduceIte] at hij
    exact (s.orderEmbOfFin hs).injective hij

/-- Permutation from sorted exchanged columns to the raw column replacement. -/
noncomputable def exchangePermutation (s : Finset α) (hs : s.card = n) (l : Fin n)
    (entering : α) (he : entering ∉ s) : Equiv.Perm (Fin n) := by
  let ht := (card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs
  let f : Fin n → Fin n := fun i =>
    ((exchange s (s.orderEmbOfFin hs l) entering).orderIsoOfFin ht).symm
      ⟨exchangeEnumeration s hs l entering i, exchangeEnumeration_mem s hs l entering i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply exchangeEnumeration_injective s hs l entering he
    have hh := ((exchange s (s.orderEmbOfFin hs l) entering).orderIsoOfFin ht).symm.injective hij
    exact congrArg Subtype.val hh
  exact (Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩).symm

/-- Sorting after a column exchange only permutes the raw replacement columns. -/
theorem exchangePermutation_apply (s : Finset α) (hs : s.card = n) (l : Fin n)
    (entering : α) (he : entering ∉ s) (i : Fin n) :
    (exchange s (s.orderEmbOfFin hs l) entering).orderEmbOfFin
        ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs) i =
      exchangeEnumeration s hs l entering (exchangePermutation s hs l entering he i) := by
  have h := (exchangePermutation s hs l entering he).symm_apply_apply i
  change ((exchange s (s.orderEmbOfFin hs l) entering).orderIsoOfFin
    ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs)).symm
      ⟨exchangeEnumeration s hs l entering (exchangePermutation s hs l entering he i),
        exchangeEnumeration_mem s hs l entering _⟩ = i at h
  have hh := congrArg
    (fun j => (exchange s (s.orderEmbOfFin hs l) entering).orderIsoOfFin
      ((card_exchange (Finset.orderEmbOfFin_mem s hs l) he).trans hs) j) h
  simpa only [OrderIso.apply_symm_apply, Finset.coe_orderIsoOfFin_apply] using
    (congrArg Subtype.val hh).symm

end Canonical

end GameTheory.Math.FiniteBasisExchange
