import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Tauto
import GameTheory.Math.FiniteBasisExchange

/-! Cardinality invariants for finite sets of paired labels.
A set with one variable per label on average either covers every label exactly
once, or, when only a designated label may be absent, has exactly one duplicate.
-/

namespace GameTheory.Math.ComplementaryLabels

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Exactly one of each label's two variables belongs to the set. -/
def IsComplementary (s : Finset (α × Bool)) : Prop :=
  ∀ i, (i, false) ∈ s ↔ (i, true) ∉ s

/-- Every label other than the designated one is represented. -/
def CoversExcept (s : Finset (α × Bool)) (d : α) : Prop :=
  ∀ i, i ≠ d → (i, false) ∈ s ∨ (i, true) ∈ s

private def labels (s : Finset (α × Bool)) (b : Bool) : Finset α :=
  Finset.univ.filter (fun i => (i, b) ∈ s)

private theorem card_split (s : Finset (α × Bool)) :
    s.card = (labels s false).card + (labels s true).card := by
  have hs : s = (labels s false ×ˢ {false}) ∪ (labels s true ×ˢ {true}) := by
    ext ⟨i, b⟩
    cases b <;> simp [labels]
  have hd : Disjoint (labels s false ×ˢ {false}) (labels s true ×ˢ {true}) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hf : v.2 = false := by simpa using (Finset.mem_product.mp hv).2
    have ht : v.2 = true := by simpa using (Finset.mem_product.mp hw).2
    simp [hf] at ht
  calc
    s.card = ((labels s false ×ˢ {false}) ∪ (labels s true ×ˢ {true})).card :=
      congrArg Finset.card hs
    _ = (labels s false).card + (labels s true).card := by
      rw [Finset.card_union_of_disjoint hd]
      simp

private theorem count_balance (s : Finset (α × Bool))
    (hsize : s.card = Fintype.card α) :
    (labels s false ∩ labels s true).card =
      (Finset.univ \ (labels s false ∪ labels s true)).card := by
  have hc := Finset.card_union_add_card_inter (labels s false) (labels s true)
  have hs := card_split s
  have hu := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (labels s false ∪ labels s true))
  simp only [Finset.card_univ] at hu
  omega

/-- Covering all labels with the prescribed cardinality means exactly one per pair. -/
theorem isComplementary_of_covers (s : Finset (α × Bool))
    (hsize : s.card = Fintype.card α)
    (hcovers : ∀ i, (i, false) ∈ s ∨ (i, true) ∈ s) : IsComplementary s := by
  have hu : labels s false ∪ labels s true = Finset.univ := by
    ext i
    simpa [labels] using (iff_true_intro (hcovers i))
  have hd : labels s false ∩ labels s true = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [count_balance s hsize, hu]
    simp
  intro i
  have hnot : ¬((i, false) ∈ s ∧ (i, true) ∈ s) := by
    have hh := congrArg (fun t : Finset α => i ∈ t) hd
    simpa [labels] using hh.mp
  rcases hcovers i with hi | hi <;> tauto

/-- A missing designated label forces a unique duplicated label. -/
theorem exists_unique_duplicate_of_missing (s : Finset (α × Bool)) (d : α)
    (hsize : s.card = Fintype.card α) (hcovers : CoversExcept s d)
    (hd : (d, false) ∉ s ∧ (d, true) ∉ s) :
    ∃! i, (i, false) ∈ s ∧ (i, true) ∈ s := by
  have hm : Finset.univ \ (labels s false ∪ labels s true) = {d} := by
    ext i
    by_cases hi : i = d
    · subst i; simp [labels, hd]
    · have hh := hcovers i hi
      simp [labels, hi, hh]
  have hc : (labels s false ∩ labels s true).card = 1 := by
    rw [count_balance s hsize, hm]
    simp
  simpa [labels] using Finset.card_eq_one_iff_existsUnique.mp hc

/-- An almost covered set is either complementary or has precisely one duplicate. -/
theorem complementary_or_unique_duplicate (s : Finset (α × Bool)) (d : α)
    (hsize : s.card = Fintype.card α) (hcovers : CoversExcept s d) :
    IsComplementary s ∨
      ((d, false) ∉ s ∧ (d, true) ∉ s) ∧
        ∃! i, (i, false) ∈ s ∧ (i, true) ∈ s := by
  by_cases hd : (d, false) ∈ s ∨ (d, true) ∈ s
  · left
    apply isComplementary_of_covers s hsize
    intro i
    by_cases hi : i = d
    · subst i; exact hd
    · exact hcovers i hi
  · have hmissing : (d, false) ∉ s ∧ (d, true) ∉ s := not_or.mp hd
    exact Or.inr ⟨hmissing, exists_unique_duplicate_of_missing s d hsize hcovers hmissing⟩

omit [Fintype α] in
/-- Removing one member of a duplicated pair preserves coverage of every label. -/
theorem CoversExcept.exchange_duplicate {s : Finset (α × Bool)} {d k : α}
    (hcovers : CoversExcept s d) (hduplicate : (k, false) ∈ s ∧ (k, true) ∈ s)
    (b : Bool) (entering : α × Bool) :
    CoversExcept (FiniteBasisExchange.exchange s (k, b) entering) d := by
  intro i hi
  by_cases hik : i = k
  · subst i
    cases b with
    | false =>
      exact Or.inr (FiniteBasisExchange.mem_exchange.mpr
        (Or.inr ⟨by simp, hduplicate.2⟩))
    | true =>
      exact Or.inl (FiniteBasisExchange.mem_exchange.mpr
        (Or.inr ⟨by simp, hduplicate.1⟩))
  · rcases hcovers i hi with hfalse | htrue
    · exact Or.inl (FiniteBasisExchange.mem_exchange.mpr
        (Or.inr ⟨fun h => hik (congrArg Prod.fst h), hfalse⟩))
    · exact Or.inr (FiniteBasisExchange.mem_exchange.mpr
        (Or.inr ⟨fun h => hik (congrArg Prod.fst h), htrue⟩))

omit [Fintype α] in
/-- Exchanging a variable of the designated label cannot uncover any other label. -/
theorem CoversExcept.exchange_dropped {s : Finset (α × Bool)} {d : α}
    (hcovers : CoversExcept s d) (b : Bool) (entering : α × Bool) :
    CoversExcept (FiniteBasisExchange.exchange s (d, b) entering) d := by
  intro i hi
  rcases hcovers i hi with hfalse | htrue
  · exact Or.inl (FiniteBasisExchange.mem_exchange.mpr
      (Or.inr ⟨fun h => hi (congrArg Prod.fst h), hfalse⟩))
  · exact Or.inr (FiniteBasisExchange.mem_exchange.mpr
      (Or.inr ⟨fun h => hi (congrArg Prod.fst h), htrue⟩))

end GameTheory.Math.ComplementaryLabels
