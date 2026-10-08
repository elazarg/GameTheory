import Mathlib.Data.Fintype.Card

/-! Endpoints of finite successor/predecessor graphs. Only mutually consistent,
nontrivial pointers are edges; malformed pointers and unrelated cycles are allowed. -/

namespace GameTheory.Math.EndOfLine

variable {α : Type*}

/-- A nontrivial outgoing pointer whose inverse pointer agrees. -/
def HasSuccessor (P S : α → α) (x : α) : Prop :=
  S x ≠ x ∧ P (S x) = x

/-- A nontrivial incoming pointer whose inverse pointer agrees. -/
def HasPredecessor (P S : α → α) (x : α) : Prop :=
  P x ≠ x ∧ S (P x) = x

instance [DecidableEq α] (P S : α → α) (x : α) : Decidable (HasSuccessor P S x) :=
  inferInstanceAs (Decidable (S x ≠ x ∧ P (S x) = x))

instance [DecidableEq α] (P S : α → α) (x : α) : Decidable (HasPredecessor P S x) :=
  inferInstanceAs (Decidable (P x ≠ x ∧ S (P x) = x))

/-- An endpoint has exactly one mutually consistent incident edge. -/
def IsEndpoint (P S : α → α) (x : α) : Prop :=
  (HasSuccessor P S x ∧ ¬HasPredecessor P S x) ∨
    (HasPredecessor P S x ∧ ¬HasSuccessor P S x)

instance [DecidableEq α] (P S : α → α) (x : α) : Decidable (IsEndpoint P S x) :=
  inferInstanceAs (Decidable
    ((HasSuccessor P S x ∧ ¬HasPredecessor P S x) ∨
      (HasPredecessor P S x ∧ ¬HasSuccessor P S x)))

/-- Following a valid outgoing pointer produces a valid incoming pointer. -/
theorem hasPredecessor_successor (P S : α → α) {x : α}
    (h : HasSuccessor P S x) : HasPredecessor P S (S x) := by
  constructor
  · rw [h.2]
    exact Ne.symm h.1
  · rw [h.2]

/-- Following a valid incoming pointer produces a valid outgoing pointer. -/
theorem hasSuccessor_predecessor (P S : α → α) {x : α}
    (h : HasPredecessor P S x) : HasSuccessor P S (P x) := by
  constructor
  · rw [h.2]
    exact Ne.symm h.1
  · rw [h.2]

/-- Valid outgoing and incoming vertices have equal cardinality. -/
theorem card_successors_eq_predecessors [Fintype α] [DecidableEq α] (P S : α → α) :
    Fintype.card {x // HasSuccessor P S x} =
      Fintype.card {x // HasPredecessor P S x} := by
  classical
  exact Fintype.card_congr
    { toFun := fun x => ⟨S x.1, hasPredecessor_successor P S x.2⟩
      invFun := fun x => ⟨P x.1, hasSuccessor_predecessor P S x.2⟩
      left_inv := fun x => Subtype.ext x.2.2
      right_inv := fun x => Subtype.ext x.2.2 }

/-- A known source in a finite graph forces a different endpoint. -/
theorem exists_endpoint_ne_origin [Fintype α] [DecidableEq α]
    (P S : α → α) (origin : α) (hP : P origin = origin)
    (hS : S origin ≠ origin) (hlink : P (S origin) = origin) :
    ∃ v, v ≠ origin ∧ IsEndpoint P S v := by
  classical
  by_contra hnone
  have hboth : ∀ x, HasPredecessor P S x → HasSuccessor P S x := by
    intro x hin
    have hne : x ≠ origin := by
      rintro rfl
      exact hin.1 hP
    by_contra hout
    exact hnone ⟨x, hne, Or.inr ⟨hin, hout⟩⟩
  let embed : {x // HasPredecessor P S x} → {x // HasSuccessor P S x} :=
    fun x => ⟨x.1, hboth x.1 x.2⟩
  have hinj : Function.Injective embed := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.1) h)
  have hmissing : ∀ x, embed x ≠ ⟨origin, hS, hlink⟩ := by
    intro x hx
    have hval : x.1 = origin := congrArg (fun z => z.1) hx
    exact x.2.1 (by simpa only [hval] using hP)
  have hlt := Fintype.card_lt_of_injective_of_notMem embed hinj
    (b := ⟨origin, hS, hlink⟩) (by rintro ⟨x, hx⟩; exact hmissing x hx)
  rw [card_successors_eq_predecessors P S] at hlt
  exact (Nat.lt_irrefl _) hlt

end GameTheory.Math.EndOfLine
