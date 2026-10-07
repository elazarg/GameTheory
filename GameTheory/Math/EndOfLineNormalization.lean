import GameTheory.Math.EndOfLine

/-! Removing inconsistent pointers preserves the graph's incident edges and
connects its endpoints to the usual asymmetric End-of-Line witness condition. -/

namespace GameTheory.Math.EndOfLine

variable {α : Type*}

/-- An outgoing inconsistency, or an incoming inconsistency away from the origin. -/
def RawWitness (P S : α → α) (origin x : α) : Prop :=
  P (S x) ≠ x ∨ (x ≠ origin ∧ S (P x) ≠ x)

instance [DecidableEq α] (P S : α → α) (origin x : α) :
    Decidable (RawWitness P S origin x) :=
  inferInstanceAs (Decidable (P (S x) ≠ x ∨ (x ≠ origin ∧ S (P x) ≠ x)))

/-- Replace outgoing pointers that do not encode an edge by self-loops. -/
def normalizeSuccessor [DecidableEq α] (P S : α → α) (x : α) : α :=
  if HasSuccessor P S x then S x else x

/-- Replace incoming pointers that do not encode an edge by self-loops. -/
def normalizePredecessor [DecidableEq α] (P S : α → α) (x : α) : α :=
  if HasPredecessor P S x then P x else x

variable [DecidableEq α] (P S : α → α)

theorem normalizeSuccessor_ne_self_iff (x : α) :
    normalizeSuccessor P S x ≠ x ↔ HasSuccessor P S x := by
  by_cases h : HasSuccessor P S x
  · rw [normalizeSuccessor, ite_eq_left h]
    exact iff_of_true h.1 h
  · rw [normalizeSuccessor, ite_eq_right h]
    exact iff_of_false (fun he => he rfl) h

theorem normalizePredecessor_ne_self_iff (x : α) :
    normalizePredecessor P S x ≠ x ↔ HasPredecessor P S x := by
  by_cases h : HasPredecessor P S x
  · rw [normalizePredecessor, ite_eq_left h]
    exact iff_of_true h.1 h
  · rw [normalizePredecessor, ite_eq_right h]
    exact iff_of_false (fun he => he rfl) h

theorem normalizePredecessor_successor {x : α}
    (h : normalizeSuccessor P S x ≠ x) :
    normalizePredecessor P S (normalizeSuccessor P S x) = x := by
  have hs := (normalizeSuccessor_ne_self_iff P S x).mp h
  rw [normalizeSuccessor, ite_eq_left hs, normalizePredecessor,
    ite_eq_left (hasPredecessor_successor P S hs), hs.2]

theorem normalizeSuccessor_predecessor {x : α}
    (h : normalizePredecessor P S x ≠ x) :
    normalizeSuccessor P S (normalizePredecessor P S x) = x := by
  have hp := (normalizePredecessor_ne_self_iff P S x).mp h
  rw [normalizePredecessor, ite_eq_left hp, normalizeSuccessor,
    ite_eq_left (hasSuccessor_predecessor P S hp), hp.2]

theorem hasSuccessor_normalize_iff (x : α) :
    HasSuccessor (normalizePredecessor P S) (normalizeSuccessor P S) x ↔
      HasSuccessor P S x := by
  constructor
  · intro h
    exact (normalizeSuccessor_ne_self_iff P S x).mp h.1
  · intro h
    have hn := (normalizeSuccessor_ne_self_iff P S x).mpr h
    exact ⟨hn, normalizePredecessor_successor P S hn⟩

theorem hasPredecessor_normalize_iff (x : α) :
    HasPredecessor (normalizePredecessor P S) (normalizeSuccessor P S) x ↔
      HasPredecessor P S x := by
  constructor
  · intro h
    exact (normalizePredecessor_ne_self_iff P S x).mp h.1
  · intro h
    have hn := (normalizePredecessor_ne_self_iff P S x).mpr h
    exact ⟨hn, normalizeSuccessor_predecessor P S hn⟩

theorem isEndpoint_normalize_iff (x : α) :
    IsEndpoint (normalizePredecessor P S) (normalizeSuccessor P S) x ↔
      IsEndpoint P S x := by
  simp only [IsEndpoint, hasSuccessor_normalize_iff, hasPredecessor_normalize_iff]

theorem normalized_outgoing_inconsistency_iff (x : α) :
    normalizePredecessor P S (normalizeSuccessor P S x) ≠ x ↔
      HasPredecessor P S x ∧ ¬HasSuccessor P S x := by
  by_cases hs : HasSuccessor P S x
  · have he := normalizePredecessor_successor P S
      ((normalizeSuccessor_ne_self_iff P S x).mpr hs)
    simp only [he, ne_self_iff_false, hs, not_true_eq_false, and_false]
  · rw [normalizeSuccessor, ite_eq_right hs]
    simp only [normalizePredecessor_ne_self_iff, hs, not_false_eq_true, and_true]

theorem normalized_incoming_inconsistency_iff (x : α) :
    normalizeSuccessor P S (normalizePredecessor P S x) ≠ x ↔
      HasSuccessor P S x ∧ ¬HasPredecessor P S x := by
  by_cases hp : HasPredecessor P S x
  · have he := normalizeSuccessor_predecessor P S
      ((normalizePredecessor_ne_self_iff P S x).mpr hp)
    simp only [he, ne_self_iff_false, hp, not_true_eq_false, and_false]
  · rw [normalizePredecessor, ite_eq_right hp]
    simp only [normalizeSuccessor_ne_self_iff, hp, not_false_eq_true, and_true]

theorem normalized_rawWitness_iff {origin x : α}
    (hP : P origin = origin) (hS : S origin ≠ origin)
    (hlink : P (S origin) = origin) :
    RawWitness (normalizePredecessor P S) (normalizeSuccessor P S) origin x ↔
      x ≠ origin ∧ IsEndpoint P S x := by
  rw [RawWitness, normalized_outgoing_inconsistency_iff,
    normalized_incoming_inconsistency_iff]
  have hsource : HasSuccessor P S origin := ⟨hS, hlink⟩
  have hnot : ¬HasPredecessor P S origin := fun h => h.1 hP
  by_cases hx : x = origin
  · subst x
    simp only [hsource, hnot, not_true_eq_false, and_false,
      ne_self_iff_false, false_and, or_self]
  · constructor
    · rintro (hin | ⟨_, hout⟩)
      · exact ⟨hx, Or.inr hin⟩
      · exact ⟨hx, Or.inl hout⟩
    · rintro ⟨_, hout | hin⟩
      · exact Or.inr ⟨hx, hout⟩
      · exact Or.inl hin

omit [DecidableEq α] in
theorem endpoint_rawWitness {origin x : α} (hne : x ≠ origin)
    (h : IsEndpoint P S x) : RawWitness P S origin x := by
  rcases h with ⟨hs, hp⟩ | ⟨hp, hs⟩
  · right
    refine ⟨hne, ?_⟩
    intro he
    apply hp
    refine ⟨?_, he⟩
    intro hpx
    have : S x = x := by simpa only [hpx] using he
    exact hs.1 this
  · left
    intro he
    apply hs
    refine ⟨?_, he⟩
    intro hsx
    have : P x = x := by simpa only [hsx] using he
    exact hp.1 this

/-- Weak source promises suffice for raw witnesses: a broken initial link is itself an answer. -/
theorem exists_rawWitness [Fintype α] (origin : α)
    (hP : P origin = origin) (hS : S origin ≠ origin) :
    ∃ x, RawWitness P S origin x := by
  by_cases hlink : P (S origin) = origin
  · obtain ⟨x, hne, hx⟩ := exists_endpoint_ne_origin P S origin hP hS hlink
    exact ⟨x, endpoint_rawWitness P S hne hx⟩
  · exact ⟨origin, Or.inl hlink⟩

end GameTheory.Math.EndOfLine
