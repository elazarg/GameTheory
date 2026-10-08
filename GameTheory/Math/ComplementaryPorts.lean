import GameTheory.Math.ComplementaryLabels

/-! Ports of complementary and almost complementary finite label sets.

A complementary set has one port at the dropped label. An almost complementary
set has the two variables of its unique duplicated label as ports. Switching
between these ports and exchanging a port variable preserve the label invariant.
-/

namespace GameTheory.Math.ComplementaryPorts
open ComplementaryLabels FiniteBasisExchange
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A zero variable that may enter along a dropped-label complementary path. -/
def IsPort (s : Finset (α × Bool)) (d : α) (v : α × Bool) : Prop :=
  v ∈ s ∧ (v.1 = d ∨ ((v.1, false) ∈ s ∧ (v.1, true) ∈ s))

/-- Switch the duplicated-label port; retain a dropped-label endpoint port. -/
def switch (_s : Finset (α × Bool)) (d : α) (v : α × Bool) : α × Bool :=
  if v.1 = d then v else (v.1, !v.2)

omit [Fintype α] [DecidableEq α] in
theorem complementary_port_iff {s : Finset (α × Bool)} {d : α}
    (hc : IsComplementary s) (v : α × Bool) :
    IsPort s d v ↔ v.1 = d ∧ v ∈ s := by
  constructor
  · rintro ⟨hv, hd | hh⟩
    · exact ⟨hd, hv⟩
    · exact ((hc v.1).mp hh.1 hh.2).elim
  · rintro ⟨hd, hv⟩
    exact ⟨hv, Or.inl hd⟩

omit [Fintype α] in
/-- A complementary set has exactly one dropped-label port. -/
theorem exists_unique_port {s : Finset (α × Bool)} (d : α) (hc : IsComplementary s) :
    ∃! v, IsPort s d v := by
  classical
  by_cases hf : (d, false) ∈ s
  · refine ⟨(d, false), ⟨hf, Or.inl rfl⟩, ?_⟩
    rintro ⟨i, b⟩ hv
    obtain ⟨hi, hm⟩ := (complementary_port_iff hc _).mp hv
    change i = d at hi
    subst i
    cases b
    · rfl
    · exact ((hc d).mp hf hm).elim
  · have ht : (d, true) ∈ s := by
      by_contra h
      exact hf ((hc d).mpr h)
    refine ⟨(d, true), ⟨ht, Or.inl rfl⟩, ?_⟩
    rintro ⟨i, b⟩ hv
    obtain ⟨hi, hm⟩ := (complementary_port_iff hc _).mp hv
    change i = d at hi
    subst i
    cases b
    · exact (hf hm).elim
    · rfl

/-- The unique duplicated label supplies exactly the two ports of a nonendpoint. -/
theorem noncomplementary_ports {s : Finset (α × Bool)} (d : α)
    (hsize : s.card = Fintype.card α) (hcovers : CoversExcept s d)
    (hnot : ¬ IsComplementary s) :
    ∃ k, k ≠ d ∧ ((k, false) ∈ s ∧ (k, true) ∈ s) ∧
      ∀ v, IsPort s d v ↔ v = (k, false) ∨ v = (k, true) := by
  obtain ⟨hmissing, k, hk, huniq⟩ :=
    (complementary_or_unique_duplicate s d hsize hcovers).resolve_left hnot
  have hkd : k ≠ d := by
    intro h
    rw [h] at hk
    exact hmissing.1 hk.1
  refine ⟨k, hkd, hk, ?_⟩
  rintro ⟨i, b⟩
  constructor
  · rintro ⟨hv, hd | hh⟩
    · change i = d at hd
      subst i
      cases b
      · exact (hmissing.1 hv).elim
      · exact (hmissing.2 hv).elim
    · have hi := huniq i hh
      subst i
      cases b <;> simp
  · intro h
    rcases h with h | h
    · rw [h]
      exact ⟨hk.1, Or.inr hk⟩
    · rw [h]
      exact ⟨hk.2, Or.inr hk⟩

omit [Fintype α] in
/-- Switching a valid port stays at a valid port of the same label set. -/
theorem switch_isPort {s : Finset (α × Bool)} {d : α} {v : α × Bool}
    (hv : IsPort s d v) : IsPort s d (switch s d v) := by
  by_cases hd : v.1 = d
  · simpa only [switch, ite_eq_left hd] using hv
  · have hh := hv.2.resolve_left hd
    rcases v with ⟨i, b⟩
    cases b <;> simp only [switch, hd, ↓reduceIte, Bool.not_false, Bool.not_true]
    · exact ⟨hh.2, Or.inr hh⟩
    · exact ⟨hh.1, Or.inr hh⟩

omit [Fintype α] in
/-- Switching twice restores the port. -/
theorem switch_switch (s : Finset (α × Bool)) (d : α) (v : α × Bool) :
    switch s d (switch s d v) = v := by
  rcases v with ⟨i, b⟩
  by_cases hd : i = d <;> simp [switch, hd]

/-- A valid port is fixed by switching precisely at a complementary endpoint. -/
theorem switch_eq_self_iff_complementary {s : Finset (α × Bool)} {d : α}
    (hsize : s.card = Fintype.card α) (hcovers : CoversExcept s d)
    {v : α × Bool} (hv : IsPort s d v) : switch s d v = v ↔ IsComplementary s := by
  constructor
  · intro h
    have hd : v.1 = d := by
      by_contra hd
      rcases v with ⟨i, b⟩
      cases b <;> simp [switch, hd] at h
    rcases complementary_or_unique_duplicate s d hsize hcovers with hc | ⟨hm, _⟩
    · exact hc
    · rcases v with ⟨i, b⟩
      change i = d at hd
      subst i
      cases b
      · exact (hm.1 hv.1).elim
      · exact (hm.2 hv.1).elim
  · intro hc
    have hd := ((complementary_port_iff hc v).mp hv).1
    simp only [switch, ite_eq_left hd]

omit [Fintype α] in
/-- Exchanging a port preserves coverage away from the dropped label. -/
theorem exchange_covers {s : Finset (α × Bool)} {d : α} {v u : α × Bool}
    (hcovers : CoversExcept s d) (hv : IsPort s d v) :
    CoversExcept (exchange s v u) d := by
  rcases v with ⟨i, b⟩
  rcases hv.2 with hd | hh
  · change i = d at hd
    subst i
    exact hcovers.exchange_dropped b u
  · exact hcovers.exchange_duplicate hh b u

omit [Fintype α] in
/-- The leaving variable becomes a port after entering along a valid port. -/
theorem exchange_isPort {s : Finset (α × Bool)} {d : α} {v u : α × Bool}
    (hcovers : CoversExcept s d) (hv : IsPort s d v) (hu : u ∉ s) :
    IsPort (exchange s v u) d u := by
  refine ⟨entering_mem _ _ _, ?_⟩
  by_cases hd : u.1 = d
  · exact Or.inl hd
  · right
    have hlabel : u.1 ≠ v.1 := by
      intro h
      have hdup := hv.2.resolve_left (fun h' => hd (h.trans h'))
      rcases u with ⟨i, b⟩
      cases b
      · apply hu
        simpa only [← h] using hdup.1
      · apply hu
        simpa only [← h] using hdup.2
    have hc := hcovers u.1 hd
    rcases u with ⟨i, b⟩
    cases b
    · have ht : (i, true) ∈ s := hc.resolve_left hu
      exact ⟨entering_mem _ _ _, mem_exchange.mpr (Or.inr
        ⟨fun h => by apply hlabel; cases h; rfl, ht⟩)⟩
    · have hf : (i, false) ∈ s := hc.resolve_right hu
      exact ⟨mem_exchange.mpr (Or.inr
        ⟨fun h => by apply hlabel; cases h; rfl, hf⟩), entering_mem _ _ _⟩

end GameTheory.Math.ComplementaryPorts
