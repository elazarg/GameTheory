import GameTheory.Math.EndOfLine

/-! An involution can exchange the continuations at internal vertices while preserving
every endpoint. The cut condition prevents a exchanged edge from becoming a self-loop. -/

namespace GameTheory.Math.EndOfLine

variable {α : Type*} (P S T : α → α)

/-- Reattach an incoming edge to the exchanged continuation vertex. -/
def tailSwitchPredecessor (x : α) : α := T (P x)

/-- Follow the outgoing edge of the exchanged continuation vertex. -/
def tailSwitchSuccessor (x : α) : α := S (T x)

variable (hinv : ∀ x, T (T x) = x)
  (hP : ∀ x, P x ≠ x → S (P x) = x)
  (hS : ∀ x, S x ≠ x → P (S x) = x)
  (hchanged : ∀ x, T x ≠ x → P x ≠ x ∧ S x ≠ x)
  (hcut : ∀ x, T x ≠ x → S (T x) ≠ x)

include hinv hP hchanged hcut in
/-- Exchanging internal continuations preserves nontrivial incoming pointers. -/
theorem tailSwitch_predecessor_ne_self_iff (x : α) :
    tailSwitchPredecessor P T x ≠ x ↔ P x ≠ x := by
  classical
  by_cases hx : T x = x
  · constructor
    · intro h hp
      exact h (by simp [tailSwitchPredecessor, hp, hx])
    · intro hp ht
      apply hp
      have := congrArg T ht
      simpa only [tailSwitchPredecessor, hinv, hx] using this
  · have hp := (hchanged x hx).1
    refine ⟨fun _ => hp, fun _ ht => ?_⟩
    have he : P x = T x := by
      have := congrArg T ht
      simpa only [tailSwitchPredecessor, hinv] using this
    exact hcut x hx (by rw [← he]; exact hP x hp)

include hchanged hcut in
/-- Exchanging internal continuations preserves nontrivial outgoing pointers. -/
theorem tailSwitch_successor_ne_self_iff (x : α) :
    tailSwitchSuccessor S T x ≠ x ↔ S x ≠ x := by
  classical
  by_cases hx : T x = x
  · simp only [tailSwitchSuccessor, hx]
  · exact iff_of_true (hcut x hx) (hchanged x hx).2

include hinv hP hchanged hcut in
/-- A switched nontrivial incoming edge still has its reciprocal outgoing edge. -/
theorem tailSwitch_predecessor_consistent (x : α)
    (h : tailSwitchPredecessor P T x ≠ x) :
    tailSwitchSuccessor S T (tailSwitchPredecessor P T x) = x := by
  have hp := (tailSwitch_predecessor_ne_self_iff P S T hinv hP hchanged hcut x).mp h
  simp only [tailSwitchSuccessor, tailSwitchPredecessor, hinv, hP x hp]

include hinv hS hchanged in
/-- A switched nontrivial outgoing edge still has its reciprocal incoming edge. -/
theorem tailSwitch_successor_consistent (x : α)
    (h : tailSwitchSuccessor S T x ≠ x) :
    tailSwitchPredecessor P T (tailSwitchSuccessor S T x) = x := by
  classical
  have hs : S (T x) ≠ T x := by
    by_cases hx : T x = x
    · simpa only [tailSwitchSuccessor, hx] using h
    · exact (hchanged (T x) (by rw [hinv]; exact Ne.symm hx)).2
  simp only [tailSwitchPredecessor, tailSwitchSuccessor, hS (T x) hs, hinv]

include hinv hP hchanged hcut in
/-- Exchanging internal continuations preserves consistent incoming-edge presence. -/
theorem tailSwitch_hasPredecessor_iff (x : α) :
    HasPredecessor (tailSwitchPredecessor P T) (tailSwitchSuccessor S T) x ↔
      HasPredecessor P S x := by
  constructor
  · intro h
    have hp := (tailSwitch_predecessor_ne_self_iff P S T hinv hP hchanged hcut x).mp h.1
    exact ⟨hp, hP x hp⟩
  · intro h
    have hp := (tailSwitch_predecessor_ne_self_iff P S T hinv hP hchanged hcut x).mpr h.1
    exact ⟨hp, tailSwitch_predecessor_consistent P S T hinv hP hchanged hcut x hp⟩

include hinv hS hchanged hcut in
/-- Exchanging internal continuations preserves consistent outgoing-edge presence. -/
theorem tailSwitch_hasSuccessor_iff (x : α) :
    HasSuccessor (tailSwitchPredecessor P T) (tailSwitchSuccessor S T) x ↔
      HasSuccessor P S x := by
  constructor
  · intro h
    have hs := (tailSwitch_successor_ne_self_iff P S T hchanged hcut x).mp h.1
    exact ⟨hs, hS x hs⟩
  · intro h
    have hs := (tailSwitch_successor_ne_self_iff P S T hchanged hcut x).mpr h.1
    exact ⟨hs, tailSwitch_successor_consistent P S T hinv hS hchanged x hs⟩

include hinv hP hS hchanged hcut in
/-- Exchanging internal continuations preserves every endpoint of the graph. -/
theorem tailSwitch_isEndpoint_iff (x : α) :
    IsEndpoint (tailSwitchPredecessor P T) (tailSwitchSuccessor S T) x ↔
      IsEndpoint P S x := by
  simp only [IsEndpoint,
    tailSwitch_hasPredecessor_iff P S T hinv hP hchanged hcut,
    tailSwitch_hasSuccessor_iff P S T hinv hS hchanged hcut]

end GameTheory.Math.EndOfLine
