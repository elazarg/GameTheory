import GameTheoryComplexity.Backend.GridRoutingCodec
import GameTheoryComplexity.Backend.GridRoutingEndpointMachine
import GameTheory.Math.GridWireBounds

/-! Two fixed-width coordinate fields transport the globally switched grid
graph to words. Accepted words cover the entire coordinate capacity; malformed
lengths remain isolated. Runtime certificates are supplied separately. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.GridWire GameTheory.Math.EndOfLine

/-- The coordinate fields contain the quadratic-width routing rectangle. -/
theorem routingCoordinateCapacity (b : ℕ) :
    3 * (2 ^ b) * (2 ^ b) ≤ 2 ^ routingCoordinateWidth b ∧
      6 * (2 ^ b) ≤ 2 ^ routingCoordinateWidth b := by
  have hn : 1 ≤ 2 ^ b := by have h := Nat.two_pow_pos b; omega
  have hnn : 2 ^ b ≤ (2 ^ b) * (2 ^ b) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ b) hn
  have he : 2 ^ routingCoordinateWidth b = 8 * ((2 ^ b) * (2 ^ b)) := by
    simp [routingCoordinateWidth, two_mul, pow_add, Nat.mul_assoc, Nat.mul_comm]
  rw [he]
  rw [Nat.mul_assoc]
  omega

/-- Both grid pointers preserve the coordinate field capacity. -/
theorem routingPointer_bounded {b : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hp : p.1 < 2 ^ routingCoordinateWidth b ∧ p.2 < 2 ^ routingCoordinateWidth b) :
    (gridRoutedPredecessor (2 ^ b) P S p).1 < 2 ^ routingCoordinateWidth b ∧
      (gridRoutedPredecessor (2 ^ b) P S p).2 < 2 ^ routingCoordinateWidth b ∧
      (gridRoutedSuccessor (2 ^ b) P S p).1 < 2 ^ routingCoordinateWidth b ∧
      (gridRoutedSuccessor (2 ^ b) P S p).2 < 2 ^ routingCoordinateWidth b := by
  have h := gridRouted_pointer_bounds (routingCoordinateCapacity b).1
    (routingCoordinateCapacity b).2 hp (P := P) (S := S)
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-- Serialize one of the two global grid pointers, isolating malformed words. -/
def wordRoutingPointer (b : ℕ) (P S : ℕ → ℕ) (incoming : Bool)
    (word : List Bool) : List Bool :=
  match decodeRoutingPoint b word with
  | none => word
  | some p => encodeRoutingPoint b
      (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p)

private theorem pointPointer_bounded {b : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hp : p.1 < 2 ^ routingCoordinateWidth b ∧ p.2 < 2 ^ routingCoordinateWidth b)
    (incoming : Bool) :
    (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p).1 < 2 ^ routingCoordinateWidth b ∧
    (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p).2 < 2 ^ routingCoordinateWidth b := by
  have h := routingPointer_bounded hp (P := P) (S := S)
  cases incoming
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · exact ⟨h.1, h.2.1⟩

theorem wordRoutingPointer_of_decode {b : ℕ} {P S : ℕ → ℕ} {word : List Bool} {p : ℕ × ℕ}
    (hd : decodeRoutingPoint b word = some p) (incoming : Bool) :
    wordRoutingPointer b P S incoming word = encodeRoutingPoint b
      (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p) := by
  simp [wordRoutingPointer, hd]

theorem wordRoutingPointer_encode {b : ℕ} {P S : ℕ → ℕ} {p : ℕ × ℕ}
    (hp : p.1 < 2 ^ routingCoordinateWidth b ∧ p.2 < 2 ^ routingCoordinateWidth b)
    (incoming : Bool) :
    wordRoutingPointer b P S incoming (encodeRoutingPoint b p) = encodeRoutingPoint b
      (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p) :=
  wordRoutingPointer_of_decode (decodeRoutingPoint_encode b p hp.1 hp.2) incoming

@[simp] theorem wordRoutingPointer_length (b : ℕ) (P S : ℕ → ℕ)
    (incoming : Bool) (word : List Bool) :
    (wordRoutingPointer b P S incoming word).length = word.length := by
  cases hd : decodeRoutingPoint b word with
  | none => simp [wordRoutingPointer, hd]
  | some p =>
    rw [wordRoutingPointer_of_decode hd, encodeRoutingPoint_length, decodeRoutingPoint_length hd]

private theorem wordRoutingPointer_ne_iff {b : ℕ} {P S : ℕ → ℕ} {word : List Bool}
    {p : ℕ × ℕ} (hd : decodeRoutingPoint b word = some p) (incoming : Bool) :
    wordRoutingPointer b P S incoming word ≠ word ↔
      (if incoming then gridRoutedPredecessor (2 ^ b) P S p
      else gridRoutedSuccessor (2 ^ b) P S p) ≠ p := by
  have hv := decodeRoutingPoint_bound hd
  have hp := pointPointer_bounded hv incoming (P := P) (S := S)
  rw [wordRoutingPointer_of_decode hd, ← encodeRoutingPoint_decode hd]
  constructor
  · intro h he
    apply h
    rw [he]
  · intro h he
    exact h (encodeRoutingPoint_injective hp.1 hp.2 hv.1 hv.2 he)

private theorem wordRoutingPointer_inverse_iff {b : ℕ} {P S : ℕ → ℕ} {word : List Bool}
    {p : ℕ × ℕ} (hd : decodeRoutingPoint b word = some p) (incoming : Bool) :
    wordRoutingPointer b P S (!incoming) (wordRoutingPointer b P S incoming word) = word ↔
      (if !incoming then gridRoutedPredecessor (2 ^ b) P S
          (if incoming then gridRoutedPredecessor (2 ^ b) P S p
          else gridRoutedSuccessor (2 ^ b) P S p)
      else gridRoutedSuccessor (2 ^ b) P S
          (if incoming then gridRoutedPredecessor (2 ^ b) P S p
          else gridRoutedSuccessor (2 ^ b) P S p)) = p := by
  have hv := decodeRoutingPoint_bound hd
  have hp := pointPointer_bounded hv incoming (P := P) (S := S)
  have hpp := pointPointer_bounded hp (!incoming) (P := P) (S := S)
  rw [wordRoutingPointer_of_decode hd, wordRoutingPointer_encode hp,
    ← encodeRoutingPoint_decode hd]
  constructor
  · exact encodeRoutingPoint_injective hpp.1 hpp.2 hv.1 hv.2
  · intro h
    rw [h]

/-- Every nontrivial word step has its reciprocal word step. -/
theorem wordRoutingPointer_consistent (b : ℕ) (P S : ℕ → ℕ) (incoming : Bool)
    (word : List Bool) (hne : wordRoutingPointer b P S incoming word ≠ word) :
    wordRoutingPointer b P S (!incoming) (wordRoutingPointer b P S incoming word) = word := by
  cases hd : decodeRoutingPoint b word with
  | none => exact False.elim (hne (by simp [wordRoutingPointer, hd]))
  | some p =>
    apply (wordRoutingPointer_inverse_iff hd incoming).mpr
    have hp := (wordRoutingPointer_ne_iff hd incoming).mp hne
    cases incoming
    · exact gridRouted_successor_consistent _ _ _ _ hp
    · exact gridRouted_predecessor_consistent _ _ _ _ hp

/-- Accepted word endpoints agree exactly with coordinate endpoints. -/
theorem wordRouting_endpoint_iff {b : ℕ} {P S : ℕ → ℕ} {word : List Bool} {p : ℕ × ℕ}
    (hd : decodeRoutingPoint b word = some p) :
    IsEndpoint (wordRoutingPointer b P S true) (wordRoutingPointer b P S false) word ↔
      IsEndpoint (gridRoutedPredecessor (2 ^ b) P S)
        (gridRoutedSuccessor (2 ^ b) P S) p := by
  have hp := wordRoutingPointer_inverse_iff hd true (P := P) (S := S)
  have hs := wordRoutingPointer_inverse_iff hd false (P := P) (S := S)
  simp only [Bool.not_true, Bool.not_false, ↓reduceIte] at hp hs
  unfold IsEndpoint HasPredecessor HasSuccessor
  rw [wordRoutingPointer_ne_iff hd true, wordRoutingPointer_ne_iff hd false, hp, hs]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- The all-zero point word retains a valid original zero-source promise. -/
theorem wordRouting_source {b : ℕ} {P S : ℕ → ℕ}
    (hSi : S 0 < 2 ^ b) (hP : P 0 = 0) (hS : S 0 ≠ 0) (hlink : P (S 0) = 0) :
    wordRoutingPointer b P S true (encodeRoutingPoint b (0, 0)) =
        encodeRoutingPoint b (0, 0) ∧
      wordRoutingPointer b P S false (encodeRoutingPoint b (0, 0)) ≠
        encodeRoutingPoint b (0, 0) ∧
      wordRoutingPointer b P S true
        (wordRoutingPointer b P S false (encodeRoutingPoint b (0, 0))) =
        encodeRoutingPoint b (0, 0) := by
  have hz : 0 < 2 ^ routingCoordinateWidth b := Nat.two_pow_pos _
  have hd := decodeRoutingPoint_encode b (0, 0) hz hz
  have h := gridRouted_source (Nat.two_pow_pos b) hSi hP hS hlink
  refine ⟨?_, (wordRoutingPointer_ne_iff hd false).mpr h.2.1,
    (wordRoutingPointer_inverse_iff hd false).mpr h.2.2⟩
  rw [wordRoutingPointer_of_decode hd]
  exact congrArg (encodeRoutingPoint b) h.1

/-- Every word endpoint decodes to a bounded original vertex endpoint. -/
theorem wordRouting_endpoint_decodes {b : ℕ} {P S : ℕ → ℕ} {word : List Bool}
    (hP : ∀ i, i < 2 ^ b → P i < 2 ^ b) (hS : ∀ i, i < 2 ^ b → S i < 2 ^ b)
    (he : IsEndpoint (wordRoutingPointer b P S true) (wordRoutingPointer b P S false) word) :
    ∃ i, i < 2 ^ b ∧ decodeRoutingPoint b word = some (vertexPoint i) ∧ IsEndpoint P S i := by
  cases hd : decodeRoutingPoint b word with
  | none => simp [IsEndpoint, HasPredecessor, HasSuccessor, wordRoutingPointer, hd] at he
  | some p =>
    obtain ⟨i, hi, rfl, hend⟩ := gridRouted_endpoint_decodes hP hS
      ((wordRouting_endpoint_iff hd).mp he)
    exact ⟨i, hi, rfl, hend⟩

/-- Excluding the all-zero source word excludes the original zero vertex as well. -/
theorem wordRouting_endpoint_ne_origin {b : ℕ} {P S : ℕ → ℕ} {word : List Bool}
    (hP : ∀ i, i < 2 ^ b → P i < 2 ^ b) (hS : ∀ i, i < 2 ^ b → S i < 2 ^ b)
    (hne : word ≠ encodeRoutingPoint b (0, 0))
    (he : IsEndpoint (wordRoutingPointer b P S true) (wordRoutingPointer b P S false) word) :
    ∃ i, i < 2 ^ b ∧ i ≠ 0 ∧ decodeRoutingPoint b word = some (vertexPoint i) ∧
      IsEndpoint P S i := by
  obtain ⟨i, hi, hd, hend⟩ := wordRouting_endpoint_decodes hP hS he
  refine ⟨i, hi, ?_, hd, hend⟩
  intro h
  subst i
  exact hne (encodeRoutingPoint_decode hd).symm

/-- Every routed endpoint has a canonical binary original-endpoint label. -/
theorem wordRouting_endpoint_label {ruler word : List Bool} {P S : ℕ → ℕ}
    (hP : ∀ i, i < 2 ^ ruler.length → P i < 2 ^ ruler.length)
    (hS : ∀ i, i < 2 ^ ruler.length → S i < 2 ^ ruler.length)
    (he : IsEndpoint (wordRoutingPointer ruler.length P S true)
      (wordRoutingPointer ruler.length P S false) word) :
    ∃ i, i < 2 ^ ruler.length ∧ IsEndpoint P S i ∧
      routingEndpointLabelBits ruler word = Nat.toBitsLE ruler.length i := by
  obtain ⟨i, hi, hd, hend⟩ := wordRouting_endpoint_decodes hP hS he
  exact ⟨i, hi, hend, routingEndpointLabelBits_eq_bits hd hi⟩

end GameTheory.Complexity.Backend
