import GameTheoryComplexity.Backend.SpernerGridCodec
import GameTheory.Math.SpernerGridGraph

/-! Binary word semantics for the local Sperner graph. The source has the zero
word, triangles use fixed coordinate blocks, and every rejected word is isolated.
This transport layer proves graph agreement; machine runtime is a separate certificate. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner

/-- Lift the local graph pointer to words, leaving rejected encodings isolated. -/
def wordGridPointer (b : ℕ) (interior : ℕ → ℕ → Fin 3) (incoming : Bool)
    (word : List Bool) : List Bool :=
  match decodeGridNode b word with
  | none => word
  | some node => encodeGridNode b (gridPointer (2 ^ b) interior incoming node)

private theorem gridPointer_bounded (b : ℕ) (interior : ℕ → ℕ → Fin 3)
    (incoming : Bool) (node : Option GridTriangle)
    (hv : ∀ t, node = some t → ValidTriangle (2 ^ b) t) :
    ∀ t, gridPointer (2 ^ b) interior incoming node = some t →
      ValidTriangle (2 ^ b) t := by
  intro u hu
  cases node with
  | none =>
    cases incoming
    · simp only [gridPointer, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hu
      subst u
      exact ⟨Nat.two_pow_pos b, Nat.two_pow_pos b⟩
    · simp [gridPointer] at hu
  | some t =>
    have ht := hv t rfl
    simp only [gridPointer, ht, ↓reduceIte] at hu
    cases hd : gridDoor (standardGridColor (2 ^ b) interior) t incoming with
    | none => simp only [hd, Option.some.injEq] at hu; subst u; exact ht
    | some p =>
      simp only [hd] at hu
      cases ha : across (2 ^ b) t p with
      | none =>
        rw [ha] at hu
        cases incoming
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hu
          subst u
          exact ht
        · simp at hu
      | some vq =>
        rcases vq with ⟨v, q⟩
        simp only [ha, Option.some.injEq] at hu
        subst u
        exact across_valid ht ha

/-- On every accepted code, word evaluation is exactly encoded node evaluation. -/
theorem wordGridPointer_of_decode {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) (interior : ℕ → ℕ → Fin 3)
    (incoming : Bool) :
    wordGridPointer b interior incoming word =
      encodeGridNode b (gridPointer (2 ^ b) interior incoming node) := by
  simp only [wordGridPointer, hd]

/-- Encoding a bounded node commutes with pointer evaluation. -/
theorem wordGridPointer_encode (b : ℕ) (interior : ℕ → ℕ → Fin 3) (incoming : Bool)
    (node : Option GridTriangle) (hv : ∀ t, node = some t → ValidTriangle (2 ^ b) t) :
    wordGridPointer b interior incoming (encodeGridNode b node) =
      encodeGridNode b (gridPointer (2 ^ b) interior incoming node) :=
  wordGridPointer_of_decode (decodeGridNode_encode b node hv) interior incoming

private theorem encode_bounded_injective {b : ℕ} {a c : Option GridTriangle}
    (ha : ∀ t, a = some t → ValidTriangle (2 ^ b) t)
    (hc : ∀ t, c = some t → ValidTriangle (2 ^ b) t) :
    encodeGridNode b a = encodeGridNode b c ↔ a = c := by
  constructor
  · intro h
    have hd := congrArg (decodeGridNode b) h
    rw [decodeGridNode_encode b a ha, decodeGridNode_encode b c hc] at hd
    exact Option.some.inj hd
  · rintro rfl
    rfl

/-- Word pointers preserve length, including every rejected encoding. -/
@[simp] theorem wordGridPointer_length (b : ℕ) (interior : ℕ → ℕ → Fin 3)
    (incoming : Bool) (word : List Bool) :
    (wordGridPointer b interior incoming word).length = word.length := by
  cases hd : decodeGridNode b word with
  | none => simp [wordGridPointer, hd]
  | some node =>
    rw [wordGridPointer_of_decode hd, encodeGridNode_length, decodeGridNode_length hd]

private theorem word_pointer_ne_iff {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) (interior : ℕ → ℕ → Fin 3)
    (incoming : Bool) :
    wordGridPointer b interior incoming word ≠ word ↔
      gridPointer (2 ^ b) interior incoming node ≠ node := by
  have hv := decodeGridNode_valid hd
  have hp := gridPointer_bounded b interior incoming node hv
  rw [wordGridPointer_of_decode hd, ← encodeGridNode_decode hd]
  exact (encode_bounded_injective hp hv).not

private theorem word_pointer_inverse_iff {b : ℕ} {word : List Bool}
    {node : Option GridTriangle} (hd : decodeGridNode b word = some node)
    (interior : ℕ → ℕ → Fin 3) (incoming : Bool) :
    wordGridPointer b interior (!incoming) (wordGridPointer b interior incoming word) = word ↔
      gridPointer (2 ^ b) interior (!incoming)
        (gridPointer (2 ^ b) interior incoming node) = node := by
  have hv := decodeGridNode_valid hd
  have hp := gridPointer_bounded b interior incoming node hv
  have hpp := gridPointer_bounded b interior (!incoming) _ hp
  rw [wordGridPointer_of_decode hd, wordGridPointer_encode _ _ _ _ hp,
    ← encodeGridNode_decode hd]
  exact encode_bounded_injective hpp hv

/-- Endpoint predicates agree exactly across the accepted binary representation. -/
theorem word_grid_endpoint_iff {b : ℕ} {word : List Bool} {node : Option GridTriangle}
    (hd : decodeGridNode b word = some node) (interior : ℕ → ℕ → Fin 3) :
    GameTheory.Math.EndOfLine.IsEndpoint
        (wordGridPointer b interior true) (wordGridPointer b interior false) word ↔
      GameTheory.Math.EndOfLine.IsEndpoint
        (gridPointer (2 ^ b) interior true) (gridPointer (2 ^ b) interior false) node := by
  have hp : wordGridPointer b interior false (wordGridPointer b interior true word) = word ↔
      gridPointer (2 ^ b) interior false (gridPointer (2 ^ b) interior true node) = node :=
    word_pointer_inverse_iff hd interior true
  have hs : wordGridPointer b interior true (wordGridPointer b interior false word) = word ↔
      gridPointer (2 ^ b) interior true (gridPointer (2 ^ b) interior false node) = node :=
    word_pointer_inverse_iff hd interior false
  unfold GameTheory.Math.EndOfLine.IsEndpoint GameTheory.Math.EndOfLine.HasPredecessor
    GameTheory.Math.EndOfLine.HasSuccessor
  rw [word_pointer_ne_iff hd interior true, word_pointer_ne_iff hd interior false,
    hp, hs]

/-- The all-zero code is a genuine source, even at zero coordinate-bit width. -/
theorem word_grid_source (b : ℕ) (interior : ℕ → ℕ → Fin 3) :
    wordGridPointer b interior true (encodeGridNode b none) = encodeGridNode b none ∧
      wordGridPointer b interior false (encodeGridNode b none) ≠ encodeGridNode b none ∧
      wordGridPointer b interior true
        (wordGridPointer b interior false (encodeGridNode b none)) = encodeGridNode b none := by
  have hd := decodeGridNode_source b
  have hs := grid_source (2 ^ b) interior (Nat.two_pow_pos b)
  refine ⟨?_, (word_pointer_ne_iff hd interior false).mpr hs.2.1,
    (word_pointer_inverse_iff hd interior false).mpr hs.2.2⟩
  rw [wordGridPointer_of_decode hd]
  simp only [gridPointer, ↓reduceIte]

/-- Every non-source word endpoint decodes to a bounded trichromatic triangle.
Malformed and unused words cannot supply spurious endpoints. -/
theorem word_grid_endpoint_decodes {b : ℕ} {word : List Bool}
    (interior : ℕ → ℕ → Fin 3) (hne : word ≠ encodeGridNode b none)
    (he : GameTheory.Math.EndOfLine.IsEndpoint
      (wordGridPointer b interior true) (wordGridPointer b interior false) word) :
    ∃ t, decodeGridNode b word = some (some t) ∧ ValidTriangle (2 ^ b) t ∧
      Trichromatic
        (standardGridColor (2 ^ b) interior (corner t 0).1 (corner t 0).2)
        (standardGridColor (2 ^ b) interior (corner t 1).1 (corner t 1).2)
        (standardGridColor (2 ^ b) interior (corner t 2).1 (corner t 2).2) := by
  cases hd : decodeGridNode b word with
  | none =>
    simp [GameTheory.Math.EndOfLine.IsEndpoint, GameTheory.Math.EndOfLine.HasPredecessor,
      GameTheory.Math.EndOfLine.HasSuccessor, wordGridPointer, hd] at he
  | some node =>
    have hnode : node ≠ none := by
      intro h
      subst node
      exact hne (encodeGridNode_decode hd).symm
    have hg := (word_grid_endpoint_iff hd interior).mp he
    obtain ⟨t, ht, hv, htri⟩ := grid_endpoint_decodes (Nat.two_pow_pos b) hnode hg
    exact ⟨t, congrArg some ht, hv, htri⟩

/-- Binary endpoint witnesses have exactly two coordinate blocks and two header bits. -/
theorem exists_word_grid_endpoint (b : ℕ) (interior : ℕ → ℕ → Fin 3) :
    ∃ word, word.length = gridNodeWidth b ∧ word ≠ encodeGridNode b none ∧
      GameTheory.Math.EndOfLine.IsEndpoint
        (wordGridPointer b interior true) (wordGridPointer b interior false) word := by
  obtain ⟨t, hv, he⟩ := exists_grid_endpoint (2 ^ b) interior (Nat.two_pow_pos b)
  have hb : ∀ u, some t = some u → ValidTriangle (2 ^ b) u := by
    intro u hu
    cases hu
    exact hv
  have hsource : ∀ u, (none : Option GridTriangle) = some u →
      ValidTriangle (2 ^ b) u := by intro u hu; cases hu
  have hd := decodeGridNode_encode b (some t) hb
  refine ⟨encodeGridNode b (some t), encodeGridNode_length _ _, ?_,
    (word_grid_endpoint_iff hd interior).mpr he⟩
  exact (encode_bounded_injective hb hsource).not.mpr (by simp)

end GameTheory.Complexity.Backend
