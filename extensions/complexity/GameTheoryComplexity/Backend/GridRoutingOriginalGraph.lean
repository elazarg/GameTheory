import GameTheoryComplexity.Backend.GridRoutingQueries
import GameTheoryComplexity.Backend.EndOfLinePointerNormalization

/-! Fixed-width binary pointers and their bounded natural extensions represent
the same incident edges. Normalized circuit queries supply natural source and
endpoint certificates for the routed Sperner construction. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.EndOfLine
open _root_.Complexity _root_.Complexity.Cobham

/-- Fixed-width serialization is injective on bounded labels. -/
theorem routingOriginal_encode_eq_iff (b : ℕ) {i j : ℕ}
    (hi : i < 2 ^ b) (hj : j < 2 ^ b) :
    Nat.toBitsLE b i = Nat.toBitsLE b j ↔ i = j := by
  constructor
  · intro h
    have hv := congrArg Nat.fromBitsLE h
    simpa only [Nat.fromBitsLE_toBitsLE hi, Nat.fromBitsLE_toBitsLE hj] using hv
  · rintro rfl
    rfl

/-- A length-preserving query agrees exactly with its natural extension. -/
theorem routingOriginalPointer_encode (ruler : List Bool) (query : List Bool → List Bool)
    (hlen : ∀ word, (query word).length = word.length) {i : ℕ}
    (hi : i < 2 ^ ruler.length) :
    Nat.toBitsLE ruler.length (routingOriginalPointer ruler query i) =
      query (Nat.toBitsLE ruler.length i) := by
  have hp : routingPadBits ruler (query (Nat.toBitsLE ruler.length i)) =
      query (Nat.toBitsLE ruler.length i) := by
    rw [routingPadBits_eq_toBitsLE]
    have h := Nat.toBitsLE_fromBitsLE (query (Nat.toBitsLE ruler.length i))
    simpa only [hlen, Nat.length_toBitsLE] using h
  simp only [routingOriginalPointer, ite_eq_left hi, hp]
  have h := Nat.toBitsLE_fromBitsLE (query (Nat.toBitsLE ruler.length i))
  simpa only [hlen, Nat.length_toBitsLE] using h

/-- Natural and binary outgoing edges coincide. -/
theorem routingOriginal_hasSuccessor_iff (ruler : List Bool) (P S : List Bool → List Bool)
    (hP : ∀ word, (P word).length = word.length)
    (hS : ∀ word, (S word).length = word.length) {i : ℕ}
    (hi : i < 2 ^ ruler.length) :
    HasSuccessor (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) i ↔
      HasSuccessor P S (Nat.toBitsLE ruler.length i) := by
  have hs := routingOriginalPointer_encode ruler S hS hi
  have hsi := routingOriginalPointer_lt ruler S hi
  have hpsi := routingOriginalPointer_lt ruler P hsi
  have hps : Nat.toBitsLE ruler.length
      (routingOriginalPointer ruler P (routingOriginalPointer ruler S i)) =
      P (S (Nat.toBitsLE ruler.length i)) :=
    (routingOriginalPointer_encode ruler P hP hsi).trans (congrArg P hs)
  simp only [HasSuccessor]
  rw [← hps, ← hs]
  exact (and_congr
    (not_congr (routingOriginal_encode_eq_iff ruler.length hsi hi))
    (routingOriginal_encode_eq_iff ruler.length hpsi hi)).symm

/-- Natural and binary incoming edges coincide. -/
theorem routingOriginal_hasPredecessor_iff (ruler : List Bool) (P S : List Bool → List Bool)
    (hP : ∀ word, (P word).length = word.length)
    (hS : ∀ word, (S word).length = word.length) {i : ℕ}
    (hi : i < 2 ^ ruler.length) :
    HasPredecessor (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) i ↔
      HasPredecessor P S (Nat.toBitsLE ruler.length i) :=
  routingOriginal_hasSuccessor_iff ruler S P hS hP hi

/-- Every natural endpoint corresponds to its fixed-width binary endpoint. -/
theorem routingOriginal_endpoint_iff (ruler : List Bool) (P S : List Bool → List Bool)
    (hP : ∀ word, (P word).length = word.length)
    (hS : ∀ word, (S word).length = word.length) {i : ℕ}
    (hi : i < 2 ^ ruler.length) :
    IsEndpoint (routingOriginalPointer ruler P) (routingOriginalPointer ruler S) i ↔
      IsEndpoint P S (Nat.toBitsLE ruler.length i) := by
  simp only [IsEndpoint, routingOriginal_hasSuccessor_iff ruler P S hP hS hi,
    routingOriginal_hasPredecessor_iff ruler P S hP hS hi]

/-- Normalized natural circuit pointers preserve original endpoint status. -/
theorem routingNormalized_endpoint_iff (input : List Bool) {i : ℕ}
    (hi : i < 2 ^ (pairFst input).length) :
    IsEndpoint (routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input))
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input)) i ↔
      IsEndpoint (endOfLinePredecessor input) (endOfLineSuccessor input)
        (Nat.toBitsLE (pairFst input).length i) :=
  (routingOriginal_endpoint_iff (pairFst input) _ _
    (endOfLineNormalizedPredecessor_length input)
    (endOfLineNormalizedSuccessor_length input) hi).trans
    (endOfLineNormalized_endpoint_iff input _)

/-- A canonical binary source gives the same natural source and reverse link. -/
theorem routingOriginal_source (ruler : List Bool) (P S : List Bool → List Bool)
    (hP : ∀ word, (P word).length = word.length)
    (hS : ∀ word, (S word).length = word.length)
    (hp : P (Nat.toBitsLE ruler.length 0) = Nat.toBitsLE ruler.length 0)
    (hs : S (Nat.toBitsLE ruler.length 0) ≠ Nat.toBitsLE ruler.length 0)
    (hlink : P (S (Nat.toBitsLE ruler.length 0)) = Nat.toBitsLE ruler.length 0) :
    routingOriginalPointer ruler P 0 = 0 ∧ routingOriginalPointer ruler S 0 ≠ 0 ∧
      routingOriginalPointer ruler P (routingOriginalPointer ruler S 0) = 0 := by
  have hz : 0 < 2 ^ ruler.length := Nat.two_pow_pos _
  have hpe := routingOriginalPointer_encode ruler P hP hz
  have hse := routingOriginalPointer_encode ruler S hS hz
  have hsi := routingOriginalPointer_lt ruler S hz
  have hpsi := routingOriginalPointer_lt ruler P hsi
  refine ⟨(routingOriginal_encode_eq_iff ruler.length
    (routingOriginalPointer_lt ruler P hz) hz).mp (hpe.trans hp), ?_, ?_⟩
  · intro he
    apply hs
    rw [← hse, he]
  · apply (routingOriginal_encode_eq_iff ruler.length hpsi hz).mp
    exact (routingOriginalPointer_encode ruler P hP hsi).trans
      ((congrArg P hse).trans hlink)

/-- The genuine-source promise survives circuit normalization and numeric extension. -/
theorem routingNormalized_source {input : List Bool} (hsource : endOfLineSourceValid input) :
    routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input) 0 = 0 ∧
      routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input) 0 ≠ 0 ∧
      routingOriginalPointer (pairFst input) (endOfLineNormalizedPredecessor input)
        (routingOriginalPointer (pairFst input) (endOfLineNormalizedSuccessor input) 0) = 0 := by
  have ho : Nat.toBitsLE (pairFst input).length 0 = endOfLineOrigin input := by
    have hz : ∀ b, Nat.toBits b 0 = List.replicate b false := by
      intro b
      induction b with
      | zero => rfl
      | succ b ih => simp [Nat.toBits, ih, List.replicate_succ]
    simp [endOfLineOrigin, endOfLineWidth, Nat.toBitsLE, hz]
  have hp : endOfLineNormalizedPredecessor input (endOfLineOrigin input) =
      endOfLineOrigin input := by
    rw [endOfLineNormalizedPredecessor_eq, normalizePredecessor]
    split_ifs
    · exact hsource.1
    · rfl
  have hs : endOfLineNormalizedSuccessor input (endOfLineOrigin input) ≠
      endOfLineOrigin input := by
    rw [endOfLineNormalizedSuccessor_eq, normalizeSuccessor_ne_self_iff]
    exact ⟨hsource.2.1, hsource.2.2⟩
  have hlink : endOfLineNormalizedPredecessor input
      (endOfLineNormalizedSuccessor input (endOfLineOrigin input)) = endOfLineOrigin input := by
    simp only [endOfLineNormalizedPredecessor_eq, endOfLineNormalizedSuccessor_eq] at hs ⊢
    exact normalizePredecessor_successor _ _ hs
  apply routingOriginal_source (pairFst input) _ _
    (endOfLineNormalizedPredecessor_length input) (endOfLineNormalizedSuccessor_length input)
  · simpa only [ho] using hp
  · simpa only [ho] using hs
  · simpa only [ho] using hlink

end GameTheory.Complexity.Backend
