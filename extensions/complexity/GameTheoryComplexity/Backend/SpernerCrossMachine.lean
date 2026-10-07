import GameTheoryComplexity.Backend.SpernerGridCodecMachine
import GameTheoryComplexity.Backend.SpernerBinarySteps

/-! Polynomial-time crossing of a selected grid edge on binary node words.
Coordinate tests distinguish exterior edges before ripple arithmetic is used.
Only interior crossings change a coordinate, preserving its fixed-width encoding. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner

private def crossingNode (upper : Bool) (x y : List Bool) : List Bool :=
  [true, upper] ++ x ++ y

/-- Cross one selected side using fixed-width coordinate tests and ripple steps.
An exterior edge returns the source for incoming crossings and the original word otherwise. -/
def gridCrossWord (ruler : List Bool) (incoming : Bool) (p : Fin 3)
    (word : List Bool) : List Bool :=
  let x := gridNodeXBits ruler word
  let y := gridNodeYBits ruler word
  let zero := List.replicate ruler.length false
  let max := List.replicate ruler.length true
  let exterior := if incoming then gridWidthWord ruler else word
  let upper := if p = 0 then crossingNode false x y
    else if p = 1 then caseBit₀ (eqFlag y max) exterior
      (crossingNode false x (gridSuccBits y))
    else caseBit₀ (eqFlag x zero) exterior (crossingNode false (gridPredBits x) y)
  let lower := if p = 0 then caseBit₀ (eqFlag y zero) exterior
      (crossingNode true x (gridPredBits y))
    else if p = 1 then caseBit₀ (eqFlag x max) exterior
      (crossingNode true (gridSuccBits x) y)
    else crossingNode true x y
  caseBit₀ (gridNodeHalfFlag word) upper lower

private theorem crossingNode_mem_FP (upper : Bool) {x y : List Bool → List Bool}
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => crossingNode upper (x z) (y z)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP [true, upper]) hx) hy

/-- Selected-side crossing has an actual polynomial-time word-machine certificate. -/
theorem gridCrossWordFn_mem_FP (incoming : Bool) (p : Fin 3)
    {ruler word : List Bool → List Bool} (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => gridCrossWord (ruler z) incoming p (word z)) ∈ FP := by
  have hx := gridNodeXBitsFn_mem_FP hr hw
  have hy := gridNodeYBitsFn_mem_FP hr hw
  have hzero : (fun z => List.replicate (ruler z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hr
  have hmax : (fun z => List.replicate (ruler z).length true) ∈ FP :=
    mem_FP_comp hr unaryLength_mem_FP
  have hext : (fun z => if incoming then gridWidthWord (ruler z) else word z) ∈ FP := by
    cases incoming
    · exact hw
    · exact gridWidthWordFn_mem_FP hr
  have hxp := mem_FP_comp hx gridPredBits_mem_FP
  have hyp := mem_FP_comp hy gridPredBits_mem_FP
  have hxs := mem_FP_comp hx gridSuccBits_mem_FP
  have hys := mem_FP_comp hy gridSuccBits_mem_FP
  fin_cases p
  · exact selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw)
      (crossingNode_mem_FP false hx hy)
      (selectFn_mem_FP (eqFlagFn_mem_FP hy hzero) hext (crossingNode_mem_FP true hx hyp))
  · exact selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw)
      (selectFn_mem_FP (eqFlagFn_mem_FP hy hmax) hext (crossingNode_mem_FP false hx hys))
      (selectFn_mem_FP (eqFlagFn_mem_FP hx hmax) hext (crossingNode_mem_FP true hxs hy))
  · exact selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw)
      (selectFn_mem_FP (eqFlagFn_mem_FP hx hzero) hext (crossingNode_mem_FP false hxp hy))
      (crossingNode_mem_FP true hx hy)

private theorem fromBitsLE_replicate (b : ℕ) :
    Nat.fromBitsLE (List.replicate b false) = 0 ∧
      Nat.fromBitsLE (List.replicate b true) = 2 ^ b - 1 := by
  induction b with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | succ b ih =>
    have hp := Nat.two_pow_pos b
    simp [List.replicate_succ, Nat.fromBitsLE_cons, ih, pow_succ]
    omega

private theorem zeroBits_iff {b x : ℕ} (hx : x < 2 ^ b) :
    Nat.toBitsLE b x = List.replicate b false ↔ x = 0 := by
  constructor
  · intro he
    have h := congrArg Nat.fromBitsLE he
    simpa [Nat.fromBitsLE_toBitsLE hx, (fromBitsLE_replicate b).1] using h
  · intro he
    apply Nat.fromBitsLE_inj_of_length_eq (by simp)
    rw [Nat.fromBitsLE_toBitsLE hx, (fromBitsLE_replicate b).1]
    exact he

private theorem maxBits_iff {b x : ℕ} (hx : x < 2 ^ b) :
    Nat.toBitsLE b x = List.replicate b true ↔ x + 1 = 2 ^ b := by
  constructor
  · intro he
    have h := congrArg Nat.fromBitsLE he
    rw [Nat.fromBitsLE_toBitsLE hx, (fromBitsLE_replicate b).2] at h
    omega
  · intro he
    apply Nat.fromBitsLE_inj_of_length_eq (by simp)
    rw [Nat.fromBitsLE_toBitsLE hx, (fromBitsLE_replicate b).2]
    omega

private theorem succBits_encode {b x : ℕ} (hx : x + 1 < 2 ^ b) :
    gridSuccBits (Nat.toBitsLE b x) = Nat.toBitsLE b (x + 1) := by
  have hx' : x < 2 ^ b := by omega
  apply Nat.fromBitsLE_inj_of_length_eq (by simp)
  rw [gridSuccBits_value_of_lt _ (by simpa [Nat.fromBitsLE_toBitsLE hx'] using hx),
    Nat.fromBitsLE_toBitsLE hx', Nat.fromBitsLE_toBitsLE hx]

private theorem predBits_encode {b x : ℕ} (hx : x < 2 ^ b) (hp : 0 < x) :
    gridPredBits (Nat.toBitsLE b x) = Nat.toBitsLE b (x - 1) := by
  have hx' : x - 1 < 2 ^ b := by omega
  apply Nat.fromBitsLE_inj_of_length_eq (by simp)
  rw [gridPredBits_value_of_pos _ (by simpa [Nat.fromBitsLE_toBitsLE hx] using hp),
    Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hx']

private theorem case_eqFlag (a b yes no : List Bool) :
    caseBit₀ (eqFlag a b) yes no = if a = b then yes else no := by
  rcases eqFlag_flag a b with h | h
  · have he := (eqFlag_eq_true_iff a b).mp h
    rw [h, ite_eq_left he]
    rfl
  · have he : a ≠ b := by
      intro he
      have ht := (eqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [h, he, caseBit₀]

/-- Binary crossing agrees exactly with geometric adjacency on every valid triangle. -/
theorem gridCrossWord_encode (ruler : List Bool) (incoming : Bool) (p : Fin 3)
    (t : GridTriangle) (hv : ValidTriangle (2 ^ ruler.length) t) :
    gridCrossWord ruler incoming p (encodeGridNode ruler.length (some t)) =
      match across (2 ^ ruler.length) t p with
      | none => if incoming then encodeGridNode ruler.length none
          else encodeGridNode ruler.length (some t)
      | some (u, _) => encodeGridNode ruler.length (some u) := by
  rcases t with ⟨x, y, upper⟩
  rcases hv with ⟨hx, hy⟩
  have hxb : gridNodeXBits ruler (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      Nat.toBitsLE ruler.length x := by simp [gridNodeXBits, encodeGridNode]
  have hyb : gridNodeYBits ruler (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      Nat.toBitsLE ruler.length y := by simp [gridNodeYBits, encodeGridNode]
  have hh : gridNodeHalfFlag (encodeGridNode ruler.length (some ⟨x, y, upper⟩)) =
      [upper] := by simp [gridNodeHalfFlag, encodeGridNode, bitAt_eq, bitOf]
  cases upper <;> fin_cases p
  all_goals simp only [gridCrossWord, hxb, hyb, hh]
  all_goals simp [case_eqFlag, zeroBits_iff hx, zeroBits_iff hy,
    maxBits_iff hx, maxBits_iff hy, across]
  all_goals first | rfl | (split_ifs <;> simp_all [crossingNode, gridWidthWord, encodeGridNode])
  all_goals first
    | omega
    | exact succBits_encode (by omega)
    | exact predBits_encode hx (by omega)
    | exact predBits_encode hy (by omega)

end GameTheory.Complexity.Backend
