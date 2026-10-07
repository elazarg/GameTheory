import GameTheoryComplexity.Backend.SpernerGridCodecMachine
import GameTheoryComplexity.Backend.SpernerBinarySteps
import GameTheory.Math.GridSperner

/-! Corner colors are computed on binary coordinate words. One extra coordinate
bit retains boundary increments, and local equality controls enforce the fixed
Sperner boundary before querying the interior-color computation. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner
open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps

/-- Two flags distinguish colors one and two from color zero. -/
def encodeGridColor (c : Fin 3) : List Bool := [decide (c = 1), decide (c = 2)]

/-- Decode any word as a color, giving the first flag priority. -/
def decodeGridColor (word : List Bool) : Fin 3 :=
  if word.headD false then 1 else if word.tail.headD false then 2 else 0

/-- Normalize an arbitrary query result to its canonical two-bit color. -/
def normalizeGridColor (word : List Bool) : List Bool := encodeGridColor (decodeGridColor word)

@[simp] theorem decodeGridColor_encode (c : Fin 3) :
    decodeGridColor (encodeGridColor c) = c := by fin_cases c <;> rfl

/-- Canonicalization of a color result has an actual polynomial-time certificate. -/
theorem normalizeGridColor_mem_FP : normalizeGridColor ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have ht : (fun z : List Bool => bitAt [] z) ∈ FP :=
    CobhamFP_subset_FP (headFlagFn (FP_subset_CobhamFP hid))
  have h := selectFn_mem_FP ht (constFn_mem_FP (encodeGridColor 1))
    (selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hid)
      (constFn_mem_FP (encodeGridColor 2)) (constFn_mem_FP (encodeGridColor 0)))
  have heq (word : List Bool) : normalizeGridColor word =
      caseBit₀ (bitAt [] word) (encodeGridColor 1)
        (caseBit₀ (gridNodeHalfFlag word) (encodeGridColor 2) (encodeGridColor 0)) := by
    cases word with
    | nil => rfl
    | cons first rest =>
      cases first
      · cases rest with
        | nil => rfl
        | cons second rest => cases second <;> rfl
      · rfl
  simpa only [← heq] using h

/-- Interpret an interior query on extended fixed-width coordinate encodings. -/
def gridInteriorColor (b : ℕ) (query : List Bool → List Bool) (x y : ℕ) : Fin 3 :=
  decodeGridColor (query (Nat.toBitsLE (b + 1) x ++ Nat.toBitsLE (b + 1) y))

private def cornerXBits (ruler word : List Bool) (p : Fin 3) : List Bool :=
  let x := gridNodeXBits ruler word ++ [false]
  if p = 0 then x else if p = 1 then gridSuccBits x
  else caseBit₀ (gridNodeHalfFlag word) x (gridSuccBits x)

private def cornerYBits (ruler word : List Bool) (p : Fin 3) : List Bool :=
  let y := gridNodeYBits ruler word ++ [false]
  if p = 0 then y else if p = 1 then
    caseBit₀ (gridNodeHalfFlag word) (gridSuccBits y) y else gridSuccBits y

private def boundaryColorBits (ruler : List Bool) (query : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  let zero := List.replicate ruler.length false ++ [false]
  let limit := List.replicate ruler.length false ++ [true]
  caseBit₀ (eqFlag y zero)
    (caseBit₀ (eqFlag x zero) (encodeGridColor 0) (encodeGridColor 1))
    (caseBit₀ (orBit (eqFlag x limit) (eqFlag y limit)) (encodeGridColor 2)
      (caseBit₀ (eqFlag x zero) (encodeGridColor 0) (normalizeGridColor (query (x ++ y)))))

/-- Compute one canonical corner color from an encoded triangle and coordinate ruler. -/
def gridCornerColor (ruler : List Bool) (query : List Bool → List Bool) (word : List Bool)
    (p : Fin 3) : List Bool :=
  boundaryColorBits ruler query (cornerXBits ruler word p) (cornerYBits ruler word p)

private theorem cornerXBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) (p : Fin 3) :
    (fun z => cornerXBits (ruler z) (word z) p) ∈ FP := by
  have hx := appendFn_mem_FP (gridNodeXBitsFn_mem_FP hr hw) (constFn_mem_FP [false])
  have hs := mem_FP_comp hx gridSuccBits_mem_FP
  have hh := selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw) hx hs
  fin_cases p
  · exact hx
  · exact hs
  · exact hh

private theorem cornerYBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) (p : Fin 3) :
    (fun z => cornerYBits (ruler z) (word z) p) ∈ FP := by
  have hy := appendFn_mem_FP (gridNodeYBitsFn_mem_FP hr hw) (constFn_mem_FP [false])
  have hs := mem_FP_comp hy gridSuccBits_mem_FP
  have hh := selectFn_mem_FP (gridNodeHalfFlagFn_mem_FP hw) hs hy
  fin_cases p
  · exact hy
  · exact hh
  · exact hs

private theorem boundaryColorBitsFn_mem_FP {ruler x y : List Bool → List Bool}
    (hr : ruler ∈ FP) (hx : x ∈ FP) (hy : y ∈ FP)
    (query : List Bool → List Bool → List Bool)
    (hq : (fun z => query z (x z ++ y z)) ∈ FP) :
    (fun z => boundaryColorBits (ruler z) (query z) (x z) (y z)) ∈ FP := by
  have hz : (fun z => List.replicate (ruler z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) hr
  have hzero := appendFn_mem_FP hz (constFn_mem_FP [false])
  have hlimit := appendFn_mem_FP hz (constFn_mem_FP [true])
  have hquery := mem_FP_comp hq normalizeGridColor_mem_FP
  have hxzero := eqFlagFn_mem_FP hx hzero
  have hyzero := eqFlagFn_mem_FP hy hzero
  have hlim := orBitFn_mem_FP (eqFlagFn_mem_FP hx hlimit) (eqFlagFn_mem_FP hy hlimit)
  have h := selectFn_mem_FP hyzero
    (selectFn_mem_FP hxzero (constFn_mem_FP (encodeGridColor 0))
      (constFn_mem_FP (encodeGridColor 1)))
    (selectFn_mem_FP hlim (constFn_mem_FP (encodeGridColor 2))
      (selectFn_mem_FP hxzero (constFn_mem_FP (encodeGridColor 0)) hquery))
  exact h

/-- Corner-color evaluation composes polynomial-time rulers, words and interior queries. -/
theorem gridCornerColorFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) (query : List Bool → List Bool) (hq : query ∈ FP)
    (p : Fin 3) : (fun z => gridCornerColor (ruler z) query (word z) p) ∈ FP :=
  boundaryColorBitsFn_mem_FP hr (cornerXBitsFn_mem_FP hr hw p)
    (cornerYBitsFn_mem_FP hr hw p) (fun _ => query)
      (mem_FP_comp (appendFn_mem_FP (cornerXBitsFn_mem_FP hr hw p)
        (cornerYBitsFn_mem_FP hr hw p)) hq)

/-- Uniform corner evaluation also permits the serialized query seed to vary. -/
theorem gridCornerColorUniformFn_mem_FP (p : Fin 3)
    {ruler seed word : List Bool → List Bool} (hr : ruler ∈ FP) (hs : seed ∈ FP)
    (hw : word ∈ FP) (query : List Bool → List Bool → List Bool)
    (hq : (fun z => query (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => gridCornerColor (ruler z) (query (seed z)) (word z) p) ∈ FP := by
  have hx := cornerXBitsFn_mem_FP hr hw p
  have hy := cornerYBitsFn_mem_FP hr hw p
  have hquery : (fun z => query (seed z)
      (cornerXBits (ruler z) (word z) p ++ cornerYBits (ruler z) (word z) p)) ∈ FP := by
    have h := mem_FP_comp (pairFn_mem_FP hs (appendFn_mem_FP hx hy)) hq
    simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using h
  exact boundaryColorBitsFn_mem_FP hr hx hy (fun z => query (seed z)) hquery

private theorem zeroBits_value (b : ℕ) : Nat.fromBitsLE (List.replicate b false) = 0 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]

private theorem falseSuffix_value (bits : List Bool) :
    Nat.fromBitsLE (bits ++ [false]) = Nat.fromBitsLE bits := by
  simp [Nat.fromBitsLE, List.reverse_append, Nat.fromBits]

private theorem trueSuffix_value (bits : List Bool) :
    Nat.fromBitsLE (bits ++ [true]) = 2 ^ bits.length + Nat.fromBitsLE bits := by
  simp [Nat.fromBitsLE, List.reverse_append, Nat.fromBits]

private theorem extendedBits_encode {b x : ℕ} (hx : x < 2 ^ b) :
    Nat.toBitsLE b x ++ [false] = Nat.toBitsLE (b + 1) x := by
  have hwide : x < 2 ^ (b + 1) := by rw [pow_succ]; omega
  apply Nat.fromBitsLE_inj_of_length_eq (by simp)
  rw [falseSuffix_value, Nat.fromBitsLE_toBitsLE hx, Nat.fromBitsLE_toBitsLE hwide]

private theorem successorExtendedBits_encode {b x : ℕ} (hx : x < 2 ^ b) :
    gridSuccBits (Nat.toBitsLE b x ++ [false]) = Nat.toBitsLE (b + 1) (x + 1) := by
  have hwide : x + 1 < 2 ^ (b + 1) := by
    have hp := Nat.two_pow_pos b
    rw [pow_succ]
    omega
  have hval : Nat.fromBitsLE (Nat.toBitsLE b x ++ [false]) = x := by
    rw [falseSuffix_value, Nat.fromBitsLE_toBitsLE hx]
  apply Nat.fromBitsLE_inj_of_length_eq (by simp)
  rw [gridSuccBits_value_of_lt _ (by simpa only [hval, List.length_append,
    Nat.length_toBitsLE, List.length_singleton] using hwide), hval,
    Nat.fromBitsLE_toBitsLE hwide]

private theorem encoded_eq_iff {width value : ℕ} (hv : value < 2 ^ width)
    (bits : List Bool) (hlen : bits.length = width) :
    Nat.toBitsLE width value = bits ↔ value = Nat.fromBitsLE bits := by
  constructor
  · intro h
    have he := congrArg Nat.fromBitsLE h
    simpa only [Nat.fromBitsLE_toBitsLE hv] using he
  · intro h
    apply Nat.fromBitsLE_inj_of_length_eq (by simp [hlen])
    rw [Nat.fromBitsLE_toBitsLE hv, h]

private theorem cornerXBits_encode (ruler : List Bool) (t : GridTriangle) (p : Fin 3)
    (hv : ValidTriangle (2 ^ ruler.length) t) :
    cornerXBits ruler (encodeGridNode ruler.length (some t)) p =
      Nat.toBitsLE (ruler.length + 1) (corner t p).1 := by
  rcases t with ⟨x, y, upper⟩
  have hx := hv.1
  have hs : gridSuccBits (Nat.toBitsLE (ruler.length + 1) x) =
      Nat.toBitsLE (ruler.length + 1) (x + 1) := by
    rw [← extendedBits_encode hx]
    exact successorExtendedBits_encode hx
  cases upper <;> fin_cases p <;>
    simp [cornerXBits, gridNodeXBits, encodeGridNode, gridNodeHalfFlag, bitAt_eq, bitOf,
      corner, extendedBits_encode hx, hs, caseBit₀]

private theorem cornerYBits_encode (ruler : List Bool) (t : GridTriangle) (p : Fin 3)
    (hv : ValidTriangle (2 ^ ruler.length) t) :
    cornerYBits ruler (encodeGridNode ruler.length (some t)) p =
      Nat.toBitsLE (ruler.length + 1) (corner t p).2 := by
  rcases t with ⟨x, y, upper⟩
  have hy := hv.2
  have hs : gridSuccBits (Nat.toBitsLE (ruler.length + 1) y) =
      Nat.toBitsLE (ruler.length + 1) (y + 1) := by
    rw [← extendedBits_encode hy]
    exact successorExtendedBits_encode hy
  cases upper <;> fin_cases p <;>
    simp [cornerYBits, gridNodeYBits, encodeGridNode, gridNodeHalfFlag, bitAt_eq, bitOf,
      corner, extendedBits_encode hy, hs, caseBit₀]

private theorem eqFlag_decide (a b : List Bool) : eqFlag a b = [decide (a = b)] := by
  rcases eqFlag_flag a b with h | h
  · have he := (eqFlag_eq_true_iff a b).mp h
    rw [h]
    simp only [he, decide_true]
  · have he : a ≠ b := by
      intro he
      have ht := (eqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      cases ht
    simp only [h, he, decide_false]

private theorem boundaryColorBits_encode (ruler : List Bool) (query : List Bool → List Bool)
    (x y : ℕ) (hx : x ≤ 2 ^ ruler.length) (hy : y ≤ 2 ^ ruler.length) :
    boundaryColorBits ruler query (Nat.toBitsLE (ruler.length + 1) x)
        (Nat.toBitsLE (ruler.length + 1) y) =
      encodeGridColor (standardGridColor (2 ^ ruler.length)
        (gridInteriorColor ruler.length query) x y) := by
  have hp := Nat.two_pow_pos ruler.length
  have hne : (0 : ℕ) ≠ 2 ^ ruler.length := by omega
  have hxwide : x < 2 ^ (ruler.length + 1) := by rw [pow_succ]; omega
  have hywide : y < 2 ^ (ruler.length + 1) := by rw [pow_succ]; omega
  have hzero : Nat.fromBitsLE (List.replicate ruler.length false ++ [false]) = 0 := by
    rw [falseSuffix_value, zeroBits_value]
  have hlimit : Nat.fromBitsLE (List.replicate ruler.length false ++ [true]) =
      2 ^ ruler.length := by rw [trueSuffix_value, List.length_replicate, zeroBits_value, add_zero]
  have hxzero := encoded_eq_iff hxwide
    (List.replicate ruler.length false ++ [false]) (by simp)
  have hyzero := encoded_eq_iff hywide
    (List.replicate ruler.length false ++ [false]) (by simp)
  have hxlimit := encoded_eq_iff hxwide
    (List.replicate ruler.length false ++ [true]) (by simp)
  have hylimit := encoded_eq_iff hywide
    (List.replicate ruler.length false ++ [true]) (by simp)
  rw [hzero] at hxzero hyzero
  rw [hlimit] at hxlimit hylimit
  simp only [boundaryColorBits, eqFlag_decide, hxzero, hyzero, hxlimit, hylimit]
  by_cases hy0 : y = 0 <;> by_cases hx0 : x = 0 <;>
    by_cases hxn : x = 2 ^ ruler.length <;> by_cases hyn : y = 2 ^ ruler.length <;>
      simp [hy0, hx0, hxn, hyn, hne, standardGridColor, gridInteriorColor, normalizeGridColor,
        orBit, caseBit₀]

/-- The binary corner computation agrees with the canonical grid coloring at every valid cell. -/
theorem gridCornerColor_encode (ruler : List Bool) (query : List Bool → List Bool)
    (t : GridTriangle) (p : Fin 3) (hv : ValidTriangle (2 ^ ruler.length) t) :
    gridCornerColor ruler query (encodeGridNode ruler.length (some t)) p =
      encodeGridColor (standardGridColor (2 ^ ruler.length)
        (gridInteriorColor ruler.length query) (corner t p).1 (corner t p).2) := by
  rw [gridCornerColor, cornerXBits_encode ruler t p hv, cornerYBits_encode ruler t p hv]
  have hx : (corner t p).1 ≤ 2 ^ ruler.length := by
    rcases t with ⟨x, y, upper⟩
    rcases hv with ⟨hx, hy⟩
    dsimp at hx hy
    cases upper <;> fin_cases p <;> simp [corner] <;> omega
  have hy : (corner t p).2 ≤ 2 ^ ruler.length := by
    rcases t with ⟨x, y, upper⟩
    rcases hv with ⟨hx, hy⟩
    dsimp at hx hy
    cases upper <;> fin_cases p <;> simp [corner] <;> omega
  exact boundaryColorBits_encode ruler query _ _ hx hy

end GameTheory.Complexity.Backend
