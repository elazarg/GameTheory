module

public import GameTheoryComplexity.Backend.SpernerGridCodecMachine
public import GameTheoryComplexity.Backend.SpernerBinarySteps
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheory.Math.GridSperner

@[expose] public section

/-! Corner colors are computed on binary coordinate words. One extra coordinate
bit retains boundary increments, and local equality controls enforce the fixed
Sperner boundary before querying the interior-color computation. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner
open Turing.MultiTapeTM ComputableInPolyTime WordOperations Cslib.BitString

/-- Two flags distinguish colors one and two from color zero. -/
def encodeGridColor (c : Fin 3) : List Bool := [decide (c = 1), decide (c = 2)]

/-- Decode any word as a color, giving the first flag priority. -/
def decodeGridColor (word : List Bool) : Fin 3 :=
  if word.headD false then 1 else if word.tail.headD false then 2 else 0

/-- Normalize arbitrary query results to canonical two-bit colors. -/
def normalizeGridColor (word : List Bool) : List Bool := encodeGridColor (decodeGridColor word)

@[simp] theorem decodeGridColor_encode (c : Fin 3) :
    decodeGridColor (encodeGridColor c) = c := by fin_cases c <;> rfl

@[fun_prop] theorem normalizeGridColor_polyTime :
    ComputableInPolyTime normalizeGridColor encBits encBits := by
  have hf : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := ComputableInPolyTime.headD false
  have hs := hf.comp bitsTail
  have h : ComputableInPolyTime (fun word : List Bool =>
      if word.headD false then encodeGridColor 1 else
        if word.tail.headD false then encodeGridColor 2 else encodeGridColor 0)
      encBits encBits := hf.ite (const (encodeGridColor 1))
    (hs.ite (const (encodeGridColor 2)) (const (encodeGridColor 0)))
  have heq (word : List Bool) : normalizeGridColor word =
      if word.headD false then encodeGridColor 1 else
        if word.tail.headD false then encodeGridColor 2 else encodeGridColor 0 := by
    cases word with
    | nil => rfl
    | cons first rest =>
      cases first
      · cases rest with
        | nil => rfl
        | cons second rest => cases second <;> rfl
      · rfl
  rw [show normalizeGridColor = _ from funext heq]
  exact h

/-- Interpret an interior query on extended fixed-width coordinates. -/
def gridInteriorColor (b : ℕ) (query : List Bool → List Bool) (x y : ℕ) : Fin 3 :=
  decodeGridColor (query (lowBits (b + 1) x ++ lowBits (b + 1) y))

private def cornerXBits (ruler word : List Bool) (p : Fin 3) : List Bool :=
  let x := gridNodeXBits ruler word ++ [false]
  if p = 0 then x else if p = 1 then gridSuccBits x
  else select (gridNodeHalfFlag word) x (gridSuccBits x)

private def cornerYBits (ruler word : List Bool) (p : Fin 3) : List Bool :=
  let y := gridNodeYBits ruler word ++ [false]
  if p = 0 then y else if p = 1 then
    select (gridNodeHalfFlag word) (gridSuccBits y) y else gridSuccBits y

/-- Enforce the canonical boundary on extended coordinate words. -/
def boundaryColorBits (ruler : List Bool) (query : List Bool → List Bool)
    (x y : List Bool) : List Bool :=
  let zero := List.replicate ruler.length false ++ [false]
  let limit := List.replicate ruler.length false ++ [true]
  select (eqFlag y zero)
    (select (eqFlag x zero) (encodeGridColor 0) (encodeGridColor 1))
    (select (orFlag (eqFlag x limit) (eqFlag y limit)) (encodeGridColor 2)
      (select (eqFlag x zero) (encodeGridColor 0) (normalizeGridColor (query (x ++ y)))))

/-- Compute one canonical corner color from the triangle word. -/
def gridCornerColor (ruler : List Bool) (query : List Bool → List Bool) (word : List Bool)
    (p : Fin 3) : List Bool :=
  let x := gridNodeXBits ruler word ++ [false]
  let y := gridNodeYBits ruler word ++ [false]
  let cx := if p = 0 then x else if p = 1 then gridSuccBits x
    else select (gridNodeHalfFlag word) x (gridSuccBits x)
  let cy := if p = 0 then y else if p = 1 then
    select (gridNodeHalfFlag word) (gridSuccBits y) y else gridSuccBits y
  boundaryColorBits ruler query cx cy

private theorem select_cert {α : Type} {enc : α ↪ List Bool}
    {flag yes no : α → List Bool}
    (hf : ComputableInPolyTime flag enc encBits)
    (hy : ComputableInPolyTime yes enc encBits) (hn : ComputableInPolyTime no enc encBits) :
    ComputableInPolyTime (fun a => select (flag a) (yes a) (no a)) enc encBits :=
  select_polyTime.comp (hf.prod (hy.prod hn))

private theorem eq_cert {α : Type} {enc : α ↪ List Bool} {x y : α → List Bool}
    (hx : ComputableInPolyTime x enc encBits) (hy : ComputableInPolyTime y enc encBits) :
    ComputableInPolyTime (fun a => eqFlag (x a) (y a)) enc encBits :=
  eqFlag_polyTime.comp (hx.prod hy)

private theorem cornerXBits_polyTime {α : Type} {enc : α ↪ List Bool}
    {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits)
    (p : Fin 3) : ComputableInPolyTime (fun a => cornerXBits (ruler a) (word a) p)
      enc encBits := by
  have hx := bitsAppend (gridNodeXBits_polyTime hr hw) (const [false])
  have hs := gridSuccBits_polyTime.comp hx
  have hh := select_cert (gridNodeHalfFlag_polyTime hw) hx hs
  fin_cases p
  · exact hx
  · exact hs
  · exact hh

private theorem cornerYBits_polyTime {α : Type} {enc : α ↪ List Bool}
    {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits)
    (p : Fin 3) : ComputableInPolyTime (fun a => cornerYBits (ruler a) (word a) p)
      enc encBits := by
  have hy := bitsAppend (gridNodeYBits_polyTime hr hw) (const [false])
  have hs := gridSuccBits_polyTime.comp hy
  have hh := select_cert (gridNodeHalfFlag_polyTime hw) hs hy
  fin_cases p
  · exact hy
  · exact hh
  · exact hs

/-- Boundary enforcement charges the actual query on the supplied words. -/
@[fun_prop] theorem boundaryColorBits_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler x y : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hx : ComputableInPolyTime x enc encBits)
    (hy : ComputableInPolyTime y enc encBits) (query : α → List Bool → List Bool)
    (hq : ComputableInPolyTime (fun a => query a (x a ++ y a)) enc encBits) :
    ComputableInPolyTime (fun a => boundaryColorBits (ruler a) (query a) (x a) (y a))
      enc encBits := by
  have hz := (bitsReplicate false).comp (length_bits.comp hr)
  have hzero := bitsAppend hz (const [false])
  have hlimit := bitsAppend hz (const [true])
  have hquery := normalizeGridColor_polyTime.comp hq
  have hxzero := eq_cert hx hzero
  have hyzero := eq_cert hy hzero
  have hlim := orFlag_polyTime.comp ((eq_cert hx hlimit).prod (eq_cert hy hlimit))
  exact select_cert hyzero (select_cert hxzero (const (encodeGridColor 0))
    (const (encodeGridColor 1))) (select_cert hlim (const (encodeGridColor 2))
      (select_cert hxzero (const (encodeGridColor 0)) hquery))

/-- Corner evaluation charges a uniformly supplied native interior query. -/
@[fun_prop] theorem gridCornerColor_polyTime
    {α : Type} {enc : α ↪ List Bool} {ruler word : α → List Bool}
    (hr : ComputableInPolyTime ruler enc encBits) (hw : ComputableInPolyTime word enc encBits)
    (query : α → List Bool → List Bool)
    (hq : ComputableInPolyTime (fun p : α × List Bool => query p.1 p.2)
      (encPair enc encBits) encBits) (p : Fin 3) :
    ComputableInPolyTime (fun a => gridCornerColor (ruler a) (query a) (word a) p)
      enc encBits := by
  change ComputableInPolyTime (fun a => boundaryColorBits (ruler a) (query a)
    (cornerXBits (ruler a) (word a) p) (cornerYBits (ruler a) (word a) p)) enc encBits
  have hx := cornerXBits_polyTime hr hw p
  have hy := cornerYBits_polyTime hr hw p
  exact boundaryColorBits_polyTime hr hx hy query (hq.comp (id'.prod (bitsAppend hx hy)))

private theorem zeroBits_value (b : ℕ) : lsbValue (List.replicate b false) = 0 :=
  lsbValue_replicate_false b

private theorem falseSuffix_value (bits : List Bool) :
    lsbValue (bits ++ [false]) = lsbValue bits := by
  simp [lsbValue_append, lsbValue]

private theorem trueSuffix_value (bits : List Bool) :
    lsbValue (bits ++ [true]) = 2 ^ bits.length + lsbValue bits := by
  simp [lsbValue_append, lsbValue, Nat.add_comm]

private theorem extendedBits_encode {b x : ℕ} (hx : x < 2 ^ b) :
    lowBits b x ++ [false] = lowBits (b + 1) x := by
  have hwide : x < 2 ^ (b + 1) := by rw [pow_succ]; omega
  apply lsbValue_injective (by simp)
  rw [falseSuffix_value, lsbValue_lowBits hx, lsbValue_lowBits hwide]

private theorem successorExtendedBits_encode {b x : ℕ} (hx : x < 2 ^ b) :
    gridSuccBits (lowBits b x ++ [false]) = lowBits (b + 1) (x + 1) := by
  have hwide : x + 1 < 2 ^ (b + 1) := by
    have hp := Nat.two_pow_pos b
    rw [pow_succ]
    omega
  have hval : lsbValue (lowBits b x ++ [false]) = x := by
    rw [falseSuffix_value, lsbValue_lowBits hx]
  apply lsbValue_injective (by simp)
  rw [gridSuccBits_value_of_lt _ (by simpa only [hval, List.length_append,
    length_lowBits, List.length_singleton] using hwide), hval,
    lsbValue_lowBits hwide]

private theorem encoded_eq_iff {width value : ℕ} (hv : value < 2 ^ width)
    (bits : List Bool) (hlen : bits.length = width) :
    lowBits width value = bits ↔ value = lsbValue bits := by
  constructor
  · intro h
    have he := congrArg lsbValue h
    simpa only [lsbValue_lowBits hv] using he
  · intro h
    apply lsbValue_injective (by simp [hlen])
    rw [lsbValue_lowBits hv, h]

private theorem cornerXBits_encode (ruler : List Bool) (t : GridTriangle) (p : Fin 3)
    (hv : ValidTriangle (2 ^ ruler.length) t) :
    cornerXBits ruler (encodeGridNode ruler.length (some t)) p =
      lowBits (ruler.length + 1) (corner t p).1 := by
  rcases t with ⟨x, y, upper⟩
  have hx := hv.1
  have hs : gridSuccBits (lowBits (ruler.length + 1) x) =
      lowBits (ruler.length + 1) (x + 1) := by
    rw [← extendedBits_encode hx]
    exact successorExtendedBits_encode hx
  cases upper <;> fin_cases p <;>
    simp [cornerXBits, gridNodeXBits, encodeGridNode, gridNodeHalfFlag,
      corner, extendedBits_encode hx, hs, select]

private theorem cornerYBits_encode (ruler : List Bool) (t : GridTriangle) (p : Fin 3)
    (hv : ValidTriangle (2 ^ ruler.length) t) :
    cornerYBits ruler (encodeGridNode ruler.length (some t)) p =
      lowBits (ruler.length + 1) (corner t p).2 := by
  rcases t with ⟨x, y, upper⟩
  have hy := hv.2
  have hs : gridSuccBits (lowBits (ruler.length + 1) y) =
      lowBits (ruler.length + 1) (y + 1) := by
    rw [← extendedBits_encode hy]
    exact successorExtendedBits_encode hy
  cases upper <;> fin_cases p <;>
    simp [cornerYBits, gridNodeYBits, encodeGridNode, gridNodeHalfFlag,
      corner, extendedBits_encode hy, hs, select]

private theorem eqFlag_decide (a b : List Bool) : eqFlag a b = [decide (a = b)] := rfl

/-- Extended coordinate encodings agree with the canonical boundary-corrected coloring. -/
theorem boundaryColorBits_encode (ruler : List Bool) (query : List Bool → List Bool)
    (x y : ℕ) (hx : x ≤ 2 ^ ruler.length) (hy : y ≤ 2 ^ ruler.length) :
    boundaryColorBits ruler query (lowBits (ruler.length + 1) x)
        (lowBits (ruler.length + 1) y) =
      encodeGridColor (standardGridColor (2 ^ ruler.length)
        (gridInteriorColor ruler.length query) x y) := by
  have hp := Nat.two_pow_pos ruler.length
  have hne : (0 : ℕ) ≠ 2 ^ ruler.length := by omega
  have hxwide : x < 2 ^ (ruler.length + 1) := by rw [pow_succ]; omega
  have hywide : y < 2 ^ (ruler.length + 1) := by rw [pow_succ]; omega
  have hzero : lsbValue (List.replicate ruler.length false ++ [false]) = 0 := by
    rw [falseSuffix_value, zeroBits_value]
  have hlimit : lsbValue (List.replicate ruler.length false ++ [true]) =
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
        orFlag, select]

/-- The binary corner computation agrees with the canonical grid coloring at every valid cell. -/
theorem gridCornerColor_encode (ruler : List Bool) (query : List Bool → List Bool)
    (t : GridTriangle) (p : Fin 3) (hv : ValidTriangle (2 ^ ruler.length) t) :
    gridCornerColor ruler query (encodeGridNode ruler.length (some t)) p =
      encodeGridColor (standardGridColor (2 ^ ruler.length)
        (gridInteriorColor ruler.length query) (corner t p).1 (corner t p).2) := by
  change boundaryColorBits ruler query
    (cornerXBits ruler (encodeGridNode ruler.length (some t)) p)
    (cornerYBits ruler (encodeGridNode ruler.length (some t)) p) = _
  rw [cornerXBits_encode ruler t p hv, cornerYBits_encode ruler t p hv]
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
