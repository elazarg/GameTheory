module

public import GameTheoryComplexity.Backend.BimatrixRawGate
public import GameTheoryComplexity.Backend.CircuitGateLookup
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.BinarySignedAddition

@[expose] public section

/-! Signed coefficient queries read the concrete serialized gate fields directly.
Both reference contributions are retained when they alias. Missing bits default
to false, missing unary references have length zero, and signed padding is
preserved even when the represented coefficient is zero. -/

namespace GameTheory.Complexity.Backend.BimatrixRawGateMachine

open Cslib.Circuits Turing.MultiTapeTM

private def capacityWord (ruler : List Bool) : List Bool :=
  false :: false :: binaryLengthWord ruler

/-- The first absolute-reference ruler in a gate suffix. -/
def firstReference (suffix : List Bool) : List Bool := circuitUnaryPrefix (suffix.drop 3)

/-- The second absolute-reference ruler in a gate suffix. -/
def secondReference (suffix : List Bool) : List Bool :=
  circuitUnaryPrefix (circuitUnaryRest (suffix.drop 3))

private def contribution (dimension row reference : List Bool) (neg : Bool) : List Bool :=
  if row.length / 2 = reference.length ∧ row.length % 2 = 1 then
    if neg then binarySignedNeg (capacityWord dimension) else capacityWord dimension
  else []

private def assemble (dimension row left right : List Bool) (op neg₀ neg₁ : Bool) : List Bool :=
  binarySignedAdd
    (binarySignedAdd (contribution dimension row left neg₀) (contribution dimension row right neg₁))
    (binarySignedSub
      (binarySignedAdd (if neg₀ then [false, false, true] else [])
        (if neg₁ then [false, false, true] else []))
      (if op then [false, true, true] else [false, true]))

/-- Query one gate suffix using a dimension ruler and a row-action ruler. -/
def coefficientWord (dimension suffix row : List Bool) : List Bool :=
  let capacity := false :: false :: binaryLengthWord dimension
  let part := fun (reference : List Bool) (neg : Bool) =>
    if row.length / 2 = reference.length ∧ row.length % 2 = 1 then
      if neg then binarySignedNeg capacity else capacity
    else []
  binarySignedAdd
    (binarySignedAdd
      (part (firstReference suffix) (suffix.getD 1 false))
      (part (secondReference suffix) (suffix.getD 2 false)))
    (binarySignedSub
      (binarySignedAdd (if suffix.getD 1 false then [false, false, true] else [])
        (if suffix.getD 2 false then [false, false, true] else []))
      (if suffix.getD 0 false then [false, true, true] else [false, true]))

/-- Add the offset ruler's length to both references before querying a gate. -/
def shiftedCoefficientWord (dimension suffix offset row : List Bool) : List Bool :=
  let capacity := false :: false :: binaryLengthWord dimension
  let part := fun (reference : List Bool) (neg : Bool) =>
    if row.length / 2 = reference.length ∧ row.length % 2 = 1 then
      if neg then binarySignedNeg capacity else capacity
    else []
  binarySignedAdd
    (binarySignedAdd
      (part (offset ++ firstReference suffix) (suffix.getD 1 false))
      (part (offset ++ secondReference suffix) (suffix.getD 2 false)))
    (binarySignedSub
      (binarySignedAdd (if suffix.getD 1 false then [false, false, true] else [])
        (if suffix.getD 2 false then [false, false, true] else []))
      (if suffix.getD 0 false then [false, true, true] else [false, true]))

/-- Select an ordinal gate before querying its signed coefficient. -/
def selectedCoefficientWord (dimension code index row : List Bool) : List Bool :=
  coefficientWord dimension (circuitGateSuffix code index) row

/-- Select and relocate an ordinal gate before querying its signed coefficient. -/
def selectedShiftedCoefficientWord (dimension code index offset row : List Bool) : List Bool :=
  shiftedCoefficientWord dimension (circuitGateSuffix code index) offset row

private theorem capacityWord_value (ruler : List Bool) :
    binarySignedValue (capacityWord ruler) = 2 * ruler.length := by
  change (ofBits (false :: binaryLengthWord ruler) : ℤ) = 2 * ruler.length
  have h : ofBits (false :: binaryLengthWord ruler) = 2 * ruler.length := by
    change Nat.bit false (ofBits (binaryLengthWord ruler)) = 2 * ruler.length
    rw [binaryLengthWord_value, Nat.bit_false_apply]
  exact_mod_cast h

private theorem contribution_value (dimension row reference : List Bool) (neg : Bool) :
    binarySignedValue (contribution dimension row reference neg) =
      (2 * dimension.length : ℤ) *
        ((if neg then -1 else 1) *
          (if row.length / 2 = reference.length ∧ row.length % 2 = 1 then 1 else 0)) := by
  have hz : binarySignedValue [] = 0 := rfl
  by_cases h : row.length / 2 = reference.length ∧ row.length % 2 = 1 <;> cases neg <;>
    simp [contribution, h, binarySignedNeg_value, capacityWord_value, hz]

private theorem constant_values (b : Bool) :
    (binarySignedValue (if b then [false, false, true] else []) = if b then 2 else 0) ∧
      (binarySignedValue (if b then [false, true, true] else [false, true]) =
        if b then 3 else 1) := by
  cases b <;> constructor <;> rfl

private theorem assemble_value (dimension row left right : List Bool) (op neg₀ neg₁ : Bool) :
    binarySignedValue (assemble dimension row left right op neg₀ neg₁) =
      2 * (dimension.length : ℤ) *
        (((if neg₀ then -1 else 1) *
          (if row.length / 2 = left.length ∧ row.length % 2 = 1 then 1 else 0)) +
         ((if neg₁ then -1 else 1) *
          (if row.length / 2 = right.length ∧ row.length % 2 = 1 then 1 else 0))) +
      (if neg₀ then 2 else 0) + (if neg₁ then 2 else 0) - (if op then 3 else 1) := by
  rw [assemble, binarySignedAdd_value, binarySignedAdd_value, binarySignedSub_value,
    binarySignedAdd_value, contribution_value, contribution_value,
    (constant_values neg₀).1, (constant_values neg₁).1, (constant_values op).2]
  ring

/-- Exact meaning of every suffix query, including malformed or exhausted streams. -/
theorem coefficientWord_value (dimension suffix row : List Bool) :
    binarySignedValue (coefficientWord dimension suffix row) =
      2 * (dimension.length : ℤ) *
        (((if suffix.getD 1 false then -1 else 1) *
          (if row.length / 2 = (firstReference suffix).length ∧ row.length % 2 = 1 then 1 else 0)) +
         ((if suffix.getD 2 false then -1 else 1) *
          (if row.length / 2 = (secondReference suffix).length ∧ row.length % 2 = 1 then 1 else 0))) +
      (if suffix.getD 1 false then 2 else 0) + (if suffix.getD 2 false then 2 else 0) -
      (if suffix.getD 0 false then 3 else 1) :=
  assemble_value dimension row (firstReference suffix) (secondReference suffix)
    (suffix.getD 0 false) (suffix.getD 1 false) (suffix.getD 2 false)

/-- Offset rulers shift both references even on malformed or exhausted streams. -/
theorem shiftedCoefficientWord_value (dimension suffix offset row : List Bool) :
    binarySignedValue (shiftedCoefficientWord dimension suffix offset row) =
      2 * (dimension.length : ℤ) *
        (((if suffix.getD 1 false then -1 else 1) *
          (if row.length / 2 = (offset ++ firstReference suffix).length ∧ row.length % 2 = 1
            then 1 else 0)) +
         ((if suffix.getD 2 false then -1 else 1) *
          (if row.length / 2 = (offset ++ secondReference suffix).length ∧ row.length % 2 = 1
            then 1 else 0))) +
      (if suffix.getD 1 false then 2 else 0) + (if suffix.getD 2 false then 2 else 0) -
      (if suffix.getD 0 false then 3 else 1) :=
  assemble_value dimension row (offset ++ firstReference suffix) (offset ++ secondReference suffix)
    (suffix.getD 0 false) (suffix.getD 1 false) (suffix.getD 2 false)

private theorem references_polyTime {Input : Type} {input : Input ↪ List Bool}
    {suffix : Input → List Bool} (hs : ComputableInPolyTime suffix input encBits) :
    ComputableInPolyTime (fun a => firstReference (suffix a)) input encBits ∧
      ComputableInPolyTime (fun a => secondReference (suffix a)) input encBits := by
  have hdrop := ComputableInPolyTime.bitsDropWithInput hs (ComputableInPolyTime.const 3)
  exact ⟨circuitUnaryPrefix_polyTime hdrop,
    circuitUnaryPrefix_polyTime (circuitUnaryRest_polyTime hdrop)⟩

private theorem contribution_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension row reference : Input → List Bool} {neg : Input → Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hr : ComputableInPolyTime row input encBits)
    (href : ComputableInPolyTime reference input encBits)
    (hn : ComputableInPolyTime neg input encBool) :
    ComputableInPolyTime (fun a => contribution (dimension a) (row a) (reference a) (neg a))
      input encBits := by
  have hcap : ComputableInPolyTime (fun a => capacityWord (dimension a)) input encBits :=
    ComputableInPolyTime.bitsCons (.const false)
      (ComputableInPolyTime.bitsCons (.const false) (binaryLengthWord_polyTime.comp hd))
  have hrow := ComputableInPolyTime.length_bits_comp hr
  have hhalf := (ComputableInPolyTime.unary_div_const 2).comp hrow
  have heq := ComputableInPolyTime.decide_eq' hhalf
    (ComputableInPolyTime.length_bits_comp href)
  have hmod := ComputableInPolyTime.unary_mod.comp (hrow.prod (ComputableInPolyTime.const 2))
  have hodd := ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 1)
  exact (ComputableInPolyTime.decide_and heq hodd).ite_decide
    (hn.ite (binarySignedNeg_polyTime hcap) hcap) (ComputableInPolyTime.const [])

private theorem assemble_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension row left right : Input → List Bool} {op neg₀ neg₁ : Input → Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hr : ComputableInPolyTime row input encBits)
    (hl : ComputableInPolyTime left input encBits)
    (hrr : ComputableInPolyTime right input encBits)
    (hop : ComputableInPolyTime op input encBool)
    (hn₀ : ComputableInPolyTime neg₀ input encBool)
    (hn₁ : ComputableInPolyTime neg₁ input encBool) :
    ComputableInPolyTime (fun a =>
      assemble (dimension a) (row a) (left a) (right a) (op a) (neg₀ a) (neg₁ a))
      input encBits :=
  binarySignedAdd_polyTime
    (binarySignedAdd_polyTime (contribution_polyTime hd hr hl hn₀)
      (contribution_polyTime hd hr hrr hn₁))
    (binarySignedSub_polyTime
      (binarySignedAdd_polyTime (hn₀.ite (.const [false, false, true]) (.const []))
        (hn₁.ite (.const [false, false, true]) (.const [])))
      (hop.ite (.const [false, true, true]) (.const [false, true])))

/-- Coefficient queries charge every input producer under its actual encoding. -/
@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension suffix row : Input → List Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hs : ComputableInPolyTime suffix input encBits)
    (hr : ComputableInPolyTime row input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (dimension a) (suffix a) (row a))
      input encBits :=
  assemble_polyTime hd hr (references_polyTime hs).1 (references_polyTime hs).2
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 0) false)
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 1) false)
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 2) false)

/-- Relocated queries also charge the captured offset ruler. -/
@[fun_prop] theorem shiftedCoefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension suffix offset row : Input → List Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hs : ComputableInPolyTime suffix input encBits)
    (ho : ComputableInPolyTime offset input encBits)
    (hr : ComputableInPolyTime row input encBits) :
    ComputableInPolyTime (fun a =>
      shiftedCoefficientWord (dimension a) (suffix a) (offset a) (row a)) input encBits :=
  assemble_polyTime hd hr
    (ComputableInPolyTime.bitsAppend ho (references_polyTime hs).1)
    (ComputableInPolyTime.bitsAppend ho (references_polyTime hs).2)
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 0) false)
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 1) false)
    (ComputableInPolyTime.bitsGetDWithInput hs (.const 2) false)

/-- Ordinal lookup and the following coefficient query compose under the original input encoding. -/
@[fun_prop] theorem selectedCoefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension code index row : Input → List Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hc : ComputableInPolyTime code input encBits)
    (hi : ComputableInPolyTime index input encBits)
    (hr : ComputableInPolyTime row input encBits) :
    ComputableInPolyTime (fun a =>
      selectedCoefficientWord (dimension a) (code a) (index a) (row a)) input encBits :=
  coefficientWord_polyTime hd (circuitGateSuffix_polyTime hc hi) hr

/-- Lookup, relocation, and signed coefficient emission preserve polynomial time. -/
@[fun_prop] theorem selectedShiftedCoefficientWord_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {dimension code index offset row : Input → List Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hc : ComputableInPolyTime code input encBits)
    (hi : ComputableInPolyTime index input encBits)
    (ho : ComputableInPolyTime offset input encBits)
    (hr : ComputableInPolyTime row input encBits) :
    ComputableInPolyTime (fun a =>
      selectedShiftedCoefficientWord (dimension a) (code a) (index a) (offset a) (row a))
      input encBits :=
  shiftedCoefficientWord_polyTime hd (circuitGateSuffix_polyTime hc hi) ho hr

private theorem contribution_length (dimension row reference : List Bool) (neg : Bool) :
    (contribution dimension row reference neg).length ≤ dimension.length + 4 := by
  have hcap : (capacityWord dimension).length ≤ dimension.length + 3 := by
    have h := binaryLengthWord_length dimension
    simp only [capacityWord, List.length_cons]
    omega
  have hn := binarySignedNeg_length (capacityWord dimension)
  unfold contribution
  split
  · split
    · exact hn.trans (by omega)
    · exact hcap.trans (by omega)
  · simp

private theorem assemble_length (dimension row left right : List Bool) (op neg₀ neg₁ : Bool) :
    (assemble dimension row left right op neg₀ neg₁).length ≤ dimension.length + 10 := by
  let a := contribution dimension row left neg₀
  let b := contribution dimension row right neg₁
  let x : List Bool := if neg₀ then [false, false, true] else []
  let y : List Bool := if neg₁ then [false, false, true] else []
  let z : List Bool := if op then [false, true, true] else [false, true]
  have ha : a.length ≤ dimension.length + 4 := contribution_length _ _ _ _
  have hb : b.length ≤ dimension.length + 4 := contribution_length _ _ _ _
  have hx : x.length ≤ 3 := by cases neg₀ <;> decide
  have hy : y.length ≤ 3 := by cases neg₁ <;> decide
  have hz : z.length ≤ 3 := by cases op <;> decide
  have hab := binarySignedAdd_length a b
  have hxy := binarySignedAdd_length x y
  have hsub := binarySignedSub_length (binarySignedAdd x y) z
  have h := binarySignedAdd_length (binarySignedAdd a b)
    (binarySignedSub (binarySignedAdd x y) z)
  exact h.trans (by omega)

/-- Query outputs grow only linearly in the dimension ruler, on every input. -/
theorem coefficientWord_length (dimension suffix row : List Bool) :
    (coefficientWord dimension suffix row).length ≤ dimension.length + 10 :=
  assemble_length dimension row (firstReference suffix) (secondReference suffix)
    (suffix.getD 0 false) (suffix.getD 1 false) (suffix.getD 2 false)

/-- Relocation retains the same unconditional signed-output length bound. -/
theorem shiftedCoefficientWord_length (dimension suffix offset row : List Bool) :
    (shiftedCoefficientWord dimension suffix offset row).length ≤ dimension.length + 10 :=
  assemble_length dimension row (offset ++ firstReference suffix) (offset ++ secondReference suffix)
    (suffix.getD 0 false) (suffix.getD 1 false) (suffix.getD 2 false)

/-- Ordinal selection does not enlarge the signed-output bound. -/
theorem selectedCoefficientWord_length (dimension code index row : List Bool) :
    (selectedCoefficientWord dimension code index row).length ≤ dimension.length + 10 :=
  coefficientWord_length dimension _ row

/-- Selection and relocation retain the dimension-only signed-output bound. -/
theorem selectedShiftedCoefficientWord_length (dimension code index offset row : List Bool) :
    (selectedShiftedCoefficientWord dimension code index offset row).length ≤ dimension.length + 10 :=
  shiftedCoefficientWord_length dimension _ offset row

private theorem fields_encode (op : CircuitFormat.signature.Op) (left right : ℕ)
    (rest : List Bool) :
    (CircuitFormat.encodeGate op left right ++ rest).getD 0 false = op.1 ∧
    (CircuitFormat.encodeGate op left right ++ rest).getD 1 false = op.2.1 ∧
    (CircuitFormat.encodeGate op left right ++ rest).getD 2 false = op.2.2 ∧
    (firstReference (CircuitFormat.encodeGate op left right ++ rest)).length = left ∧
    (secondReference (CircuitFormat.encodeGate op left right ++ rest)).length = right := by
  simp only [CircuitFormat.encodeGate, List.append_assoc, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ]
  simp only [firstReference, secondReference, List.drop_succ_cons, List.drop_zero]
  rw [circuitUnaryPrefix_encode, circuitUnaryRest_encode, circuitUnaryPrefix_encode]
  simp only [List.length_replicate, and_self]

/-- A canonical serialized native gate recovers its exact comparator coefficients. -/
theorem coefficientWord_encode (dimension row : List Bool)
    (raw : CircuitFormat.signature.Op × List ℕ)
    (href : Program.IsCodeFrom CircuitFormat.signature dimension.length 0 [raw])
    (rest : List Bool) (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue (coefficientWord dimension
      (CircuitFormat.encodeGate raw.1 (raw.2.getD 0 0) (raw.2.getD 1 0) ++ rest) row) =
      BimatrixRawGate.coefficients raw href r := by
  obtain ⟨hop, hn₀, hn₁, hr₀, hr₁⟩ :=
    fields_encode raw.1 (raw.2.getD 0 0) (raw.2.getD 1 0) rest
  rw [coefficientWord_value, hop, hn₀, hn₁, hr₀, hr₁]
  have he (a : Fin dimension.length) :
      (row.length / 2 = a.val ∧ row.length % 2 = 1) ↔
        r = finProdFinEquiv (a, 1) := by
    rw [hr, Fin.ext_iff]
    change (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r.val = 1 + 2 * a.val
    omega
  dsimp only [BimatrixRawGate.coefficients, BimatrixRawGate.threshold]
  simp only [he ⟨raw.2.getD 0 0, BimatrixRawGate.reference_lt raw href 0⟩,
    he ⟨raw.2.getD 1 0, BimatrixRawGate.reference_lt raw href 1⟩]

/-- Relocating the serialized references recovers the exact relocated native gate. -/
theorem shiftedCoefficientWord_encode (dimension row offset : List Bool)
    (raw : CircuitFormat.signature.Op × List ℕ)
    (href : Program.IsCodeFrom CircuitFormat.signature dimension.length 0
      [(raw.1, raw.2.map (offset.length + ·))])
    (rest : List Bool) (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue (shiftedCoefficientWord dimension
      (CircuitFormat.encodeGate raw.1 (raw.2.getD 0 0) (raw.2.getD 1 0) ++ rest) offset row) =
      BimatrixRawGate.coefficients (raw.1, raw.2.map (offset.length + ·)) href r := by
  rcases raw with ⟨op, args⟩
  have hargs : args.length = 2 := by simpa only [List.length_map] using href.1.1
  obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hargs
  change binarySignedValue (shiftedCoefficientWord dimension
    (CircuitFormat.encodeGate op left right ++ rest) offset row) =
    BimatrixRawGate.coefficients (op, [offset.length + left, offset.length + right]) href r
  have he : binarySignedValue (shiftedCoefficientWord dimension
      (CircuitFormat.encodeGate op left right ++ rest) offset row) =
      binarySignedValue (coefficientWord dimension
        (CircuitFormat.encodeGate op (offset.length + left) (offset.length + right)) row) := by
    obtain ⟨hop, hn₀, hn₁, hr₀, hr₁⟩ := fields_encode op left right rest
    obtain ⟨hop', hn₀', hn₁', hr₀', hr₁'⟩ :=
      fields_encode op (offset.length + left) (offset.length + right) []
    rw [List.append_nil] at hop' hn₀' hn₁' hr₀' hr₁'
    rw [shiftedCoefficientWord_value, coefficientWord_value, hop, hn₀, hn₁, hop', hn₀', hn₁']
    simp only [List.length_append, hr₀, hr₁, hr₀', hr₁']
  rw [he]
  simpa only [List.append_nil, List.getD_cons_zero, List.getD_cons_succ] using
    coefficientWord_encode dimension row (op, [offset.length + left, offset.length + right])
      href [] r hr

/-- Native gate selection preserves the canonical coefficient factory and all aliases. -/
theorem selectedCoefficientWord_encode (dimension row index : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2)
    (hi : index.length < gates.length)
    (href : Program.IsCodeFrom CircuitFormat.signature dimension.length 0 [gates[index.length]])
    (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue (selectedCoefficientWord dimension (CircuitFormat.encode gates) index row) =
      BimatrixRawGate.coefficients gates[index.length] href r := by
  change binarySignedValue (coefficientWord dimension
    (circuitGateSuffix (CircuitFormat.encode gates) index) row) = _
  rw [circuitGateSuffix_encode gates harity index, List.drop_eq_getElem_cons hi, List.flatMap_cons]
  exact coefficientWord_encode dimension row gates[index.length] href _ r hr

/-- Selecting and relocating a gate preserves its exact native comparator coefficients. -/
theorem selectedShiftedCoefficientWord_encode (dimension row index offset : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2)
    (hi : index.length < gates.length)
    (href : Program.IsCodeFrom CircuitFormat.signature dimension.length 0
      [(gates[index.length].1, gates[index.length].2.map (offset.length + ·))])
    (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue
      (selectedShiftedCoefficientWord dimension (CircuitFormat.encode gates) index offset row) =
      BimatrixRawGate.coefficients
        (gates[index.length].1, gates[index.length].2.map (offset.length + ·)) href r := by
  change binarySignedValue (shiftedCoefficientWord dimension
    (circuitGateSuffix (CircuitFormat.encode gates) index) offset row) = _
  rw [circuitGateSuffix_encode gates harity index, List.drop_eq_getElem_cons hi, List.flatMap_cons]
  exact shiftedCoefficientWord_encode dimension row offset gates[index.length] href _ r hr

/-- Exhausted selection uses the same total empty-suffix query as every other input. -/
theorem selectedCoefficientWord_encode_of_length_le (dimension row index : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) (h : gates.length ≤ index.length) :
    selectedCoefficientWord dimension (CircuitFormat.encode gates) index row =
      coefficientWord dimension [] row := by
  unfold selectedCoefficientWord
  rw [circuitGateSuffix_encode_of_length_le gates harity index h]

/-- Exhausted relocated selection retains its total empty-suffix behavior. -/
theorem selectedShiftedCoefficientWord_encode_of_length_le (dimension row index offset : List Bool)
    (gates : List (CircuitFormat.signature.Op × List ℕ))
    (harity : ∀ gate ∈ gates, gate.2.length = 2) (h : gates.length ≤ index.length) :
    selectedShiftedCoefficientWord dimension (CircuitFormat.encode gates) index offset row =
      shiftedCoefficientWord dimension [] offset row := by
  unfold selectedShiftedCoefficientWord
  rw [circuitGateSuffix_encode_of_length_le gates harity index h]

end GameTheory.Complexity.Backend.BimatrixRawGateMachine
