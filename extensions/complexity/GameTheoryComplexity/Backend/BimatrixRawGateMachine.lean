import GameTheoryComplexity.Backend.BimatrixRawGate
import GameTheoryComplexity.Backend.CircuitGateLookup
import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
import GameTheoryComplexity.Backend.BinarySignedAddition

/-! Certified signed-coefficient queries for serialized raw gates.
Input negations are inline and both reference contributions are retained when they alias.
Missing bits default to false and missing unary references have length zero. -/
namespace GameTheory.Complexity.Backend.BimatrixRawGateMachine
open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

private def capacityWord (ruler : List Bool) : List Bool :=
  false :: false :: binaryLengthWord ruler

/-- The first absolute-reference ruler in a gate suffix. -/
def firstReference (suffix : List Bool) : List Bool := circuitUnaryPrefix (suffix.drop 3)
/-- The second absolute-reference ruler in a gate suffix. -/
def secondReference (suffix : List Bool) : List Bool :=
  circuitUnaryPrefix (circuitUnaryRest (suffix.drop 3))

private def contribution (dimension row reference negFlag : List Bool) : List Bool :=
  caseBit₀ (andBit (binaryLengthParity row) (lenEqFlag (binaryHalfRuler row) reference))
    (caseBit₀ negFlag (binarySignedNeg (capacityWord dimension)) (capacityWord dimension)) []

/-- Arguments: output-count ruler, serialized first-gate suffix, row-action ruler. -/
def coefficientWord (v : Fin 3 → List Bool) : List Bool :=
  binarySignedAdd
    (binarySignedAdd
      (contribution (v 0) (v 2) (firstReference (v 1)) (bitAt [false] (v 1)))
      (contribution (v 0) (v 2) (secondReference (v 1)) (bitAt [false, false] (v 1))))
    (binarySignedSub
      (binarySignedAdd (caseBit₀ (bitAt [false] (v 1)) [false, false, true] [])
        (caseBit₀ (bitAt [false, false] (v 1)) [false, false, true] []))
      (caseBit₀ (bitAt [] (v 1)) [false, true, true] [false, true]))

/-- Arguments: output-count ruler, circuit code, gate ordinal ruler, row-action ruler. -/
def selectedCoefficientWord (v : Fin 4 → List Bool) : List Bool :=
  coefficientWord ![v 0, circuitGateSuffix (v 1) (v 2), v 3]

private theorem capacityWord_value (ruler : List Bool) :
    binarySignedValue (capacityWord ruler) = 2 * ruler.length := by
  simp only [capacityWord, binarySignedValue, List.headD_cons, Bool.false_eq_true,
    ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem lenEq_value (a b : List Bool) :
    lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]

private theorem contribution_value (dimension row reference : List Bool) (neg : Bool) :
    binarySignedValue (contribution dimension row reference [neg]) =
      (2 * dimension.length : ℤ) *
        ((if neg then -1 else 1) *
          (if row.length / 2 = reference.length ∧ row.length % 2 = 1 then 1 else 0)) := by
  rw [contribution, binaryLengthParity_value, lenEq_value, binaryHalfRuler_length]
  have hz : binarySignedValue [] = 0 := rfl
  by_cases he : row.length / 2 = reference.length <;>
    by_cases ho : row.length % 2 = 1 <;> cases neg <;>
      simp [he, ho, andBit, caseBit₀, binarySignedNeg_value, capacityWord_value, hz]

private theorem twoFlag_value (b : Bool) :
    binarySignedValue (caseBit₀ [b] [false, false, true] []) = if b then 2 else 0 := by
  cases b <;> rfl

private theorem thresholdFlag_value (b : Bool) :
    binarySignedValue (caseBit₀ [b] [false, true, true] [false, true]) =
      if b then 3 else 1 := by
  cases b <;> rfl

/-- Exact integer meaning of every query, including malformed and exhausted gate suffixes. -/
theorem coefficientWord_value (dimension suffix row : List Bool) :
    binarySignedValue (coefficientWord ![dimension, suffix, row]) =
      2 * (dimension.length : ℤ) *
        (((if suffix[1]?.getD false then -1 else 1) *
          (if row.length / 2 = (firstReference suffix).length ∧ row.length % 2 = 1 then 1 else 0)) +
         ((if suffix[2]?.getD false then -1 else 1) *
          (if row.length / 2 = (secondReference suffix).length ∧ row.length % 2 = 1
            then 1 else 0))) +
      (if suffix[1]?.getD false then 2 else 0) +
      (if suffix[2]?.getD false then 2 else 0) - (if suffix[0]?.getD false then 3 else 1) := by
  change binarySignedValue (binarySignedAdd
    (binarySignedAdd (contribution dimension row (firstReference suffix) (bitAt [false] suffix))
      (contribution dimension row (secondReference suffix) (bitAt [false, false] suffix)))
    (binarySignedSub
      (binarySignedAdd (caseBit₀ (bitAt [false] suffix) [false, false, true] [])
        (caseBit₀ (bitAt [false, false] suffix) [false, false, true] []))
      (caseBit₀ (bitAt [] suffix) [false, true, true] [false, true]))) = _
  rw [binarySignedAdd_value, binarySignedAdd_value, binarySignedSub_value, binarySignedAdd_value]
  rw [bitAt_getElem?, bitAt_getElem?, bitAt_getElem?]
  change binarySignedValue (contribution dimension row (firstReference suffix)
      [suffix[1]?.getD false]) +
    binarySignedValue (contribution dimension row (secondReference suffix)
      [suffix[2]?.getD false]) +
    (binarySignedValue (caseBit₀ [suffix[1]?.getD false] [false, false, true] []) +
      binarySignedValue (caseBit₀ [suffix[2]?.getD false] [false, false, true] []) -
      binarySignedValue (caseBit₀ [suffix[0]?.getD false] [false, true, true] [false, true])) = _
  rw [contribution_value, contribution_value, twoFlag_value, twoFlag_value, thresholdFlag_value]
  ring

private theorem capacityWord_cobham :
    Cobham fun v : Fin 1 → List Bool => capacityWord (v 0) :=
  appendFn (Cobham.const [false, false]) binaryLengthWord_cobham

private theorem firstReference_cobham :
    Cobham fun v : Fin 1 → List Bool => firstReference (v 0) :=
  Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 =>
    dropFn (Cobham.const [false, false, false]) (.proj 0)

private theorem secondReference_cobham :
    Cobham fun v : Fin 1 → List Bool => secondReference (v 0) :=
  Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 =>
    Cobham.comp (FP_subset_CobhamFP circuitUnaryRest_mem_FP) fun _ : Fin 1 =>
      dropFn (Cobham.const [false, false, false]) (.proj 0)

private theorem contribution_fn {p : ℕ}
    {dimension row reference negFlag : (Fin p → List Bool) → List Bool}
    (hd : Cobham dimension) (hr : Cobham row) (href : Cobham reference)
    (hn : Cobham negFlag) :
    Cobham fun v => contribution (dimension v) (row v) (reference v) (negFlag v) := by
  have hcap := Cobham.comp capacityWord_cobham fun _ : Fin 1 => hd
  exact Cobham.iteFn
    (Cobham.andFn (Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 => hr)
      (lenEqFlag_mem (Cobham.comp binaryHalfRuler_cobham fun _ : Fin 1 => hr) href))
    (Cobham.iteFn hn (Cobham.comp binarySignedNeg_cobham fun _ : Fin 1 => hcap) hcap)
    Cobham.empty

/-- The first-gate coefficient query has an actual polynomial-time certificate. -/
theorem coefficientWord_cobham : Cobham coefficientWord := by
  have hneg0 : Cobham fun v : Fin 3 → List Bool => bitAt [false] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const [false]) (.proj 1)
  have hneg1 : Cobham fun v : Fin 3 → List Bool => bitAt [false, false] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const [false, false]) (.proj 1)
  have hop : Cobham fun v : Fin 3 → List Bool => bitAt [] (v 1) :=
    Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1)
  have hfirst : Cobham fun v : Fin 3 → List Bool => firstReference (v 1) :=
    Cobham.comp firstReference_cobham fun _ : Fin 1 => .proj 1
  have hsecond : Cobham fun v : Fin 3 → List Bool => secondReference (v 1) :=
    Cobham.comp secondReference_cobham fun _ : Fin 1 => .proj 1
  exact Cobham.comp₂ binarySignedAdd_cobham
    (Cobham.comp₂ binarySignedAdd_cobham
      (contribution_fn (.proj 0) (.proj 2) hfirst hneg0)
      (contribution_fn (.proj 0) (.proj 2) hsecond hneg1))
    (Cobham.comp₂ binarySignedSub_cobham
      (Cobham.comp₂ binarySignedAdd_cobham
        (Cobham.iteFn hneg0 (Cobham.const [false, false, true]) Cobham.empty)
        (Cobham.iteFn hneg1 (Cobham.const [false, false, true]) Cobham.empty))
      (Cobham.iteFn hop (Cobham.const [false, true, true]) (Cobham.const [false, true])))

theorem coefficientWord_mem_FPn : FPn coefficientWord :=
  cobham_iff_FPn.mp coefficientWord_cobham

/-- Selecting an ordinal gate before querying its coefficient remains polynomial time. -/
theorem selectedCoefficientWord_cobham : Cobham selectedCoefficientWord :=
  Cobham.comp₃ coefficientWord_cobham (.proj 0)
    (Cobham.comp₂ circuitGateSuffix_cobham (.proj 1) (.proj 2)) (.proj 3)

theorem selectedCoefficientWord_mem_FPn : FPn selectedCoefficientWord :=
  cobham_iff_FPn.mp selectedCoefficientWord_cobham

private theorem fields_encode (raw : RawGate) (rest : List Bool) :
    (raw.encode ++ rest)[0]?.getD false = raw.opBit ∧
    (raw.encode ++ rest)[1]?.getD false = raw.negated₀ ∧
    (raw.encode ++ rest)[2]?.getD false = raw.negated₁ ∧
    (firstReference (raw.encode ++ rest)).length = raw.input₀ ∧
    (secondReference (raw.encode ++ rest)).length = raw.input₁ := by
  simp only [RawGate.encode, List.append_assoc, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [firstReference, secondReference, List.drop_succ_cons, List.drop_zero]
  rw [circuitUnaryPrefix_encode, circuitUnaryRest_encode, circuitUnaryPrefix_encode]
  simp only [List.length_replicate, and_self]

/-- Canonical gate serialization recovers the exact coefficient factory, retaining aliases. -/
theorem coefficientWord_encode (dimension row : List Bool) (raw : RawGate)
    (href : raw.WellFormedAt dimension.length) (rest : List Bool)
    (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue (coefficientWord ![dimension, raw.encode ++ rest, row]) =
      BimatrixRawGate.coefficients raw href r := by
  rcases href with ⟨h0, h1⟩
  obtain ⟨hop, hn0, hn1, hr0, hr1⟩ := fields_encode raw rest
  rw [coefficientWord_value, hop, hn0, hn1, hr0, hr1]
  change _ = 2 * (dimension.length : ℤ) *
    (((if raw.negated₀ then -1 else 1) *
      (if r = finProdFinEquiv ((⟨raw.input₀, h0⟩ : Fin dimension.length), 1) then 1 else 0)) +
     ((if raw.negated₁ then -1 else 1) *
      (if r = finProdFinEquiv ((⟨raw.input₁, h1⟩ : Fin dimension.length), 1) then 1 else 0))) +
    (if raw.negated₀ then 2 else 0) + (if raw.negated₁ then 2 else 0) -
      BimatrixRawGate.threshold raw
  have he (a : Fin dimension.length) :
      (row.length / 2 = a.val ∧ row.length % 2 = 1) ↔ r = finProdFinEquiv (a, 1) := by
    rw [hr, Fin.ext_iff]
    change (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r.val = 1 + 2 * a.val
    omega
  simp only [he ⟨raw.input₀, h0⟩, he ⟨raw.input₁, h1⟩]
  cases h : raw.op <;>
    simp only [RawGate.opBit, BimatrixRawGate.threshold, h, ite_true,
      Bool.false_eq_true, ite_false]

private theorem select_length (flag x y : List Bool) :
    (caseBit₀ flag x y).length ≤ max x.length y.length := by
  cases flag with
  | nil => exact le_max_right _ _
  | cons b flag => cases b <;> simp [caseBit₀]

private theorem capacityWord_length (dimension : List Bool) :
    (capacityWord dimension).length ≤ dimension.length + 3 := by
  have h := binaryLengthWord_length dimension
  simp only [capacityWord, List.length_cons]
  omega

private theorem contribution_length (dimension row reference negFlag : List Bool) :
    (contribution dimension row reference negFlag).length ≤ dimension.length + 4 := by
  have hn := binarySignedNeg_length (capacityWord dimension)
  have hc := capacityWord_length dimension
  have hs := select_length negFlag (binarySignedNeg (capacityWord dimension))
    (capacityWord dimension)
  have hg := select_length
    (andBit (binaryLengthParity row) (lenEqFlag (binaryHalfRuler row) reference))
    (caseBit₀ negFlag (binarySignedNeg (capacityWord dimension)) (capacityWord dimension)) []
  simp only [List.length_nil, max_zero] at hg
  exact hg.trans (by omega)

/-- Query output length depends only linearly on the output-count ruler. -/
theorem coefficientWord_length (v : Fin 3 → List Bool) :
    (coefficientWord v).length ≤ (v 0).length + 10 := by
  let a := contribution (v 0) (v 2) (firstReference (v 1)) (bitAt [false] (v 1))
  let b := contribution (v 0) (v 2) (secondReference (v 1)) (bitAt [false, false] (v 1))
  let x := caseBit₀ (bitAt [false] (v 1)) [false, false, true] []
  let y := caseBit₀ (bitAt [false, false] (v 1)) [false, false, true] []
  let z := caseBit₀ (bitAt [] (v 1)) [false, true, true] [false, true]
  have ha : a.length ≤ (v 0).length + 4 := contribution_length _ _ _ _
  have hb : b.length ≤ (v 0).length + 4 := contribution_length _ _ _ _
  have hx : x.length ≤ 3 := by
    exact (select_length _ _ _).trans (by decide)
  have hy : y.length ≤ 3 := by
    exact (select_length _ _ _).trans (by decide)
  have hz : z.length ≤ 3 := by
    exact (select_length _ _ _).trans (by decide)
  have hab := binarySignedAdd_length a b
  have hxy := binarySignedAdd_length x y
  have hsub := binarySignedSub_length (binarySignedAdd x y) z
  have h := binarySignedAdd_length (binarySignedAdd a b)
    (binarySignedSub (binarySignedAdd x y) z)
  exact h.trans (by omega)

/-- Gate lookup does not enlarge the coefficient-query output bound. -/
theorem selectedCoefficientWord_length (v : Fin 4 → List Bool) :
    (selectedCoefficientWord v).length ≤ (v 0).length + 10 := coefficientWord_length _

/-- An exhausted canonical lookup uses the same documented total empty-suffix behavior. -/
theorem selectedCoefficientWord_encode_of_length_le (dimension row index : List Bool)
    (raw : RawCircuit) (h : raw.length ≤ index.length) :
    selectedCoefficientWord ![dimension, raw.encode, index, row] =
      coefficientWord ![dimension, [], row] := by
  change coefficientWord ![dimension, circuitGateSuffix raw.encode index, row] = _
  rw [circuitGateSuffix_encode_of_length_le raw index h]

/-- Selecting a canonical gate and querying it agrees with the canonical coefficient factory. -/
theorem selectedCoefficientWord_encode (dimension row index : List Bool) (raw : RawCircuit)
    (hi : index.length < raw.length) (href : raw[index.length].WellFormedAt dimension.length)
    (r : Fin (dimension.length * 2)) (hr : row.length = r.val) :
    binarySignedValue (selectedCoefficientWord ![dimension, raw.encode, index, row]) =
      BimatrixRawGate.coefficients raw[index.length] href r := by
  change binarySignedValue (coefficientWord
    ![dimension, circuitGateSuffix raw.encode index, row]) = _
  rw [circuitGateSuffix_encode, List.drop_eq_getElem_cons hi, List.flatMap_cons]
  exact coefficientWord_encode dimension row raw[index.length] href _ r hr

end GameTheory.Complexity.Backend.BimatrixRawGateMachine
