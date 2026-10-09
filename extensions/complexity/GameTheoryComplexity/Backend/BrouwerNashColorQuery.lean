import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BrouwerNashProgram
import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BinaryUnaryEncoding
import GameTheoryComplexity.Backend.BinaryIndexedLookup
import GameTheoryComplexity.Backend.BinarySignedFiniteSum
import GameTheoryComplexity.Backend.BimatrixRawGateMachine
/-!
# Executable coefficient and kind queries for corner color circuits

The query scans copied coordinate wires and relocated raw gates in the canonical
Brouwer game program. Fixed sample and corner families are composed explicitly;
variable gate and digit ordinals use length-controlled indexed lookup.
-/

namespace GameTheory.Complexity.Backend.BrouwerNashColorQuery
open _root_.Complexity _root_.Complexity.Cobham
open BrouwerNashLayout BrouwerNashProgram
private def scale (n : ℕ) (r : List Bool) := smash r (List.replicate n true)
private def headers (v : Fin 4 → List Bool) : Fin 3 → List Bool := ![v 1, v 2, v 3]
private def depth (v : Fin 4 → List Bool) := BrouwerNashHeaders.sourceDepthRuler (headers v)
private def base (t : Fin 41) (v : Fin 4 → List Bool) :=
  BrouwerNashHeaders.globalRuler (headers v) ++
    scale t.val (BrouwerNashHeaders.sampleRuler (headers v))
/-- Absolute source wire for a copied corner digit; arguments are digit ordinal and headers. -/
def cornerBitRuler (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (v : Fin 4 → List Bool) : List Bool :=
  let b := depth v
  let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3
  if upper then
    caseBit₀ (lenEqFlag (v 0) b)
      (caseBit₀ (lenEqFlag b []) (List.replicate 2 false)
        (base t v ++ List.replicate 2 false ++ scale 4 b ++ scale (4 * axis.val) b ++
          scale 4 b.tail ++ List.replicate 3 false))
      (base t v ++ List.replicate 2 false ++ scale 4 b ++ scale (4 * axis.val) b ++
        scale 4 (v 0) ++ List.replicate 2 false)
  else
    caseBit₀ (lenEqFlag (v 0) b) (List.replicate 3 false)
      (base t v ++ List.replicate 2 false ++ scale (2 * axis.val) b ++
        scale 2 ((b.drop (v 0).length).tail))
private theorem scale_cobham {a : ℕ} (n : ℕ) {f : (Fin a → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => scale n (f v) :=
  (Cobham.comp₂ .smash hf (.const (List.replicate n true))).of_eq fun _ => rfl
private theorem header_cobham {f : (Fin 3 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v : Fin 4 → List Bool => f (headers v) :=
  (Cobham.comp hf (fun i => .proj i.succ)).of_eq fun v => by
    congr 1
    ext i
    fin_cases i <;> rfl
private theorem depth_cobham : Cobham depth :=
  header_cobham BrouwerNashHeaders.sourceDepthRuler_cobham
private theorem base_cobham (t : Fin 41) : Cobham (base t) :=
  .appendFn (header_cobham BrouwerNashHeaders.globalRuler_cobham)
    (scale_cobham _ (header_cobham BrouwerNashHeaders.sampleRuler_cobham))
theorem cornerBitRuler_cobham (t : Fin 41) (corner : Fin 4) (axis : Fin 2) :
    Cobham (cornerBitRuler t corner axis) := by
  unfold cornerBitRuler
  dsimp only
  by_cases hu : (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3)
  · simp only [hu, ite_true]
    exact .iteFn (lenEqFlag_mem (.proj 0) depth_cobham)
      (.iteFn (lenEqFlag_mem depth_cobham (.const [])) (.const _)
        (.appendFn (.appendFn (.appendFn (.appendFn (.appendFn (base_cobham t)
          (.const _)) (scale_cobham _ depth_cobham)) (scale_cobham _ depth_cobham))
          (scale_cobham _ (.tailFn depth_cobham))) (.const _)))
      (.appendFn (.appendFn (.appendFn (.appendFn (.appendFn (base_cobham t)
        (.const _)) (scale_cobham _ depth_cobham)) (scale_cobham _ depth_cobham))
        (scale_cobham _ (.proj 0))) (.const _))
  · simp only [hu, ite_false]
    exact .iteFn (lenEqFlag_mem (.proj 0) depth_cobham) (.const _)
      (.appendFn (.appendFn (.appendFn (base_cobham t) (.const _))
        (scale_cobham _ depth_cobham))
        (scale_cobham _ (.tailFn (.dropFn (.proj 0) depth_cobham))))
private theorem depth_length (v : Fin 4 → List Bool) :
    (depth v).length = (pairFst (v 1)).length := rfl
private theorem base_length (t : Fin 41) (v : Fin 4 → List Bool) :
    (base t v).length = sampleBase (pairFst (v 1)).length
      (circuitUnaryPrefix (v 2)).length (circuitUnaryPrefix (v 3)).length t := by
  simp only [base, List.length_append, scale, smash_length, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    headers, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    sampleBase, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  ring
private theorem flagCase_length (x y a b : List Bool) :
    (caseBit₀ (lenEqFlag x y) a b).length = if x.length = y.length then a.length else b.length := by
  rcases lenEqFlag_flag x y with he | he
  · rw [he]
    simp only [caseBit₀, (lenEqFlag_eq_true_iff x y).mp he, ite_true, Bool.cond_true]
  · have hn : x.length ≠ y.length := by
      intro h
      have ht := (lenEqFlag_eq_true_iff x y).mpr h
      rw [he] at ht
      contradiction
    simp only [he, caseBit₀, hn, ite_false, Bool.cond_false]
private theorem cornerBitRuler_length_formula (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (v : Fin 4 → List Bool) :
    let b := (pairFst (v 1)).length
    let ell₀ := (circuitUnaryPrefix (v 2)).length
    let ell₁ := (circuitUnaryPrefix (v 3)).length
    let j := (v 0).length
    let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
      else corner.val = 1 ∨ corner.val = 3
    (cornerBitRuler t corner axis v).length =
      if upper then
        if j = b then if b = 0 then one
          else sampleBase b ell₀ ell₁ t + increment b axis (b - 1) 3
        else sampleBase b ell₀ ell₁ t + increment b axis j 2
      else if j = b then zero
        else sampleBase b ell₀ ell₁ t + primaryBit b axis j := by
  dsimp only
  unfold cornerBitRuler
  dsimp only
  by_cases hu : (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3)
  · simp only [hu, ite_true, flagCase_length, depth_length]
    by_cases hj : (v 0).length = (pairFst (v 1)).length
    · simp only [hj, ite_true, List.length_nil]
      by_cases hb : (pairFst (v 1)).length = 0
      · simp only [hb, ite_true, List.length_replicate, one]
      · simp only [hb, ite_false, List.length_append, List.length_replicate,
          scale, smash_length, List.length_tail, depth_length, base_length,
          increment, incrementBase, Nat.mul_comm, Nat.mul_assoc]
        omega
    · simp only [hj, ite_false, List.length_append, List.length_replicate,
        scale, smash_length, depth_length, base_length, increment, incrementBase,
        Nat.mul_comm, Nat.mul_assoc]
      omega
  · simp only [hu, ite_false, flagCase_length, depth_length,
      List.length_append, List.length_replicate, scale, smash_length,
      List.length_tail, List.length_drop, depth_length, base_length, primaryBit, digit, zero,
      Nat.mul_comm, Nat.mul_assoc]
    split <;> omega
/-- The copied source ruler is the exact canonical corner reference on allocated digits. -/
theorem cornerBitRuler_length (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (v : Fin 4 → List Bool) (hj : (v 0).length ≤ (pairFst (v 1)).length) :
    (cornerBitRuler t corner axis v).length =
      (cornerBit (pairFst (v 1)).length (circuitUnaryPrefix (v 2)).length
        (circuitUnaryPrefix (v 3)).length t corner axis (v 0).length).val := by
  let b := (pairFst (v 1)).length
  let e₀ := (circuitUnaryPrefix (v 2)).length
  let e₁ := (circuitUnaryPrefix (v 3)).length
  let j := (v 0).length
  have hjb : j ≤ b := hj
  rw [cornerBitRuler_length_formula]
  change (if (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
      else corner.val = 1 ∨ corner.val = 3) then
    if j = b then if b = 0 then one else sampleBase b e₀ e₁ t + increment b axis (b - 1) 3
    else sampleBase b e₀ e₁ t + increment b axis j 2
    else if j = b then zero else sampleBase b e₀ e₁ t + primaryBit b axis j) =
      (cornerBit b e₀ e₁ t corner axis j).val
  unfold cornerBit
  by_cases hu : (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3)
  · simp only [hu, ite_true]
    by_cases he : j = b
    · simp only [he, ite_true]
      by_cases hb : b = 0
      · simp only [hb, ite_true, slot_val _ _ _ _ (one_lt_dimension _ _ _)]
      · simp only [hb, ite_false, sampleRef]
        exact (slot_val _ _ _ _ (sample_lt_dimension _ _ _ t _
          (increment_lt_sampleWidth b e₀ e₁ axis (b - 1) (by omega) 3))).symm
    · simp only [he, ite_false, sampleRef]
      exact (slot_val _ _ _ _ (sample_lt_dimension _ _ _ t _
        (increment_lt_sampleWidth b e₀ e₁ axis j (by omega) 2))).symm
  · simp only [hu, ite_false]
    by_cases he : j = b
    · simp only [he, ite_true]
      have hz : zero < dimension b e₀ e₁ := by
        have h := one_lt_dimension b e₀ e₁
        unfold zero one dimension units globalCount precision at *
        omega
      exact (slot_val _ _ _ _ hz).symm
    · simp only [he, ite_false, sampleRef]
      have hl : primaryBit b axis j < sampleWidth b e₀ e₁ := by
        have ha := axis.isLt
        dsimp [primaryBit, digit, sampleWidth, cornerWidth, arity]
        have hmul : 2 * b * axis.val ≤ 2 * b := by
          simpa using Nat.mul_le_mul_left (2 * b) (show axis.val ≤ 1 by omega)
        omega
      exact (slot_val _ _ _ _ (sample_lt_dimension _ _ _ t _ hl)).symm
private def queryHeaders (v : Fin 5 → List Bool) : Fin 3 → List Bool := ![v 2, v 3, v 4]
private theorem queryHeader_cobham {f : (Fin 3 → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v : Fin 5 → List Bool => f (queryHeaders v) :=
  (Cobham.comp hf (fun i => .proj i.succ.succ)).of_eq fun v => by
    congr 1
    ext i
    fin_cases i <;> rfl
private theorem tail_cobham {a : ℕ} {f : (Fin a → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v : Fin (a + 1) → List Bool => f (Fin.tail v) :=
  Cobham.comp hf fun i => .proj i.succ
/-- Absolute copied-input offset for one compiled corner-color flag. -/
def inputRuler (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 3 → List Bool) : List Bool :=
  BrouwerNashHeaders.globalRuler v ++ scale t.val (BrouwerNashHeaders.sampleRuler v) ++
    List.replicate 10 false ++ scale 12 (BrouwerNashHeaders.sourceDepthRuler v) ++
    scale corner.val (BrouwerNashHeaders.cornerRuler v) ++
    (if flag.val = 0 then [] else BrouwerNashHeaders.arityRuler v ++ circuitUnaryPrefix (v 1))
theorem inputRuler_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (inputRuler t corner flag) := by
  unfold inputRuler
  apply Cobham.appendFn
  · exact .appendFn (.appendFn (.appendFn
      (.appendFn BrouwerNashHeaders.globalRuler_cobham
        (scale_cobham _ BrouwerNashHeaders.sampleRuler_cobham)) (.const _))
      (scale_cobham _ BrouwerNashHeaders.sourceDepthRuler_cobham))
      (scale_cobham _ BrouwerNashHeaders.cornerRuler_cobham)
  · by_cases h : flag.val = 0
    · simp only [h, ite_true]
      exact .const []
    · simp only [h, ite_false]
      exact .appendFn BrouwerNashHeaders.arityRuler_cobham
        (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP) fun _ : Fin 1 => .proj 1)
@[simp] theorem inputRuler_length (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 3 → List Bool) :
    (inputRuler t corner flag v).length =
      sampleBase (pairFst (v 0)).length (circuitUnaryPrefix (v 1)).length
        (circuitUnaryPrefix (v 2)).length t +
      colorInput (pairFst (v 0)).length (circuitUnaryPrefix (v 1)).length
        (circuitUnaryPrefix (v 2)).length corner flag := by
  simp only [inputRuler, List.length_append, scale, smash_length, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    BrouwerNashHeaders.cornerRuler_length, BrouwerNashHeaders.sourceDepthRuler_length,
    sampleBase, colorInput, colorBase, weightBase]
  split <;> simp only [List.length_nil, List.length_append,
    BrouwerNashHeaders.arityRuler_length] <;> ring
private def rawCode (flag : Fin 2) (v : Fin 5 → List Bool) : List Bool :=
  if flag.val = 0 then v 3 else v 4
private theorem rawCode_cobham (flag : Fin 2) : Cobham (rawCode flag) := by
  unfold rawCode
  by_cases h : flag.val = 0
  · simp only [h, ite_true]
    exact .proj 3
  · simp only [h, ite_false]
    exact .proj 4
private def rawTest (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 6 → List Bool) : List Bool :=
  lenEqFlag (v 1) (inputRuler t corner flag (queryHeaders (Fin.tail v)) ++
    BrouwerNashHeaders.arityRuler (queryHeaders (Fin.tail v)) ++ v 0)
private def rawTerm (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 6 → List Bool) : List Bool :=
  BimatrixRawGateMachine.selectedShiftedCoefficientWord
    ![BrouwerNashHeaders.dimensionRuler (queryHeaders (Fin.tail v)),
      rawCode flag (Fin.tail v), v 0, inputRuler t corner flag (queryHeaders (Fin.tail v)), v 2]
private theorem rawTest_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (rawTest t corner flag) :=
  lenEqFlag_mem (.proj 1) (.appendFn
    (.appendFn (tail_cobham (queryHeader_cobham (inputRuler_cobham t corner flag)))
      (tail_cobham (queryHeader_cobham BrouwerNashHeaders.arityRuler_cobham))) (.proj 0))
private theorem rawTerm_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (rawTerm t corner flag) := by
  let gs : Fin 5 → (Fin 6 → List Bool) → List Bool := Fin.cases
    (fun v => BrouwerNashHeaders.dimensionRuler (queryHeaders (Fin.tail v)))
    (Fin.cases (fun v => rawCode flag (Fin.tail v))
      (Fin.cases (fun v => v 0)
        (Fin.cases (fun v => inputRuler t corner flag (queryHeaders (Fin.tail v)))
          (fun _ v => v 2))))
  have hd : Cobham (fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.dimensionRuler (queryHeaders (Fin.tail v))) :=
    tail_cobham (queryHeader_cobham BrouwerNashHeaders.dimensionRuler_cobham)
  have hr : Cobham (fun v : Fin 6 → List Bool => rawCode flag (Fin.tail v)) :=
    tail_cobham (rawCode_cobham flag)
  have hi : Cobham (fun v : Fin 6 → List Bool =>
      inputRuler t corner flag (queryHeaders (Fin.tail v))) :=
    tail_cobham (queryHeader_cobham (inputRuler_cobham t corner flag))
  have h := Cobham.comp (gs := gs)
    BimatrixRawGateMachine.selectedShiftedCoefficientWord_cobham (by
      intro i
      cases i using Fin.cases
      · simpa only [gs, Fin.cases_zero] using hd
      · rename_i i
        cases i using Fin.cases
        · simpa only [gs, Fin.cases_zero, Fin.cases_succ] using hr
        · rename_i i
          cases i using Fin.cases
          · exact .proj 0
          · rename_i i
            cases i using Fin.cases
            · simpa only [gs, Fin.cases_zero, Fin.cases_succ] using hi
            · exact .proj 2)
  unfold rawTerm
  apply h.of_eq
  intro v
  congr 1
  ext i
  fin_cases i <;> rfl
/-- Exact bounded lookup of a relocated compiled color-gate coefficient. -/
def rawCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) : List Bool :=
  binaryIndexedLookup (rawTest t corner flag) (rawTerm t corner flag)
    (circuitUnaryPrefix (rawCode flag v)) (BrouwerNashHeaders.widthRuler (queryHeaders v)) v
theorem rawCoefficientWord_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (rawCoefficientWord t corner flag) := by
  let gs : Fin 7 → (Fin 5 → List Bool) → List Bool := Fin.cases
    (fun v => circuitUnaryPrefix (rawCode flag v))
    (Fin.cases (fun v => BrouwerNashHeaders.widthRuler (queryHeaders v)) (fun j v => v j))
  have h := Cobham.comp (gs := gs)
    (binaryIndexedLookup_cobham (rawTest_cobham t corner flag) (rawTerm_cobham t corner flag))
    (by
      intro i
      cases i using Fin.cases
      · change Cobham (fun v : Fin 5 → List Bool => circuitUnaryPrefix (rawCode flag v))
        exact Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP)
          (fun _ : Fin 1 => rawCode_cobham flag)
      · rename_i i
        cases i using Fin.cases
        · change Cobham (fun v : Fin 5 → List Bool =>
            BrouwerNashHeaders.widthRuler (queryHeaders v))
          exact queryHeader_cobham BrouwerNashHeaders.widthRuler_cobham
        · rename_i j
          change Cobham (fun v : Fin 5 → List Bool => v j)
          exact .proj j)
  unfold rawCoefficientWord
  exact h.of_eq fun _ => rfl
private theorem lenEqFlag_value (x y : List Bool) :
    lenEqFlag x y = [decide (x.length = y.length)] := by
  rcases lenEqFlag_flag x y with h | h
  · simp only [h, (lenEqFlag_eq_true_iff x y).mp h, decide_true]
  · have hn : x.length ≠ y.length := by
      intro he
      rw [(lenEqFlag_eq_true_iff x y).mpr he] at h
      contradiction
    simp only [h, hn, decide_false]
private theorem rawTest_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (r : List Bool) :
    rawTest t corner flag (Fin.cons r v) = [decide ((v 0).length =
      (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + r.length)] := by
  simp only [rawTest, Fin.tail_cons, lenEqFlag_value,
    List.length_append, Fin.cons_zero]
  rfl
/-- Every nonmatching output returns zero, including malformed serialized circuits. -/
theorem rawCoefficientWord_value_zero (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool)
    (hno : ∀ i < (circuitUnaryPrefix (rawCode flag v)).length,
      (v 0).length ≠ (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + i) :
    binarySignedValue (rawCoefficientWord t corner flag v) = 0 := by
  apply binaryIndexedLookup_value_zero
    (rawTest t corner flag) (rawTerm t corner flag) _ _ v
  intro ord hi
  rw [rawTest_value]
  simp only [hno ord.length hi, decide_false]
/-- At an allocated serialized gate, the bounded query returns its canonical coefficient. -/
theorem rawCoefficientWord_value_at (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (hcode : rawCode flag v = raw.encode) (j : Fin raw.length)
    (ho : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val)
    (href : (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length).WellFormedAt
      (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length)
    (r : Fin ((BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length * 2))
    (hr : (v 1).length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag v) =
      BimatrixRawGate.coefficients
        (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length) href r := by
  let z := BimatrixRawGate.coefficients
    (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length) href r
  let hit := fun i => decide ((v 0).length =
    (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + i)
  have hterm (ord : List Bool) (hh : hit ord.length = true) :
      binarySignedValue (rawTerm t corner flag (Fin.cons ord v)) = z := by
    have hi : ord.length = j.val := by have he := of_decide_eq_true hh; omega
    change binarySignedValue (BimatrixRawGateMachine.selectedShiftedCoefficientWord
      ![BrouwerNashHeaders.dimensionRuler (queryHeaders v), rawCode flag v, ord,
        inputRuler t corner flag (queryHeaders v), v 1]) = z
    rw [hcode]
    have hf : (raw[ord.length].shift (inputRuler t corner flag (queryHeaders
      v)).length).WellFormedAt (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length := by
      simpa only [hi] using href
    have he := BimatrixRawGateMachine.selectedShiftedCoefficientWord_encode
      (BrouwerNashHeaders.dimensionRuler (queryHeaders v)) (v 1) ord
      (inputRuler t corner flag (queryHeaders v)) raw (by rw [hi]; exact j.isLt) hf r hr
    simpa only [hi] using he
  have hk := BrouwerNashHeaders.dimensionRuler_pos (queryHeaders v)
  have hz : z.natAbs ≤ 100 * (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length := by
    have ha := BimatrixRawGate.coefficients_bound
      (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length) href r
    have he : |z| ≤ (100 : ℤ) * (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length := by
      dsimp only [z]
      have hkz : (1 : ℤ) ≤ (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length := by
        exact_mod_cast hk
      linarith
    apply (Nat.cast_le (α := ℤ)).mp
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] using he
  have he := binaryIndexedLookup_value (rawTest t corner flag) (rawTerm t corner flag)
    (BrouwerNashHeaders.widthRuler (queryHeaders v)) v hit z
    (fun ord => rawTest_value t corner flag v ord) hterm
    (by rw [BrouwerNashHeaders.widthRuler_length]; omega)
    (BrouwerNashHeaders.widthRuler_fits (queryHeaders v) z hz)
    (circuitUnaryPrefix (rawCode flag v))
  have hex : ∃ i < (circuitUnaryPrefix (rawCode flag v)).length, hit i = true := by
    refine ⟨j.val, ?_, ?_⟩
    · rw [hcode, circuitUnaryPrefix_rawEncode_length]
      exact j.isLt
    · exact decide_eq_true ho
  rw [ite_eq_left hex] at he
  exact he
private def scalarWord (v : Fin 5 → List Bool) : List Bool :=
  [false, false] ++ binaryLengthWord (BrouwerNashHeaders.dimensionRuler (queryHeaders v))
private theorem scalarWord_cobham : Cobham scalarWord := by
  unfold scalarWord
  have hd : Cobham (fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.dimensionRuler (queryHeaders v)) :=
    queryHeader_cobham BrouwerNashHeaders.dimensionRuler_cobham
  have hl : Cobham (fun v : Fin 5 → List Bool =>
      binaryLengthWord (BrouwerNashHeaders.dimensionRuler (queryHeaders v))) :=
    (Cobham.comp binaryLengthWord_cobham (fun _ : Fin 1 => hd)).of_eq fun _ => rfl
  have hs : Cobham (fun v : Fin 5 → List Bool => [false, false] ++
      binaryLengthWord (BrouwerNashHeaders.dimensionRuler (queryHeaders v))) :=
    Cobham.appendFn (.const [false, false]) hl
  exact hs
private theorem scalarWord_value (v : Fin 5 → List Bool) :
    binarySignedValue (scalarWord v) =
      2 * ((BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length : ℤ) := by
  simp only [scalarWord, List.cons_append, List.nil_append, binarySignedValue, List.headD_cons,
    Bool.false_eq_true,
    ite_false, List.tail_cons, Nat.fromBitsLE_cons, zero_add,
    binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]
private def copyTest (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (v : Fin 6 → List Bool) : List Bool :=
  lenEqFlag (v 1) (inputRuler t corner flag (queryHeaders (Fin.tail v)) ++
    scale axis.val (BrouwerNashHeaders.sourceDepthRuler (queryHeaders (Fin.tail v)) ++ [false]) ++
    v 0)
private def copyTerm (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (v : Fin 6 → List Bool) : List Bool :=
  binarySignedIndicator ![v 2, cornerBitRuler t corner axis ![v 0, v 3, v 4, v 5],
    scalarWord (Fin.tail v)]
private theorem copyTest_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2) :
    Cobham (copyTest t corner flag axis) :=
  lenEqFlag_mem (.proj 1) (.appendFn
    (.appendFn (tail_cobham (queryHeader_cobham (inputRuler_cobham t corner flag)))
      (scale_cobham _ (.appendFn
        (tail_cobham (queryHeader_cobham BrouwerNashHeaders.sourceDepthRuler_cobham))
        (.const [false])))) (.proj 0))
private theorem copyTerm_cobham (t : Fin 41) (corner : Fin 4) (axis : Fin 2) :
    Cobham (copyTerm t corner axis) := by
  let gs : Fin 4 → (Fin 6 → List Bool) → List Bool :=
    Fin.cases (fun v => v 0) (fun i v => v i.succ.succ.succ)
  have hc := Cobham.comp (gs := gs) (cornerBitRuler_cobham t corner axis) (by
    intro i
    cases i using Fin.cases
    · exact .proj 0
    · rename_i i
      exact .proj i.succ.succ.succ)
  have hs : Cobham (fun v : Fin 6 → List Bool => scalarWord (Fin.tail v)) :=
    tail_cobham scalarWord_cobham
  have h := Cobham.comp₃ binarySignedIndicator_cobham (.proj 2) hc hs
  unfold copyTerm
  exact h.of_eq fun _ => rfl
/-- Bounded copy lookup over the extended coordinate field for one corner and axis. -/
def copyCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (v : Fin 5 → List Bool) : List Bool :=
  binaryIndexedLookup (copyTest t corner flag axis) (copyTerm t corner axis)
    (BrouwerNashHeaders.sourceDepthRuler (queryHeaders v) ++ [false])
    (BrouwerNashHeaders.widthRuler (queryHeaders v)) v
theorem copyCoefficientWord_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2) :
    Cobham (copyCoefficientWord t corner flag axis) := by
  let gs : Fin 7 → (Fin 5 → List Bool) → List Bool := Fin.cases
    (fun v => BrouwerNashHeaders.sourceDepthRuler (queryHeaders v) ++ [false])
    (Fin.cases (fun v => BrouwerNashHeaders.widthRuler (queryHeaders v)) (fun j v => v j))
  have hc : Cobham (fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.sourceDepthRuler (queryHeaders v) ++ [false]) :=
    .appendFn (queryHeader_cobham BrouwerNashHeaders.sourceDepthRuler_cobham) (.const [false])
  have hw : Cobham (fun v : Fin 5 → List Bool =>
      BrouwerNashHeaders.widthRuler (queryHeaders v)) :=
    queryHeader_cobham BrouwerNashHeaders.widthRuler_cobham
  have h := Cobham.comp (gs := gs)
    (binaryIndexedLookup_cobham (copyTest_cobham t corner flag axis) (copyTerm_cobham t corner
      axis))
    (by
      intro i
      cases i using Fin.cases
      · simpa only [gs, Fin.cases_zero] using hc
      · rename_i i
        cases i using Fin.cases
        · simpa only [gs, Fin.cases_zero, Fin.cases_succ] using hw
        · rename_i j
          exact .proj j)
  unfold copyCoefficientWord
  exact h.of_eq fun _ => rfl
private theorem copyTest_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (v : Fin 5 → List Bool) (ord : List Bool) :
    copyTest t corner flag axis (Fin.cons ord v) = [decide ((v 0).length =
      (inputRuler t corner flag (queryHeaders v)).length +
        axis.val * ((pairFst (v 2)).length + 1) + ord.length)] := by
  simp only [copyTest, Fin.tail_cons, lenEqFlag_value, List.length_append,
    scale, smash_length, List.length_replicate, List.length_singleton,
    BrouwerNashHeaders.sourceDepthRuler_length]
  change [decide ((v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
    ((pairFst (v 2)).length + 1) * axis.val + ord.length)] = _
  rw [Nat.mul_comm ((pairFst (v 2)).length + 1)]
/-- A copied corner-bit wire has exactly the canonical positive-action coefficient. -/
theorem copyCoefficientWord_value_at (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (v : Fin 5 → List Bool) (j : ℕ) (hj : j ≤ (pairFst (v 2)).length)
    (ho : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      axis.val * ((pairFst (v 2)).length + 1) + j) :
    binarySignedValue (copyCoefficientWord t corner flag axis v) =
      if (v 1).length / 2 = (cornerBit (pairFst (v 2)).length
          (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length t corner axis j).val ∧
        (v 1).length % 2 = 1
      then 2 * ((BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length : ℤ) else 0 := by
  let input := cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
    (circuitUnaryPrefix (v 4)).length t corner axis j
  let z : ℤ := if (v 1).length / 2 = input.val ∧ (v 1).length % 2 = 1
    then 2 * (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length else 0
  let hit := fun i => decide ((v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
    axis.val * ((pairFst (v 2)).length + 1) + i)
  have hterm (ord : List Bool) (hh : hit ord.length = true) :
      binarySignedValue (copyTerm t corner axis (Fin.cons ord v)) = z := by
    have hi : ord.length = j := by have he := of_decide_eq_true hh; omega
    have hc := cornerBitRuler_length t corner axis ![ord, v 2, v 3, v 4]
      (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hi] using hj)
    change (cornerBitRuler t corner axis ![ord, v 2, v 3, v 4]).length =
      (cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length t corner axis ord.length).val at hc
    rw [hi] at hc
    change binarySignedValue (binarySignedIndicator ![v 1,
      cornerBitRuler t corner axis ![ord, v 2, v 3, v 4], scalarWord v]) = z
    rw [binarySignedIndicator_value, scalarWord_value, hc]
  have hz : z.natAbs ≤ 100 * (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length := by
    dsimp only [z]
    split
    · simp only [Int.natAbs_mul, Int.natAbs_natCast]
      change 2 * (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length ≤ _
      omega
    · simp only [Int.natAbs_zero]
      omega
  have he := binaryIndexedLookup_value (copyTest t corner flag axis) (copyTerm t corner axis)
    (BrouwerNashHeaders.widthRuler (queryHeaders v)) v hit z
    (fun ord => copyTest_value t corner flag axis v ord) hterm
    (by rw [BrouwerNashHeaders.widthRuler_length]; omega)
    (BrouwerNashHeaders.widthRuler_fits (queryHeaders v) z hz)
    (BrouwerNashHeaders.sourceDepthRuler (queryHeaders v) ++ [false])
  have hex : ∃ i < (BrouwerNashHeaders.sourceDepthRuler (queryHeaders v) ++ [false]).length,
      hit i = true := by
    refine ⟨j, ?_, decide_eq_true ho⟩
    simp only [List.length_append, List.length_singleton,
      BrouwerNashHeaders.sourceDepthRuler_length]
    change j < (pairFst (v 2)).length + 1
    omega
  rw [ite_eq_left hex] at he
  exact he
/-- Copy queries return zero outside their allocated extended coordinate field. -/
theorem copyCoefficientWord_value_zero (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (v : Fin 5 → List Bool)
    (hno : ∀ j ≤ (pairFst (v 2)).length, (v 0).length ≠
      (inputRuler t corner flag (queryHeaders v)).length +
        axis.val * ((pairFst (v 2)).length + 1) + j) :
    binarySignedValue (copyCoefficientWord t corner flag axis v) = 0 := by
  apply binaryIndexedLookup_value_zero
    (copyTest t corner flag axis) (copyTerm t corner axis) _ _ v
  intro ord hi
  rw [copyTest_value]
  have hb : ord.length ≤ (pairFst (v 2)).length := by
    simp only [List.length_append, List.length_singleton,
      BrouwerNashHeaders.sourceDepthRuler_length] at hi
    change ord.length < (pairFst (v 2)).length + 1 at hi
    omega
  simp only [hno ord.length hb, decide_false]
private theorem querySum_ofFn_cobham {p n : ℕ}
    (fs : Fin n → (Fin p → List Bool) → List Bool) (hs : ∀ i, Cobham (fs i)) :
    Cobham (binarySignedQuerySum (List.ofFn fs)) := by
  apply binarySignedQuerySum_cobham
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  exact hs i
private def cornerCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) : List Bool :=
  binarySignedAdd (copyCoefficientWord t corner flag 0 v)
    (binarySignedAdd (copyCoefficientWord t corner flag 1 v) (rawCoefficientWord t corner flag v))
private theorem cornerCoefficientWord_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (cornerCoefficientWord t corner flag) :=
  Cobham.comp₂ binarySignedAdd_cobham (copyCoefficientWord_cobham t corner flag 0)
    (Cobham.comp₂ binarySignedAdd_cobham (copyCoefficientWord_cobham t corner flag 1)
      (rawCoefficientWord_cobham t corner flag))
/-- Sum the disjoint color-copy and raw-circuit coefficient families of all forty-one samples. -/
def coefficientWord : (Fin 5 → List Bool) → List Bool :=
  binarySignedQuerySum (List.ofFn (fun t : Fin 41 =>
    binarySignedQuerySum (List.ofFn (fun corner : Fin 4 =>
      binarySignedQuerySum (List.ofFn (fun flag : Fin 2 => cornerCoefficientWord t corner flag))))))
theorem coefficientWord_cobham : Cobham coefficientWord :=
  querySum_ofFn_cobham _ (fun t => querySum_ofFn_cobham _
    (fun corner => querySum_ofFn_cobham _ (fun flag => cornerCoefficientWord_cobham t corner
      flag)))
theorem coefficientWord_mem_FPn : FPn coefficientWord := cobham_iff_FPn.mp coefficientWord_cobham
private def rawKindWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) : List Bool :=
  let start := inputRuler t corner flag (queryHeaders v) ++
    BrouwerNashHeaders.arityRuler (queryHeaders v)
  andBit (lenLeFlag (v 0) start)
    (notBit (lenLeFlag (v 0) (start ++ circuitUnaryPrefix (rawCode flag v))))
private theorem rawKindWord_cobham (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
    Cobham (rawKindWord t corner flag) := by
  have hs : Cobham (fun v : Fin 5 → List Bool => inputRuler t corner flag (queryHeaders v) ++
      BrouwerNashHeaders.arityRuler (queryHeaders v)) :=
    .appendFn (queryHeader_cobham (inputRuler_cobham t corner flag))
      (queryHeader_cobham BrouwerNashHeaders.arityRuler_cobham)
  have hc : Cobham (fun v : Fin 5 → List Bool => circuitUnaryPrefix (rawCode flag v)) :=
    Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP)
      (fun _ : Fin 1 => rawCode_cobham flag)
  exact .andFn (lenLeFlag_mem (.proj 0) hs)
    (.notFn (lenLeFlag_mem (.proj 0) (.appendFn hs hc)))
private def orFunctions {p : ℕ} :
    List ((Fin p → List Bool) → List Bool) → (Fin p → List Bool) → List Bool
  | [], _ => [false]
  | f :: fs, v => orBit (f v) (orFunctions fs v)
private theorem orFunctions_cobham {p : ℕ} (fs : List ((Fin p → List Bool) → List Bool))
    (hs : ∀ f ∈ fs, Cobham f) : Cobham (orFunctions fs) := by
  induction fs with
  | nil => exact .const [false]
  | cons f fs ih =>
    exact Cobham.orFn (hs f (by simp))
      (ih (fun g hg => hs g (by simp only [List.mem_cons]; exact Or.inr hg)))
private theorem orFunctions_ofFn_cobham {p n : ℕ}
    (fs : Fin n → (Fin p → List Bool) → List Bool) (hs : ∀ i, Cobham (fs i)) :
    Cobham (orFunctions (List.ofFn fs)) := by
  apply orFunctions_cobham
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  exact hs i
/-- Comparator flags hold exactly in allocated raw color-gate regions; copied inputs are affine. -/
def kindWord : (Fin 5 → List Bool) → List Bool :=
  orFunctions (List.ofFn (fun t : Fin 41 =>
    orFunctions (List.ofFn (fun corner : Fin 4 =>
      orFunctions (List.ofFn (fun flag : Fin 2 => rawKindWord t corner flag))))))
theorem kindWord_cobham : Cobham kindWord :=
  orFunctions_ofFn_cobham _ (fun t => orFunctions_ofFn_cobham _
    (fun corner => orFunctions_ofFn_cobham _ (fun flag => rawKindWord_cobham t corner flag)))
theorem kindWord_mem_FPn : FPn kindWord := cobham_iff_FPn.mp kindWord_cobham
open scoped BigOperators
private theorem sparse_sum {n : ℕ} (out start : ℕ) (z : ℤ) (f : Fin n → ℤ)
    (hat : ∀ i, out = start + i.val → z = f i)
    (hzero : (∀ i : Fin n, out ≠ start + i.val) → z = 0) :
    z = ∑ i : Fin n, if out = start + i.val then f i else 0 := by
  by_cases hh : ∃ i : Fin n, out = start + i.val
  · obtain ⟨i, hi⟩ := hh
    rw [Finset.sum_eq_single i]
    · simp only [hi, ite_true]
      exact hat i hi
    · intro j hj hji
      have hn : out ≠ start + j.val := by
        intro he
        exact hji (Fin.ext (by omega))
      simp only [hn, ite_false]
    · simp
  · have hn : ∀ i : Fin n, out ≠ start + i.val := by
      intro i hi
      exact hh ⟨i, hi⟩
    rw [hzero hn]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (hn i)
private theorem copyCoefficientWord_value_gate (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (axis : Fin 2) (v : Fin 5 → List Bool) (j : ℕ) (hj : j ≤ (pairFst (v 2)).length)
    (ho : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      axis.val * ((pairFst (v 2)).length + 1) + j)
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (copyCoefficientWord t corner flag axis v) =
      (affine₂ (cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length t corner axis j)
        (slot (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length zero)
        (2 * (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length : ℤ)) 0 0).coefficients r := by
  rw [copyCoefficientWord_value_at t corner flag axis v j hj ho,
    BrouwerNashCoefficientQuery.affine₂_coefficients]
  simp only [hr, BrouwerNashCoefficientQuery.pairedAction_iff, ite_self, add_zero,
    BrouwerNashHeaders.dimensionRuler_length]
  rfl
private theorem copyCoefficientWord_value_sum (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (axis : Fin 2) (v : Fin 5 → List Bool)
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (copyCoefficientWord t corner flag axis v) =
      ∑ j : Fin ((pairFst (v 2)).length + 1),
        if (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
            axis.val * ((pairFst (v 2)).length + 1) + j.val
        then (affine₂ (cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length t corner axis j.val)
          (slot (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
            (circuitUnaryPrefix (v 4)).length zero)
          (2 * (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
            (circuitUnaryPrefix (v 4)).length : ℤ)) 0 0).coefficients r else 0 := by
  apply sparse_sum
  · intro j hj
    exact copyCoefficientWord_value_gate t corner flag axis v j.val
      (by have hh := j.isLt; omega) hj r hr
  · intro hn
    apply copyCoefficientWord_value_zero
    intro j hj
    exact hn ⟨j, by omega⟩
private theorem rawCoefficientWord_value_dimension (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (hcode : rawCode flag v = raw.encode) (j : Fin raw.length)
    (ho : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val)
    (k : ℕ) (hk : (BrouwerNashHeaders.dimensionRuler (queryHeaders v)).length = k)
    (href : (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length).WellFormedAt k)
    (r : Fin (k * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag v) =
      BimatrixRawGate.coefficients
        (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length) href r := by
  subst k
  exact rawCoefficientWord_value_at t corner flag v raw hcode j ho href r hr
private theorem rawCoefficientWord_value_gate (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (hcode : rawCode flag v = raw.encode) (j : Fin raw.length)
    (ho : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val)
    (href : (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length).WellFormedAt
      (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length))
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag v) =
      (guardedRaw (raw[j.val].shift (inputRuler t corner flag (queryHeaders
        v)).length)).coefficients r := by
  rw [guardedRaw_eq _ href]
  dsimp only [BimatrixRawGate.gate]
  exact rawCoefficientWord_value_dimension t corner flag v raw hcode j ho _
    (BrouwerNashHeaders.dimensionRuler_length (queryHeaders v)) href r hr
private theorem rawCoefficientWord_value_sum (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (hcode : rawCode flag v = raw.encode)
    (hwf : ∀ j : Fin raw.length,
      (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length).WellFormedAt
        (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length))
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag v) =
      ∑ j : Fin raw.length, if (v 0).length =
          (inputRuler t corner flag (queryHeaders v)).length +
            (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val
        then (guardedRaw (raw[j.val].shift
          (inputRuler t corner flag (queryHeaders v)).length)).coefficients r else 0 := by
  apply sparse_sum
  · intro j hj
    exact rawCoefficientWord_value_gate t corner flag v raw hcode j hj (hwf j) r hr
  · intro hn
    apply rawCoefficientWord_value_zero
    intro j hj
    rw [hcode, circuitUnaryPrefix_rawEncode_length] at hj
    exact hn ⟨j, hj⟩
private theorem rawEnd_le_dimension (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) :
    (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
      (circuitUnaryPrefix (rawCode flag v)).length ≤
      dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length := by
  let b := (pairFst (v 2)).length
  let e₀ := (circuitUnaryPrefix (v 3)).length
  let e₁ := (circuitUnaryPrefix (v 4)).length
  have hc : corner.val * cornerWidth b e₀ e₁ + cornerWidth b e₀ e₁ ≤
      4 * cornerWidth b e₀ e₁ := by
    calc
      _ = (corner.val + 1) * cornerWidth b e₀ e₁ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have hh := corner.isLt; omega)
  have hs := sample_lt_dimension b e₀ e₁ t (colorBase b + 4 * cornerWidth b e₀ e₁)
    (by dsimp [colorBase, weightBase, sampleWidth]; omega)
  have hw : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
  rw [inputRuler_length, BrouwerNashHeaders.arityRuler_length]
  change sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag + arity b +
    (circuitUnaryPrefix (rawCode flag v)).length ≤ dimension b e₀ e₁
  unfold colorInput rawCode
  by_cases hf : flag.val = 0
  · simp only [hf, ite_true, add_zero]
    change sampleBase b e₀ e₁ t + (colorBase b + corner.val * cornerWidth b e₀ e₁) +
      arity b + e₀ ≤ dimension b e₀ e₁
    omega
  · simp only [hf, ite_false]
    change sampleBase b e₀ e₁ t + (colorBase b + corner.val * cornerWidth b e₀ e₁ +
      (arity b + e₀)) + arity b + e₁ ≤ dimension b e₀ e₁
    omega
private theorem rawShift_wellFormed (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (hcode : rawCode flag v = raw.encode)
    (hraw : raw.WellFormed (arity (pairFst (v 2)).length)) (j : Fin raw.length) :
    (raw[j.val].shift (inputRuler t corner flag (queryHeaders v)).length).WellFormedAt
      (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length) := by
  have he := rawEnd_le_dimension t corner flag v
  rw [hcode, circuitUnaryPrefix_rawEncode_length, BrouwerNashHeaders.arityRuler_length] at he
  change (inputRuler t corner flag (queryHeaders v)).length + arity (pairFst (v 2)).length +
    raw.length ≤ dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length at he
  have hj := j.isLt
  have hf := hraw.2 j
  change raw[j.val].input₀ < arity (pairFst (v 2)).length + j.val ∧
    raw[j.val].input₁ < arity (pairFst (v 2)).length + j.val at hf
  dsimp only [_root_.Complexity.CircuitCode.RawGate.WellFormedAt,
    _root_.Complexity.CircuitCode.RawGate.shift]
  constructor <;> omega
private theorem lenLeFlag_value (x y : List Bool) :
    lenLeFlag x y = [decide (y.length ≤ x.length)] := by
  rcases lenLeFlag_flag x y with h | h
  · simp only [h, (lenLeFlag_eq_true_iff x y).mp h, decide_true]
  · have hn : ¬y.length ≤ x.length := by
      intro he
      rw [(lenLeFlag_eq_true_iff x y).mpr he] at h
      contradiction
    simp only [h, hn, decide_false]
private theorem rawKindWord_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (v : Fin 5 → List Bool) :
    rawKindWord t corner flag v = [decide (
      (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length ≤ (v 0).length ∧
      (v 0).length < (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
          (circuitUnaryPrefix (rawCode flag v)).length)] := by
  unfold rawKindWord
  dsimp only
  rw [lenLeFlag_value, lenLeFlag_value]
  simp only [List.length_append]
  by_cases hs : (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length ≤ (v 0).length
  · simp only [hs, true_and, decide_true]
    by_cases he : (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
          (circuitUnaryPrefix (rawCode flag v)).length ≤ (v 0).length
    · have hn : ¬(v 0).length < (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
          (circuitUnaryPrefix (rawCode flag v)).length := by omega
      simp only [he, hn, decide_true, decide_false, andBit, notBit, caseBit₀, Bool.cond_true,
        Bool.cond_false]
    · have hl : (v 0).length < (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
          (circuitUnaryPrefix (rawCode flag v)).length := by omega
      simp only [he, hl, decide_true, decide_false, andBit, notBit, caseBit₀, Bool.cond_true,
        Bool.cond_false]
  · simp only [hs, false_and, decide_false, andBit, caseBit₀, Bool.cond_false]
private theorem orFunctions_value {p : ℕ}
    (fs : List ((Fin p → List Bool) → List Bool)) (v : Fin p → List Bool) :
    orFunctions fs v = [fs.any (fun f => (f v).headD false)] := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [orFunctions, ih]
    cases hf : f v with
    | nil =>
      simp only [orBit, caseBit₀, List.any_cons, hf, List.headD_nil, Bool.false_or]
      cases fs.any (fun f => (f v).headD false) <;> rfl
    | cons b tail =>
      cases b <;> simp only [orBit, caseBit₀, List.any_cons, hf, List.headD_cons,
        Bool.cond_true, Bool.cond_false, Bool.false_or, Bool.true_or]
      cases fs.any (fun f => (f v).headD false) <;> rfl
private theorem orFunctions_ofFn_value {p n : ℕ}
    (fs : Fin n → (Fin p → List Bool) → List Bool) (v : Fin p → List Bool) :
    orFunctions (List.ofFn fs) v = [decide (∃ i, (fs i v).headD false = true)] := by
  rw [orFunctions_value]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hh⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact decide_eq_true ⟨i, hh⟩
  · intro h
    obtain ⟨i, hh⟩ := of_decide_eq_true h
    exact ⟨fs i, List.mem_ofFn.mpr ⟨i, rfl⟩, hh⟩
/-- The computed kind flag is exactly the union of the allocated raw-circuit intervals. -/
theorem kindWord_value (v : Fin 5 → List Bool) :
    kindWord v = [decide (∃ t : Fin 41, ∃ corner : Fin 4, ∃ flag : Fin 2,
      (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length ≤ (v 0).length ∧
      (v 0).length < (inputRuler t corner flag (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length +
          (circuitUnaryPrefix (rawCode flag v)).length)] := by
  unfold kindWord
  simp only [orFunctions_ofFn_value, List.headD_cons, decide_eq_true_eq, rawKindWord_value]
private theorem querySum_ofFn_value {p n : ℕ}
    (fs : Fin n → (Fin p → List Bool) → List Bool) (v : Fin p → List Bool) :
    binarySignedValue (binarySignedQuerySum (List.ofFn fs) v) =
      ∑ i : Fin n, binarySignedValue (fs i v) :=
      by
  rw [binarySignedQuerySum_value, List.map_ofFn, List.sum_ofFn]
  rfl
/-- The full coefficient query is the guarded sum of its canonical copy and raw gate factories. -/
theorem coefficientWord_value (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val) :
    binarySignedValue (coefficientWord v) =
      ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
        ((∑ axis : Fin 2, ∑ j : Fin ((pairFst (v 2)).length + 1),
          if (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
              axis.val * ((pairFst (v 2)).length + 1) + j.val
          then (affine₂ (cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
            (circuitUnaryPrefix (v 4)).length t corner axis j.val)
            (slot (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
              (circuitUnaryPrefix (v 4)).length zero)
            (2 * (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
              (circuitUnaryPrefix (v 4)).length : ℤ)) 0 0).coefficients r else 0) +
        (let raw := if flag.val = 0 then raw₀ else raw₁
          ∑ j : Fin raw.length, if (v 0).length =
              (inputRuler t corner flag (queryHeaders v)).length +
                (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val
            then (guardedRaw (raw[j.val].shift
              (inputRuler t corner flag (queryHeaders v)).length)).coefficients r else 0)) := by
  unfold coefficientWord
  rw [querySum_ofFn_value]
  apply Finset.sum_congr rfl
  intro t ht
  rw [querySum_ofFn_value]
  apply Finset.sum_congr rfl
  intro corner hc
  rw [querySum_ofFn_value]
  apply Finset.sum_congr rfl
  intro flag hf
  rw [cornerCoefficientWord, binarySignedAdd_value, binarySignedAdd_value,
    copyCoefficientWord_value_sum t corner flag 0 v r hr,
    copyCoefficientWord_value_sum t corner flag 1 v r hr]
  let raw := if flag.val = 0 then raw₀ else raw₁
  have he : rawCode flag v = raw.encode := by
    unfold rawCode raw
    split <;> assumption
  have hw : raw.WellFormed (arity (pairFst (v 2)).length) := by
    unfold raw
    split <;> assumption
  rw [rawCoefficientWord_value_sum t corner flag v raw he
    (fun j => rawShift_wellFormed t corner flag v raw he hw j) r hr]
  rw [Fin.sum_univ_two]
  ring
private theorem block_unique (width i j r s : ℕ) (hr : r < width) (hs : s < width)
    (he : width * i + r = width * j + s) : i = j ∧ r = s := by
  have hw : 0 < width := by omega
  have hi : (width * i + r) / width = i ∧ (width * i + r) % width = r :=
    (Nat.div_mod_unique hw).mpr ⟨by omega, hr⟩
  have hj : (width * i + r) / width = j ∧ (width * i + r) % width = s :=
    (Nat.div_mod_unique hw).mpr ⟨by omega, hs⟩
  exact ⟨hi.1.symm.trans hj.1, hi.2.symm.trans hj.2⟩
private theorem colorLocal_lt (b e₀ e₁ : ℕ) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth b e₀ e₁) :
    colorBase b + corner.val * cornerWidth b e₀ e₁ + offset < sampleWidth b e₀ e₁ := by
  have hc : corner.val * cornerWidth b e₀ e₁ + cornerWidth b e₀ e₁ ≤
      4 * cornerWidth b e₀ e₁ := by
    calc
      _ = (corner.val + 1) * cornerWidth b e₀ e₁ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have hh := corner.isLt; omega)
  have hs : colorBase b + 4 * cornerWidth b e₀ e₁ < sampleWidth b e₀ e₁ := by
    dsimp [colorBase, weightBase, sampleWidth]
    omega
  omega
private theorem colorPosition_injective (b e₀ e₁ : ℕ) (t t' : Fin 41)
    (corner corner' : Fin 4) (offset offset' : ℕ)
    (ho : offset < cornerWidth b e₀ e₁) (ho' : offset' < cornerWidth b e₀ e₁)
    (he : sampleBase b e₀ e₁ t + colorBase b + corner.val * cornerWidth b e₀ e₁ + offset =
      sampleBase b e₀ e₁ t' + colorBase b + corner'.val * cornerWidth b e₀ e₁ + offset') :
    t = t' ∧ corner = corner' ∧ offset = offset' := by
  have h₀ := colorLocal_lt b e₀ e₁ corner offset ho
  have h₁ := colorLocal_lt b e₀ e₁ corner' offset' ho'
  have hs : sampleWidth b e₀ e₁ * t.val +
      (colorBase b + corner.val * cornerWidth b e₀ e₁ + offset) =
    sampleWidth b e₀ e₁ * t'.val +
      (colorBase b + corner'.val * cornerWidth b e₀ e₁ + offset') := by
    simp only [sampleBase, Nat.mul_comm t.val (sampleWidth b e₀ e₁),
      Nat.mul_comm t'.val (sampleWidth b e₀ e₁)] at he
    omega
  have hb := block_unique _ _ _ _ _ h₀ h₁ hs
  have ht : t = t' := Fin.ext hb.1
  have hec : cornerWidth b e₀ e₁ * corner.val + offset =
      cornerWidth b e₀ e₁ * corner'.val + offset' := by
    have hh := hb.2
    rw [Nat.mul_comm corner.val (cornerWidth b e₀ e₁),
      Nat.mul_comm corner'.val (cornerWidth b e₀ e₁)] at hh
    omega
  have hc := block_unique _ _ _ _ _ ho ho' hec
  exact ⟨ht, Fin.ext hc.1, hc.2⟩
private theorem rawIntervals_iff (b e₀ e₁ out : ℕ) (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth b e₀ e₁)
    (he : out = sampleBase b e₀ e₁ t + colorBase b + corner.val * cornerWidth b e₀ e₁ + offset) :
    (∃ t' : Fin 41, ∃ corner' : Fin 4, ∃ flag : Fin 2,
      sampleBase b e₀ e₁ t' + colorInput b e₀ e₁ corner' flag + arity b ≤ out ∧
      out < sampleBase b e₀ e₁ t' + colorInput b e₀ e₁ corner' flag + arity b +
        (if flag.val = 0 then e₀ else e₁)) ↔
    (arity b ≤ offset ∧ offset < arity b + e₀) ∨
      (2 * arity b + e₀ ≤ offset ∧ offset < cornerWidth b e₀ e₁) := by
  constructor
  · rintro ⟨t', corner', flag, hlo, hhi⟩
    let start := sampleBase b e₀ e₁ t' + colorBase b + corner'.val * cornerWidth b e₀ e₁
    let off := out - start
    have hstart : start ≤ out := by unfold start; unfold colorInput at hlo; omega
    have hout : out = start + off := by omega
    have hoff : off < cornerWidth b e₀ e₁ := by
      unfold colorInput at hhi
      unfold start at hout
      by_cases hf : flag.val = 0
      · simp only [hf, ite_true, add_zero] at hhi
        have hw : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
        omega
      · simp only [hf, ite_false] at hhi
        have hw : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
        omega
    have hpos := colorPosition_injective b e₀ e₁ t t' corner corner' offset off ho hoff
      (he.symm.trans hout)
    have ht := hpos.1
    have hc := hpos.2.1
    have hu := hpos.2.2
    subst t'
    subst corner'
    unfold colorInput at hlo hhi
    by_cases hf : flag.val = 0
    · simp only [hf, ite_true, add_zero] at hlo hhi
      exact Or.inl (by constructor <;> omega)
    · simp only [hf, ite_false] at hlo hhi
      exact Or.inr ⟨by omega, ho⟩
  · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · refine ⟨t, corner, 0, ?_⟩
      simp only [colorInput, Fin.val_zero, ite_true, add_zero]
      constructor <;> omega
    · refine ⟨t, corner, 1, ?_⟩
      simp only [colorInput, Fin.val_one, Nat.one_ne_zero, ite_false]
      have hw : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
      constructor <;> omega
private theorem colorRawShift_wellFormed (b : ℕ)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length) :
    (((if flag.val = 0 then raw₀ else raw₁)[j.val]).shift
      (sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner
        flag)).WellFormedAt (dimension b raw₀.length raw₁.length) := by
  have hs := sample_lt_dimension b raw₀.length raw₁.length t
    (colorBase b + 4 * cornerWidth b raw₀.length raw₁.length)
    (by dsimp [colorBase, weightBase, sampleWidth]; omega)
  have hc : corner.val * cornerWidth b raw₀.length raw₁.length +
      cornerWidth b raw₀.length raw₁.length ≤ 4 * cornerWidth b raw₀.length raw₁.length := by
    calc
      _ = (corner.val + 1) * cornerWidth b raw₀.length raw₁.length := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have hh := corner.isLt; omega)
  have hl : cornerWidth b raw₀.length raw₁.length =
      2 * arity b + raw₀.length + raw₁.length := rfl
  fin_cases flag
  · have hg := hw₀.2 j
    change raw₀[j.val].input₀ < arity b + j.val ∧ raw₀[j.val].input₁ < arity b + j.val at hg
    have hj : j.val < raw₀.length := j.isLt
    change (sampleBase b raw₀.length raw₁.length t +
        (colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + 0)) +
          raw₀[j.val].input₀ <
        dimension b raw₀.length raw₁.length ∧
      (sampleBase b raw₀.length raw₁.length t +
        (colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + 0)) +
          raw₀[j.val].input₁ <
        dimension b raw₀.length raw₁.length
    constructor <;> omega
  · have hg := hw₁.2 j
    change raw₁[j.val].input₀ < arity b + j.val ∧ raw₁[j.val].input₁ < arity b + j.val at hg
    have hj : j.val < raw₁.length := j.isLt
    change (sampleBase b raw₀.length raw₁.length t +
        (colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length +
           (arity b + raw₀.length))) + raw₁[j.val].input₀ < dimension b raw₀.length raw₁.length ∧
      (sampleBase b raw₀.length raw₁.length t +
        (colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length +
           (arity b + raw₀.length))) + raw₁[j.val].input₁ < dimension b raw₀.length raw₁.length
    constructor <;> omega
private theorem colorRegionGate_comparator_iff (b : ℕ)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hw₀ : raw₀.WellFormed (arity b)) (hw₁ : raw₁.WellFormed (arity b))
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth b raw₀.length raw₁.length) :
    (colorRegionGate b raw₀ raw₁ t corner offset).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator ↔
      (arity b ≤ offset ∧ offset < arity b + raw₀.length) ∨
        (2 * arity b + raw₀.length ≤ offset ∧ offset < cornerWidth b raw₀.length raw₁.length) := by
  by_cases h₀ : offset < arity b
  · have he := colorRegionGate_copy b raw₀ raw₁ t corner 0 offset h₀
    simp only [Fin.val_zero, ite_true, zero_add] at he
    rw [he]
    simp only [affine₂, GameTheory.Finite.BimatrixArithmeticGate.gate,
      reduceCtorEq, false_iff]
    omega
  · by_cases h₁ : offset < arity b + raw₀.length
    · let j : Fin raw₀.length := ⟨offset - arity b, by omega⟩
      have he := colorRegionGate_raw₀ b raw₀ raw₁ t corner j
      have hj : arity b + j.val = offset := by dsimp [j]; omega
      rw [hj] at he
      have hf := colorRawShift_wellFormed b raw₀ raw₁ hw₀ hw₁ t corner 0 j
      simp only [Fin.val_zero, ite_true] at hf
      change ((raw₀.get j).shift (sampleBase b raw₀.length raw₁.length t +
        colorInput b raw₀.length raw₁.length corner 0)).WellFormedAt _ at hf
      rw [he, guardedRaw_eq _ hf]
      simp only [BimatrixRawGate.gate, true_iff]
      exact Or.inl ⟨by omega, h₁⟩
    · by_cases h₂ : offset < 2 * arity b + raw₀.length
      · let j := offset - (arity b + raw₀.length)
        have hj : j < arity b := by dsimp [j]; omega
        have he := colorRegionGate_copy b raw₀ raw₁ t corner 1 j hj
        simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at he
        have heq : arity b + raw₀.length + j = offset := by dsimp [j]; omega
        rw [heq] at he
        rw [he]
        simp only [affine₂, GameTheory.Finite.BimatrixArithmeticGate.gate,
          reduceCtorEq, false_iff]
        omega
      · let j : Fin raw₁.length := ⟨offset - (2 * arity b + raw₀.length), by
          have hl : cornerWidth b raw₀.length raw₁.length =
            2 * arity b + raw₀.length + raw₁.length := rfl
          omega⟩
        have he := colorRegionGate_raw₁ b raw₀ raw₁ t corner j
        have hj : 2 * arity b + raw₀.length + j.val = offset := by dsimp [j]; omega
        rw [hj] at he
        have hf := colorRawShift_wellFormed b raw₀ raw₁ hw₀ hw₁ t corner 1 j
        simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at hf
        change ((raw₁.get j).shift (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 1)).WellFormedAt _ at hf
        rw [he, guardedRaw_eq _ hf]
        simp only [BimatrixRawGate.gate, true_iff]
        exact Or.inr ⟨by omega, ho⟩
/-- At an allocated color output, the computed flag is the canonical program gate kind. -/
theorem kindWord_eq_colorRegion (out action source : List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hw₀ : raw₀.WellFormed (arity (pairFst source).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst source).length))
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (pairFst source).length raw₀.length raw₁.length)
    (hout : out.length = sampleBase (pairFst source).length raw₀.length raw₁.length t +
      colorBase (pairFst source).length +
        corner.val * cornerWidth (pairFst source).length raw₀.length raw₁.length + offset) :
    kindWord ![out, action, source, raw₀.encode, raw₁.encode] =
      [decide ((colorRegionGate (pairFst source).length raw₀ raw₁ t corner offset).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  have hp₀ : (circuitUnaryPrefix raw₀.encode).length = raw₀.length := by
    exact circuitUnaryPrefix_rawEncode_length _
  have hp₁ : (circuitUnaryPrefix raw₁.encode).length = raw₁.length := by
    exact circuitUnaryPrefix_rawEncode_length _
  rw [kindWord_value]
  have h3 : (![out, action, source, raw₀.encode, raw₁.encode] : Fin 5 → List Bool) 3 = raw₀.encode
    := rfl
  have h4 : (![out, action, source, raw₀.encode, raw₁.encode] : Fin 5 → List Bool) 4 = raw₁.encode
    := rfl
  simp only [inputRuler_length, BrouwerNashHeaders.arityRuler_length, queryHeaders,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, rawCode, h3, h4,
    apply_ite, hp₀, hp₁]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  refine Iff.trans ?_ ((rawIntervals_iff (pairFst source).length raw₀.length raw₁.length out.length
    t corner offset ho hout).trans
      (colorRegionGate_comparator_iff (pairFst source).length raw₀ raw₁ hw₀ hw₁ t corner offset
        ho).symm)
  apply exists_congr; intro sample
  apply exists_congr; intro vertex
  apply exists_congr; intro flag
  by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false]
/-- No allocated color gate contributes outside the color regions. -/
theorem coefficientWord_zero_outside (v : Fin 5 → List Bool)
    (hno : ∀ (t : Fin 41) (corner : Fin 4) offset,
      offset < cornerWidth (pairFst (v 2)).length
        (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length →
      (v 0).length ≠ sampleBase (pairFst (v 2)).length
        (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length t +
          colorBase (pairFst (v 2)).length + corner.val * cornerWidth
            (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
              (circuitUnaryPrefix (v 4)).length + offset) :
    binarySignedValue (coefficientWord v) = 0 := by
  let b := (pairFst (v 2)).length
  let e₀ := (circuitUnaryPrefix (v 3)).length
  let e₁ := (circuitUnaryPrefix (v 4)).length
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag (queryHeaders v)).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, b, e₀, e₁] using inputRuler_length t corner flag (queryHeaders v)
  unfold coefficientWord
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro t ht
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro corner hc
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro flag hf
  have hcopy (axis : Fin 2) :
      binarySignedValue (copyCoefficientWord t corner flag axis v) = 0 := by
    apply copyCoefficientWord_value_zero
    intro j hj he
    let off := (if flag.val = 0 then 0 else arity b + e₀) + axis.val * (b + 1) + j
    have ha := axis.isLt
    have hjb : j ≤ b := hj
    have hlocal : axis.val * (b + 1) + j < arity b := by
      have hm : axis.val * (b + 1) ≤ b + 1 := by
        calc
          _ ≤ 1 * (b + 1) := Nat.mul_le_mul_right _ (by omega)
          _ = _ := one_mul _
      change axis.val * (b + 1) + j < 2 * (b + 1)
      omega
    have hoff : off < cornerWidth b e₀ e₁ := by
      dsimp only [off, cornerWidth]
      split_ifs <;> omega
    apply (show (v 0).length ≠ sampleBase b e₀ e₁ t + colorBase b +
      corner.val * cornerWidth b e₀ e₁ + off from hno t corner off hoff)
    rw [hin, colorInput] at he
    change (v 0).length = sampleBase b e₀ e₁ t +
      (colorBase b + corner.val * cornerWidth b e₀ e₁ +
        (if flag.val = 0 then 0 else arity b + e₀)) + axis.val * (b + 1) + j at he
    dsimp only [off]
    omega
  have hraw : binarySignedValue (rawCoefficientWord t corner flag v) = 0 := by
    apply rawCoefficientWord_value_zero
    intro j hj he
    let off := (if flag.val = 0 then 0 else arity b + e₀) + arity b + j
    have hoff : off < cornerWidth b e₀ e₁ := by
      dsimp only [off, cornerWidth]
      dsimp only [rawCode] at hj
      by_cases hflag : flag.val = 0
      · simp only [hflag, ite_true] at hj ⊢
        change j < e₀ at hj
        omega
      · simp only [hflag, ite_false] at hj ⊢
        change j < e₁ at hj
        omega
    apply (show (v 0).length ≠ sampleBase b e₀ e₁ t + colorBase b +
      corner.val * cornerWidth b e₀ e₁ + off from hno t corner off hoff)
    have harity : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length = arity b := by
      simpa only [queryHeaders, Matrix.cons_val_zero, b] using
        BrouwerNashHeaders.arityRuler_length (queryHeaders v)
    rw [hin, colorInput, harity] at he
    dsimp only [off]
    omega
  rw [cornerCoefficientWord, binarySignedAdd_value, binarySignedAdd_value,
    hcopy 0, hcopy 1, hraw]
  rfl
/-- The color kind query is false outside the allocated color portion of every sample. -/
theorem kindWord_zero_of_outside (v : Fin 5 → List Bool)
    (hno : ∀ t : Fin 41, ¬(sampleBase (pairFst (v 2)).length
      (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length t +
        colorBase (pairFst (v 2)).length ≤ (v 0).length ∧
      (v 0).length < sampleBase (pairFst (v 2)).length
        (circuitUnaryPrefix (v 3)).length (circuitUnaryPrefix (v 4)).length t +
          minimumBase (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
            (circuitUnaryPrefix (v 4)).length)) : kindWord v = [false] := by
  rw [kindWord_value]
  congr 1
  apply decide_eq_false_iff_not.mpr
  rintro ⟨t, corner, flag, hlo, hhi⟩
  apply hno t
  let b := (pairFst (v 2)).length
  let e₀ := (circuitUnaryPrefix (v 3)).length
  let e₁ := (circuitUnaryPrefix (v 4)).length
  have hin : (inputRuler t corner flag (queryHeaders v)).length =
      sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, b, e₀, e₁] using
        inputRuler_length t corner flag (queryHeaders v)
  have harity : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length = arity b := by
    simpa only [queryHeaders, Matrix.cons_val_zero, b] using
      BrouwerNashHeaders.arityRuler_length (queryHeaders v)
  rw [hin, harity, colorInput] at hlo hhi
  have hc : corner.val * cornerWidth b e₀ e₁ + cornerWidth b e₀ e₁ ≤
      4 * cornerWidth b e₀ e₁ := by
    calc
      _ = (corner.val + 1) * cornerWidth b e₀ e₁ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have hh := corner.isLt; omega)
  change sampleBase b e₀ e₁ t + colorBase b ≤ (v 0).length ∧
    (v 0).length < sampleBase b e₀ e₁ t + minimumBase b e₀ e₁
  have hl : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
  dsimp only [rawCode] at hhi
  by_cases hf : flag.val = 0
  · simp only [hf, ite_true] at hlo hhi
    change (v 0).length < sampleBase b e₀ e₁ t + (colorBase b +
      corner.val * cornerWidth b e₀ e₁ + 0) + arity b + e₀ at hhi
    dsimp only [minimumBase]
    constructor <;> omega
  · simp only [hf, ite_false] at hlo hhi
    change (v 0).length < sampleBase b e₀ e₁ t + (colorBase b +
      corner.val * cornerWidth b e₀ e₁ + (arity b + e₀)) + arity b + e₁ at hhi
    dsimp only [minimumBase]
    constructor <;> omega
private theorem copyOffset_lt (b e₀ e₁ : ℕ) (flag axis : Fin 2)
    (j : Fin (b + 1)) :
    (if flag.val = 0 then 0 else arity b + e₀) + axis.val * (b + 1) + j.val <
      cornerWidth b e₀ e₁ := by
  have hj := j.isLt
  fin_cases flag <;> fin_cases axis <;> norm_num only [arity, cornerWidth] <;>
    simp only [ite_true, ite_false, zero_mul, one_mul, zero_add] <;> omega
private theorem copyOffset_injective (b e₀ : ℕ) (f f' a a' : Fin 2)
    (j j' : Fin (b + 1))
    (he : (if f.val = 0 then 0 else arity b + e₀) + a.val * (b + 1) + j.val =
      (if f'.val = 0 then 0 else arity b + e₀) + a'.val * (b + 1) + j'.val) :
    f.val = f'.val ∧ a.val = a'.val ∧ j.val = j'.val := by
  have hj := j.isLt
  have hj' := j'.isLt
  fin_cases f <;> fin_cases f' <;> fin_cases a <;> fin_cases a' <;>
    norm_num only [arity] at he ⊢ <;>
    simp only [ite_true, ite_false, zero_mul, one_mul, zero_add] at he ⊢ <;>
      (try simp only [true_and]) <;> omega
private theorem copyOffset_ne_rawOffset (b e₀ e₁ : ℕ) (f f' a : Fin 2)
    (j : Fin (b + 1)) (l : ℕ) (hl : l < if f'.val = 0 then e₀ else e₁) :
    (if f.val = 0 then 0 else arity b + e₀) + a.val * (b + 1) + j.val ≠
      (if f'.val = 0 then 0 else arity b + e₀) + arity b + l := by
  have hj := j.isLt
  intro he
  fin_cases f <;> fin_cases f' <;> fin_cases a <;>
    norm_num only [arity] at he hl <;>
    simp only [ite_true, ite_false, zero_mul, one_mul, zero_add] at he hl <;> omega
private theorem copyPosition_eq_iff (b e₀ e₁ : ℕ)
    (t t' : Fin 41) (c c' : Fin 4) (f f' a a' : Fin 2) (j j' : Fin (b + 1)) :
    sampleBase b e₀ e₁ t + colorInput b e₀ e₁ c f + a.val * (b + 1) + j.val =
      sampleBase b e₀ e₁ t' + colorInput b e₀ e₁ c' f' + a'.val * (b + 1) + j'.val ↔
        t = t' ∧ c = c' ∧ f = f' ∧ a = a' ∧ j = j' := by
  constructor
  · intro he
    let o := (if f.val = 0 then 0 else arity b + e₀) + a.val * (b + 1) + j.val
    let o' := (if f'.val = 0 then 0 else arity b + e₀) + a'.val * (b + 1) + j'.val
    have hpos : sampleBase b e₀ e₁ t + colorBase b + c.val * cornerWidth b e₀ e₁ + o =
        sampleBase b e₀ e₁ t' + colorBase b + c'.val * cornerWidth b e₀ e₁ + o' := by
      dsimp only [o, o', colorInput] at he ⊢
      omega
    have hx := colorPosition_injective b e₀ e₁ t t' c c' o o'
      (copyOffset_lt b e₀ e₁ f a j) (copyOffset_lt b e₀ e₁ f' a' j') hpos
    have hs := copyOffset_injective b e₀ f f' a a' j j' hx.2.2
    exact ⟨hx.1, hx.2.1, Fin.ext hs.1, Fin.ext hs.2.1, Fin.ext hs.2.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
private theorem rawOffset_lt (b e₀ e₁ : ℕ) (flag : Fin 2) (j : ℕ)
    (hj : j < if flag.val = 0 then e₀ else e₁) :
    (if flag.val = 0 then 0 else arity b + e₀) + arity b + j < cornerWidth b e₀ e₁ := by
  dsimp only [cornerWidth]
  by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false] at hj ⊢ <;> omega
/-- The selected copied coordinate contributes exactly its canonical affine coefficient. -/
theorem coefficientWord_eq_copy (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag axis : Fin 2)
    (j : Fin ((pairFst (v 2)).length + 1))
    (hout : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      axis.val * ((pairFst (v 2)).length + 1) + j.val) :
    binarySignedValue (coefficientWord v) =
      (affine₂ (cornerBit (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
        (circuitUnaryPrefix (v 4)).length t corner axis j.val)
        (slot (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length zero)
        (2 * (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
          (circuitUnaryPrefix (v 4)).length : ℤ)) 0 0).coefficients r := by
  let b := (pairFst (v 2)).length
  let e₀ := (circuitUnaryPrefix (v 3)).length
  let e₁ := (circuitUnaryPrefix (v 4)).length
  have hp₀ : e₀ = raw₀.length := by
    dsimp [e₀]; rw [hc₀]
    exact circuitUnaryPrefix_rawEncode_length _
  have hp₁ : e₁ = raw₁.length := by
    dsimp [e₁]; rw [hc₁]
    exact circuitUnaryPrefix_rawEncode_length _
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag (queryHeaders v)).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, b, e₀, e₁] using
        inputRuler_length t corner flag (queryHeaders v)
  have harity : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length = arity b := by
    simpa only [queryHeaders, Matrix.cons_val_zero, b] using
      BrouwerNashHeaders.arityRuler_length (queryHeaders v)
  have hcopy (t' : Fin 41) (c' : Fin 4) (f' a' : Fin 2) (j' : Fin (b + 1)) :
      (v 0).length = (inputRuler t' c' f' (queryHeaders v)).length +
        a'.val * (b + 1) + j'.val ↔
      t' = t ∧ c' = corner ∧ f' = flag ∧ a' = axis ∧ j' = j := by
    rw [hout, hin, hin, eq_comm]
    exact copyPosition_eq_iff b e₀ e₁ t' t c' corner f' flag a' axis j' j
  have hraw (t' : Fin 41) (c' : Fin 4) (f' : Fin 2)
      (j' : Fin (if f'.val = 0 then raw₀ else raw₁).length) :
      (v 0).length ≠ (inputRuler t' c' f' (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j'.val := by
    intro he
    have hl : j'.val < if f'.val = 0 then e₀ else e₁ := by
      rw [hp₀, hp₁]
      by_cases hf : f'.val = 0 <;> simpa only [hf, ite_true, ite_false] using j'.isLt
    let o := (if flag.val = 0 then 0 else arity b + e₀) + axis.val * (b + 1) + j.val
    let o' := (if f'.val = 0 then 0 else arity b + e₀) + arity b + j'.val
    have hpos : sampleBase b e₀ e₁ t + colorBase b +
        corner.val * cornerWidth b e₀ e₁ + o = sampleBase b e₀ e₁ t' + colorBase b +
          c'.val * cornerWidth b e₀ e₁ + o' := by
      rw [hout] at he
      simp only [hin, harity] at he
      change sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag +
        axis.val * (b + 1) + j.val = sampleBase b e₀ e₁ t' +
          colorInput b e₀ e₁ c' f' + arity b + j'.val at he
      dsimp only [o, o', colorInput] at he ⊢
      omega
    have hx := colorPosition_injective b e₀ e₁ t t' corner c' o o'
      (copyOffset_lt b e₀ e₁ flag axis j) (rawOffset_lt b e₀ e₁ f' j'.val hl) hpos
    exact copyOffset_ne_rawOffset b e₀ e₁ flag f' axis j j'.val hl hx.2.2
  rw [coefficientWord_value v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr]
  dsimp only [b] at hcopy
  simp only [hcopy, hraw, ite_false, Finset.sum_const_zero, add_zero, ite_and,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
private theorem rawOffset_injective (b e₀ e₁ : ℕ) (f f' : Fin 2) (j j' : ℕ)
    (hj : j < if f.val = 0 then e₀ else e₁)
    (hj' : j' < if f'.val = 0 then e₀ else e₁)
    (he : (if f.val = 0 then 0 else arity b + e₀) + arity b + j =
      (if f'.val = 0 then 0 else arity b + e₀) + arity b + j') :
    f.val = f'.val ∧ j = j' := by
  fin_cases f <;> fin_cases f' <;> norm_num only [arity] at he hj hj' ⊢ <;>
    simp only [ite_true, ite_false, zero_add] at he hj hj' ⊢ <;>
      (try simp only [true_and]) <;> omega
private theorem rawPosition_eq_iff (b e₀ e₁ : ℕ)
    (t t' : Fin 41) (c c' : Fin 4) (f f' : Fin 2) (j j' : ℕ)
    (hj : j < if f.val = 0 then e₀ else e₁)
    (hj' : j' < if f'.val = 0 then e₀ else e₁) :
    sampleBase b e₀ e₁ t + colorInput b e₀ e₁ c f + arity b + j =
      sampleBase b e₀ e₁ t' + colorInput b e₀ e₁ c' f' + arity b + j' ↔
        t = t' ∧ c = c' ∧ f = f' ∧ j = j' := by
  constructor
  · intro he
    let o := (if f.val = 0 then 0 else arity b + e₀) + arity b + j
    let o' := (if f'.val = 0 then 0 else arity b + e₀) + arity b + j'
    have hpos : sampleBase b e₀ e₁ t + colorBase b + c.val * cornerWidth b e₀ e₁ + o =
        sampleBase b e₀ e₁ t' + colorBase b + c'.val * cornerWidth b e₀ e₁ + o' := by
      dsimp only [o, o', colorInput] at he ⊢
      omega
    have hx := colorPosition_injective b e₀ e₁ t t' c c' o o'
      (rawOffset_lt b e₀ e₁ f j hj) (rawOffset_lt b e₀ e₁ f' j' hj') hpos
    have hs := rawOffset_injective b e₀ e₁ f f' j j' hj hj' hx.2.2
    exact ⟨hx.1, hx.2.1, Fin.ext hs.1, hs.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl
/-- A selected relocated raw gate contributes exactly its canonical coefficient. -/
theorem coefficientWord_eq_raw (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length (circuitUnaryPrefix (v 3)).length
      (circuitUnaryPrefix (v 4)).length * 2)) (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length)
    (hout : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val) :
    binarySignedValue (coefficientWord v) =
      (guardedRaw (((if flag.val = 0 then raw₀ else raw₁)[j.val]).shift
        (inputRuler t corner flag (queryHeaders v)).length)).coefficients r := by
  let b := (pairFst (v 2)).length
  let e₀ := (circuitUnaryPrefix (v 3)).length
  let e₁ := (circuitUnaryPrefix (v 4)).length
  have hp₀ : e₀ = raw₀.length := by
    dsimp [e₀]; rw [hc₀]
    exact circuitUnaryPrefix_rawEncode_length _
  have hp₁ : e₁ = raw₁.length := by
    dsimp [e₁]; rw [hc₁]
    exact circuitUnaryPrefix_rawEncode_length _
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag (queryHeaders v)).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, b, e₀, e₁] using
        inputRuler_length t corner flag (queryHeaders v)
  have harity : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length = arity b := by
    simpa only [queryHeaders, Matrix.cons_val_zero, b] using
      BrouwerNashHeaders.arityRuler_length (queryHeaders v)
  have hlen (f : Fin 2) (l : Fin (if f.val = 0 then raw₀ else raw₁).length) :
      l.val < if f.val = 0 then e₀ else e₁ := by
    rw [hp₀, hp₁]
    by_cases hf : f.val = 0 <;> simpa only [hf, ite_true, ite_false] using l.isLt
  have hcopy (t' : Fin 41) (c' : Fin 4) (f' a' : Fin 2) (j' : Fin (b + 1)) :
      (v 0).length ≠ (inputRuler t' c' f' (queryHeaders v)).length +
        a'.val * (b + 1) + j'.val := by
    intro he
    let o := (if f'.val = 0 then 0 else arity b + e₀) + a'.val * (b + 1) + j'.val
    let o' := (if flag.val = 0 then 0 else arity b + e₀) + arity b + j.val
    have hpos : sampleBase b e₀ e₁ t' + colorBase b +
        c'.val * cornerWidth b e₀ e₁ + o = sampleBase b e₀ e₁ t + colorBase b +
          corner.val * cornerWidth b e₀ e₁ + o' := by
      rw [hout] at he
      simp only [hin, harity] at he
      change sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag + arity b + j.val =
        sampleBase b e₀ e₁ t' + colorInput b e₀ e₁ c' f' + a'.val * (b + 1) + j'.val at he
      dsimp only [o, o', colorInput] at he ⊢
      omega
    have hx := colorPosition_injective b e₀ e₁ t' t c' corner o o'
      (copyOffset_lt b e₀ e₁ f' a' j') (rawOffset_lt b e₀ e₁ flag j.val (hlen flag j)) hpos
    exact copyOffset_ne_rawOffset b e₀ e₁ f' flag a' j' j.val (hlen flag j) hx.2.2
  have hraw (t' : Fin 41) (c' : Fin 4) (f' : Fin 2)
      (j' : Fin (if f'.val = 0 then raw₀ else raw₁).length) :
      (v 0).length = (inputRuler t' c' f' (queryHeaders v)).length +
        (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j'.val ↔
      t' = t ∧ c' = corner ∧ f' = flag ∧ j'.val = j.val := by
    rw [hout, hin, hin, harity, eq_comm]
    exact rawPosition_eq_iff b e₀ e₁ t' t c' corner f' flag j'.val j.val
      (hlen f' j') (hlen flag j)
  rw [coefficientWord_value v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr]
  dsimp only [b] at hcopy
  simp only [hcopy, hraw, ite_false, Finset.sum_const_zero, zero_add, ite_and,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_inj]
private theorem coefficientWord_eq_copy_lengths (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (e₀ e₁ : ℕ)
    (he₀ : (circuitUnaryPrefix (v 3)).length = e₀)
    (he₁ : (circuitUnaryPrefix (v 4)).length = e₁)
    (r : Fin (dimension (pairFst (v 2)).length e₀
      e₁ * 2)) (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag axis : Fin 2)
    (j : Fin ((pairFst (v 2)).length + 1))
    (hout : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      axis.val * ((pairFst (v 2)).length + 1) + j.val) :
    binarySignedValue (coefficientWord v) =
      (affine₂ (cornerBit (pairFst (v 2)).length e₀
        e₁ t corner axis j.val)
        (slot (pairFst (v 2)).length e₀
          e₁ zero)
        (2 * (dimension (pairFst (v 2)).length e₀
          e₁ : ℤ)) 0 0).coefficients r := by
  subst e₀ e₁
  exact coefficientWord_eq_copy v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner flag axis j hout
private theorem coefficientWord_eq_raw_lengths (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (e₀ e₁ : ℕ)
    (he₀ : (circuitUnaryPrefix (v 3)).length = e₀)
    (he₁ : (circuitUnaryPrefix (v 4)).length = e₁)
    (r : Fin (dimension (pairFst (v 2)).length e₀
      e₁ * 2)) (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length)
    (hout : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
      (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val) :
    binarySignedValue (coefficientWord v) =
      (guardedRaw (((if flag.val = 0 then raw₀ else raw₁)[j.val]).shift
        (inputRuler t corner flag (queryHeaders v)).length)).coefficients r := by
  subst e₀ e₁
  exact coefficientWord_eq_raw v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner flag j hout
/-- The canonical color kind depends only on the parsed raw circuit lengths. -/
theorem kindWord_eq_colorRegion_of_lengths (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (he₀ : (circuitUnaryPrefix (v 3)).length = raw₀.length)
    (he₁ : (circuitUnaryPrefix (v 4)).length = raw₁.length)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (pairFst (v 2)).length raw₀.length raw₁.length)
    (hout : (v 0).length = sampleBase (pairFst (v 2)).length raw₀.length raw₁.length t +
      colorBase (pairFst (v 2)).length +
        corner.val * cornerWidth (pairFst (v 2)).length raw₀.length raw₁.length + offset) :
    kindWord v = [decide ((colorRegionGate (pairFst (v 2)).length
      raw₀ raw₁ t corner offset).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  have hin (t : Fin 41) (c : Fin 4) (f : Fin 2) :
      (inputRuler t c f (queryHeaders v)).length =
        sampleBase (pairFst (v 2)).length raw₀.length raw₁.length t +
          colorInput (pairFst (v 2)).length raw₀.length raw₁.length c f := by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, he₀, he₁] using inputRuler_length t c f (queryHeaders v)
  have ha : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length =
      arity (pairFst (v 2)).length := by
    simpa only [queryHeaders, Matrix.cons_val_zero] using
      BrouwerNashHeaders.arityRuler_length (queryHeaders v)
  rw [kindWord_value]
  simp only [hin, ha, rawCode, apply_ite, he₀, he₁]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  refine Iff.trans ?_ ((rawIntervals_iff (pairFst (v 2)).length raw₀.length raw₁.length
    (v 0).length t corner offset ho hout).trans
      (colorRegionGate_comparator_iff (pairFst (v 2)).length raw₀ raw₁ hw₀ hw₁
        t corner offset ho).symm)
  apply exists_congr; intro sample
  apply exists_congr; intro vertex
  apply exists_congr; intro flag
  by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false]
private theorem coefficientWord_eq_copyOffset (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length raw₀.length raw₁.length * 2))
    (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (offset : ℕ)
    (ho : offset < arity (pairFst (v 2)).length)
    (hout : (v 0).length = (inputRuler t corner flag (queryHeaders v)).length + offset) :
    binarySignedValue (coefficientWord v) =
      (affine₂ (cornerBit (pairFst (v 2)).length raw₀.length raw₁.length t corner
        ⟨(offset / ((pairFst (v 2)).length + 1)) % 2, Nat.mod_lt _ (by decide)⟩
        (offset % ((pairFst (v 2)).length + 1)))
        (slot (pairFst (v 2)).length raw₀.length raw₁.length zero)
        (2 * (dimension (pairFst (v 2)).length raw₀.length raw₁.length : ℤ)) 0 0).coefficients r
          := by
  let b := (pairFst (v 2)).length
  let axis : Fin 2 := ⟨(offset / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩
  let j : Fin (b + 1) := ⟨offset % (b + 1), Nat.mod_lt _ (by omega)⟩
  have hq : offset / (b + 1) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    change offset < 2 * (b + 1) at ho
    omega
  have hqr : axis.val * (b + 1) + j.val = offset := by
    dsimp only [axis, j]
    rw [Nat.mod_eq_of_lt hq, Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have hp₀ : (circuitUnaryPrefix (v 3)).length = raw₀.length := by
    rw [hc₀]
    exact circuitUnaryPrefix_rawEncode_length _
  have hp₁ : (circuitUnaryPrefix (v 4)).length = raw₁.length := by
    rw [hc₁]
    exact circuitUnaryPrefix_rawEncode_length _
  apply coefficientWord_eq_copy_lengths v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
    raw₀.length raw₁.length hp₀ hp₁ r hr t corner flag axis j
  change (v 0).length = (inputRuler t corner flag (queryHeaders v)).length +
    axis.val * (b + 1) + j.val
  rw [add_assoc, hqr]
  exact hout
/-- At an allocated color output, the scalar query equals the canonical gate coefficient. -/
theorem coefficientWord_eq_colorRegion (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length raw₀.length raw₁.length * 2))
    (hr : (v 1).length = r.val)
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (pairFst (v 2)).length raw₀.length raw₁.length)
    (hout : (v 0).length = sampleBase (pairFst (v 2)).length raw₀.length raw₁.length t +
      colorBase (pairFst (v 2)).length + corner.val *
        cornerWidth (pairFst (v 2)).length raw₀.length raw₁.length + offset) :
    binarySignedValue (coefficientWord v) =
      (colorRegionGate (pairFst (v 2)).length raw₀ raw₁ t corner offset).coefficients r := by
  let b := (pairFst (v 2)).length
  have hp₀ : (circuitUnaryPrefix (v 3)).length = raw₀.length := by
    rw [hc₀]
    exact circuitUnaryPrefix_rawEncode_length _
  have hp₁ : (circuitUnaryPrefix (v 4)).length = raw₁.length := by
    rw [hc₁]
    exact circuitUnaryPrefix_rawEncode_length _
  have hin (flag : Fin 2) : (inputRuler t corner flag (queryHeaders v)).length =
      sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner flag :=
        by
    simpa only [queryHeaders, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, b, hp₀, hp₁] using
        inputRuler_length t corner flag (queryHeaders v)
  have ha : (BrouwerNashHeaders.arityRuler (queryHeaders v)).length = arity b := by
    simpa only [queryHeaders, Matrix.cons_val_zero, b] using
      BrouwerNashHeaders.arityRuler_length (queryHeaders v)
  by_cases h₀ : offset < arity b
  · have he := colorRegionGate_copy b raw₀ raw₁ t corner 0 offset h₀
    simp only [Fin.val_zero, ite_true, zero_add] at he
    rw [he]
    apply coefficientWord_eq_copyOffset v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner 0 offset h₀
    rw [hin, colorInput]
    simp only [Fin.val_zero, ite_true]
    change (v 0).length = sampleBase b raw₀.length raw₁.length t + colorBase b +
      corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
    omega
  · by_cases h₁ : offset < arity b + raw₀.length
    · let j : Fin raw₀.length := ⟨offset - arity b, by omega⟩
      have he := colorRegionGate_raw₀ b raw₀ raw₁ t corner j
      have hj : arity b + j.val = offset := by dsimp only [j]; omega
      rw [hj] at he
      rw [he]
      have hh := coefficientWord_eq_raw_lengths v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
        raw₀.length raw₁.length hp₀ hp₁ r hr t corner 0 j
      have houtput : (v 0).length = (inputRuler t corner 0 (queryHeaders v)).length +
          (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val := by
        rw [hin, ha, colorInput]
        simp only [Fin.val_zero, ite_true]
        dsimp only [j]
        change (v 0).length = sampleBase b raw₀.length raw₁.length t + colorBase b +
          corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
        omega

      rw [hin] at houtput
      simp only [hin, Fin.val_zero, ite_true] at hh
      exact hh houtput
    · by_cases h₂ : offset < 2 * arity b + raw₀.length
      · let j := offset - (arity b + raw₀.length)
        have hj : j < arity b := by dsimp only [j]; omega
        have he := colorRegionGate_copy b raw₀ raw₁ t corner 1 j hj
        simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at he
        have heq : arity b + raw₀.length + j = offset := by dsimp only [j]; omega
        rw [heq] at he
        rw [he]
        apply coefficientWord_eq_copyOffset v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner 1 j hj
        rw [hin, colorInput]
        simp only [Fin.val_one, Nat.one_ne_zero, ite_false]
        dsimp only [j]
        change (v 0).length = sampleBase b raw₀.length raw₁.length t + colorBase b +
          corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
        omega
      · let j : Fin raw₁.length := ⟨offset - (2 * arity b + raw₀.length), by
          change offset < 2 * arity b + raw₀.length + raw₁.length at ho
          omega⟩
        have he := colorRegionGate_raw₁ b raw₀ raw₁ t corner j
        have hj : 2 * arity b + raw₀.length + j.val = offset := by dsimp only [j]; omega
        rw [hj] at he
        rw [he]
        have hh := coefficientWord_eq_raw_lengths v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
          raw₀.length raw₁.length hp₀ hp₁ r hr t corner 1 j
        have houtput : (v 0).length = (inputRuler t corner 1 (queryHeaders v)).length +
            (BrouwerNashHeaders.arityRuler (queryHeaders v)).length + j.val := by
          rw [hin, ha, colorInput]
          simp only [Fin.val_one, Nat.one_ne_zero, ite_false]
          dsimp only [j]
          change (v 0).length = sampleBase b raw₀.length raw₁.length t + colorBase b +
            corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
          omega

        rw [hin] at houtput
        simp only [hin, Fin.val_one, Nat.one_ne_zero, ite_false] at hh
        exact hh houtput
/-- The scalar color query agrees with any allocated color gate of the sample program. -/
theorem coefficientWord_eq_sampleGate (v : Fin 5 → List Bool)
    (raw₀ raw₁ : _root_.Complexity.CircuitCode.RawCircuit)
    (hc₀ : v 3 = raw₀.encode) (hc₁ : v 4 = raw₁.encode)
    (hw₀ : raw₀.WellFormed (arity (pairFst (v 2)).length))
    (hw₁ : raw₁.WellFormed (arity (pairFst (v 2)).length))
    (r : Fin (dimension (pairFst (v 2)).length raw₀.length raw₁.length * 2))
    (hr : (v 1).length = r.val) (t : Fin 41) (offset : ℕ)
    (hlo : colorBase (pairFst (v 2)).length ≤ offset)
    (hhi : offset < minimumBase (pairFst (v 2)).length raw₀.length raw₁.length)
    (hout : (v 0).length = sampleBase (pairFst (v 2)).length raw₀.length raw₁.length t + offset) :
    binarySignedValue (coefficientWord v) =
      (sampleGate (pairFst (v 2)).length raw₀ raw₁ t offset).coefficients r := by
  let b := (pairFst (v 2)).length
  let w := cornerWidth b raw₀.length raw₁.length
  have hw : 0 < w := by dsimp only [w, cornerWidth, arity]; omega
  have hb : (offset - colorBase b) / w < 4 := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    change offset < colorBase b + 4 * w at hhi
    omega
  let corner : Fin 4 := ⟨(offset - colorBase b) / w, hb⟩
  let localOffset := (offset - colorBase b) % w
  have hl : localOffset < cornerWidth b raw₀.length raw₁.length := Nat.mod_lt _ hw
  have he : colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length + localOffset =
    offset := by
    have hrec := Nat.div_add_mod (offset - colorBase b) w
    rw [Nat.mul_comm] at hrec
    dsimp only [corner, localOffset, w] at hrec ⊢
    change colorBase b ≤ offset at hlo
    omega
  have hg := sampleGate_colorRegion b raw₀ raw₁ t corner localOffset hl
  rw [he] at hg
  rw [hg]
  apply coefficientWord_eq_colorRegion v raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner localOffset hl
  change (v 0).length = sampleBase b raw₀.length raw₁.length t + offset at hout
  change (v 0).length = sampleBase b raw₀.length raw₁.length t + colorBase b +
    corner.val * cornerWidth b raw₀.length raw₁.length + localOffset
  omega
end GameTheory.Complexity.Backend.BrouwerNashColorQuery
