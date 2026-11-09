module

public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BrouwerNashProgram
public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BinarySignedIndicator
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding
public import GameTheoryComplexity.Backend.BinaryIndexedLookup
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum
public import GameTheoryComplexity.Backend.BimatrixRawGateMachine
public import GameTheoryComplexity.Backend.CircuitCodeShiftCorrectness

@[expose] public section
/-!
# Executable coefficient and kind queries for corner color circuits

The query scans copied coordinate wires and relocated raw gates in the canonical
Brouwer game program. Fixed sample and corner families are composed explicitly;
variable gate and digit ordinals use length-controlled indexed lookup.
-/

namespace GameTheory.Complexity.Backend.BrouwerNashColorQuery
open Cslib.Circuits Turing.MultiTapeTM
open BrouwerNashLayout BrouwerNashProgram

local notation "QueryContext" => ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool))
local notation "queryEncoding" => encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)

private def scale (n : ℕ) (r : List Bool) : List Bool := List.replicate (r.length * n) true

private def base (t : Fin 41) (source code₀ code₁ : List Bool) : List Bool :=
  BrouwerNashHeaders.globalRuler source ++
    scale t.val (BrouwerNashHeaders.sampleRuler source code₀ code₁)

/-- Absolute source wire for one copied corner digit. -/
def cornerBitRuler (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (ordinal source code₀ code₁ : List Bool) : List Bool :=
  let b := BrouwerNashHeaders.sourceDepthRuler source
  let scale (n : ℕ) (r : List Bool) := List.replicate (r.length * n) true
  let start := BrouwerNashHeaders.globalRuler source ++
    scale t.val (BrouwerNashHeaders.sampleRuler source code₀ code₁)
  let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3
  if upper then
    if ordinal.length = b.length then
      if b.length = 0 then [false, false]
      else start ++ [false, false] ++ scale 4 b ++ scale (4 * axis.val) b ++
        scale 4 b.tail ++ [false, false, false]
    else start ++ [false, false] ++ scale 4 b ++ scale (4 * axis.val) b ++
      scale 4 ordinal ++ [false, false]
  else if ordinal.length = b.length then [false, false, false]
    else start ++ [false, false] ++ scale (2 * axis.val) b ++
      scale 2 ((b.drop ordinal.length).tail)

private theorem scale_polyTime (n : ℕ) {Input : Type} {input : Input ↪ List Bool}
    {ruler : Input → List Bool} (hr : ComputableInPolyTime ruler input encBits) :
    ComputableInPolyTime (fun a => scale n (ruler a)) input encBits :=
  (ComputableInPolyTime.bitsReplicate true).comp
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hr)
      (ComputableInPolyTime.const n))

private theorem base_polyTime (t : Fin 41) {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => base t (source a) (code₀ a) (code₁ a)) input encBits :=
  ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.globalRuler_polyTime hs)
    (scale_polyTime t.val (BrouwerNashHeaders.sampleRuler_polyTime hs h₀ h₁))

theorem cornerBitRuler_polyTime (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {ordinal source code₀ code₁ : Input → List Bool}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => cornerBitRuler t corner axis (ordinal a) (source a)
      (code₀ a) (code₁ a)) input encBits := by
  have hb := BrouwerNashHeaders.sourceDepthRuler_polyTime hs
  have hstart := base_polyTime t hs h₀ h₁
  have heq := (ComputableInPolyTime.length_bits_comp hi).decide_eq'
    (ComputableInPolyTime.length_bits_comp hb)
  have hempty := (ComputableInPolyTime.length_bits_comp hb).decide_eq'
    (ComputableInPolyTime.const 0)
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hb
  have hdrop := ComputableInPolyTime.bitsDropWithInput hb (ComputableInPolyTime.length_bits_comp hi)
  have hdropTail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hdrop
  have hupper := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend hstart (ComputableInPolyTime.const [false,false]))
      (scale_polyTime 4 hb)) (scale_polyTime (4 * axis.val) hb)
  have hlast := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hupper (scale_polyTime 4 htail))
    (ComputableInPolyTime.const [false,false,false])
  have hnext := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hupper (scale_polyTime 4 hi))
    (ComputableInPolyTime.const [false,false])
  have hlower := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend hstart (ComputableInPolyTime.const [false,false]))
      (scale_polyTime (2 * axis.val) hb)) (scale_polyTime 2 hdropTail)
  unfold cornerBitRuler
  dsimp only
  by_cases hu : (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3)
  · simp only [hu, ite_true]
    exact (heq.ite
      (hempty.ite (ComputableInPolyTime.const [false, false]) hlast) hnext).of_enc_eq
      (fun a => by simp only [decide_eq_true_eq, base, scale, Function.comp_apply])
  · simp only [hu, ite_false]
    exact (heq.ite (ComputableInPolyTime.const [false, false, false]) hlower).of_enc_eq
      (fun a => by simp only [decide_eq_true_eq, base, scale, Function.comp_apply])

private theorem base_length (t : Fin 41) (source code₀ code₁ : List Bool) :
    (base t source code₀ code₁).length = sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t := by
  simp only [base, List.length_append, scale, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    sampleBase]
  ring

private theorem cornerBitRuler_length_formula (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (ordinal source code₀ code₁ : List Bool) :
    let b := (CircuitWords.first source).length
    let ell₀ := (circuitUnaryPrefix code₀).length
    let ell₁ := (circuitUnaryPrefix code₁).length
    let j := ordinal.length
    let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
      else corner.val = 1 ∨ corner.val = 3
    (cornerBitRuler t corner axis ordinal source code₀ code₁).length =
      if upper then
        if j = b then if b = 0 then one
          else sampleBase b ell₀ ell₁ t + increment b axis (b - 1) 3
        else sampleBase b ell₀ ell₁ t + increment b axis j 2
      else if j = b then zero
        else sampleBase b ell₀ ell₁ t + primaryBit b axis j := by
  have hbase := base_length t source code₀ code₁
  simp only [base, List.length_append, scale, List.length_replicate, Nat.mul_comm] at hbase
  dsimp only
  unfold cornerBitRuler
  dsimp only
  simp only [List.length_tail, List.length_drop, BrouwerNashHeaders.sourceDepthRuler_length]
  split_ifs <;>
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      increment, incrementBase, primaryBit, digit, zero, one, Nat.mul_comm, Nat.mul_assoc] <;> omega

/-- The copied source ruler is the exact canonical corner reference on allocated digits. -/
theorem cornerBitRuler_length (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (ordinal source code₀ code₁ : List Bool) (hj : ordinal.length ≤ (CircuitWords.first source).length) :
    (cornerBitRuler t corner axis ordinal source code₀ code₁).length =
      (cornerBit (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
        (circuitUnaryPrefix code₁).length t corner axis ordinal.length).val := by
  let b := (CircuitWords.first source).length
  let e₀ := (circuitUnaryPrefix code₀).length
  let e₁ := (circuitUnaryPrefix code₁).length
  let j := ordinal.length
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

/-- Absolute copied-input offset for one compiled corner-color flag. -/
def inputRuler (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (source code₀ code₁ : List Bool) : List Bool :=
  let scale (n : ℕ) (r : List Bool) := List.replicate (r.length * n) true
  BrouwerNashHeaders.globalRuler source ++ scale t.val (BrouwerNashHeaders.sampleRuler source code₀ code₁) ++
    List.replicate 10 false ++ scale 12 (BrouwerNashHeaders.sourceDepthRuler source) ++
    scale corner.val (BrouwerNashHeaders.cornerRuler source code₀ code₁) ++
    (if flag.val = 0 then [] else BrouwerNashHeaders.arityRuler source ++ circuitUnaryPrefix code₀)

theorem inputRuler_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source code₀ code₁ : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits) :
    ComputableInPolyTime (fun a => inputRuler t corner flag (source a) (code₀ a) (code₁ a))
      input encBits := by
  have hstart := base_polyTime t hs h₀ h₁
  have hprefix := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend hstart (ComputableInPolyTime.const (List.replicate 10 false)))
      (scale_polyTime 12 (BrouwerNashHeaders.sourceDepthRuler_polyTime hs)))
    (scale_polyTime corner.val (BrouwerNashHeaders.cornerRuler_polyTime hs h₀ h₁))
  unfold inputRuler
  dsimp only
  by_cases h : flag.val = 0
  · simp only [h, ite_true]
    exact ComputableInPolyTime.bitsAppend hprefix (ComputableInPolyTime.const [])
  · simp only [h, ite_false]
    exact ComputableInPolyTime.bitsAppend hprefix (ComputableInPolyTime.bitsAppend
      (BrouwerNashHeaders.arityRuler_polyTime hs) (circuitUnaryPrefix_polyTime h₀))

@[simp] theorem inputRuler_length (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (source code₀ code₁ : List Bool) :
    (inputRuler t corner flag source code₀ code₁).length =
      sampleBase (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
        (circuitUnaryPrefix code₁).length t +
      colorInput (CircuitWords.first source).length (circuitUnaryPrefix code₀).length
        (circuitUnaryPrefix code₁).length corner flag := by
  simp only [inputRuler, List.length_append, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length,
    BrouwerNashHeaders.cornerRuler_length, BrouwerNashHeaders.sourceDepthRuler_length,
    sampleBase, colorInput, colorBase, weightBase]
  split <;> simp only [List.length_nil, List.length_append,
    BrouwerNashHeaders.arityRuler_length] <;> ring

private def rawCode (flag : Fin 2) (context : QueryContext) : List Bool :=
  if flag.val = 0 then context.1.2.1 else context.1.2.2

private theorem rawCode_polyTime (flag : Fin 2) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => rawCode flag (context a)) input encBits := by
  by_cases h : flag.val = 0
  · simpa only [rawCode, h, ite_true] using hc.fst'.snd'.fst'
  · simpa only [rawCode, h, ite_false] using hc.fst'.snd'.snd'

private def rawTest (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (ordinal : List Bool) (context : QueryContext) : List Bool :=
  [decide (context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
    BrouwerNashHeaders.arityRuler context.1.1 ++ ordinal).length)]

/-- Query one parsed raw gate after relocating its two actual references. -/
def indexedRawCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (ordinal : List Bool) (context : QueryContext) : List Bool :=
  BimatrixRawGateMachine.selectedShiftedCoefficientWord
    (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2)
    (if flag.val = 0 then context.1.2.1 else context.1.2.2) ordinal
    (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2) context.2.2

private theorem rawTest_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {ordinal : Input → List Bool}
    {context : Input → QueryContext} (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => rawTest t corner flag (ordinal a) (context a)) input encBits :=
  ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.length_bits_comp hc.snd'.fst').decide_eq'
      (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend (inputRuler_polyTime t corner flag hc.fst'.fst'
          hc.fst'.snd'.fst' hc.fst'.snd'.snd')
          (BrouwerNashHeaders.arityRuler_polyTime hc.fst'.fst')) hi))) (ComputableInPolyTime.const [])

theorem indexedRawCoefficientWord_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {ordinal : Input → List Bool}
    {context : Input → QueryContext} (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => indexedRawCoefficientWord t corner flag (ordinal a) (context a))
      input encBits :=
  BimatrixRawGateMachine.selectedShiftedCoefficientWord_polyTime
    (BrouwerNashHeaders.dimensionRuler_polyTime hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd')
    (rawCode_polyTime flag hc) hi
    (inputRuler_polyTime t corner flag hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd') hc.snd'.snd'

/-- Bounded lookup retains the serialized gate-count ruler, including malformed-code behavior. -/
def rawCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (source code₀ code₁ out action : List Bool) : List Bool :=
  let test (ordinal : List Bool) (context : QueryContext) : List Bool :=
    [decide (context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
      BrouwerNashHeaders.arityRuler context.1.1 ++ ordinal).length)]
  binaryIndexedLookup test (indexedRawCoefficientWord t corner flag)
    (circuitUnaryPrefix (if flag.val = 0 then code₀ else code₁))
    (BrouwerNashHeaders.widthRuler source code₀ code₁) ((source, (code₀, code₁)), (out, action))

private theorem rawCoefficientWord_eq (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) :
    rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2 =
      binaryIndexedLookup (rawTest t corner flag) (indexedRawCoefficientWord t corner flag)
        (circuitUnaryPrefix (rawCode flag context))
        (BrouwerNashHeaders.widthRuler context.1.1 context.1.2.1 context.1.2.2) context := rfl

theorem rawCoefficientWord_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => rawCoefficientWord t corner flag (source a) (code₀ a) (code₁ a)
      (out a) (action a)) input encBits := by
  have hc := (hs.prod (h₀.prod h₁)).prod (ho.prod ha)
  have htest := rawTest_polyTime t corner flag
    (ComputableInPolyTime.snd queryEncoding encBits) (ComputableInPolyTime.fst queryEncoding encBits)
  have hterm := indexedRawCoefficientWord_polyTime t corner flag
    (ComputableInPolyTime.snd queryEncoding encBits) (ComputableInPolyTime.fst queryEncoding encBits)
  exact (binaryIndexedLookup_polyTime htest hterm
    (circuitUnaryPrefix_polyTime (rawCode_polyTime flag hc))
    (BrouwerNashHeaders.widthRuler_polyTime hs h₀ h₁) hc).of_enc_eq
    (fun a => congrArg encBits (rawCoefficientWord_eq t corner flag
      ((source a, (code₀ a, code₁ a)), (out a, action a))))

private theorem rawTest_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) (ordinal : List Bool) :
    rawTest t corner flag ordinal context = [decide (context.2.1.length =
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length + ordinal.length)] := by
  simp only [rawTest, List.length_append]

/-- Every nonmatching output returns zero, including malformed serialized circuits. -/
theorem rawCoefficientWord_value_zero (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext)
    (hno : ∀ i < (circuitUnaryPrefix (if flag.val = 0 then context.1.2.1 else context.1.2.2)).length,
      context.2.1.length ≠ (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length + i) :
    binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2
      context.2.1 context.2.2) = 0 := by
  rw [rawCoefficientWord_eq]
  apply binaryIndexedLookup_value_zero
    (rawTest t corner flag) (indexedRawCoefficientWord t corner flag) _ _ context
  intro ordinal hi
  rw [rawTest_value]
  simp only [hno ordinal.length hi, decide_false]

/-- At an allocated checked gate, the bounded query returns both relocated coefficients. -/
theorem rawCoefficientWord_value_at (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) (gates : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature
      (BrouwerNashHeaders.arityRuler context.1.1).length 0 gates)
    (hcode : (if flag.val = 0 then context.1.2.1 else context.1.2.2) = CircuitFormat.encode gates)
    (j : Fin gates.length)
    (ho : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length + j.val)
    (href : Program.IsCodeFrom CircuitFormat.signature
      (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length 0
      [(gates[j.val].1, gates[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·))])
    (r : Fin ((BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length * 2))
    (hr : context.2.2.length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2
      context.2.1 context.2.2) = BimatrixRawGate.coefficients
      (gates[j.val].1, gates[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)) href r := by
  have harity : ∀ gate ∈ gates, gate.2.length = 2 := by
    intro gate hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    exact (hraw.getElem i hi).1
  let offset := inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2
  let dimension := BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2
  let z := BimatrixRawGate.coefficients (gates[j.val].1, gates[j.val].2.map (offset.length + ·)) href r
  let hit := fun i => decide (context.2.1.length = offset.length +
    (BrouwerNashHeaders.arityRuler context.1.1).length + i)
  have hterm (ordinal : List Bool) (hh : hit ordinal.length = true) :
      binarySignedValue (indexedRawCoefficientWord t corner flag ordinal context) = z := by
    have hi : ordinal.length = j.val := by
      have he : context.2.1.length = offset.length +
          (BrouwerNashHeaders.arityRuler context.1.1).length + ordinal.length := of_decide_eq_true hh
      have ho' : context.2.1.length = offset.length +
          (BrouwerNashHeaders.arityRuler context.1.1).length + j.val := ho
      omega
    unfold indexedRawCoefficientWord
    rw [hcode]
    have hf : Program.IsCodeFrom CircuitFormat.signature dimension.length 0
        [(gates[ordinal.length].1, gates[ordinal.length].2.map (offset.length + ·))] := by
      simpa only [hi, offset, dimension] using href
    have he := BimatrixRawGateMachine.selectedShiftedCoefficientWord_encode dimension context.2.2 ordinal
      offset gates harity (by rw [hi]; exact j.isLt) hf r hr
    simpa only [hi, offset, dimension, z] using he
  have hk := BrouwerNashHeaders.dimensionRuler_pos context.1.1 context.1.2.1 context.1.2.2
  have hz : z.natAbs ≤ 100 * dimension.length := by
    have ha := BimatrixRawGate.coefficients_bound
      (gates[j.val].1, gates[j.val].2.map (offset.length + ·)) href r
    have he : |z| ≤ (100 : ℤ) * dimension.length := by
      dsimp only [z]
      have hkz : (1 : ℤ) ≤ dimension.length := by exact_mod_cast hk
      linarith
    apply (Nat.cast_le (α := ℤ)).mp
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] using he
  rw [rawCoefficientWord_eq]
  have he := binaryIndexedLookup_value (rawTest t corner flag) (indexedRawCoefficientWord t corner flag)
    (BrouwerNashHeaders.widthRuler context.1.1 context.1.2.1 context.1.2.2) context hit z
    (fun ordinal => rawTest_value t corner flag context ordinal) hterm
    (by rw [BrouwerNashHeaders.widthRuler_length]; omega)
    (BrouwerNashHeaders.widthRuler_fits context.1.1 context.1.2.1 context.1.2.2 z hz)
    (circuitUnaryPrefix (rawCode flag context))
  have hex : ∃ i < (circuitUnaryPrefix (rawCode flag context)).length, hit i = true := by
    refine ⟨j.val, ?_, decide_eq_true ho⟩
    change j.val < (circuitUnaryPrefix (if flag.val = 0 then context.1.2.1 else context.1.2.2)).length
    rw [hcode, circuitUnaryPrefix_encode_length gates harity]
    exact j.isLt
  rw [ite_eq_left hex] at he
  exact he

private def scalarWord (context : QueryContext) : List Bool :=
  [false, false] ++ binaryLengthWord
    (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2)

private theorem scalarWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => scalarWord (context a)) input encBits := by
  have hcert := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false,false])
    (binaryLengthWord_polyTime.comp (BrouwerNashHeaders.dimensionRuler_polyTime
      hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'))
  simpa only [scalarWord, Function.comp_apply] using hcert

private theorem scalarWord_value (context : QueryContext) :
    binarySignedValue (scalarWord context) =
      2 * ((BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length : ℤ) := by
  simp only [scalarWord, List.cons_append, List.nil_append, binarySignedValue,
    List.headD_cons, Bool.false_eq_true, ite_false, List.tail_cons]
  have hbits (bits : List Bool) : ofBits (false :: bits) = 2 * ofBits bits := by
    simp only [ofBits, List.foldr_cons, Nat.bit_val, Bool.toNat_false, add_zero]
  rw [hbits, binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private def copyTest (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (ordinal : List Bool) (context : QueryContext) : List Bool :=
  [decide (context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
    scale axis.val (BrouwerNashHeaders.sourceDepthRuler context.1.1 ++ [false]) ++ ordinal).length)]

/-- A copied input contributes its signed indicator at the exact corner source wire. -/
def indexedCopyCoefficientWord (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    (ordinal : List Bool) (context : QueryContext) : List Bool :=
  binarySignedIndicator ![context.2.2,
    cornerBitRuler t corner axis ordinal context.1.1 context.1.2.1 context.1.2.2,
    [false,false] ++ binaryLengthWord
      (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2)]

private theorem copyTest_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {ordinal : Input → List Bool}
    {context : Input → QueryContext} (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => copyTest t corner flag axis (ordinal a) (context a)) input encBits :=
  ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.length_bits_comp hc.snd'.fst').decide_eq'
      (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend (inputRuler_polyTime t corner flag hc.fst'.fst'
          hc.fst'.snd'.fst' hc.fst'.snd'.snd')
          (scale_polyTime axis.val (ComputableInPolyTime.bitsAppend
            (BrouwerNashHeaders.sourceDepthRuler_polyTime hc.fst'.fst')
            (ComputableInPolyTime.const [false])))) hi))) (ComputableInPolyTime.const [])

theorem indexedCopyCoefficientWord_polyTime (t : Fin 41) (corner : Fin 4) (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {ordinal : Input → List Bool}
    {context : Input → QueryContext} (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => indexedCopyCoefficientWord t corner axis (ordinal a) (context a))
      input encBits := by
  have hargs : ComputableInPolyTime (fun a : Input => ![(context a).2.2,
      cornerBitRuler t corner axis (ordinal a) (context a).1.1 (context a).1.2.1 (context a).1.2.2,
      scalarWord (context a)]) input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hc.snd'.snd'
    · exact cornerBitRuler_polyTime t corner axis hi hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'
    · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero'] using scalarWord_polyTime hc
  exact binarySignedIndicator_polyTime.comp hargs

/-- Scan the original extended coordinate ruler for a copied-input coefficient. -/
def copyCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (source code₀ code₁ out action : List Bool) : List Bool :=
  let test (ordinal : List Bool) (context : QueryContext) : List Bool :=
    [decide (context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
      List.replicate ((BrouwerNashHeaders.sourceDepthRuler context.1.1 ++ [false]).length * axis.val) true ++
      ordinal).length)]
  binaryIndexedLookup test (indexedCopyCoefficientWord t corner axis)
    (BrouwerNashHeaders.sourceDepthRuler source ++ [false])
    (BrouwerNashHeaders.widthRuler source code₀ code₁) ((source,(code₀,code₁)),(out,action))

private theorem copyCoefficientWord_eq (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (context : QueryContext) :
    copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2 =
      binaryIndexedLookup (copyTest t corner flag axis) (indexedCopyCoefficientWord t corner axis)
        (BrouwerNashHeaders.sourceDepthRuler context.1.1 ++ [false])
        (BrouwerNashHeaders.widthRuler context.1.1 context.1.2.1 context.1.2.2) context := rfl

theorem copyCoefficientWord_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => copyCoefficientWord t corner flag axis (source a) (code₀ a) (code₁ a)
      (out a) (action a)) input encBits := by
  have hc := (hs.prod (h₀.prod h₁)).prod (ho.prod ha)
  have htest := copyTest_polyTime t corner flag axis
    (ComputableInPolyTime.snd queryEncoding encBits) (ComputableInPolyTime.fst queryEncoding encBits)
  have hterm := indexedCopyCoefficientWord_polyTime t corner axis
    (ComputableInPolyTime.snd queryEncoding encBits) (ComputableInPolyTime.fst queryEncoding encBits)
  exact (binaryIndexedLookup_polyTime htest hterm
    (ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.sourceDepthRuler_polyTime hs)
      (ComputableInPolyTime.const [false]))
    (BrouwerNashHeaders.widthRuler_polyTime hs h₀ h₁) hc).of_enc_eq
    (fun a => congrArg encBits (copyCoefficientWord_eq t corner flag axis
      ((source a, (code₀ a, code₁ a)), (out a, action a))))

private theorem copyTest_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (context : QueryContext) (ordinal : List Bool) :
    copyTest t corner flag axis ordinal context = [decide (context.2.1.length =
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        axis.val * ((CircuitWords.first context.1.1).length + 1) + ordinal.length)] := by
  simp only [copyTest, List.length_append, scale, List.length_replicate, List.length_singleton,
    BrouwerNashHeaders.sourceDepthRuler_length]
  rw [Nat.mul_comm ((CircuitWords.first context.1.1).length + 1)]

/-- A copied corner-bit wire has exactly the canonical positive-action coefficient. -/
theorem copyCoefficientWord_value_at (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (context : QueryContext) (j : ℕ) (hj : j ≤ (CircuitWords.first context.1.1).length)
    (ho : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      axis.val * ((CircuitWords.first context.1.1).length + 1) + j) :
    binarySignedValue (copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      if context.2.2.length / 2 = (cornerBit (CircuitWords.first context.1.1).length
          (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length t corner axis j).val ∧
        context.2.2.length % 2 = 1
      then 2 * ((BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length : ℤ) else 0 := by
  let input := cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
    (circuitUnaryPrefix context.1.2.2).length t corner axis j
  let z : ℤ := if context.2.2.length / 2 = input.val ∧ context.2.2.length % 2 = 1
    then 2 * (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length else 0
  let hit := fun i => decide (context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
    axis.val * ((CircuitWords.first context.1.1).length + 1) + i)
  have hterm (ord : List Bool) (hh : hit ord.length = true) :
      binarySignedValue (indexedCopyCoefficientWord t corner axis ord context) = z := by
    have hi : ord.length = j := by have he := of_decide_eq_true hh; omega
    have hc := cornerBitRuler_length t corner axis ord context.1.1 context.1.2.1 context.1.2.2
      (by simpa only [hi] using hj)
    change (cornerBitRuler t corner axis ord context.1.1 context.1.2.1 context.1.2.2).length =
      (cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length t corner axis ord.length).val at hc
    rw [hi] at hc
    change binarySignedValue (binarySignedIndicator ![context.2.2,
      cornerBitRuler t corner axis ord context.1.1 context.1.2.1 context.1.2.2, scalarWord context]) = z
    rw [binarySignedIndicator_value, scalarWord_value, hc]
  have hz : z.natAbs ≤ 100 * (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length := by
    dsimp only [z]
    split
    · simp only [Int.natAbs_mul, Int.natAbs_natCast]
      change 2 * (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length ≤ _
      omega
    · simp only [Int.natAbs_zero]
      omega
  have he := binaryIndexedLookup_value (copyTest t corner flag axis) (indexedCopyCoefficientWord t corner axis)
    (BrouwerNashHeaders.widthRuler context.1.1 context.1.2.1 context.1.2.2) context hit z
    (fun ord => copyTest_value t corner flag axis context ord) hterm
    (by rw [BrouwerNashHeaders.widthRuler_length]; omega)
    (BrouwerNashHeaders.widthRuler_fits context.1.1 context.1.2.1 context.1.2.2 z hz)
    (BrouwerNashHeaders.sourceDepthRuler context.1.1 ++ [false])
  have hex : ∃ i < (BrouwerNashHeaders.sourceDepthRuler context.1.1 ++ [false]).length,
      hit i = true := by
    refine ⟨j, ?_, decide_eq_true ho⟩
    simp only [List.length_append, List.length_singleton,
      BrouwerNashHeaders.sourceDepthRuler_length]
    omega
  rw [ite_eq_left hex] at he
  rw [copyCoefficientWord_eq]
  exact he

/-- Copy queries return zero outside their allocated extended coordinate field. -/
theorem copyCoefficientWord_value_zero (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (axis : Fin 2)
    (context : QueryContext)
    (hno : ∀ j ≤ (CircuitWords.first context.1.1).length, context.2.1.length ≠
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        axis.val * ((CircuitWords.first context.1.1).length + 1) + j) :
    binarySignedValue (copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) = 0 := by
  rw [copyCoefficientWord_eq]
  apply binaryIndexedLookup_value_zero
    (copyTest t corner flag axis) (indexedCopyCoefficientWord t corner axis) _ _ context
  intro ord hi
  rw [copyTest_value]
  have hb : ord.length ≤ (CircuitWords.first context.1.1).length := by
    simp only [List.length_append, List.length_singleton,
      BrouwerNashHeaders.sourceDepthRuler_length] at hi
    change ord.length < (CircuitWords.first context.1.1).length + 1 at hi
    omega
  simp only [hno ord.length hb, decide_false]

private def cornerCoefficientWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) : List Bool :=
  binarySignedAdd
    (copyCoefficientWord t corner flag 0 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)
    (binarySignedAdd
      (copyCoefficientWord t corner flag 1 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)
      (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2))

private theorem cornerCoefficientWord_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => cornerCoefficientWord t corner flag (context a)) input encBits := by
  have hcert := binarySignedAdd_polyTime
    (copyCoefficientWord_polyTime t corner flag 0 hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'
      hc.snd'.fst' hc.snd'.snd')
    (binarySignedAdd_polyTime
      (copyCoefficientWord_polyTime t corner flag 1 hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'
        hc.snd'.fst' hc.snd'.snd')
      (rawCoefficientWord_polyTime t corner flag hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'
        hc.snd'.fst' hc.snd'.snd'))
  simpa only [cornerCoefficientWord, Function.comp_apply] using hcert

/-- Sum all sample, corner and color-flag families in their original nested right-fold order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedQuerySum (List.ofFn (fun t : Fin 41 => fun context : QueryContext =>
    binarySignedQuerySum (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
      binarySignedQuerySum (List.ofFn (fun flag : Fin 2 => fun context : QueryContext =>
        binarySignedAdd
          (copyCoefficientWord t corner flag 0 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)
          (binarySignedAdd
            (copyCoefficientWord t corner flag 1 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)
            (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2))))
        context)) context)) ((source,(code₀,code₁)),(out,action))

private theorem coefficientWord_eq (context : QueryContext) :
    coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2 =
      binarySignedQuerySum (List.ofFn (fun t : Fin 41 => fun context : QueryContext =>
        binarySignedQuerySum (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
          binarySignedQuerySum (List.ofFn (fun flag : Fin 2 => cornerCoefficientWord t corner flag))
            context)) context)) context := rfl

private theorem querySum_ofFn_polyTime {Context Input : Type} {n : ℕ}
    {contextEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    (queries : Fin n → Context → List Bool)
    (hq : ∀ i, ComputableInPolyTime (queries i) contextEncoding encBits)
    {context : Input → Context} (hc : ComputableInPolyTime context input contextEncoding) :
    ComputableInPolyTime (fun a => binarySignedQuerySum (List.ofFn queries) (context a)) input encBits := by
  apply binarySignedQuerySum_polyTime _ _ hc
  intro query h
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact hq i

theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hcert := querySum_ofFn_polyTime
    (fun t : Fin 41 => fun context : QueryContext =>
      binarySignedQuerySum (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
        binarySignedQuerySum (List.ofFn (fun flag : Fin 2 => cornerCoefficientWord t corner flag))
          context)) context)
    (fun t => querySum_ofFn_polyTime _
      (fun corner => querySum_ofFn_polyTime _
        (fun flag => cornerCoefficientWord_polyTime t corner flag ComputableInPolyTime.id')
        ComputableInPolyTime.id') ComputableInPolyTime.id')
    ((hs.prod (h₀.prod h₁)).prod (ho.prod ha))
  exact hcert.of_enc_eq (fun a => congrArg encBits
    (coefficientWord_eq ((source a,(code₀ a,code₁ a)),(out a,action a))))

private def rawKindWord (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) : List Bool :=
  let start := inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
    BrouwerNashHeaders.arityRuler context.1.1
  [decide (start.length ≤ context.2.1.length ∧
    context.2.1.length < (start ++ circuitUnaryPrefix (rawCode flag context)).length)]

private theorem rawKindWord_polyTime (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {context : Input → QueryContext}
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => rawKindWord t corner flag (context a)) input encBits := by
  have hstart := ComputableInPolyTime.bitsAppend (inputRuler_polyTime t corner flag
    hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd') (BrouwerNashHeaders.arityRuler_polyTime hc.fst'.fst')
  have hout := ComputableInPolyTime.length_bits_comp hc.snd'.fst'
  have hle := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_le'
    (ComputableInPolyTime.length_bits_comp hstart).tidy hout.tidy)
  have hlt := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_lt' hout.tidy
    (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.bitsAppend hstart
      (circuitUnaryPrefix_polyTime (rawCode_polyTime flag hc)))).tidy)
  have hcert := ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_and hle hlt)
    (ComputableInPolyTime.const [])
  simpa only [rawKindWord, Function.comp_apply] using hcert

private def orFunctions {Context : Type} (queries : List (Context → List Bool))
    (context : Context) : List Bool :=
  queries.foldr (fun query rest => WordOperations.orFlag (query context) rest) [false]

private theorem orFunctions_polyTime {Context Input : Type}
    {contextEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    (queries : List (Context → List Bool))
    (hq : ∀ query ∈ queries, ComputableInPolyTime query contextEncoding encBits)
    {context : Input → Context} (hc : ComputableInPolyTime context input contextEncoding) :
    ComputableInPolyTime (fun a => orFunctions queries (context a)) input encBits := by
  induction queries with
  | nil => exact ComputableInPolyTime.const [false]
  | cons query queries ih =>
    exact WordOperations.orFlag_polyTime.comp
      (((hq query List.mem_cons_self).comp hc).prod
        (ih (fun q h => hq q (List.mem_cons_of_mem _ h))))

private theorem orFunctions_ofFn_polyTime {Context Input : Type} {n : ℕ}
    {contextEncoding : Context ↪ List Bool} {input : Input ↪ List Bool}
    (queries : Fin n → Context → List Bool)
    (hq : ∀ i, ComputableInPolyTime (queries i) contextEncoding encBits)
    {context : Input → Context} (hc : ComputableInPolyTime context input contextEncoding) :
    ComputableInPolyTime (fun a => orFunctions (List.ofFn queries) (context a)) input encBits := by
  apply orFunctions_polyTime _ _ hc
  intro query h
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact hq i

/-- Comparator kinds cover the raw-circuit intervals; copied input gates are affine. -/
def kindWord (source code₀ code₁ out : List Bool) : List Bool :=
  let combine (queries : List (QueryContext → List Bool)) (context : QueryContext) :=
    queries.foldr (fun query rest => WordOperations.orFlag (query context) rest) [false]
  combine (List.ofFn (fun t : Fin 41 => fun context : QueryContext =>
    combine (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
      combine (List.ofFn (fun flag : Fin 2 => fun context : QueryContext =>
        let start := inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2 ++
          BrouwerNashHeaders.arityRuler context.1.1
        [decide (start.length ≤ context.2.1.length ∧ context.2.1.length <
          (start ++ circuitUnaryPrefix (if flag.val = 0 then context.1.2.1 else context.1.2.2)).length)]))
        context)) context)) ((source,(code₀,code₁)),(out,[]))

private theorem kindWord_eq (source code₀ code₁ out : List Bool) :
    kindWord source code₀ code₁ out =
      orFunctions (List.ofFn (fun t : Fin 41 => fun context : QueryContext =>
        orFunctions (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
          orFunctions (List.ofFn (fun flag : Fin 2 => rawKindWord t corner flag)) context)) context))
        ((source,(code₀,code₁)),(out,[])) := rfl

theorem kindWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => kindWord (source a) (code₀ a) (code₁ a) (out a)) input encBits := by
  have hcert := orFunctions_ofFn_polyTime
    (fun t : Fin 41 => fun context : QueryContext =>
      orFunctions (List.ofFn (fun corner : Fin 4 => fun context : QueryContext =>
        orFunctions (List.ofFn (fun flag : Fin 2 => rawKindWord t corner flag)) context)) context)
    (fun t => orFunctions_ofFn_polyTime _
      (fun corner => orFunctions_ofFn_polyTime _
        (fun flag => rawKindWord_polyTime t corner flag ComputableInPolyTime.id')
        ComputableInPolyTime.id') ComputableInPolyTime.id')
    ((hs.prod (h₀.prod h₁)).prod (ho.prod (ComputableInPolyTime.const [])))
  exact hcert.of_enc_eq (fun a => congrArg encBits (kindWord_eq (source a) (code₀ a) (code₁ a) (out a)))

private theorem checked_arity {width position : ℕ}
    {gates : List (CircuitFormat.signature.Op × List ℕ)}
    (hraw : Program.IsCodeFrom CircuitFormat.signature width position gates) :
    ∀ gate ∈ gates, gate.2.length = 2 := by
  intro gate hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  exact (hraw.getElem i hi).1

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
    (axis : Fin 2) (context : QueryContext) (j : ℕ) (hj : j ≤ (CircuitWords.first context.1.1).length)
    (ho : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      axis.val * ((CircuitWords.first context.1.1).length + 1) + j)
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (affine₂ (cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length t corner axis j)
        (slot (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length zero)
        (2 * (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length : ℤ)) 0 0).coefficients r := by
  rw [copyCoefficientWord_value_at t corner flag axis context j hj ho,
    BrouwerNashCoefficientQuery.affine₂_coefficients]
  simp only [hr, BrouwerNashCoefficientQuery.pairedAction_iff, ite_self, add_zero,
    BrouwerNashHeaders.dimensionRuler_length]

private theorem copyCoefficientWord_value_sum (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (axis : Fin 2) (context : QueryContext)
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      ∑ j : Fin ((CircuitWords.first context.1.1).length + 1),
        if context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
            axis.val * ((CircuitWords.first context.1.1).length + 1) + j.val
        then (affine₂ (cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length t corner axis j.val)
          (slot (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
            (circuitUnaryPrefix context.1.2.2).length zero)
          (2 * (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
            (circuitUnaryPrefix context.1.2.2).length : ℤ)) 0 0).coefficients r else 0 := by
  apply sparse_sum
  · intro j hj
    exact copyCoefficientWord_value_gate t corner flag axis context j.val
      (by have hh := j.isLt; omega) hj r hr
  · intro hn
    apply copyCoefficientWord_value_zero
    intro j hj
    exact hn ⟨j, by omega⟩

private theorem rawCoefficientWord_value_dimension (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) (raw : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw)
    (hcode : rawCode flag context = (CircuitFormat.encode raw)) (j : Fin raw.length)
    (ho : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length + j.val)
    (k : ℕ) (hk : (BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2).length = k)
    (href : Program.IsCodeFrom CircuitFormat.signature k 0 [((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))])
    (r : Fin (k * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      BimatrixRawGate.coefficients
        ((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·))) href r := by
  subst k
  exact rawCoefficientWord_value_at t corner flag context raw
    (by simpa only [BrouwerNashHeaders.arityRuler_length] using hraw) hcode j ho href r hr

private theorem rawCoefficientWord_value_gate (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) (raw : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw)
    (hcode : rawCode flag context = (CircuitFormat.encode raw)) (j : Fin raw.length)
    (ho : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length + j.val)
    (href : Program.IsCodeFrom CircuitFormat.signature (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length) 0 [((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))])
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (guardedRaw ((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))).coefficients r := by
  rw [guardedRaw_eq _ href]
  dsimp only [BimatrixRawGate.gate]
  exact rawCoefficientWord_value_dimension t corner flag context raw hraw hcode j ho _
    (BrouwerNashHeaders.dimensionRuler_length context.1.1 context.1.2.1 context.1.2.2) href r hr

private theorem rawCoefficientWord_value_sum (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) (raw : List (CircuitFormat.signature.Op × List ℕ))
    (hraw : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw)
    (hcode : rawCode flag context = (CircuitFormat.encode raw))
    (hwf : ∀ j : Fin raw.length,
      Program.IsCodeFrom CircuitFormat.signature (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length) 0 [((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))])
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      ∑ j : Fin raw.length, if context.2.1.length =
          (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
            (BrouwerNashHeaders.arityRuler context.1.1).length + j.val
        then (guardedRaw ((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))).coefficients r else 0 := by
  apply sparse_sum
  · intro j hj
    exact rawCoefficientWord_value_gate t corner flag context raw hraw hcode j hj (hwf j) r hr
  · intro hn
    apply rawCoefficientWord_value_zero
    intro j hj
    have hcode' : (if flag.val = 0 then context.1.2.1 else context.1.2.2) =
        CircuitFormat.encode raw := hcode
    rw [hcode', circuitUnaryPrefix_encode_length raw (checked_arity hraw)] at hj
    exact hn ⟨j, hj⟩

private theorem rawEnd_le_dimension (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) :
    (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length +
      (circuitUnaryPrefix (rawCode flag context)).length ≤
      dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length := by
  let b := (CircuitWords.first context.1.1).length
  let e₀ := (circuitUnaryPrefix context.1.2.1).length
  let e₁ := (circuitUnaryPrefix context.1.2.2).length
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
    (circuitUnaryPrefix (rawCode flag context)).length ≤ dimension b e₀ e₁
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
    (context : QueryContext) (raw : List (CircuitFormat.signature.Op × List ℕ))
    (hcode : rawCode flag context = (CircuitFormat.encode raw))
    (hraw : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw) (j : Fin raw.length) :
    Program.IsCodeFrom CircuitFormat.signature (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length) 0 [((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))] := by
  have he := rawEnd_le_dimension t corner flag context
  rw [hcode, circuitUnaryPrefix_encode_length raw (checked_arity hraw),
    BrouwerNashHeaders.arityRuler_length] at he
  exact circuitRelocatedGate_valid hraw he j

private theorem rawKindWord_value (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (context : QueryContext) :
    rawKindWord t corner flag context = [decide (
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length ≤ context.2.1.length ∧
      context.2.1.length < (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length +
          (circuitUnaryPrefix (rawCode flag context)).length)] := by
  simp only [rawKindWord, List.length_append]

private theorem orFunctions_value {Context : Type}
    (queries : List (Context → List Bool)) (context : Context) :
    orFunctions queries context = [queries.any (fun query => (query context).headD false)] := by
  induction queries with
  | nil => rfl
  | cons query queries ih =>
    change [(query context).headD false || (orFunctions queries context).headD false] = _
    rw [ih]
    rfl

private theorem orFunctions_ofFn_value {Context : Type} {n : ℕ}
    (queries : Fin n → Context → List Bool) (context : Context) :
    orFunctions (List.ofFn queries) context =
      [decide (∃ i, (queries i context).headD false = true)] := by
  rw [orFunctions_value]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨query, hquery, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hquery
    exact decide_eq_true ⟨i, h⟩
  · intro h
    obtain ⟨i, hi⟩ := of_decide_eq_true h
    exact ⟨queries i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

/-- The computed kind flag is exactly the union of the allocated raw-circuit intervals. -/
theorem kindWord_value (context : QueryContext) :
    kindWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 = [decide (∃ t : Fin 41, ∃ corner : Fin 4, ∃ flag : Fin 2,
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length ≤ context.2.1.length ∧
      context.2.1.length < (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length +
          (circuitUnaryPrefix (if flag.val = 0 then context.1.2.1 else context.1.2.2)).length)] := by
  rw [kindWord_eq]
  simp only [orFunctions_ofFn_value, List.headD_cons, decide_eq_true_eq, rawKindWord_value, rawCode]

private theorem querySum_ofFn_value {Context : Type} {n : ℕ}
    (fs : Fin n → Context → List Bool) (context : Context) :
    binarySignedValue (binarySignedQuerySum (List.ofFn fs) context) =
      ∑ i : Fin n, binarySignedValue (fs i context) :=
      by
  rw [binarySignedQuerySum_value, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The full coefficient query is the guarded sum of its canonical copy and raw gate factories. -/
theorem coefficientWord_value (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      ∑ t : Fin 41, ∑ corner : Fin 4, ∑ flag : Fin 2,
        ((∑ axis : Fin 2, ∑ j : Fin ((CircuitWords.first context.1.1).length + 1),
          if context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
              axis.val * ((CircuitWords.first context.1.1).length + 1) + j.val
          then (affine₂ (cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
            (circuitUnaryPrefix context.1.2.2).length t corner axis j.val)
            (slot (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
              (circuitUnaryPrefix context.1.2.2).length zero)
            (2 * (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
              (circuitUnaryPrefix context.1.2.2).length : ℤ)) 0 0).coefficients r else 0) +
        (let raw := if flag.val = 0 then raw₀ else raw₁
          ∑ j : Fin raw.length, if context.2.1.length =
              (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
                (BrouwerNashHeaders.arityRuler context.1.1).length + j.val
            then (guardedRaw ((raw[j.val].1, raw[j.val].2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))).coefficients r else 0)) := by
  rw [coefficientWord_eq]
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
    copyCoefficientWord_value_sum t corner flag 0 context r hr,
    copyCoefficientWord_value_sum t corner flag 1 context r hr]
  let raw := if flag.val = 0 then raw₀ else raw₁
  have he : rawCode flag context = (CircuitFormat.encode raw) := by
    unfold rawCode raw
    split <;> assumption
  have hw : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw := by
    unfold raw
    split <;> assumption
  rw [rawCoefficientWord_value_sum t corner flag context raw hw he
    (fun j => rawShift_wellFormed t corner flag context raw he hw j) r hr]
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
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw₀) (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw₁)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length) :
    Program.IsCodeFrom CircuitFormat.signature (dimension b raw₀.length raw₁.length) 0 [((((if flag.val = 0 then raw₀ else raw₁)[j.val]).1, ((if flag.val = 0 then raw₀ else raw₁)[j.val]).2.map ((sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner
        flag) + ·)))] := by
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
  let raw := if flag.val = 0 then raw₀ else raw₁
  have hraw : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw := by
    unfold raw
    split <;> assumption
  have hbound : (sampleBase b raw₀.length raw₁.length t +
      colorInput b raw₀.length raw₁.length corner flag) + arity b + raw.length ≤
        dimension b raw₀.length raw₁.length := by
    unfold colorInput raw
    by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false] <;> omega
  exact circuitRelocatedGate_valid hraw hbound j

private theorem colorRegionGate_comparator_iff (b : ℕ)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw₀) (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw₁)
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
      change Program.IsCodeFrom CircuitFormat.signature _ 0 [(((raw₀.get j).1, (raw₀.get j).2.map ((sampleBase b raw₀.length raw₁.length t +
        colorInput b raw₀.length raw₁.length corner 0) + ·)))] at hf
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
        change Program.IsCodeFrom CircuitFormat.signature _ 0 [(((raw₁.get j).1, (raw₁.get j).2.map ((sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 1) + ·)))] at hf
        rw [he, guardedRaw_eq _ hf]
        simp only [BimatrixRawGate.gate, true_iff]
        exact Or.inr ⟨by omega, ho⟩

/-- At an allocated color output, the computed flag is the canonical program gate kind. -/
theorem kindWord_eq_colorRegion (source out : List Bool)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first source).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first source).length) 0 raw₁)
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (CircuitWords.first source).length raw₀.length raw₁.length)
    (hout : out.length = sampleBase (CircuitWords.first source).length raw₀.length raw₁.length t +
      colorBase (CircuitWords.first source).length +
        corner.val * cornerWidth (CircuitWords.first source).length raw₀.length raw₁.length + offset) :
    kindWord source (CircuitFormat.encode raw₀) (CircuitFormat.encode raw₁) out =
      [decide ((colorRegionGate (CircuitWords.first source).length raw₀ raw₁ t corner offset).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  have hp₀ := circuitUnaryPrefix_encode_length raw₀ (checked_arity hw₀)
  have hp₁ := circuitUnaryPrefix_encode_length raw₁ (checked_arity hw₁)
  rw [kindWord_value ((source,(CircuitFormat.encode raw₀,CircuitFormat.encode raw₁)),(out,[]))]
  simp only [inputRuler_length, BrouwerNashHeaders.arityRuler_length,
    apply_ite, hp₀, hp₁]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  refine Iff.trans ?_ ((rawIntervals_iff (CircuitWords.first source).length raw₀.length raw₁.length out.length
    t corner offset ho hout).trans
      (colorRegionGate_comparator_iff (CircuitWords.first source).length raw₀ raw₁ hw₀ hw₁ t corner offset
        ho).symm)
  apply exists_congr; intro sample
  apply exists_congr; intro vertex
  apply exists_congr; intro flag
  by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false]

/-- No allocated color gate contributes outside the color regions. -/
theorem coefficientWord_zero_outside (context : QueryContext)
    (hno : ∀ (t : Fin 41) (corner : Fin 4) offset,
      offset < cornerWidth (CircuitWords.first context.1.1).length
        (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length →
      context.2.1.length ≠ sampleBase (CircuitWords.first context.1.1).length
        (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length t +
          colorBase (CircuitWords.first context.1.1).length + corner.val * cornerWidth
            (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
              (circuitUnaryPrefix context.1.2.2).length + offset) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) = 0 := by
  let b := (CircuitWords.first context.1.1).length
  let e₀ := (circuitUnaryPrefix context.1.2.1).length
  let e₁ := (circuitUnaryPrefix context.1.2.2).length
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [ b, e₀, e₁] using inputRuler_length t corner flag context.1.1 context.1.2.1 context.1.2.2
  rw [coefficientWord_eq]
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro t ht
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro corner hc
  rw [querySum_ofFn_value]
  apply Finset.sum_eq_zero; intro flag hf
  have hcopy (axis : Fin 2) :
      binarySignedValue (copyCoefficientWord t corner flag axis context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) = 0 := by
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
    apply (show context.2.1.length ≠ sampleBase b e₀ e₁ t + colorBase b +
      corner.val * cornerWidth b e₀ e₁ + off from hno t corner off hoff)
    rw [hin, colorInput] at he
    change context.2.1.length = sampleBase b e₀ e₁ t +
      (colorBase b + corner.val * cornerWidth b e₀ e₁ +
        (if flag.val = 0 then 0 else arity b + e₀)) + axis.val * (b + 1) + j at he
    dsimp only [off]
    omega
  have hraw : binarySignedValue (rawCoefficientWord t corner flag context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) = 0 := by
    apply rawCoefficientWord_value_zero
    intro j hj he
    let off := (if flag.val = 0 then 0 else arity b + e₀) + arity b + j
    have hoff : off < cornerWidth b e₀ e₁ := by
      dsimp only [off, cornerWidth]
      by_cases hflag : flag.val = 0
      · simp only [hflag, ite_true] at hj ⊢
        change j < e₀ at hj
        omega
      · simp only [hflag, ite_false] at hj ⊢
        change j < e₁ at hj
        omega
    apply (show context.2.1.length ≠ sampleBase b e₀ e₁ t + colorBase b +
      corner.val * cornerWidth b e₀ e₁ + off from hno t corner off hoff)
    have harity : (BrouwerNashHeaders.arityRuler context.1.1).length = arity b := by
      simpa only [ b] using
        BrouwerNashHeaders.arityRuler_length context.1.1
    rw [hin, colorInput, harity] at he
    dsimp only [off]
    omega
  rw [cornerCoefficientWord, binarySignedAdd_value, binarySignedAdd_value,
    hcopy 0, hcopy 1, hraw]
  rfl

/-- The color kind query is false outside the allocated color portion of every sample. -/
theorem kindWord_zero_of_outside (context : QueryContext)
    (hno : ∀ t : Fin 41, ¬(sampleBase (CircuitWords.first context.1.1).length
      (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length t +
        colorBase (CircuitWords.first context.1.1).length ≤ context.2.1.length ∧
      context.2.1.length < sampleBase (CircuitWords.first context.1.1).length
        (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length t +
          minimumBase (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
            (circuitUnaryPrefix context.1.2.2).length)) : kindWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 = [false] := by
  rw [kindWord_value context]
  congr 1
  apply decide_eq_false_iff_not.mpr
  rintro ⟨t, corner, flag, hlo, hhi⟩
  apply hno t
  let b := (CircuitWords.first context.1.1).length
  let e₀ := (circuitUnaryPrefix context.1.2.1).length
  let e₁ := (circuitUnaryPrefix context.1.2.2).length
  have hin : (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length =
      sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [ b, e₀, e₁] using
        inputRuler_length t corner flag context.1.1 context.1.2.1 context.1.2.2
  have harity : (BrouwerNashHeaders.arityRuler context.1.1).length = arity b := by
    simpa only [ b] using
      BrouwerNashHeaders.arityRuler_length context.1.1
  rw [hin, harity, colorInput] at hlo hhi
  have hc : corner.val * cornerWidth b e₀ e₁ + cornerWidth b e₀ e₁ ≤
      4 * cornerWidth b e₀ e₁ := by
    calc
      _ = (corner.val + 1) * cornerWidth b e₀ e₁ := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have hh := corner.isLt; omega)
  change sampleBase b e₀ e₁ t + colorBase b ≤ context.2.1.length ∧
    context.2.1.length < sampleBase b e₀ e₁ t + minimumBase b e₀ e₁
  have hl : cornerWidth b e₀ e₁ = 2 * arity b + e₀ + e₁ := rfl
  by_cases hf : flag.val = 0
  · simp only [hf, ite_true] at hlo hhi
    change context.2.1.length < sampleBase b e₀ e₁ t + (colorBase b +
      corner.val * cornerWidth b e₀ e₁ + 0) + arity b + e₀ at hhi
    dsimp only [minimumBase]
    constructor <;> omega
  · simp only [hf, ite_false] at hlo hhi
    change context.2.1.length < sampleBase b e₀ e₁ t + (colorBase b +
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
theorem coefficientWord_eq_copy (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag axis : Fin 2)
    (j : Fin ((CircuitWords.first context.1.1).length + 1))
    (hout : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      axis.val * ((CircuitWords.first context.1.1).length + 1) + j.val) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (affine₂ (cornerBit (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
        (circuitUnaryPrefix context.1.2.2).length t corner axis j.val)
        (slot (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length zero)
        (2 * (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
          (circuitUnaryPrefix context.1.2.2).length : ℤ)) 0 0).coefficients r := by
  let b := (CircuitWords.first context.1.1).length
  let e₀ := (circuitUnaryPrefix context.1.2.1).length
  let e₁ := (circuitUnaryPrefix context.1.2.2).length
  have hp₀ : e₀ = raw₀.length := by
    dsimp [e₀]; rw [hc₀]
    exact circuitUnaryPrefix_encode_length raw₀ (checked_arity hw₀)
  have hp₁ : e₁ = raw₁.length := by
    dsimp [e₁]; rw [hc₁]
    exact circuitUnaryPrefix_encode_length raw₁ (checked_arity hw₁)
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [ b, e₀, e₁] using
        inputRuler_length t corner flag context.1.1 context.1.2.1 context.1.2.2
  have harity : (BrouwerNashHeaders.arityRuler context.1.1).length = arity b := by
    simpa only [ b] using
      BrouwerNashHeaders.arityRuler_length context.1.1
  have hcopy (t' : Fin 41) (c' : Fin 4) (f' a' : Fin 2) (j' : Fin (b + 1)) :
      context.2.1.length = (inputRuler t' c' f' context.1.1 context.1.2.1 context.1.2.2).length +
        a'.val * (b + 1) + j'.val ↔
      t' = t ∧ c' = corner ∧ f' = flag ∧ a' = axis ∧ j' = j := by
    rw [hout, hin, hin, eq_comm]
    exact copyPosition_eq_iff b e₀ e₁ t' t c' corner f' flag a' axis j' j
  have hraw (t' : Fin 41) (c' : Fin 4) (f' : Fin 2)
      (j' : Fin (if f'.val = 0 then raw₀ else raw₁).length) :
      context.2.1.length ≠ (inputRuler t' c' f' context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length + j'.val := by
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
  rw [coefficientWord_value context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr]
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
theorem coefficientWord_eq_raw (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length (circuitUnaryPrefix context.1.2.1).length
      (circuitUnaryPrefix context.1.2.2).length * 2)) (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length)
    (hout : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length + j.val) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (guardedRaw ((((if flag.val = 0 then raw₀ else raw₁)[j.val]).1, ((if flag.val = 0 then raw₀ else raw₁)[j.val]).2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))).coefficients r := by
  let b := (CircuitWords.first context.1.1).length
  let e₀ := (circuitUnaryPrefix context.1.2.1).length
  let e₁ := (circuitUnaryPrefix context.1.2.2).length
  have hp₀ : e₀ = raw₀.length := by
    dsimp [e₀]; rw [hc₀]
    exact circuitUnaryPrefix_encode_length raw₀ (checked_arity hw₀)
  have hp₁ : e₁ = raw₁.length := by
    dsimp [e₁]; rw [hc₁]
    exact circuitUnaryPrefix_encode_length raw₁ (checked_arity hw₁)
  have hin (t : Fin 41) (corner : Fin 4) (flag : Fin 2) :
      (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length =
        sampleBase b e₀ e₁ t + colorInput b e₀ e₁ corner flag := by
    simpa only [ b, e₀, e₁] using
        inputRuler_length t corner flag context.1.1 context.1.2.1 context.1.2.2
  have harity : (BrouwerNashHeaders.arityRuler context.1.1).length = arity b := by
    simpa only [ b] using
      BrouwerNashHeaders.arityRuler_length context.1.1
  have hlen (f : Fin 2) (l : Fin (if f.val = 0 then raw₀ else raw₁).length) :
      l.val < if f.val = 0 then e₀ else e₁ := by
    rw [hp₀, hp₁]
    by_cases hf : f.val = 0 <;> simpa only [hf, ite_true, ite_false] using l.isLt
  have hcopy (t' : Fin 41) (c' : Fin 4) (f' a' : Fin 2) (j' : Fin (b + 1)) :
      context.2.1.length ≠ (inputRuler t' c' f' context.1.1 context.1.2.1 context.1.2.2).length +
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
      context.2.1.length = (inputRuler t' c' f' context.1.1 context.1.2.1 context.1.2.2).length +
        (BrouwerNashHeaders.arityRuler context.1.1).length + j'.val ↔
      t' = t ∧ c' = corner ∧ f' = flag ∧ j'.val = j.val := by
    rw [hout, hin, hin, harity, eq_comm]
    exact rawPosition_eq_iff b e₀ e₁ t' t c' corner f' flag j'.val j.val
      (hlen f' j') (hlen flag j)
  rw [coefficientWord_value context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr]
  dsimp only [b] at hcopy
  simp only [hcopy, hraw, ite_false, Finset.sum_const_zero, zero_add, ite_and,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_inj]

private theorem coefficientWord_eq_copy_lengths (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (e₀ e₁ : ℕ)
    (he₀ : (circuitUnaryPrefix context.1.2.1).length = e₀)
    (he₁ : (circuitUnaryPrefix context.1.2.2).length = e₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length e₀
      e₁ * 2)) (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag axis : Fin 2)
    (j : Fin ((CircuitWords.first context.1.1).length + 1))
    (hout : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      axis.val * ((CircuitWords.first context.1.1).length + 1) + j.val) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (affine₂ (cornerBit (CircuitWords.first context.1.1).length e₀
        e₁ t corner axis j.val)
        (slot (CircuitWords.first context.1.1).length e₀
          e₁ zero)
        (2 * (dimension (CircuitWords.first context.1.1).length e₀
          e₁ : ℤ)) 0 0).coefficients r := by
  subst e₀ e₁
  exact coefficientWord_eq_copy context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner flag axis j hout

private theorem coefficientWord_eq_raw_lengths (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (e₀ e₁ : ℕ)
    (he₀ : (circuitUnaryPrefix context.1.2.1).length = e₀)
    (he₁ : (circuitUnaryPrefix context.1.2.2).length = e₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length e₀
      e₁ * 2)) (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : Fin (if flag.val = 0 then raw₀ else raw₁).length)
    (hout : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
      (BrouwerNashHeaders.arityRuler context.1.1).length + j.val) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (guardedRaw ((((if flag.val = 0 then raw₀ else raw₁)[j.val]).1, ((if flag.val = 0 then raw₀ else raw₁)[j.val]).2.map ((inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + ·)))).coefficients r := by
  subst e₀ e₁
  exact coefficientWord_eq_raw context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner flag j hout

/-- The canonical color kind depends only on the parsed raw circuit lengths. -/
theorem kindWord_eq_colorRegion_of_lengths (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (he₀ : (circuitUnaryPrefix context.1.2.1).length = raw₀.length)
    (he₁ : (circuitUnaryPrefix context.1.2.2).length = raw₁.length)
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (CircuitWords.first context.1.1).length raw₀.length raw₁.length)
    (hout : context.2.1.length = sampleBase (CircuitWords.first context.1.1).length raw₀.length raw₁.length t +
      colorBase (CircuitWords.first context.1.1).length +
        corner.val * cornerWidth (CircuitWords.first context.1.1).length raw₀.length raw₁.length + offset) :
    kindWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 = [decide ((colorRegionGate (CircuitWords.first context.1.1).length
      raw₀ raw₁ t corner offset).kind =
        GameTheory.Finite.BimatrixGateProgram.GateKind.comparator)] := by
  have hin (t : Fin 41) (c : Fin 4) (f : Fin 2) :
      (inputRuler t c f context.1.1 context.1.2.1 context.1.2.2).length =
        sampleBase (CircuitWords.first context.1.1).length raw₀.length raw₁.length t +
          colorInput (CircuitWords.first context.1.1).length raw₀.length raw₁.length c f := by
    simpa only [ he₀, he₁] using inputRuler_length t c f context.1.1 context.1.2.1 context.1.2.2
  have ha : (BrouwerNashHeaders.arityRuler context.1.1).length =
      arity (CircuitWords.first context.1.1).length := by
    simpa only [ Matrix.cons_val_zero] using
      BrouwerNashHeaders.arityRuler_length context.1.1
  rw [kindWord_value context]
  simp only [hin, ha, apply_ite, he₀, he₁]
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  refine Iff.trans ?_ ((rawIntervals_iff (CircuitWords.first context.1.1).length raw₀.length raw₁.length
    context.2.1.length t corner offset ho hout).trans
      (colorRegionGate_comparator_iff (CircuitWords.first context.1.1).length raw₀ raw₁ hw₀ hw₁
        t corner offset ho).symm)
  apply exists_congr; intro sample
  apply exists_congr; intro vertex
  apply exists_congr; intro flag
  by_cases hf : flag.val = 0 <;> simp only [hf, ite_true, ite_false]

private theorem coefficientWord_eq_copyOffset (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length raw₀.length raw₁.length * 2))
    (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (flag : Fin 2) (offset : ℕ)
    (ho : offset < arity (CircuitWords.first context.1.1).length)
    (hout : context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length + offset) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (affine₂ (cornerBit (CircuitWords.first context.1.1).length raw₀.length raw₁.length t corner
        ⟨(offset / ((CircuitWords.first context.1.1).length + 1)) % 2, Nat.mod_lt _ (by decide)⟩
        (offset % ((CircuitWords.first context.1.1).length + 1)))
        (slot (CircuitWords.first context.1.1).length raw₀.length raw₁.length zero)
        (2 * (dimension (CircuitWords.first context.1.1).length raw₀.length raw₁.length : ℤ)) 0 0).coefficients r
          := by
  let b := (CircuitWords.first context.1.1).length
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
  have hp₀ : (circuitUnaryPrefix context.1.2.1).length = raw₀.length := by
    rw [hc₀]
    exact circuitUnaryPrefix_encode_length raw₀ (checked_arity hw₀)
  have hp₁ : (circuitUnaryPrefix context.1.2.2).length = raw₁.length := by
    rw [hc₁]
    exact circuitUnaryPrefix_encode_length raw₁ (checked_arity hw₁)
  apply coefficientWord_eq_copy_lengths context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
    raw₀.length raw₁.length hp₀ hp₁ r hr t corner flag axis j
  change context.2.1.length = (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length +
    axis.val * (b + 1) + j.val
  rw [add_assoc, hqr]
  exact hout

/-- At an allocated color output, the scalar query equals the canonical gate coefficient. -/
theorem coefficientWord_eq_colorRegion (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length raw₀.length raw₁.length * 2))
    (hr : context.2.2.length = r.val)
    (t : Fin 41) (corner : Fin 4) (offset : ℕ)
    (ho : offset < cornerWidth (CircuitWords.first context.1.1).length raw₀.length raw₁.length)
    (hout : context.2.1.length = sampleBase (CircuitWords.first context.1.1).length raw₀.length raw₁.length t +
      colorBase (CircuitWords.first context.1.1).length + corner.val *
        cornerWidth (CircuitWords.first context.1.1).length raw₀.length raw₁.length + offset) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (colorRegionGate (CircuitWords.first context.1.1).length raw₀ raw₁ t corner offset).coefficients r := by
  let b := (CircuitWords.first context.1.1).length
  have hp₀ : (circuitUnaryPrefix context.1.2.1).length = raw₀.length := by
    rw [hc₀]
    exact circuitUnaryPrefix_encode_length raw₀ (checked_arity hw₀)
  have hp₁ : (circuitUnaryPrefix context.1.2.2).length = raw₁.length := by
    rw [hc₁]
    exact circuitUnaryPrefix_encode_length raw₁ (checked_arity hw₁)
  have hin (flag : Fin 2) : (inputRuler t corner flag context.1.1 context.1.2.1 context.1.2.2).length =
      sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner flag :=
        by
    simpa only [ b, hp₀, hp₁] using
        inputRuler_length t corner flag context.1.1 context.1.2.1 context.1.2.2
  have ha : (BrouwerNashHeaders.arityRuler context.1.1).length = arity b := by
    simpa only [ b] using
      BrouwerNashHeaders.arityRuler_length context.1.1
  by_cases h₀ : offset < arity b
  · have he := colorRegionGate_copy b raw₀ raw₁ t corner 0 offset h₀
    simp only [Fin.val_zero, ite_true, zero_add] at he
    rw [he]
    apply coefficientWord_eq_copyOffset context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner 0 offset h₀
    rw [hin, colorInput]
    simp only [Fin.val_zero, ite_true]
    change context.2.1.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
      corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
    omega
  · by_cases h₁ : offset < arity b + raw₀.length
    · let j : Fin raw₀.length := ⟨offset - arity b, by omega⟩
      have he := colorRegionGate_raw₀ b raw₀ raw₁ t corner j
      have hj : arity b + j.val = offset := by dsimp only [j]; omega
      rw [hj] at he
      rw [he]
      have hh := coefficientWord_eq_raw_lengths context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
        raw₀.length raw₁.length hp₀ hp₁ r hr t corner 0 j
      have houtput : context.2.1.length = (inputRuler t corner 0 context.1.1 context.1.2.1 context.1.2.2).length +
          (BrouwerNashHeaders.arityRuler context.1.1).length + j.val := by
        rw [hin, ha, colorInput]
        simp only [Fin.val_zero, ite_true]
        dsimp only [j]
        change context.2.1.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
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
        apply coefficientWord_eq_copyOffset context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner 1 j hj
        rw [hin, colorInput]
        simp only [Fin.val_one, Nat.one_ne_zero, ite_false]
        dsimp only [j]
        change context.2.1.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
          corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
        omega
      · let j : Fin raw₁.length := ⟨offset - (2 * arity b + raw₀.length), by
          change offset < 2 * arity b + raw₀.length + raw₁.length at ho
          omega⟩
        have he := colorRegionGate_raw₁ b raw₀ raw₁ t corner j
        have hj : 2 * arity b + raw₀.length + j.val = offset := by dsimp only [j]; omega
        rw [hj] at he
        rw [he]
        have hh := coefficientWord_eq_raw_lengths context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁
          raw₀.length raw₁.length hp₀ hp₁ r hr t corner 1 j
        have houtput : context.2.1.length = (inputRuler t corner 1 context.1.1 context.1.2.1 context.1.2.2).length +
            (BrouwerNashHeaders.arityRuler context.1.1).length + j.val := by
          rw [hin, ha, colorInput]
          simp only [Fin.val_one, Nat.one_ne_zero, ite_false]
          dsimp only [j]
          change context.2.1.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
            corner.val * cornerWidth b raw₀.length raw₁.length + offset at hout
          omega

        rw [hin] at houtput
        simp only [hin, Fin.val_one, Nat.one_ne_zero, ite_false] at hh
        exact hh houtput

/-- The scalar color query agrees with any allocated color gate of the sample program. -/
theorem coefficientWord_eq_sampleGate (context : QueryContext)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
    (hc₀ : context.1.2.1 = (CircuitFormat.encode raw₀)) (hc₁ : context.1.2.2 = (CircuitFormat.encode raw₁))
    (hw₀ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₀)
    (hw₁ : Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first context.1.1).length) 0 raw₁)
    (r : Fin (dimension (CircuitWords.first context.1.1).length raw₀.length raw₁.length * 2))
    (hr : context.2.2.length = r.val) (t : Fin 41) (offset : ℕ)
    (hlo : colorBase (CircuitWords.first context.1.1).length ≤ offset)
    (hhi : offset < minimumBase (CircuitWords.first context.1.1).length raw₀.length raw₁.length)
    (hout : context.2.1.length = sampleBase (CircuitWords.first context.1.1).length raw₀.length raw₁.length t + offset) :
    binarySignedValue (coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2) =
      (sampleGate (CircuitWords.first context.1.1).length raw₀ raw₁ t offset).coefficients r := by
  let b := (CircuitWords.first context.1.1).length
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
  apply coefficientWord_eq_colorRegion context raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ r hr t corner localOffset hl
  change context.2.1.length = sampleBase b raw₀.length raw₁.length t + offset at hout
  change context.2.1.length = sampleBase b raw₀.length raw₁.length t + colorBase b +
    corner.val * cornerWidth b raw₀.length raw₁.length + localOffset
  omega

end GameTheory.Complexity.Backend.BrouwerNashColorQuery
