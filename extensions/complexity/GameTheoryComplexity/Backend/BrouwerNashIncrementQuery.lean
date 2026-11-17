module

public import GameTheoryComplexity.Backend.BrouwerNashQueryRegions
public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BimatrixRawGateMachine
public import GameTheoryComplexity.Backend.BinaryIndexedLookup
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum

@[expose] public section

/-! Ripple-increment coefficient queries preserve inline negation, both aliased
reference contributions, actual suffix clocks and the concrete gate word format.
Every source-bit position is queried at each of the forty-one sample placements. -/
namespace GameTheory.Complexity.Backend.BrouwerNashIncrementQuery
open Cslib.Circuits Turing.MultiTapeTM
open scoped BigOperators

local notation "QueryContext" =>
  ((List Bool × (List Bool × List Bool)) × (List Bool × (List Bool × List Bool)))
local notation "queryEncoding" =>
  encPair (encPair encBits (encPair encBits encBits)) (encPair encBits (encPair encBits encBits))
local notation "SumContext" => ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool))
local notation "sumEncoding" =>
  encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)

private def depthR (context : QueryContext) : List Bool :=
  BrouwerNashHeaders.sourceDepthRuler context.1.1

private def dimensionR (context : QueryContext) : List Bool :=
  BrouwerNashHeaders.dimensionRuler context.1.1 context.1.2.1 context.1.2.2

private def startR (context : QueryContext) : List Bool :=
  BrouwerNashHeaders.globalRuler context.1.1 ++ List.replicate
    (context.2.1.length * (BrouwerNashHeaders.sampleRuler context.1.1 context.1.2.1 context.1.2.2).length) true

private def incrementBaseR (axis : Fin 2) (context : QueryContext) : List Bool :=
  [false, false] ++ List.replicate ((depthR context).length * (4 + 4 * axis.val)) true

private def incrementR (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  startR context ++ incrementBaseR axis context ++ List.replicate (ordinal.length * 4) true ++
    List.replicate stage.val false

private def primaryR (axis : Fin 2) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  startR context ++ [false, false] ++ List.replicate ((depthR context).length * (2 * axis.val)) true ++
    List.replicate (((depthR context).drop (ordinal.length + 1)).length * 2) true

private def carryR (axis : Fin 2) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  if ordinal.length = 0 then [false, false]
  else startR context ++ incrementBaseR axis context ++ List.replicate (ordinal.tail.length * 4) true ++
    [false, false, false]

private def firstR (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  if stage.val = 2 then incrementR axis 0 ordinal context else primaryR axis ordinal context

private def secondR (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  if stage.val = 2 then incrementR axis 1 ordinal context else carryR axis ordinal context

private def unary (ruler : List Bool) : List Bool := List.replicate ruler.length true

private def flags (stage : Fin 4) : List Bool :=
  match stage.val with
  | 0 => [true, false, true]
  | 1 => [true, true, false]
  | 2 => [false, false, false]
  | _ => [true, false, false]

private def suffix (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  flags stage ++ unary (firstR axis stage ordinal context) ++ [false] ++
    unary (secondR axis stage ordinal context) ++ [false]

private def test (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  [decide (context.2.2.1.length = (incrementR axis stage ordinal context).length ∧
    ordinal.length < (depthR context).length)]

/-- A serialized ripple gate contributes both actual reference coefficients. -/
def indexedCoefficientWord (axis : Fin 2) (stage : Fin 4)
    (ordinal : List Bool) (context : QueryContext) : List Bool :=
  let source := context.1.1
  let code₀ := context.1.2.1
  let code₁ := context.1.2.2
  let sample := context.2.1
  let depth := BrouwerNashHeaders.sourceDepthRuler source
  let start := BrouwerNashHeaders.globalRuler source ++
    List.replicate (sample.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
  let incrementBase := [false, false] ++ List.replicate (depth.length * (4 + 4 * axis.val)) true
  let increment (s : Fin 4) := start ++ incrementBase ++ List.replicate (ordinal.length * 4) true ++
    List.replicate s.val false
  let primary := start ++ [false, false] ++ List.replicate (depth.length * (2 * axis.val)) true ++
    List.replicate ((depth.drop (ordinal.length + 1)).length * 2) true
  let carry := if ordinal.length = 0 then [false, false]
    else start ++ incrementBase ++ List.replicate (ordinal.tail.length * 4) true ++ [false, false, false]
  let first := if stage.val = 2 then increment 0 else primary
  let second := if stage.val = 2 then increment 1 else carry
  let flags := match stage.val with
    | 0 => [true, false, true]
    | 1 => [true, true, false]
    | 2 => [false, false, false]
    | _ => [true, false, false]
  BimatrixRawGateMachine.coefficientWord (BrouwerNashHeaders.dimensionRuler source code₀ code₁)
    (flags ++ List.replicate first.length true ++ [false] ++ List.replicate second.length true ++ [false])
    context.2.2.2

private theorem indexedCoefficientWord_eq (axis : Fin 2) (stage : Fin 4)
    (ordinal : List Bool) (context : QueryContext) :
    indexedCoefficientWord axis stage ordinal context =
      BimatrixRawGateMachine.coefficientWord (dimensionR context) (suffix axis stage ordinal context)
        context.2.2.2 := rfl

/-- Scan the original source-depth suffixes for one ripple stage in one sample. -/
def sampleCoefficientWord (axis : Fin 2) (stage : Fin 4)
    (source code₀ code₁ sample out action : List Bool) : List Bool :=
  let test (ordinal : List Bool) (context : QueryContext) : List Bool :=
    let source := context.1.1
    let code₀ := context.1.2.1
    let code₁ := context.1.2.2
    let sample := context.2.1
    let depth := BrouwerNashHeaders.sourceDepthRuler source
    let start := BrouwerNashHeaders.globalRuler source ++
      List.replicate (sample.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
    let incrementBase := [false, false] ++ List.replicate (depth.length * (4 + 4 * axis.val)) true
    let increment := start ++ incrementBase ++ List.replicate (ordinal.length * 4) true ++
      List.replicate stage.val false
    [decide (context.2.2.1.length = increment.length ∧ ordinal.length < depth.length)]
  binaryIndexedLookup test (indexedCoefficientWord axis stage)
    (BrouwerNashHeaders.sourceDepthRuler source) (BrouwerNashHeaders.widthRuler source code₀ code₁)
    ((source, (code₀, code₁)), (sample, (out, action)))

private theorem sampleCoefficientWord_eq (axis : Fin 2) (stage : Fin 4)
    (source code₀ code₁ sample out action : List Bool) :
    sampleCoefficientWord axis stage source code₀ code₁ sample out action =
      binaryIndexedLookup (test axis stage) (indexedCoefficientWord axis stage)
        (BrouwerNashHeaders.sourceDepthRuler source) (BrouwerNashHeaders.widthRuler source code₀ code₁)
        ((source, (code₀, code₁)), (sample, (out, action))) := rfl

/-- A ripple family visits all forty-one false sample ordinals in ascending order. -/
def coefficientWord (axis : Fin 2) (stage : Fin 4)
    (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedFiniteSum (fun ordinal (context : SumContext) =>
    sampleCoefficientWord axis stage context.1.1 context.1.2.1 context.1.2.2
      ordinal context.2.1 context.2.2) 41 ((source, (code₀, code₁)), (out, action))

/-- Add the eight original axis/stage families in their existing right-fold order. -/
def allCoefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedQuerySum [
    (fun (context : SumContext) => coefficientWord 0 0 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 0 1 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 0 2 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 0 3 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 1 0 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 1 1 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 1 2 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => coefficientWord 1 3 context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)]
    ((source, (code₀, code₁)), (out, action))

private def raw (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) :
    CircuitFormat.signature.Op × List ℕ :=
  ((decide (stage.val ≠ 2), decide (stage.val = 1), decide (stage.val = 0)),
    [(firstR axis stage ordinal context).length, (secondR axis stage ordinal context).length])

private theorem depthR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => depthR (context a)) input encBits :=
  BrouwerNashHeaders.sourceDepthRuler_polyTime hc.fst'.fst'

private theorem dimensionR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => dimensionR (context a)) input encBits :=
  BrouwerNashHeaders.dimensionRuler_polyTime hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'

private theorem startR_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => startR (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.globalRuler_polyTime hc.fst'.fst')
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hc.snd'.fst')
        (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sampleRuler_polyTime
          hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'))))

private theorem incrementBaseR_polyTime (axis : Fin 2) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => incrementBaseR axis (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false])
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp (depthR_polyTime hc))
        (ComputableInPolyTime.const (4 + 4 * axis.val))))

private theorem incrementR_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => incrementR axis stage (ordinal a) (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (startR_polyTime hc) (incrementBaseR_polyTime axis hc))
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hi) (ComputableInPolyTime.const 4))))
    (ComputableInPolyTime.const (List.replicate stage.val false))

private theorem primaryR_polyTime (axis : Fin 2) {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => primaryR axis (ordinal a) (context a)) input encBits := by
  have hd := depthR_polyTime hc
  have hdrop := ComputableInPolyTime.bitsDropWithInput hd
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.length_bits_comp hi) (ComputableInPolyTime.const 1))
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (startR_polyTime hc) (ComputableInPolyTime.const [false, false]))
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hd)
          (ComputableInPolyTime.const (2 * axis.val)))))
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hdrop) (ComputableInPolyTime.const 2)))

private theorem carryR_polyTime (axis : Fin 2) {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => carryR axis (ordinal a) (context a)) input encBits := by
  have hempty := (ComputableInPolyTime.length_bits_comp hi).decide_eq' (ComputableInPolyTime.const 0)
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hi
  have hno := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (startR_polyTime hc) (incrementBaseR_polyTime axis hc))
      ((ComputableInPolyTime.bitsReplicate true).comp
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp htail) (ComputableInPolyTime.const 4))))
    (ComputableInPolyTime.const [false, false, false])
  exact (hempty.ite (ComputableInPolyTime.const [false, false]) hno).of_enc_eq (fun a => by
    simp only [carryR, Function.comp_apply, decide_eq_true_eq])

private theorem firstR_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => firstR axis stage (ordinal a) (context a)) input encBits := by
  by_cases h : stage.val = 2
  · simpa only [firstR, h, ite_true] using incrementR_polyTime axis 0 hi hc
  · simpa only [firstR, h, ite_false] using primaryR_polyTime axis hi hc

private theorem secondR_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => secondR axis stage (ordinal a) (context a)) input encBits := by
  by_cases h : stage.val = 2
  · simpa only [secondR, h, ite_true] using incrementR_polyTime axis 1 hi hc
  · simpa only [secondR, h, ite_false] using carryR_polyTime axis hi hc

private theorem unary_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ruler : Input → List Bool} (hr : ComputableInPolyTime ruler input encBits) :
    ComputableInPolyTime (fun a => unary (ruler a)) input encBits :=
  (ComputableInPolyTime.bitsReplicate true).comp (ComputableInPolyTime.length_bits_comp hr)

private theorem suffix_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => suffix axis stage (ordinal a) (context a)) input encBits :=
  ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend
        (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const (flags stage))
          (unary_polyTime (firstR_polyTime axis stage hi hc))) (ComputableInPolyTime.const [false]))
      (unary_polyTime (secondR_polyTime axis stage hi hc))) (ComputableInPolyTime.const [false])

private theorem test_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => test axis stage (ordinal a) (context a)) input encBits := by
  have heq := (ComputableInPolyTime.length_bits_comp hc.snd'.snd'.fst').decide_eq'
    (ComputableInPolyTime.length_bits_comp (incrementR_polyTime axis stage hi hc))
  have hlt := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' (ComputableInPolyTime.length_bits_comp hi).tidy
      (ComputableInPolyTime.length_bits_comp (depthR_polyTime hc)).tidy)
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_and heq hlt) (ComputableInPolyTime.const [])

@[fun_prop] theorem indexedCoefficientWord_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => indexedCoefficientWord axis stage (ordinal a) (context a)) input encBits := by
  exact (BimatrixRawGateMachine.coefficientWord_polyTime (dimensionR_polyTime hc)
    (suffix_polyTime axis stage hi hc) hc.snd'.snd'.snd').of_enc_eq (fun a => by
      rw [indexedCoefficientWord_eq])

@[fun_prop] theorem sampleCoefficientWord_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ sample out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ht : ComputableInPolyTime sample input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => sampleCoefficientWord axis stage
      (source a) (code₀ a) (code₁ a) (sample a) (out a) (action a)) input encBits := by
  have htest := test_polyTime axis stage (ComputableInPolyTime.snd queryEncoding encBits)
    (ComputableInPolyTime.fst queryEncoding encBits)
  have hterm := indexedCoefficientWord_polyTime axis stage (ComputableInPolyTime.snd queryEncoding encBits)
    (ComputableInPolyTime.fst queryEncoding encBits)
  exact binaryIndexedLookup_polyTime htest hterm (BrouwerNashHeaders.sourceDepthRuler_polyTime hs)
    (BrouwerNashHeaders.widthRuler_polyTime hs hc₀ hc₁) ((hs.prod (hc₀.prod hc₁)).prod (ht.prod (ho.prod ha)))

@[fun_prop] theorem coefficientWord_polyTime (axis : Fin 2) (stage : Fin 4)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord axis stage
      (source a) (code₀ a) (code₁ a) (out a) (action a)) input encBits := by
  have hc := ComputableInPolyTime.fst sumEncoding encBits
  have hi := ComputableInPolyTime.snd sumEncoding encBits
  have hsample := sampleCoefficientWord_polyTime axis stage hc.fst'.fst'
    hc.fst'.snd'.fst' hc.fst'.snd'.snd' hi hc.snd'.fst' hc.snd'.snd'
  exact binarySignedFiniteSum_polyTime hsample 41 ((hs.prod (hc₀.prod hc₁)).prod (ho.prod ha))

@[fun_prop] theorem allCoefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => allCoefficientWord
      (source a) (code₀ a) (code₁ a) (out a) (action a)) input encBits := by
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  have hid : ComputableInPolyTime (fun context : SumContext => context) sumEncoding sumEncoding := .id'
  apply binarySignedQuerySum_polyTime _ ?_ hcontext
  intro query hquery
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hquery
  rcases hquery with h | h | h | h | h | h | h | h <;>
    subst query <;> exact coefficientWord_polyTime _ _ hid.fst'.fst'
      hid.fst'.snd'.fst' hid.fst'.snd'.snd' hid.snd'.fst' hid.snd'.snd'

private theorem suffix_encode (axis : Fin 2) (stage : Fin 4)
    (ordinal : List Bool) (context : QueryContext) :
    suffix axis stage ordinal context =
      CircuitFormat.encodeGate (raw axis stage ordinal context).1
        ((raw axis stage ordinal context).2.getD 0 0) ((raw axis stage ordinal context).2.getD 1 0) := by
  fin_cases stage <;> simp [suffix, flags, raw, CircuitFormat.encodeGate, CircuitFormat.encodeUnary,
    unary, List.append_assoc]

private theorem startR_length (context : QueryContext) :
    (startR context).length = BrouwerNashLayout.globalCount (CircuitWords.first context.1.1).length +
      context.2.1.length * BrouwerNashLayout.sampleWidth (CircuitWords.first context.1.1).length
        (circuitUnaryPrefix context.1.2.1).length (circuitUnaryPrefix context.1.2.2).length := by
  simp only [startR, List.length_append, List.length_replicate,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]

private theorem incrementBaseR_length (axis : Fin 2) (context : QueryContext) :
    (incrementBaseR axis context).length =
      BrouwerNashLayout.incrementBase (CircuitWords.first context.1.1).length axis := by
  simp only [incrementBaseR, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, depthR, BrouwerNashHeaders.sourceDepthRuler_length,
    BrouwerNashLayout.incrementBase]
  ring

private theorem incrementR_length (axis : Fin 2) (stage : Fin 4)
    (ordinal : List Bool) (context : QueryContext) :
    (incrementR axis stage ordinal context).length = (startR context).length +
      BrouwerNashLayout.increment (CircuitWords.first context.1.1).length axis ordinal.length stage := by
  simp only [incrementR, List.length_append, incrementBaseR_length,
    List.length_replicate, BrouwerNashLayout.increment]
  omega

private theorem primaryR_length (axis : Fin 2) (ordinal : List Bool) (context : QueryContext) :
    (primaryR axis ordinal context).length = (startR context).length +
      BrouwerNashProgram.primaryBit (CircuitWords.first context.1.1).length axis ordinal.length := by
  have hd : (depthR context).length = (CircuitWords.first context.1.1).length := rfl
  simp only [primaryR, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, List.length_drop, hd, BrouwerNashProgram.primaryBit,
    BrouwerNashLayout.digit]
  have hs : (CircuitWords.first context.1.1).length - (ordinal.length + 1) =
      (CircuitWords.first context.1.1).length - 1 - ordinal.length := by omega
  rw [hs]
  ring

private theorem carryR_length (axis : Fin 2) (ordinal : List Bool) (context : QueryContext) :
    (carryR axis ordinal context).length = if ordinal.length = 0 then BrouwerNashLayout.one else
      (startR context).length + BrouwerNashLayout.increment (CircuitWords.first context.1.1).length axis
        (ordinal.length - 1) 3 := by
  by_cases hz : ordinal.length = 0
  · simp only [carryR, hz, ite_true, BrouwerNashLayout.one, List.length_cons, List.length_nil]
  · simp only [carryR, hz, ite_false, List.length_append, incrementBaseR_length,
      List.length_tail, List.length_replicate, List.length_cons, List.length_nil, BrouwerNashLayout.increment]
    norm_num
    omega

private theorem test_value (axis : Fin 2) (stage : Fin 4) (ordinal : List Bool) (context : QueryContext) :
    test axis stage ordinal context = [decide (context.2.2.1.length = (startR context).length +
      BrouwerNashLayout.increment (CircuitWords.first context.1.1).length axis ordinal.length stage ∧
        ordinal.length < (CircuitWords.first context.1.1).length)] := by
  simp only [test, incrementR_length, depthR, BrouwerNashHeaders.sourceDepthRuler_length]

section Correctness
variable (source code₀ code₁ out action : List Bool)
local notation "b" => List.length (CircuitWords.first source)
local notation "ell₀" => List.length (circuitUnaryPrefix code₀)
local notation "ell₁" => List.length (circuitUnaryPrefix code₁)
local notation "k" => BrouwerNashLayout.dimension b ell₀ ell₁

private theorem raw_coefficients_congr {d e : ℕ} (hde : d = e)
    (g : CircuitFormat.signature.Op × List ℕ)
    (hd : Program.IsCodeFrom CircuitFormat.signature d 0 [g])
    (he : Program.IsCodeFrom CircuitFormat.signature e 0 [g])
    (i : Fin (d * 2)) (j : Fin (e * 2)) (hij : i.val = j.val) :
    BimatrixRawGate.coefficients g hd i = BimatrixRawGate.coefficients g he j := by
  subst e
  have hi : i = j := Fin.ext hij
  subst j
  rfl

private theorem term_coefficients (axis : Fin 2) (stage : Fin 4) (j : List Bool)
    (hj : j.length < b) (t : Fin 41) (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (indexedCoefficientWord axis stage j
      ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j.length stage).coefficients r := by
  let context : QueryContext := ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))
  have hs : (startR context).length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t := by
    simp only [startR_length, context, List.length_replicate, BrouwerNashLayout.sampleBase]
  have hp : BrouwerNashProgram.primaryBit b axis j.length <
      BrouwerNashLayout.sampleWidth b ell₀ ell₁ := by
    fin_cases axis <;>
      simp only [BrouwerNashProgram.primaryBit, BrouwerNashLayout.digit,
        BrouwerNashLayout.sampleWidth] <;> norm_num <;> omega
  have hprimary : (primaryR axis j context).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashProgram.primaryBit b axis j.length)).val := by
    rw [primaryR_length, hs]
    exact (BrouwerNashProgram.slot_val _ _ _ _
      (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hp)).symm
  have hi (s : Fin 4) : (incrementR axis s j context).length =
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashLayout.increment b axis j.length s)).val := by
    rw [incrementR_length, hs]
    exact (BrouwerNashProgram.slot_val _ _ _ _ (BrouwerNashLayout.sample_lt_dimension _ _ _ t _
      (BrouwerNashProgram.increment_lt_sampleWidth _ _ _ axis _ hj s))).symm
  have hc : (carryR axis j context).length = if j.length = 0 then BrouwerNashLayout.one else
      (BrouwerNashProgram.sampleRef b ell₀ ell₁ t
        (BrouwerNashLayout.increment b axis (j.length - 1) 3)).val := by
    rw [carryR_length, hs]
    split_ifs with hz
    · rfl
    · exact (BrouwerNashProgram.slot_val _ _ _ _ (BrouwerNashLayout.sample_lt_dimension _ _ _ t _
        (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis
          (j.length - 1) (by omega) 3))).symm
  have hfirst : (firstR axis stage j context).length < k := by
    rw [firstR]
    split_ifs
    · rw [hi]
      exact Fin.isLt _
    · rw [hprimary]
      exact Fin.isLt _
  have hsecond : (secondR axis stage j context).length < k := by
    rw [secondR]
    split_ifs
    · rw [hi]
      exact Fin.isLt _
    · rw [hc]
      split_ifs
      · exact BrouwerNashProgram.one_lt_dimension _ _ _
      · exact Fin.isLt _
  have href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw axis stage j context] := by
    refine ⟨⟨rfl, ?_⟩, trivial⟩
    intro ref h
    change ref ∈ [(firstR axis stage j context).length, (secondR axis stage j context).length] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact hfirst
    · have he := List.mem_singleton.mp h
      subst ref
      exact hsecond
  have hdim : (dimensionR context).length = k := by
    simp only [dimensionR, context, BrouwerNashHeaders.dimensionRuler_length]
  change binarySignedValue (BimatrixRawGateMachine.coefficientWord
    (dimensionR context) (suffix axis stage j context) action) = _
  rw [suffix_encode]
  have href' : Program.IsCodeFrom CircuitFormat.signature (dimensionR context).length 0
      [raw axis stage j context] := by rwa [hdim]
  let r' : Fin ((dimensionR context).length * 2) := ⟨r.val, by rw [hdim]; exact r.isLt⟩
  have he := BimatrixRawGateMachine.coefficientWord_encode
    (dimensionR context) action (raw axis stage j context) href' [] r' hr
  rw [List.append_nil] at he
  rw [he]
  have hg : BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j.length stage =
      BrouwerNashProgram.guardedRaw (raw axis stage j context) := by
    unfold BrouwerNashProgram.incrementGate
    apply congrArg BrouwerNashProgram.guardedRaw
    fin_cases stage <;>
      simp only [raw, firstR, secondR, Nat.reduceEqDiff, hprimary, hc, hi,
        decide_true, decide_false, ite_true, ite_false] <;> rfl
  rw [hg, BrouwerNashProgram.guardedRaw_eq _ href]
  change BimatrixRawGate.coefficients (raw axis stage j context) href' r' =
    BimatrixRawGate.coefficients (raw axis stage j context) href r
  exact raw_coefficients_congr hdim (raw axis stage j context) href' href r' r rfl

private theorem sampleCoefficientWord_value (axis : Fin 2) (stage : Fin 4) (t : Fin 41)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (sampleCoefficientWord axis stage source code₀ code₁
      (List.replicate t.val false) out action) =
      ∑ j ∈ Finset.range b, if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
        (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  let hit := fun j => decide (out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
    BrouwerNashLayout.increment b axis j stage ∧ j < b)
  let value := fun j => (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r
  have hw : 0 < (BrouwerNashHeaders.widthRuler source code₀ code₁).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hx := binaryIndexedLookup_sum_value (test axis stage) (indexedCoefficientWord axis stage)
    (BrouwerNashHeaders.widthRuler source code₀ code₁)
    ((source, (code₀, code₁)), (List.replicate t.val false, (out, action))) hit value
    (by
      intro ordinal
      rw [test_value, startR_length]
      simp only [List.length_replicate]
      rfl)
    (by
      intro ordinal hhit
      have hj := (of_decide_eq_true hhit).2
      exact term_coefficients source code₀ code₁ out action axis stage ordinal hj t r hr)
    hw (BrouwerNashHeaders.sourceDepthRuler source)
    (by
      intro i _ _
      apply BrouwerNashHeaders.widthRuler_fits
      rw [BrouwerNashHeaders.dimensionRuler_length]
      have hb := BrouwerNashProgram.incrementGate_bound b ell₀ ell₁ t axis i stage r
      rw [← Int.natCast_natAbs] at hb
      exact_mod_cast hb)
    (by
      intro i _ j _ hi hj
      have hi' := (of_decide_eq_true hi).1
      have hj' := (of_decide_eq_true hj).1
      dsimp only [BrouwerNashLayout.increment] at hi' hj'
      omega)
  rw [sampleCoefficientWord_eq, hx]
  change (∑ j ∈ Finset.range b, if hit j then value j else 0) = _
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [hit, value]
  simp only [Finset.mem_range.mp hj, and_true, decide_eq_true_eq]

/-- Each ripple family emits exactly the guarded coefficients of its canonical raw gates. -/
theorem coefficientWord_value (axis : Fin 2) (stage : Fin 4)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage (source) (code₀) (code₁) (out) (action)) =
      ∑ t : Fin 41, ∑ j ∈ Finset.range b,
        if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
          (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  rw [coefficientWord, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  exact sampleCoefficientWord_value source code₀ code₁ out action axis stage t r hr

/-- A valid ripple output selects exactly its own canonical stage, including aliased inputs. -/
theorem coefficientWord_at (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ)
    (hj : j < b) (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.increment b axis j stage) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage (source) (code₀) (code₁) (out) (action)) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r := by
  rw [coefficientWord_value source code₀ code₁ out action axis stage r hr]
  have hhit (s : Fin 41) (i : ℕ) (hi : i < b)
      (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
        BrouwerNashLayout.increment b axis i stage) : s = t ∧ i = j := by
    have hh := BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ s t _ _
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis i hi stage)
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis j hj stage)
      (he.symm.trans hout)
    refine ⟨hh.1, ?_⟩
    dsimp only [BrouwerNashLayout.increment] at hh
    omega
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single j]
    · simp only [hout, ite_true]
    · intro i hi hne
      apply ite_eq_right
      intro he
      exact hne (hhit t i (Finset.mem_range.mp hi) he).2
    · simp [hj]
  · intro s _ hne
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact hne (hhit s i (Finset.mem_range.mp hi) he).1
  · simp

/-- Outputs outside a ripple family retain the total zero fallback. -/
theorem coefficientWord_zero (axis : Fin 2) (stage : Fin 4)
    (hno : ∀ t : Fin 41, ∀ j < b, out.length ≠
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.increment b axis j stage)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (coefficientWord axis stage (source) (code₀) (code₁) (out) (action)) = 0 := by
  rw [coefficientWord_value source code₀ code₁ out action axis stage r hr]
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (hno t j (Finset.mem_range.mp hj))

/-- The complete increment query sums the canonical gates at every allocated ripple output. -/
theorem allCoefficientWord_value (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord (source) (code₀) (code₁) (out) (action)) =
      ∑ axis : Fin 2, ∑ stage : Fin 4, ∑ t : Fin 41, ∑ j ∈ Finset.range b,
        if out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
          BrouwerNashLayout.increment b axis j stage then
          (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r else 0 := by
  rw [allCoefficientWord, binarySignedQuerySum_value]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    coefficientWord_value source code₀ code₁ out action _ _ r hr,
    Fin.sum_univ_two, Fin.sum_univ_four]
  ring

private theorem increment_index_injective (a a' : Fin 2) (s s' : Fin 4)
    (i j : ℕ) (hi : i < b) (hj : j < b)
    (he : BrouwerNashLayout.increment b a i s = BrouwerNashLayout.increment b a' j s') :
    a = a' ∧ i = j ∧ s = s' := by
  have hs := s.isLt
  have hs' := s'.isLt
  fin_cases a <;> fin_cases a' <;>
    simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
      mul_zero, mul_one, add_zero] at he
  · exact ⟨rfl, by omega, Fin.ext (by omega)⟩
  · omega
  · omega
  · exact ⟨rfl, by omega, Fin.ext (by omega)⟩

/-- Across all ripple families, an allocated output selects its own gate exactly once. -/
theorem allCoefficientWord_at (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ)
    (hj : j < b) (hout : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
      BrouwerNashLayout.increment b axis j stage) (r : Fin (k * 2))
    (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord (source) (code₀) (code₁) (out) (action)) =
      (BrouwerNashProgram.incrementGate b ell₀ ell₁ t axis j stage).coefficients r := by
  rw [allCoefficientWord_value source code₀ code₁ out action r hr]
  have hhit (a : Fin 2) (st : Fin 4) (s : Fin 41) (i : ℕ) (hi : i < b)
      (he : out.length = BrouwerNashLayout.sampleBase b ell₀ ell₁ s +
        BrouwerNashLayout.increment b a i st) : a = axis ∧ st = stage := by
    have hh := BrouwerNashQueryRegions.sampleOutput_injective b ell₀ ell₁ s t _ _
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ a i hi st)
      (BrouwerNashProgram.increment_lt_sampleWidth b ell₀ ell₁ axis j hj stage)
      (he.symm.trans hout)
    have heq := increment_index_injective source a axis st stage i j hi hj hh.2
    exact ⟨heq.1, heq.2.2⟩
  rw [Finset.sum_eq_single axis]
  · rw [Finset.sum_eq_single stage]
    · rw [← coefficientWord_value source code₀ code₁ out action axis stage r hr]
      exact coefficientWord_at source code₀ code₁ out action axis stage t j hj hout r hr
    · intro st _ hne
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro i hi
      apply ite_eq_right
      intro he
      exact hne (hhit axis st s i (Finset.mem_range.mp hi) he).2
    · simp
  · intro a _ hne
    apply Finset.sum_eq_zero
    intro st _
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact hne (hhit a st s i (Finset.mem_range.mp hi) he).1
  · simp

/-- The total increment query vanishes outside every allocated ripple output. -/
theorem allCoefficientWord_zero
    (hno : ∀ (axis : Fin 2) (stage : Fin 4) (t : Fin 41) (j : ℕ), j < b →
      out.length ≠ BrouwerNashLayout.sampleBase b ell₀ ell₁ t +
        BrouwerNashLayout.increment b axis j stage)
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord (source) (code₀) (code₁) (out) (action)) = 0 := by
  rw [allCoefficientWord_value source code₀ code₁ out action r hr]
  apply Finset.sum_eq_zero
  intro axis _
  apply Finset.sum_eq_zero
  intro stage _
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (hno axis stage t j (Finset.mem_range.mp hj))

/-- Every ripple output lies in its sample's contiguous increment interval. -/
theorem allCoefficientWord_zero_of_outside
    (hno : ∀ t : Fin 41, ¬ (BrouwerNashLayout.sampleBase b ell₀ ell₁ t + 2 + 4 * b ≤
      out.length ∧ out.length < BrouwerNashLayout.sampleBase b ell₀ ell₁ t + 2 + 12 * b))
    (r : Fin (k * 2)) (hr : action.length = r.val) :
    binarySignedValue (allCoefficientWord (source) (code₀) (code₁) (out) (action)) = 0 := by
  apply allCoefficientWord_zero source code₀ code₁ out action ?_ r hr
  intro axis stage t j hj he
  apply hno t
  have ha := axis.isLt
  have hs := stage.isLt
  have hm := Nat.mul_le_mul_left (4 * b) (show axis.val ≤ 1 by omega)
  dsimp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase] at he
  omega
end Correctness

/-- The contiguous ripple interval consists exactly of four-stage bits on two axes. -/
theorem exists_incrementSlot (b i : ℕ) (hlo : 2 + 4 * b ≤ i) (hhi : i < 2 + 12 * b) :
    ∃ (axis : Fin 2) (stage : Fin 4) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.increment b axis j stage := by
  by_cases hfirst : i < 2 + 8 * b
  · refine ⟨0, ⟨(i - (2 + 4 * b)) % 4, Nat.mod_lt _ (by omega)⟩,
      (i - (2 + 4 * b)) / 4, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
        Fin.val_zero, mul_zero, add_zero]
      omega
  · refine ⟨1, ⟨(i - (2 + 8 * b)) % 4, Nat.mod_lt _ (by omega)⟩,
      (i - (2 + 8 * b)) / 4, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.increment, BrouwerNashLayout.incrementBase,
        Fin.val_one, mul_one]
      omega

/-- Every increment slot is the canonical raw ripple gate at its decoded numeric stage. -/
theorem sampleGate_increment_of_interval (b i : ℕ) (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ)) (t : Fin 41)
    (hlo : 2 + 4 * b ≤ i) (hhi : i < 2 + 12 * b) :
    ∃ (axis : Fin 2) (stage : Fin 4) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.increment b axis j stage ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        BrouwerNashProgram.incrementGate b raw₀.length raw₁.length t axis j stage := by
  obtain ⟨axis, stage, j, hj, hi⟩ := exists_incrementSlot b i hlo hhi
  refine ⟨axis, stage, j, hj, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_increment b raw₀ raw₁ t axis j hj stage

end GameTheory.Complexity.Backend.BrouwerNashIncrementQuery
