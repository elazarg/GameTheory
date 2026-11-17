module

public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinaryIndexedLookup
public import GameTheoryComplexity.Backend.BinarySignedIndicator
public import GameTheoryComplexity.Backend.BinarySignedFiniteSum
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding

@[expose] public section

/-! Extraction coefficients scan the source's actual depth-word suffixes, select
one alternating digit or residual output, and retain fixed-width signed padding.
Source, color codes, sample and both query rulers form an ordinary native context. -/
namespace GameTheory.Complexity.Backend.BrouwerNashExtractionQuery
open Turing.MultiTapeTM
open scoped BigOperators

local notation "QueryContext" =>
  ((List Bool × (List Bool × List Bool)) × (List Bool × (List Bool × List Bool)))
local notation "queryEncoding" =>
  encPair (encPair encBits (encPair encBits encBits))
    (encPair encBits (encPair encBits encBits))
local notation "SumContext" =>
  ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool))
local notation "sumEncoding" =>
  encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)

private def base (context : QueryContext) : List Bool :=
  BrouwerNashHeaders.globalRuler context.1.1 ++ List.replicate
    (context.2.1.length * (BrouwerNashHeaders.sampleRuler context.1.1 context.1.2.1 context.1.2.2).length) true

private def axisOffset (axis : Bool) (context : QueryContext) : List Bool :=
  if axis then List.replicate (2 * (BrouwerNashHeaders.sourceDepthRuler context.1.1).length) true else []

private def digitRuler (axis : Bool) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  base context ++ [false, false] ++ axisOffset axis context ++
    List.replicate (2 * ordinal.length) true

private def remainderRuler (axis : Bool) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  if ordinal.length = 0 then base context ++ (if axis then [false] else [])
  else base context ++ [false, false, false] ++ axisOffset axis context ++
    List.replicate (2 * ordinal.tail.length) true

private def test (axis next : Bool) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  [decide (context.2.2.1.length = (digitRuler axis ordinal context ++
    (if next then [false] else [])).length ∧
      ordinal.length < (BrouwerNashHeaders.sourceDepthRuler context.1.1).length)]

/-- One digit or residual query retains its exact signed scalar coefficient. -/
def indexedCoefficientWord (axis next : Bool) (ordinal : List Bool) (context : QueryContext) : List Bool :=
  let source := context.1.1
  let code₀ := context.1.2.1
  let code₁ := context.1.2.2
  let sample := context.2.1
  let action := context.2.2.2
  let base := BrouwerNashHeaders.globalRuler source ++ List.replicate
    (sample.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
  let axisOffset := if axis then
    List.replicate (2 * (BrouwerNashHeaders.sourceDepthRuler source).length) true else []
  let digitRuler := base ++ [false, false] ++ axisOffset ++ List.replicate (2 * ordinal.length) true
  let remainderRuler := if ordinal.length = 0 then base ++ (if axis then [false] else [])
    else base ++ [false, false, false] ++ axisOffset ++ List.replicate (2 * ordinal.tail.length) true
  let bits := binaryLengthWord (BrouwerNashHeaders.dimensionRuler source code₀ code₁)
  if next then binarySignedSub
    (binarySignedIndicator ![action, remainderRuler, [false, false, false] ++ bits])
    (binarySignedIndicator ![action, digitRuler, [false, false] ++ bits])
  else binarySignedSub
    (binarySignedIndicator ![action, remainderRuler, [false, false] ++ bits]) [false, true]

private theorem indexedCoefficientWord_eq (axis next : Bool)
    (ordinal : List Bool) (context : QueryContext) :
    indexedCoefficientWord axis next ordinal context =
      let bits := binaryLengthWord (BrouwerNashHeaders.dimensionRuler
        context.1.1 context.1.2.1 context.1.2.2)
      if next then binarySignedSub
        (binarySignedIndicator ![context.2.2.2, remainderRuler axis ordinal context,
          [false, false, false] ++ bits])
        (binarySignedIndicator ![context.2.2.2, digitRuler axis ordinal context,
          [false, false] ++ bits])
      else binarySignedSub
        (binarySignedIndicator ![context.2.2.2, remainderRuler axis ordinal context,
          [false, false] ++ bits]) [false, true] := rfl

/-- Scan the original depth word for one extraction output in one sample and coordinate. -/
def sampleCoefficientWord (axis next : Bool)
    (source code₀ code₁ sample out action : List Bool) : List Bool :=
  let test (ordinal : List Bool) (context : QueryContext) : List Bool :=
    let source := context.1.1
    let code₀ := context.1.2.1
    let code₁ := context.1.2.2
    let sample := context.2.1
    let out := context.2.2.1
    let base := BrouwerNashHeaders.globalRuler source ++ List.replicate
      (sample.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length) true
    let axisOffset := if axis then
      List.replicate (2 * (BrouwerNashHeaders.sourceDepthRuler source).length) true else []
    let digitRuler := base ++ [false, false] ++ axisOffset ++ List.replicate (2 * ordinal.length) true
    [decide (out.length = (digitRuler ++ (if next then [false] else [])).length ∧
      ordinal.length < (BrouwerNashHeaders.sourceDepthRuler source).length)]
  binaryIndexedLookup test (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.sourceDepthRuler source) (BrouwerNashHeaders.widthRuler source code₀ code₁)
    ((source, (code₀, code₁)), (sample, (out, action)))

private theorem sampleCoefficientWord_eq (axis next : Bool)
    (source code₀ code₁ ordinal out action : List Bool) :
    sampleCoefficientWord axis next source code₀ code₁ ordinal out action =
      binaryIndexedLookup (test axis next) (indexedCoefficientWord axis next)
        (BrouwerNashHeaders.sourceDepthRuler source)
        (BrouwerNashHeaders.widthRuler source code₀ code₁)
        ((source, (code₀, code₁)), (ordinal, (out, action))) := rfl

private def sample (ordinal : List Bool) (context : SumContext) : List Bool :=
  binarySignedAdd
    (binarySignedAdd
      (sampleCoefficientWord false false context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2)
      (sampleCoefficientWord false true context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2))
    (binarySignedAdd
      (sampleCoefficientWord true false context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2)
      (sampleCoefficientWord true true context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2))

/-- Sum the forty-one sample queries in ascending ordinal order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  let sample (ordinal : List Bool) (context : SumContext) : List Bool :=
    binarySignedAdd
      (binarySignedAdd
        (sampleCoefficientWord false false context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2)
        (sampleCoefficientWord false true context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2))
      (binarySignedAdd
        (sampleCoefficientWord true false context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2)
        (sampleCoefficientWord true true context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.1 context.2.2))
  binarySignedFiniteSum sample 41 ((source, (code₀, code₁)), (out, action))

private theorem coefficientWord_eq (source code₀ code₁ out action : List Bool) :
    coefficientWord source code₀ code₁ out action =
      binarySignedFiniteSum sample 41 ((source, (code₀, code₁)), (out, action)) := rfl

private theorem base_polyTime {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => base (context a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    (BrouwerNashHeaders.globalRuler_polyTime hc.fst'.fst')
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.length_bits_comp hc.snd'.fst')
        (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sampleRuler_polyTime
          hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd'))))

private theorem axisOffset_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {context : Input → QueryContext} (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => axisOffset axis (context a)) input encBits := by
  cases axis
  · exact ComputableInPolyTime.const []
  · exact (ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sourceDepthRuler_polyTime hc.fst'.fst')))

private theorem digitRuler_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => digitRuler axis (ordinal a) (context a)) input encBits := by
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend (base_polyTime hc) (ComputableInPolyTime.const [false, false]))
      (axisOffset_polyTime axis hc))
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.length_bits_comp hi)))

private theorem remainderRuler_polyTime (axis : Bool) {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => remainderRuler axis (ordinal a) (context a)) input encBits := by
  have hempty := (ComputableInPolyTime.length_bits_comp hi).decide_eq' (ComputableInPolyTime.const 0)
  have hbase := base_polyTime hc
  have hyes := ComputableInPolyTime.bitsAppend hbase
    (ComputableInPolyTime.const (if axis then [false] else []))
  have htail := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hi
  have hno := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsAppend hbase (ComputableInPolyTime.const [false, false, false]))
      (axisOffset_polyTime axis hc))
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.length_bits_comp htail)))
  exact (hempty.ite hyes hno).of_enc_eq (fun a => by
    simp only [remainderRuler, Function.comp_apply, decide_eq_true_eq])

private theorem test_polyTime (axis next : Bool) {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => test axis next (ordinal a) (context a)) input encBits := by
  have houtput := ComputableInPolyTime.bitsAppend (digitRuler_polyTime axis hi hc)
    (ComputableInPolyTime.const (if next then [false] else []))
  have heq := (ComputableInPolyTime.length_bits_comp hc.snd'.snd'.fst').decide_eq'
    (ComputableInPolyTime.length_bits_comp houtput)
  have hlt := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' (ComputableInPolyTime.length_bits_comp hi).tidy
      (ComputableInPolyTime.length_bits_comp
        (BrouwerNashHeaders.sourceDepthRuler_polyTime hc.fst'.fst')).tidy)
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_and heq hlt)
    (ComputableInPolyTime.const [])

@[fun_prop] theorem indexedCoefficientWord_polyTime (axis next : Bool)
    {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → QueryContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input queryEncoding) :
    ComputableInPolyTime (fun a => indexedCoefficientWord axis next (ordinal a) (context a))
      input encBits := by
  have hb := binaryLengthWord_polyTime.comp (BrouwerNashHeaders.dimensionRuler_polyTime
    hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd')
  have hcapacity := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false]) hb
  have hdouble := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false, false, false]) hb
  have hrem := remainderRuler_polyTime axis hi hc
  have hdigit := digitRuler_polyTime axis hi hc
  have indicator {ruler scalar : Input → List Bool}
      (hr : ComputableInPolyTime ruler input encBits)
      (hs : ComputableInPolyTime scalar input encBits) :
      ComputableInPolyTime (fun a => binarySignedIndicator
        ![(context a).2.2.2, ruler a, scalar a]) input encBits := by
    have hargs : ComputableInPolyTime (fun a : Input =>
        ![(context a).2.2.2, ruler a, scalar a]) input (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact hc.snd'.snd'.snd'
      · exact hr
      · simpa only [Matrix.cons_val_succ', Matrix.cons_val_zero'] using hs
    exact binarySignedIndicator_polyTime.comp hargs
  cases next
  · exact (binarySignedSub_polyTime (indicator hrem hcapacity)
      (ComputableInPolyTime.const [false, true])).of_enc_eq (fun a => by
        simp only [indexedCoefficientWord_eq, Bool.false_eq_true, ite_false, Function.comp_apply])
  · exact (binarySignedSub_polyTime (indicator hrem hdouble)
      (indicator hdigit hcapacity)).of_enc_eq (fun a => by
        simp only [indexedCoefficientWord_eq, ite_true, Function.comp_apply])

@[fun_prop] theorem sampleCoefficientWord_polyTime (axis next : Bool)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ sample out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ht : ComputableInPolyTime sample input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => sampleCoefficientWord axis next
      (source a) (code₀ a) (code₁ a) (sample a) (out a) (action a)) input encBits := by
  have htest := test_polyTime axis next
    (ComputableInPolyTime.snd queryEncoding encBits)
    (ComputableInPolyTime.fst queryEncoding encBits)
  have hterm := indexedCoefficientWord_polyTime axis next
    (ComputableInPolyTime.snd queryEncoding encBits)
    (ComputableInPolyTime.fst queryEncoding encBits)
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ht.prod (ho.prod ha))
  exact binaryIndexedLookup_polyTime htest hterm
    (BrouwerNashHeaders.sourceDepthRuler_polyTime hs)
    (BrouwerNashHeaders.widthRuler_polyTime hs hc₀ hc₁) hcontext

private theorem sample_polyTime {Input : Type} {input : Input ↪ List Bool}
    {ordinal : Input → List Bool} {context : Input → SumContext}
    (hi : ComputableInPolyTime ordinal input encBits)
    (hc : ComputableInPolyTime context input sumEncoding) :
    ComputableInPolyTime (fun a => sample (ordinal a) (context a)) input encBits := by
  have hterm (axis next : Bool) := sampleCoefficientWord_polyTime axis next
    hc.fst'.fst' hc.fst'.snd'.fst' hc.fst'.snd'.snd' hi hc.snd'.fst' hc.snd'.snd'
  exact binarySignedAdd_polyTime (binarySignedAdd_polyTime (hterm false false) (hterm false true))
    (binarySignedAdd_polyTime (hterm true false) (hterm true true))

/-- The joint query certificate charges every source, code and original ruler producer. -/
@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a)
      (out a) (action a)) input encBits := by
  have hsample := sample_polyTime (ComputableInPolyTime.snd sumEncoding encBits)
    (ComputableInPolyTime.fst sumEncoding encBits)
  have hcontext := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  exact binarySignedFiniteSum_polyTime hsample 41 hcontext

private theorem test_value (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    test axis next (ordinal) ((source, (code₀, code₁)), (sample, (out, action))) =
      [decide (out.length = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
          sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * ordinal.length +
          (if next then 1 else 0) ∧ ordinal.length < (CircuitWords.first source).length)] := by
  simp only [test, digitRuler, base, axisOffset, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, BrouwerNashHeaders.sourceDepthRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
  congr 2
  apply propext
  cases axis <;> cases next <;> simp

private theorem remainderRuler_length (axis : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (remainderRuler axis (ordinal) ((source, (code₀, code₁)), (sample, (out, action)))).length =
      BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (CircuitWords.first source).length else 0) +
            2 * (ordinal.length - 1)) := by
  unfold remainderRuler base axisOffset
  split_ifs <;>
    simp only [List.length_append, List.length_replicate, List.length_tail,
      List.length_cons, List.length_nil, BrouwerNashHeaders.globalRuler_length,
      BrouwerNashHeaders.sampleRuler_length, BrouwerNashHeaders.sourceDepthRuler_length] <;>
    omega

private theorem digitRuler_length (axis : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (digitRuler axis (ordinal) ((source, (code₀, code₁)), (sample, (out, action)))).length =
      BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * ordinal.length := by
  simp only [digitRuler, base, axisOffset, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, BrouwerNashHeaders.globalRuler_length,
    BrouwerNashHeaders.sampleRuler_length, BrouwerNashHeaders.sourceDepthRuler_length]
  cases axis <;> simp

private theorem capacity_value (r : List Bool) :
    binarySignedValue ([false, false] ++ binaryLengthWord r) = 2 * (r.length : ℤ) := by
  change ((2 * ofBits (binaryLengthWord r) : ℕ) : ℤ) = _
  rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_ofNat]

private theorem doubleCapacity_value (r : List Bool) :
    binarySignedValue ([false, false, false] ++ binaryLengthWord r) =
      4 * (r.length : ℤ) := by
  change ((2 * (2 * ofBits (binaryLengthWord r)) : ℕ) : ℤ) = _
  rw [binaryLengthWord_value, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Digit and residual coefficients have their exact signed scalar interpretations. -/
theorem indexedCoefficientWord_value (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    let k := BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
    let base := BrouwerNashLayout.globalCount (CircuitWords.first source).length +
      sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
    let rem := base + (if ordinal.length = 0 then (if axis then 1 else 0)
      else 3 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * (ordinal.length - 1))
    let digit := base + 2 + (if axis then 2 * (CircuitWords.first source).length else 0) +
      2 * ordinal.length
    binarySignedValue (indexedCoefficientWord axis next
      (ordinal) ((source, (code₀, code₁)), (sample, (out, action)))) =
      if next then
        (if action.length / 2 = rem ∧ action.length % 2 = 1 then 4 * (k : ℤ) else 0) -
        (if action.length / 2 = digit ∧ action.length % 2 = 1 then 2 * (k : ℤ) else 0)
      else (if action.length / 2 = rem ∧ action.length % 2 = 1 then 2 * (k : ℤ) else 0) - 1 := by
  dsimp only
  rw [indexedCoefficientWord_eq]
  cases next
  · simp only [Bool.false_eq_true, ite_false]
    rw [binarySignedSub_value, binarySignedIndicator_value, capacity_value,
      remainderRuler_length, BrouwerNashHeaders.dimensionRuler_length]
    rfl
  · simp only [ite_true]
    rw [binarySignedSub_value, binarySignedIndicator_value, binarySignedIndicator_value,
      doubleCapacity_value, capacity_value, remainderRuler_length, digitRuler_length,
      BrouwerNashHeaders.dimensionRuler_length]

private theorem guarded_natAbs (P : Prop) [Decidable P] (z : ℤ) :
    (if P then z else 0).natAbs ≤ z.natAbs := by
  by_cases hp : P <;> simp [hp]

private theorem indexedCoefficientWord_bound (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) :
    (binarySignedValue (indexedCoefficientWord axis next
      (ordinal) ((source, (code₀, code₁)), (sample, (out, action))))).natAbs ≤
      100 * BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
  have hk := BrouwerNashLayout.dimension_pos (CircuitWords.first source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
  rw [indexedCoefficientWord_value]
  cases next
  · simp only [Bool.false_eq_true, ite_false]
    refine (Int.natAbs_sub_le _ _).trans ?_
    have hi := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (CircuitWords.first source).length else 0) +
            2 * (ordinal.length - 1)) ∧ action.length % 2 = 1)
      (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hi ⊢
    omega
  · simp only [ite_true]
    refine (Int.natAbs_sub_le _ _).trans ?_
    have hi := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if ordinal.length = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (CircuitWords.first source).length else 0) +
            2 * (ordinal.length - 1)) ∧ action.length % 2 = 1)
      (4 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    have hj := guarded_natAbs
      (action.length / 2 = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * ordinal.length ∧
        action.length % 2 = 1)
      (2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ))
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hi hj ⊢
    omega

/-- A unique digit or residual output contributes its guarded indexed coefficient. -/
theorem sampleCoefficientWord_value (axis next : Bool)
    (sample out action source code₀ code₁ : List Bool) :
    binarySignedValue (sampleCoefficientWord axis next
      (source) (code₀) (code₁) (sample) (out) (action)) =
      ∑ i ∈ Finset.range (CircuitWords.first source).length,
        if out.length = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
            sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
            2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * i +
            (if next then 1 else 0) then
          binarySignedValue (indexedCoefficientWord axis next
            (List.replicate i false) ((source, (code₀, code₁)), (sample, (out, action)))) else 0 := by
  let hit := fun i => decide (out.length =
    BrouwerNashLayout.globalCount (CircuitWords.first source).length +
      sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
      2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * i +
      (if next then 1 else 0) ∧ i < (CircuitWords.first source).length)
  let value := fun i => binarySignedValue (indexedCoefficientWord axis next
    (List.replicate i false) ((source, (code₀, code₁)), (sample, (out, action))))
  have hw : 0 < (BrouwerNashHeaders.widthRuler (source) (code₀) (code₁)).length := by
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hx := binaryIndexedLookup_sum_value (test axis next) (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.widthRuler (source) (code₀) (code₁))
    ((source, (code₀, code₁)), (sample, (out, action))) hit value
    (fun ordinal => test_value axis next ordinal sample out action source code₀ code₁)
    (by
      intro ordinal _
      dsimp only [value]
      rw [indexedCoefficientWord_value, indexedCoefficientWord_value]
      simp only [List.length_replicate]) hw
    (BrouwerNashHeaders.sourceDepthRuler (source))
    (by
      intro i _ _
      apply BrouwerNashHeaders.widthRuler_fits
      rw [BrouwerNashHeaders.dimensionRuler_length]
      exact indexedCoefficientWord_bound axis next (List.replicate i false)
        sample out action source code₀ code₁)
    (by
      intro i _ j _ hi hj
      have hi' := of_decide_eq_true hi
      have hj' := of_decide_eq_true hj
      omega)
  change binarySignedValue (binaryIndexedLookup (test axis next) (indexedCoefficientWord axis next)
    (BrouwerNashHeaders.sourceDepthRuler (source))
    (BrouwerNashHeaders.widthRuler (source) (code₀) (code₁))
    ((source, (code₀, code₁)), (sample, (out, action)))) = _
  rw [hx]
  change (∑ i ∈ Finset.range (CircuitWords.first source).length, if hit i then value i else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  have hir := Finset.mem_range.mp hi
  dsimp only [hit, value]
  simp only [hir, and_true, decide_eq_true_eq]

/-- The emitted extraction coefficients equal the guarded sum over the canonical allocation. -/
theorem coefficientWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (coefficientWord (source) (code₀) (code₁) (out) (action)) =
      ∑ t : Fin 41, ∑ axis : Fin 2, ∑ next : Fin 2,
        ∑ i ∈ Finset.range (CircuitWords.first source).length,
          if out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
              2 + 2 * (CircuitWords.first source).length * axis.val + 2 * i + next.val then
            binarySignedValue (indexedCoefficientWord (decide (axis = 1)) (decide (next = 1))
              (List.replicate i false) ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) else 0 := by
  rw [coefficientWord_eq, binarySignedFiniteSum_value, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t _
  rw [sample, binarySignedAdd_value, binarySignedAdd_value, binarySignedAdd_value,
    sampleCoefficientWord_value, sampleCoefficientWord_value,
    sampleCoefficientWord_value, sampleCoefficientWord_value]
  simp only [Fin.sum_univ_two, List.length_replicate]
  norm_num [BrouwerNashLayout.sampleBase]

private theorem remainder_coefficients {k : ℕ} (a z : Fin k) (r : Fin (k * 2)) :
    (GameTheory.Finite.BimatrixBinaryExtraction.remainderGate a z).coefficients r =
      (if r = finProdFinEquiv (a, 1) then 4 * (k : ℤ) else 0) -
      (if r = finProdFinEquiv (z, 1) then 2 * (k : ℤ) else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  by_cases hb : bit = 0
  · subst bit
    simp [GameTheory.Finite.BimatrixBinaryExtraction.remainderGate,
      GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
  · have hb : bit = 1 := by
      apply Fin.ext
      have hlt := bit.isLt
      have hne : bit.val ≠ 0 := fun h => hb (Fin.ext h)
      omega
    subst bit
    simp [GameTheory.Finite.BimatrixBinaryExtraction.remainderGate,
      GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
    rfl

/-- An indexed query at a valid extraction stage agrees with the canonical game gate. -/
theorem indexedCoefficientWord_gate (axis next : Bool)
    (ordinal sample out action source code₀ code₁ : List Bool) (t : Fin 41) (j : ℕ)
    (hj : j < (CircuitWords.first source).length) (ho : ordinal.length = j) (ht : sample.length = t.val)
    (r : Fin (BrouwerNashLayout.dimension (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length * 2))
    (hr : action.length = r.val) :
    binarySignedValue (indexedCoefficientWord axis next
      (ordinal) ((source, (code₀, code₁)), (sample, (out, action)))) =
      if next then
        (GameTheory.Finite.BimatrixBinaryExtraction.remainderGate
          (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (CircuitWords.first source).length (if axis then 1 else 0) j))
          (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.digit (CircuitWords.first source).length
              (if axis then 1 else 0) j))).coefficients r
      else (GameTheory.Finite.BimatrixBinaryExtraction.digitGate
          (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (CircuitWords.first source).length
              (if axis then 1 else 0) j))).coefficients r := by
  have hrem : BrouwerNashLayout.remainder (CircuitWords.first source).length (if axis then 1 else 0) j <
      BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.remainder, BrouwerNashLayout.jitter,
      BrouwerNashLayout.sampleWidth]
    cases axis <;> norm_num <;> split_ifs <;> omega
  have hdig : BrouwerNashLayout.digit (CircuitWords.first source).length (if axis then 1 else 0) j <
      BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.digit, BrouwerNashLayout.sampleWidth]
    cases axis <;> norm_num <;> omega
  have hrv := BrouwerNashProgram.slot_val (CircuitWords.first source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length _
    (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hrem)
  have hdv := BrouwerNashProgram.slot_val (CircuitWords.first source).length
    (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length _
    (BrouwerNashLayout.sample_lt_dimension _ _ _ t _ hdig)
  have heRem := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.remainder (CircuitWords.first source).length (if axis then 1 else 0) j))
  have heDig := BrouwerNashCoefficientQuery.pairedAction_iff r
    (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
      (BrouwerNashLayout.digit (CircuitWords.first source).length (if axis then 1 else 0) j))
  dsimp only [BrouwerNashProgram.sampleRef] at heRem heDig
  rw [hrv] at heRem
  rw [hdv] at heDig
  rw [indexedCoefficientWord_value, ho, ht, hr]
  have heRem' :
      (r.val / 2 = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        t.val * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        (if j = 0 then (if axis then 1 else 0)
          else 3 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * (j - 1)) ∧
          r.val % 2 = 1) ↔
        r = finProdFinEquiv
          (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.remainder (CircuitWords.first source).length
              (if axis then 1 else 0) j), 1) := by
    convert heRem using 1
    · cases axis <;> by_cases hj0 : j = 0 <;>
        simp [hj0, BrouwerNashLayout.sampleBase, BrouwerNashLayout.remainder,
          BrouwerNashLayout.jitter]
    · rfl
  have heDig' :
      (r.val / 2 = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        t.val * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * j ∧ r.val % 2 = 1) ↔
        r = finProdFinEquiv
          (BrouwerNashProgram.sampleRef (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t
            (BrouwerNashLayout.digit (CircuitWords.first source).length (if axis then 1 else 0) j), 1) := by
    convert heDig using 1
    · cases axis <;> simp [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] <;> omega
    · rfl
  cases next
  · simp only [Bool.false_eq_true, ite_false,
      GameTheory.Finite.BimatrixBinaryExtraction.digitGate, mul_ite, mul_one, mul_zero,
      heRem']
  · simp only [ite_true, remainder_coefficients, heRem', heDig']

/-- A sample scan preserves the exact coefficient at its allocated extraction output. -/
theorem sampleCoefficientWord_at (axis next : Bool)
    (sample out action source code₀ code₁ : List Bool) (t : Fin 41) (j : ℕ)
    (hj : j < (CircuitWords.first source).length) (ht : sample.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (CircuitWords.first source).length (if axis then 1 else 0) j +
        (if next then 1 else 0)) :
    binarySignedValue (sampleCoefficientWord axis next
      (source) (code₀) (code₁) (sample) (out) (action)) =
      binarySignedValue (indexedCoefficientWord axis next
        (List.replicate j false) ((source, (code₀, code₁)), (sample, (out, action)))) := by
  rw [sampleCoefficientWord_value, Finset.sum_eq_single j]
  · have he : out.length = BrouwerNashLayout.globalCount (CircuitWords.first source).length +
        sample.length * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
        2 + (if axis then 2 * (CircuitWords.first source).length else 0) + 2 * j +
          (if next then 1 else 0) := by
      rw [ht]
      simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] at ho
      cases axis <;> norm_num at ho ⊢ <;> omega
    exact ite_eq_left he
  · intro i _ hne
    apply ite_eq_right
    intro he
    rw [ht] at he
    simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit] at ho
    cases axis <;> norm_num at ho he <;> omega
  · intro hno
    exact False.elim (hno (Finset.mem_range.mpr hj))

/-- With no allocated digit or remainder output, every extraction coefficient is zero. -/
theorem coefficientWord_eq_zero (out action source code₀ code₁ : List Bool)
    (hno : ∀ (t : Fin 41) (axis next : Fin 2) (j : ℕ), j < (CircuitWords.first source).length →
      out.length ≠ BrouwerNashLayout.sampleBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
        BrouwerNashLayout.digit (CircuitWords.first source).length axis j + next.val) :
    binarySignedValue (coefficientWord (source) (code₀) (code₁) (out) (action)) = 0 := by
  rw [coefficientWord_value]
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro axis _
  apply Finset.sum_eq_zero
  intro next _
  apply Finset.sum_eq_zero
  intro j hj
  apply ite_eq_right
  intro he
  apply hno t axis next j (Finset.mem_range.mp hj)
  dsimp only [BrouwerNashLayout.digit]
  omega

private theorem extraction_injective (b ell₀ ell₁ : ℕ)
    (t t' : Fin 41) (a a' s s' : Fin 2) (j j' : ℕ) (hj : j < b) (hj' : j' < b)
    (he : BrouwerNashLayout.sampleBase b ell₀ ell₁ t + BrouwerNashLayout.digit b a j + s.val =
      BrouwerNashLayout.sampleBase b ell₀ ell₁ t' +
        BrouwerNashLayout.digit b a' j' + s'.val) :
    t = t' ∧ a = a' ∧ s = s' ∧ j = j' := by
  let w := BrouwerNashLayout.sampleWidth b ell₀ ell₁
  have hw : 2 + 4 * b ≤ w := by
    dsimp [w, BrouwerNashLayout.sampleWidth]
    omega
  have ha := a.isLt
  have ha' := a'.isLt
  have hs := s.isLt
  have hs' := s'.isLt
  have ho : BrouwerNashLayout.digit b a j + s.val < w := by
    dsimp [BrouwerNashLayout.digit]
    have hmul := Nat.mul_le_mul_left (2 * b) (show a.val ≤ 1 by omega)
    omega
  have ho' : BrouwerNashLayout.digit b a' j' + s'.val < w := by
    dsimp [BrouwerNashLayout.digit]
    have hmul := Nat.mul_le_mul_left (2 * b) (show a'.val ≤ 1 by omega)
    omega
  have ht : t = t' := by
    apply Fin.ext
    dsimp [BrouwerNashLayout.sampleBase] at he
    change _ + t.val * w + _ + _ = _ + t'.val * w + _ + _ at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := Nat.mul_le_mul_right w (show t.val + 1 ≤ t'.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right w (show t'.val + 1 ≤ t.val by omega)
      rw [Nat.add_mul, one_mul] at hm
      omega
  subst t'
  have he' : BrouwerNashLayout.digit b a j + s.val =
      BrouwerNashLayout.digit b a' j' + s'.val := by omega
  refine ⟨rfl, ?_⟩
  dsimp [BrouwerNashLayout.digit] at he'
  fin_cases a <;> fin_cases a' <;> fin_cases s <;> fin_cases s' <;>
    simp_all <;> omega

/-- An allocated extraction output receives exactly its canonical coefficient query. -/
theorem coefficientWord_at (out action source code₀ code₁ : List Bool)
    (t : Fin 41) (axis next : Fin 2) (j : ℕ) (hj : j < (CircuitWords.first source).length)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (CircuitWords.first source).length axis j + next.val) :
    binarySignedValue (coefficientWord (source) (code₀) (code₁) (out) (action)) =
      binarySignedValue (indexedCoefficientWord (decide (axis = 1)) (decide (next = 1))
        (List.replicate j false) ((source, (code₀, code₁)), (List.replicate t.val false, (out, action)))) := by
  rw [coefficientWord_value]
  have hhit (t' : Fin 41) (a' s' : Fin 2) (j' : ℕ) (hj' : j' < (CircuitWords.first source).length)
      (he : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t' +
        2 + 2 * (CircuitWords.first source).length * a'.val + 2 * j' + s'.val) :
      t = t' ∧ axis = a' ∧ next = s' ∧ j = j' := by
    apply extraction_injective (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length
      t t' axis a' next s' j j' hj hj'
    simpa only [BrouwerNashLayout.digit, Nat.add_assoc] using ho.symm.trans he
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single axis]
    · rw [Finset.sum_eq_single next]
      · rw [Finset.sum_eq_single j]
        · apply ite_eq_left
          simpa only [BrouwerNashLayout.digit, Nat.add_assoc] using ho
        · intro j' hj' hne
          apply ite_eq_right
          intro he
          exact hne (hhit t axis next j' (Finset.mem_range.mp hj') he).2.2.2.symm
        · intro hno
          exact False.elim (hno (Finset.mem_range.mpr hj))
      · intro s' _ hne
        apply Finset.sum_eq_zero
        intro j' hj'
        apply ite_eq_right
        intro he
        exact hne (hhit t axis s' j' (Finset.mem_range.mp hj') he).2.2.1.symm
      · simp
    · intro a' _ hne
      apply Finset.sum_eq_zero
      intro s' _
      apply Finset.sum_eq_zero
      intro j' hj'
      apply ite_eq_right
      intro he
      exact hne (hhit t a' s' j' (Finset.mem_range.mp hj') he).2.1.symm
    · simp
  · intro t' _ hne
    apply Finset.sum_eq_zero
    intro a' _
    apply Finset.sum_eq_zero
    intro s' _
    apply Finset.sum_eq_zero
    intro j' hj'
    apply ite_eq_right
    intro he
    exact hne (hhit t' a' s' j' (Finset.mem_range.mp hj') he).1.symm
  · simp

/-- Extraction emits zero outside every sample's contiguous extraction interval. -/
theorem coefficientWord_eq_zero_of_outside (out action source code₀ code₁ : List Bool)
    (hno : ∀ t : Fin 41,
      ¬ (BrouwerNashLayout.sampleBase (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + 2 ≤
          out.length ∧
        out.length < BrouwerNashLayout.sampleBase (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
            2 + 4 * (CircuitWords.first source).length)) :
    binarySignedValue (coefficientWord (source) (code₀) (code₁) (out) (action)) = 0 := by
  apply coefficientWord_eq_zero
  intro t axis next j hj he
  apply hno t
  have ha := axis.isLt
  have hn := next.isLt
  have hm := Nat.mul_le_mul_left (2 * (CircuitWords.first source).length)
    (show axis.val ≤ 1 by omega)
  dsimp only [BrouwerNashLayout.digit] at he
  omega

/-- The contiguous extraction interval consists exactly of two-bit digit stages on two axes. -/
theorem exists_extractionSlot (b i : ℕ) (hlo : 2 ≤ i) (hhi : i < 2 + 4 * b) :
    ∃ (axis stage : Fin 2) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.digit b axis j + stage.val := by
  by_cases hfirst : i < 2 + 2 * b
  · refine ⟨0, ⟨(i - 2) % 2, Nat.mod_lt _ (by omega)⟩, (i - 2) / 2, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.digit, Fin.val_zero, mul_zero, add_zero]
      omega
  · refine ⟨1, ⟨(i - 2 - 2 * b) % 2, Nat.mod_lt _ (by omega)⟩,
      (i - 2 - 2 * b) / 2, ?_, ?_⟩
    · omega
    · simp only [BrouwerNashLayout.digit, Fin.val_one, mul_one]
      omega

/-- Every extraction slot selects its canonical digit or remainder gate. -/
theorem sampleGate_extraction_of_interval (b i : ℕ)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ)) (t : Fin 41)
    (hlo : 2 ≤ i) (hhi : i < 2 + 4 * b) :
    ∃ (axis stage : Fin 2) (j : ℕ), j < b ∧
      i = BrouwerNashLayout.digit b axis j + stage.val ∧
      BrouwerNashProgram.sampleGate b raw₀ raw₁ t i =
        if stage.val = 0 then GameTheory.Finite.BimatrixBinaryExtraction.digitGate
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.remainder b axis j))
        else GameTheory.Finite.BimatrixBinaryExtraction.remainderGate
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.remainder b axis j))
          (BrouwerNashProgram.sampleRef b raw₀.length raw₁.length t
            (BrouwerNashLayout.digit b axis j)) := by
  obtain ⟨axis, stage, j, hj, hi⟩ := exists_extractionSlot b i hlo hhi
  refine ⟨axis, stage, j, hj, hi, ?_⟩
  rw [hi]
  exact BrouwerNashProgram.sampleGate_extraction b raw₀ raw₁ t axis j hj stage

end GameTheory.Complexity.Backend.BrouwerNashExtractionQuery
