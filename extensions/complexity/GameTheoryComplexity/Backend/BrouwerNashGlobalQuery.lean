module

public import GameTheoryComplexity.Backend.BrouwerNashAverageQuery
public import GameTheoryComplexity.Backend.BrouwerNashCoefficientQuery
public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinaryIndexedLookup
public import GameTheoryComplexity.Backend.BinarySignedIndicator
public import GameTheoryComplexity.Backend.BinaryUnaryEncoding

@[expose] public section

/-! Shared affine feedback queries retain the source and both compiled color words.
Bounded lookup passes every actual precision suffix to its callback. Signed sums
retain their original addition order before the fixed-width program writer. -/
namespace GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
open Turing.MultiTapeTM Cslib.BitString
open BrouwerNashCoefficientQuery

/-- The alpha chain starts at the constant-one wire and then uses its preceding wire. -/
def alphaPredecessor (ordinal : List Bool) : List Bool :=
  if ordinal.length = 0 then [false, false] else [false, false, false] ++ ordinal

@[fun_prop] theorem alphaPredecessor_polyTime :
    ComputableInPolyTime alphaPredecessor encBits encBits := by
  have hn := ComputableInPolyTime.length_bits_comp
    (ComputableInPolyTime.id' (encIn := encBits))
  have he := hn.decide_eq' (ComputableInPolyTime.const 0)
  exact (he.ite (.const [false, false])
    (ComputableInPolyTime.bitsAppend (.const [false, false, false]) (.id'))).of_enc_eq
      (fun ordinal => by simp only [alphaPredecessor, decide_eq_true_eq])

/-- Only the designated output within the precision chain can select a term. -/
def alphaTest (source ordinal out : List Bool) : List Bool :=
  [decide (out.length = 4 + ordinal.length ∧
    ordinal.length < (BrouwerNashHeaders.precisionRuler source).length)]

@[fun_prop] theorem alphaTest_polyTime
    {Input : Type} {input : Input ↪ List Bool} {source ordinal out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hi : ComputableInPolyTime ordinal input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => alphaTest (source a) (ordinal a) (out a)) input encBits := by
  have hn := ComputableInPolyTime.length_bits_comp hi
  have he := (ComputableInPolyTime.length_bits_comp ho).decide_eq'
    (ComputableInPolyTime.unary_add' (.const 4) hn)
  have hlt := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' hn.tidy
      (ComputableInPolyTime.length_bits_comp
        (BrouwerNashHeaders.precisionRuler_polyTime hs)).tidy)
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_and he hlt) (.const [])

private theorem indicator_polyTime
    {Input : Type} {input : Input ↪ List Bool} {action position coefficient : Input → List Bool}
    (ha : ComputableInPolyTime action input encBits)
    (hp : ComputableInPolyTime position input encBits)
    (hc : ComputableInPolyTime coefficient input encBits) :
    ComputableInPolyTime
      (fun a => binarySignedIndicator ![action a, position a, coefficient a]) input encBits := by
  have hargs : ComputableInPolyTime
      (fun a => ![action a, position a, coefficient a]) input (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ha
    · exact hp
    · exact hc
  have hcert := binarySignedIndicator_polyTime.comp hargs
  exact hcert

/-- The selected predecessor contributes one dimension unit to action one. -/
def alphaTerm (source code₀ code₁ ordinal action : List Bool) : List Bool :=
  binarySignedIndicator ![action, alphaPredecessor ordinal,
    false :: binaryLengthWord (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]

@[fun_prop] theorem alphaTerm_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ ordinal action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (hi : ComputableInPolyTime ordinal input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => alphaTerm (source a) (code₀ a) (code₁ a) (ordinal a) (action a))
      input encBits := by
  have hcert := indicator_polyTime ha (alphaPredecessor_polyTime.comp hi)
    (ComputableInPolyTime.bitsCons (.const false)
      (binaryLengthWord_polyTime.comp
        (BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁)))
  simpa only [alphaTerm, Function.comp_apply] using hcert

/-- The complete alpha scan retains source, circuit, output and action words. -/
def alphaWord (source code₀ code₁ out action : List Bool) : List Bool :=
  binaryIndexedLookup
    (fun ordinal (context : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
      alphaTest context.1.1 ordinal context.2.1)
    (fun ordinal (context : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
      alphaTerm context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.2)
    (BrouwerNashHeaders.precisionRuler source)
    (BrouwerNashHeaders.widthRuler source code₀ code₁) ((source, (code₀, code₁)), (out, action))

@[fun_prop] theorem alphaWord_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => alphaWord (source a) (code₀ a) (code₁ a) (out a) (action a)) input encBits := by
  let contextEncoding := encPair (encPair encBits (encPair encBits encBits))
    (encPair encBits encBits)
  have hc := hs.prod ((hc₀.prod hc₁))
  have hp := hc.prod (ho.prod ha)
  have hcontext : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool => p.1)
      (encPair contextEncoding encBits) contextEncoding := .fst contextEncoding encBits
  have hi : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool => p.2)
      (encPair contextEncoding encBits) encBits := .snd contextEncoding encBits
  exact binaryIndexedLookup_polyTime
    (alphaTest_polyTime hcontext.fst'.fst' hi hcontext.snd'.fst')
    (alphaTerm_polyTime hcontext.fst'.fst' hcontext.fst'.snd'.fst'
      hcontext.fst'.snd'.snd' hi hcontext.snd'.snd')
    (BrouwerNashHeaders.precisionRuler_polyTime hs)
    (BrouwerNashHeaders.widthRuler_polyTime hs hc₀ hc₁) hp

/-- A signed scalar formed from a fixed multiple of the ruler length. -/
def scalar (n : ℕ) (negative : Bool) (ruler : List Bool) : List Bool :=
  negative :: binaryLengthWord (List.replicate (ruler.length * n) true)

@[fun_prop] theorem scalar_polyTime (n : ℕ) (negative : Bool)
    {Input : Type} {input : Input ↪ List Bool} {ruler : Input → List Bool}
    (hr : ComputableInPolyTime ruler input encBits) :
    ComputableInPolyTime (fun a => scalar n negative (ruler a)) input encBits :=
  ComputableInPolyTime.bitsCons (.const negative)
    (binaryLengthWord_polyTime.comp ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp hr) (.const n))))

/-- Keep a term at its exact output length; every other output contributes the empty word. -/
def atOutput (out position term : List Bool) : List Bool :=
  if out.length = position.length then term else []

@[fun_prop] theorem atOutput_polyTime
    {Input : Type} {input : Input ↪ List Bool} {out position term : Input → List Bool}
    (ho : ComputableInPolyTime out input encBits)
    (hp : ComputableInPolyTime position input encBits)
    (ht : ComputableInPolyTime term input encBits) :
    ComputableInPolyTime (fun a => atOutput (out a) (position a) (term a)) input encBits := by
  have he := (ComputableInPolyTime.length_bits_comp ho).decide_eq'
    (ComputableInPolyTime.length_bits_comp hp)
  exact (he.ite ht (.const [])).of_enc_eq
    (fun a => by simp only [atOutput, decide_eq_true_eq])

/-- The constant-one block contributes the signed representation of two. -/
def oneWord (out : List Bool) : List Bool := atOutput out [false, false] [false, false, true]

@[fun_prop] theorem oneWord_polyTime
    {Input : Type} {input : Input ↪ List Bool} {out : Input → List Bool}
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => oneWord (out a)) input encBits :=
  atOutput_polyTime ho (.const [false, false]) (.const [false, false, true])

/-- Positive scaling retains the designated predecessor and the canonical unit count. -/
def positiveWord (source code₀ code₁ out action : List Bool) : List Bool :=
  atOutput out (BrouwerNashHeaders.precisionRuler source ++ List.replicate 4 false)
    (binarySignedIndicator ![action,
      BrouwerNashHeaders.precisionRuler source ++ List.replicate 3 false,
      scalar 82 false (BrouwerNashHeaders.unitsRuler source code₀ code₁)])

@[fun_prop] theorem positiveWord_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => positiveWord (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hp := BrouwerNashHeaders.precisionRuler_polyTime hs
  exact atOutput_polyTime ho (ComputableInPolyTime.bitsAppend hp (.const (List.replicate 4 false)))
    (indicator_polyTime ha (ComputableInPolyTime.bitsAppend hp (.const (List.replicate 3 false)))
      (scalar_polyTime 82 false (BrouwerNashHeaders.unitsRuler_polyTime hs hc₀ hc₁)))

/-- The final feedback position uses three complete precision blocks. -/
def feedbackPosition (axis : Fin 2) (source : List Bool) : List Bool :=
  List.replicate ((BrouwerNashHeaders.precisionRuler source).length * 3) true ++
    List.replicate (7 + 2 * axis.val) false

@[fun_prop] theorem feedbackPosition_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => feedbackPosition axis (source a)) input encBits :=
  ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate true).comp
      (ComputableInPolyTime.unary_mul'
        (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.precisionRuler_polyTime hs))
        (.const 3)))
    (.const (List.replicate (7 + 2 * axis.val) false))

/-- Each coordinate's negative chain retains the original precision-ruler bits. -/
def negativeBase (axis : Fin 2) (source : List Bool) : List Bool :=
  BrouwerNashHeaders.precisionRuler source ++ List.replicate 7 false ++
    (if axis.val = 0 then [] else BrouwerNashHeaders.precisionRuler source)

@[fun_prop] theorem negativeBase_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits) :
    ComputableInPolyTime (fun a => negativeBase axis (source a)) input encBits := by
  have hp := BrouwerNashHeaders.precisionRuler_polyTime hs
  have hbase := ComputableInPolyTime.bitsAppend hp (.const (List.replicate 7 false))
  by_cases h : axis.val = 0
  · simpa only [negativeBase, h, ite_true, List.append_nil] using hbase
  · simpa only [negativeBase, h, ite_false] using
      (ComputableInPolyTime.bitsAppend hbase hp)

/-- The first negative-chain wire has a fixed predecessor; later wires use the actual suffix tail. -/
def negativePredecessor (axis : Fin 2) (source ordinal : List Bool) : List Bool :=
  if ordinal.length = 0 then
    BrouwerNashHeaders.precisionRuler source ++ List.replicate (5 + axis.val) false
  else negativeBase axis source ++ ordinal.tail

@[fun_prop] theorem negativePredecessor_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source ordinal : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hi : ComputableInPolyTime ordinal input encBits) :
    ComputableInPolyTime
      (fun a => negativePredecessor axis (source a) (ordinal a)) input encBits := by
  have he := (ComputableInPolyTime.length_bits_comp hi).decide_eq' (.const 0)
  have hy := ComputableInPolyTime.bitsAppend (BrouwerNashHeaders.precisionRuler_polyTime hs)
    (.const (List.replicate (5 + axis.val) false))
  have hn := ComputableInPolyTime.bitsAppend (negativeBase_polyTime axis hs)
    ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsTail).comp hi)
  exact (he.ite hy hn).of_enc_eq
    (fun a => by simp only [negativePredecessor, Function.comp_apply, decide_eq_true_eq])

/-- Negative-chain lookup is guarded by exact output length and the precision bound. -/
def negativeTest (axis : Fin 2) (source ordinal out : List Bool) : List Bool :=
  [decide (out.length = (negativeBase axis source).length + ordinal.length ∧
    ordinal.length < (BrouwerNashHeaders.precisionRuler source).length)]

@[fun_prop] theorem negativeTest_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool} {source ordinal out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hi : ComputableInPolyTime ordinal input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime
      (fun a => negativeTest axis (source a) (ordinal a) (out a)) input encBits := by
  have hn := ComputableInPolyTime.length_bits_comp hi
  have he := (ComputableInPolyTime.length_bits_comp ho).decide_eq'
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.length_bits_comp (negativeBase_polyTime axis hs)) hn)
  have hlt := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' hn.tidy
      (ComputableInPolyTime.length_bits_comp
        (BrouwerNashHeaders.precisionRuler_polyTime hs)).tidy)
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_and he hlt) (.const [])

/-- A selected negative-chain predecessor contributes one dimension unit. -/
def negativeTerm (axis : Fin 2) (source code₀ code₁ ordinal action : List Bool) : List Bool :=
  binarySignedIndicator ![action, negativePredecessor axis source ordinal,
    scalar 1 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]

@[fun_prop] theorem negativeTerm_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ ordinal action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (hi : ComputableInPolyTime ordinal input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => negativeTerm axis (source a) (code₀ a) (code₁ a) (ordinal a) (action a))
      input encBits :=
  indicator_polyTime ha (negativePredecessor_polyTime axis hs hi)
    (scalar_polyTime 1 false (BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁))

/-- Every negative-feedback coefficient is selected by the bounded precision scan. -/
def negativeWord (axis : Fin 2) (source code₀ code₁ out action : List Bool) : List Bool :=
  binaryIndexedLookup
    (fun ordinal (context : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
      negativeTest axis context.1.1 ordinal context.2.1)
    (fun ordinal (context : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
      negativeTerm axis context.1.1 context.1.2.1 context.1.2.2 ordinal context.2.2)
    (BrouwerNashHeaders.precisionRuler source)
    (BrouwerNashHeaders.widthRuler source code₀ code₁) ((source, (code₀, code₁)), (out, action))

@[fun_prop] theorem negativeWord_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => negativeWord axis (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  let contextEncoding := encPair (encPair encBits (encPair encBits encBits))
    (encPair encBits encBits)
  have hp := (hs.prod (hc₀.prod hc₁)).prod (ho.prod ha)
  have hc : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool => p.1)
      (encPair contextEncoding encBits) contextEncoding := .fst contextEncoding encBits
  have hi : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) × List Bool => p.2)
      (encPair contextEncoding encBits) encBits := .snd contextEncoding encBits
  exact binaryIndexedLookup_polyTime
    (negativeTest_polyTime axis hc.fst'.fst' hi hc.snd'.fst')
    (negativeTerm_polyTime axis hc.fst'.fst' hc.fst'.snd'.fst'
      hc.fst'.snd'.snd' hi hc.snd'.snd')
    (BrouwerNashHeaders.precisionRuler_polyTime hs)
    (BrouwerNashHeaders.widthRuler_polyTime hs hc₀ hc₁) hp

/-- Coordinate feedback doubles the final subtraction at the exact dimension scale. -/
def doubleWord (axis : Fin 2) (source code₀ code₁ out action : List Bool) : List Bool :=
  atOutput out (List.replicate axis.val false)
    (binarySignedIndicator ![action, feedbackPosition axis source ++ [false],
      scalar 4 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)])

@[fun_prop] theorem doubleWord_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => doubleWord axis (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits :=
  atOutput_polyTime ho (.const (List.replicate axis.val false))
    (indicator_polyTime ha
      (ComputableInPolyTime.bitsAppend (feedbackPosition_polyTime axis hs) (.const [false]))
      (scalar_polyTime 4 false (BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁)))

/-- Half addition retains both contributions even when its input references coincide. -/
def halfWord (axis : Fin 2) (source code₀ code₁ out action : List Bool) : List Bool :=
  atOutput out (feedbackPosition axis source)
    (binarySignedAdd
      (binarySignedIndicator ![action, List.replicate axis.val false,
        scalar 1 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)])
      (binarySignedIndicator ![action, BrouwerNashHeaders.precisionRuler source ++ List.replicate 4 false,
        scalar 1 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]))

@[fun_prop] theorem halfWord_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => halfWord axis (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hscalar := scalar_polyTime 1 false (BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁)
  exact atOutput_polyTime ho (feedbackPosition_polyTime axis hs)
    (binarySignedAdd_polyTime
      (indicator_polyTime ha (.const (List.replicate axis.val false)) hscalar)
      (indicator_polyTime ha (ComputableInPolyTime.bitsAppend
        (BrouwerNashHeaders.precisionRuler_polyTime hs) (.const (List.replicate 4 false))) hscalar))

/-- The last subtraction retains the negative signed input coefficient. -/
def subtractWord (axis : Fin 2) (source code₀ code₁ out action : List Bool) : List Bool :=
  atOutput out (feedbackPosition axis source ++ [false])
    (binarySignedAdd
      (binarySignedIndicator ![action, feedbackPosition axis source,
        scalar 2 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)])
      (binarySignedIndicator ![action,
        negativePredecessor axis source (BrouwerNashHeaders.precisionRuler source),
        scalar 1 true (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]))

@[fun_prop] theorem subtractWord_polyTime (axis : Fin 2)
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => subtractWord axis (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hd := BrouwerNashHeaders.dimensionRuler_polyTime hs hc₀ hc₁
  have hp := feedbackPosition_polyTime axis hs
  exact atOutput_polyTime ho (ComputableInPolyTime.bitsAppend hp (.const [false]))
    (binarySignedAdd_polyTime
      (indicator_polyTime ha hp (scalar_polyTime 2 false hd))
      (indicator_polyTime ha (negativePredecessor_polyTime axis hs
        (BrouwerNashHeaders.precisionRuler_polyTime hs)) (scalar_polyTime 1 true hd)))

private theorem scalar_value (n : ℕ) (negative : Bool) (ruler : List Bool) :
    binarySignedValue (scalar n negative ruler) =
      if negative then -((n * ruler.length : ℕ) : ℤ) else ((n * ruler.length : ℕ) : ℤ) := by
  cases negative <;>
    simp only [scalar, binarySignedValue, binaryLengthWord_value,
      List.length_replicate, List.headD_cons, List.tail_cons,
      Bool.false_eq_true, ite_false, ite_true] <;> simp only [Nat.cast_mul, Nat.mul_comm]

private theorem atOutput_value (out position term : List Bool) :
    binarySignedValue (atOutput out position term) =
      if out.length = position.length then binarySignedValue term else 0 := by
  by_cases h : out.length = position.length <;> simp only [atOutput, h, ite_true, ite_false]
  rfl

/-- The constant-one block contributes its affine offset at every action. -/
theorem oneWord_value (out : List Bool) :
    binarySignedValue (oneWord out) = if out.length = 2 then 2 else 0 := by
  rw [oneWord, atOutput_value]
  rfl

/-- Positive scaling uses the exact integer coefficient of the canonical block. -/
theorem positiveWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (positiveWord source code₀ code₁ out action) =
      if out.length = BrouwerNashLayout.positive (CircuitWords.first source).length then
        if action.length / 2 = BrouwerNashLayout.alpha
            (BrouwerNashLayout.precision (CircuitWords.first source).length) ∧ action.length % 2 = 1
        then 82 * (BrouwerNashLayout.units (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  rw [positiveWord, atOutput_value, binarySignedIndicator_value, scalar_value]
  simp only [List.length_append, List.length_replicate,
    BrouwerNashHeaders.precisionRuler_length, BrouwerNashHeaders.unitsRuler_length,
    BrouwerNashLayout.positive, BrouwerNashLayout.alpha, BrouwerNashLayout.precision,
    Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  simp only [Nat.add_comm]

private theorem alphaPredecessor_length (ordinal : List Bool) :
    (alphaPredecessor ordinal).length = BrouwerNashLayout.alpha ordinal.length := by
  cases ordinal with
  | nil => rfl
  | cons bit tail =>
    simp [alphaPredecessor, BrouwerNashLayout.alpha]
    omega

/-- The bounded alpha scan decodes exactly the selected halving-chain coefficient. -/
theorem alphaWord_value (out action source code₀ code₁ : List Bool) :
    binarySignedValue (alphaWord source code₀ code₁ out action) =
      if 4 ≤ out.length ∧ out.length <
          BrouwerNashLayout.precision (CircuitWords.first source).length + 4 then
        if action.length / 2 = BrouwerNashLayout.alpha (out.length - 4) ∧
            action.length % 2 = 1
        then (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  let context := ((source, (code₀, code₁)), (out, action))
  let test := fun ordinal (p : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
    alphaTest p.1.1 ordinal p.2.1
  let term := fun ordinal (p : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
    alphaTerm p.1.1 p.1.2.1 p.1.2.2 ordinal p.2.2
  let precision := BrouwerNashHeaders.precisionRuler source
  let width := BrouwerNashHeaders.widthRuler source code₀ code₁
  let k := (BrouwerNashHeaders.dimensionRuler source code₀ code₁).length
  let z : ℤ := if action.length / 2 = BrouwerNashLayout.alpha (out.length - 4) ∧
      action.length % 2 = 1 then (k : ℤ) else 0
  have hz : z.natAbs ≤ 100 * k := by
    dsimp only [z]
    split_ifs <;> simp only [Int.natAbs_natCast, Int.natAbs_zero] <;> omega
  have ht : ∀ ordinal, test ordinal context =
      [decide (out.length = 4 + ordinal.length ∧ ordinal.length < precision.length)] :=
    fun _ => rfl
  have hterm : ∀ ordinal,
      decide (out.length = 4 + ordinal.length ∧ ordinal.length < precision.length) = true →
      binarySignedValue (term ordinal context) = z := by
    intro ordinal h
    have he := (of_decide_eq_true h).1
    have hi : ordinal.length = out.length - 4 := by omega
    change binarySignedValue (binarySignedIndicator ![action, alphaPredecessor ordinal,
      false :: binaryLengthWord (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]) = z
    rw [binarySignedIndicator_value, alphaPredecessor_length, hi]
    simp only [binarySignedValue, List.headD_cons, Bool.false_eq_true, ite_false,
      List.tail_cons, binaryLengthWord_value]
    rfl
  have hw : 0 < width.length := by
    dsimp only [width]
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hc := binaryIndexedLookup_value test term width context
    (fun i => decide (out.length = 4 + i ∧ i < precision.length)) z ht hterm hw
    (BrouwerNashHeaders.widthRuler_fits source code₀ code₁ z hz) precision
  change binarySignedValue (binaryIndexedLookup test term precision width context) = _
  rw [hc]
  have he : (∃ i < precision.length,
      decide (out.length = 4 + i ∧ i < precision.length) = true) ↔
      4 ≤ out.length ∧ out.length < precision.length + 4 := by
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hout, _⟩
      omega
    · rintro ⟨hl, hu⟩
      exact ⟨out.length - 4, by omega, by omega, by omega⟩
  simp only [he]
  simp only [precision, BrouwerNashHeaders.precisionRuler_length, z, k,
    BrouwerNashHeaders.dimensionRuler_length]

private theorem negativeBase_length (axis : Fin 2) (source : List Bool) :
    (negativeBase axis source).length =
      BrouwerNashLayout.precision (CircuitWords.first source).length + 7 +
        axis.val * BrouwerNashLayout.precision (CircuitWords.first source).length := by
  fin_cases axis <;> simp [negativeBase, BrouwerNashHeaders.precisionRuler_length]
  all_goals omega

private theorem negativePredecessor_length (axis : Fin 2) (ordinal source : List Bool) :
    (negativePredecessor axis source ordinal).length =
      BrouwerNashLayout.negative (CircuitWords.first source).length axis ordinal.length := by
  by_cases hz : ordinal.length = 0
  · simp [negativePredecessor, hz, BrouwerNashLayout.negative, BrouwerNashLayout.average,
      BrouwerNashHeaders.precisionRuler_length]
    omega
  · simp [negativePredecessor, hz, BrouwerNashLayout.negative, negativeBase_length]

/-- Each negative-feedback chain selects exactly its canonical predecessor coefficient. -/
theorem negativeWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (negativeWord axis source code₀ code₁ out action) =
      let base := BrouwerNashLayout.precision (CircuitWords.first source).length + 7 +
        axis.val * BrouwerNashLayout.precision (CircuitWords.first source).length
      if base ≤ out.length ∧ out.length <
          base + BrouwerNashLayout.precision (CircuitWords.first source).length then
        if action.length / 2 = BrouwerNashLayout.negative (CircuitWords.first source).length axis
            (out.length - base) ∧ action.length % 2 = 1
        then (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  let context := ((source, (code₀, code₁)), (out, action))
  let test := fun ordinal (p : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
    negativeTest axis p.1.1 ordinal p.2.1
  let term := fun ordinal (p : (List Bool × (List Bool × List Bool)) × (List Bool × List Bool)) =>
    negativeTerm axis p.1.1 p.1.2.1 p.1.2.2 ordinal p.2.2
  let precision := BrouwerNashHeaders.precisionRuler source
  let width := BrouwerNashHeaders.widthRuler source code₀ code₁
  let base := (negativeBase axis source).length
  let k := (BrouwerNashHeaders.dimensionRuler source code₀ code₁).length
  let z : ℤ := if action.length / 2 =
      BrouwerNashLayout.negative (CircuitWords.first source).length axis (out.length - base) ∧
      action.length % 2 = 1 then (k : ℤ) else 0
  have hz : z.natAbs ≤ 100 * k := by
    dsimp only [z]
    split_ifs <;> simp only [Int.natAbs_natCast, Int.natAbs_zero] <;> omega
  have ht : ∀ ordinal, test ordinal context =
      [decide (out.length = base + ordinal.length ∧ ordinal.length < precision.length)] :=
    fun _ => rfl
  have hterm : ∀ ordinal,
      decide (out.length = base + ordinal.length ∧ ordinal.length < precision.length) = true →
      binarySignedValue (term ordinal context) = z := by
    intro ordinal h
    have he := (of_decide_eq_true h).1
    have hi : ordinal.length = out.length - base := by omega
    change binarySignedValue (binarySignedIndicator ![action,
      negativePredecessor axis source ordinal,
      scalar 1 false (BrouwerNashHeaders.dimensionRuler source code₀ code₁)]) = z
    rw [binarySignedIndicator_value, negativePredecessor_length, hi, scalar_value]
    simp only [Bool.false_eq_true, ite_false, one_mul]
    rfl
  have hw : 0 < width.length := by
    dsimp only [width]
    rw [BrouwerNashHeaders.widthRuler_length]
    omega
  have hc := binaryIndexedLookup_value test term width context
    (fun i => decide (out.length = base + i ∧ i < precision.length)) z ht hterm hw
    (BrouwerNashHeaders.widthRuler_fits source code₀ code₁ z hz) precision
  change binarySignedValue (binaryIndexedLookup test term precision width context) = _
  rw [hc]
  have he : (∃ i < precision.length,
      decide (out.length = base + i ∧ i < precision.length) = true) ↔
      base ≤ out.length ∧ out.length < base + precision.length := by
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hout, _⟩
      omega
    · rintro ⟨hl, hu⟩
      exact ⟨out.length - base, by omega, by omega, by omega⟩
  simp only [he]
  simp only [precision, BrouwerNashHeaders.precisionRuler_length, z, k,
    BrouwerNashHeaders.dimensionRuler_length, base, negativeBase_length]

private theorem feedbackPosition_length (axis : Fin 2) (source : List Bool) :
    (feedbackPosition axis source).length =
      BrouwerNashLayout.feedbackHalf (CircuitWords.first source).length axis := by
  simp only [feedbackPosition, List.length_append, List.length_replicate,
    BrouwerNashHeaders.precisionRuler_length, BrouwerNashLayout.feedbackHalf]
  omega

/-- The coordinate block reads the last subtraction at its exact doubling scale. -/
theorem doubleWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (doubleWord axis source code₀ code₁ out action) =
      if out.length = axis.val then
        if action.length / 2 = BrouwerNashLayout.feedbackSub (CircuitWords.first source).length axis ∧
            action.length % 2 = 1
        then 4 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0
      else 0 := by
  rw [doubleWord, atOutput_value, binarySignedIndicator_value, scalar_value]
  simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil,
    feedbackPosition_length, BrouwerNashHeaders.dimensionRuler_length,
    Bool.false_eq_true, ite_false, Nat.cast_mul, Nat.cast_ofNat, BrouwerNashLayout.feedbackSub]
  rfl

/-- Half addition preserves both inputs even when references coincide. -/
theorem halfWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (halfWord axis source code₀ code₁ out action) =
      if out.length = BrouwerNashLayout.feedbackHalf (CircuitWords.first source).length axis then
        (if action.length / 2 = axis.val ∧ action.length % 2 = 1
        then (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.positive (CircuitWords.first source).length ∧
            action.length % 2 = 1
        then (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0)
      else 0 := by
  rw [halfWord, atOutput_value, binarySignedAdd_value, binarySignedIndicator_value,
    binarySignedIndicator_value, scalar_value]
  simp only [List.length_replicate, List.length_append, BrouwerNashHeaders.precisionRuler_length,
    feedbackPosition_length, BrouwerNashHeaders.dimensionRuler_length,
    Bool.false_eq_true, ite_false, one_mul, BrouwerNashLayout.positive]
  rfl

/-- The last subtraction emits its negative signed predecessor coefficient. -/
theorem subtractWord_value (axis : Fin 2) (out action source code₀ code₁ : List Bool) :
    binarySignedValue (subtractWord axis source code₀ code₁ out action) =
      if out.length = BrouwerNashLayout.feedbackSub (CircuitWords.first source).length axis then
        (if action.length / 2 = BrouwerNashLayout.feedbackHalf (CircuitWords.first source).length axis ∧
            action.length % 2 = 1
        then 2 * (BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0) +
        (if action.length / 2 = BrouwerNashLayout.negative (CircuitWords.first source).length axis
            (BrouwerNashLayout.precision (CircuitWords.first source).length) ∧ action.length % 2 = 1
        then -(BrouwerNashLayout.dimension (CircuitWords.first source).length
          (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length : ℤ) else 0)
      else 0 := by
  rw [subtractWord, atOutput_value, binarySignedAdd_value, binarySignedIndicator_value,
    binarySignedIndicator_value, scalar_value, scalar_value]
  simp only [List.length_append, List.length_cons, List.length_nil,
    feedbackPosition_length, BrouwerNashHeaders.dimensionRuler_length,
    Bool.false_eq_true, ite_false, ite_true, one_mul, negativePredecessor_length,
    BrouwerNashHeaders.precisionRuler_length, Nat.cast_mul, Nat.cast_ofNat,
    BrouwerNashLayout.feedbackSub]
  rfl

/-- All shared affine families retain their original right-nested addition order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedAdd (alphaWord source code₀ code₁ out action)
    (binarySignedAdd (oneWord out)
      (binarySignedAdd (positiveWord source code₀ code₁ out action)
        (binarySignedAdd
          (binarySignedAdd (doubleWord 0 source code₀ code₁ out action)
            (doubleWord 1 source code₀ code₁ out action))
          (binarySignedAdd
            (binarySignedAdd (negativeWord 0 source code₀ code₁ out action)
              (negativeWord 1 source code₀ code₁ out action))
            (binarySignedAdd
              (binarySignedAdd (halfWord 0 source code₀ code₁ out action)
                (halfWord 1 source code₀ code₁ out action))
              (binarySignedAdd
                (binarySignedAdd (subtractWord 0 source code₀ code₁ out action)
                  (subtractWord 1 source code₀ code₁ out action))
                (BrouwerNashAverageQuery.coefficientWord source code₀ code₁ out action)))))))

/-- Native composition charges every ordinary source, circuit, output and action producer. -/
@[fun_prop] theorem coefficientWord_polyTime
    {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => coefficientWord (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hd (axis : Fin 2) := doubleWord_polyTime axis hs hc₀ hc₁ ho ha
  have hn (axis : Fin 2) := negativeWord_polyTime axis hs hc₀ hc₁ ho ha
  have hh (axis : Fin 2) := halfWord_polyTime axis hs hc₀ hc₁ ho ha
  have hs' (axis : Fin 2) := subtractWord_polyTime axis hs hc₀ hc₁ ho ha
  have hcert := binarySignedAdd_polyTime (alphaWord_polyTime hs hc₀ hc₁ ho ha)
    (binarySignedAdd_polyTime (oneWord_polyTime ho)
      (binarySignedAdd_polyTime (positiveWord_polyTime hs hc₀ hc₁ ho ha)
        (binarySignedAdd_polyTime (binarySignedAdd_polyTime (hd 0) (hd 1))
          (binarySignedAdd_polyTime (binarySignedAdd_polyTime (hn 0) (hn 1))
            (binarySignedAdd_polyTime (binarySignedAdd_polyTime (hh 0) (hh 1))
              (binarySignedAdd_polyTime (binarySignedAdd_polyTime (hs' 0) (hs' 1))
                (BrouwerNashAverageQuery.coefficientWord_polyTime hs hc₀ hc₁ ho ha)))))))
  simpa only [coefficientWord] using hcert

/-- Signed addition exposes every contribution without an intermediate capacity premise. -/
theorem coefficientWord_expansion (source code₀ code₁ out action : List Bool) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      binarySignedValue (alphaWord source code₀ code₁ out action) +
        (binarySignedValue (oneWord out) +
          (binarySignedValue (positiveWord source code₀ code₁ out action) +
            ((binarySignedValue (doubleWord 0 source code₀ code₁ out action) +
              binarySignedValue (doubleWord 1 source code₀ code₁ out action)) +
              ((binarySignedValue (negativeWord 0 source code₀ code₁ out action) +
                binarySignedValue (negativeWord 1 source code₀ code₁ out action)) +
                ((binarySignedValue (halfWord 0 source code₀ code₁ out action) +
                  binarySignedValue (halfWord 1 source code₀ code₁ out action)) +
                  ((binarySignedValue (subtractWord 0 source code₀ code₁ out action) +
                    binarySignedValue (subtractWord 1 source code₀ code₁ out action)) +
                    binarySignedValue
                      (BrouwerNashAverageQuery.coefficientWord source code₀ code₁ out action))))))) := by
  simp only [coefficientWord, binarySignedAdd_value]

end GameTheory.Complexity.Backend.BrouwerNashGlobalQuery
