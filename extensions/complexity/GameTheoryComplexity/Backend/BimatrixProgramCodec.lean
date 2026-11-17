module

public import GameTheoryComplexity.Backend.CircuitWords
public import GameTheoryComplexity.Backend.BinarySignedRowComparison
public import GameTheory.Math.FixedBlockList
public import GameTheory.Finite.BimatrixGateProgram

@[expose] public section

/-! Packed mixed-gate programs retain explicit dimension, coefficient-width,
baseline, and kind headers. The doubled-word framing is a public byte format.
Total field queries preserve truncated payloads and default missing kind bits
to affine gates. -/

namespace GameTheory.Complexity.Backend.BimatrixProgramCodec

open Turing.MultiTapeTM
open GameTheory.Finite.BimatrixGateProgram

/-- Pack the explicit headers and output-major signed coefficient payload. -/
def encode (dimension width baseline kinds coefficients : List Bool) : List Bool :=
  CircuitWords.encodePair dimension (CircuitWords.encodePair width
    (CircuitWords.encodePair baseline (CircuitWords.encodePair kinds coefficients)))

/-- Explicit output-count ruler. -/
def dimension (tape : List Bool) : List Bool := CircuitWords.first tape

/-- Explicit signed coefficient-width ruler. -/
def width (tape : List Bool) : List Bool := CircuitWords.first (CircuitWords.rest tape)

/-- Signed matching-baseline parameter. -/
def baselineWord (tape : List Bool) : List Bool :=
  CircuitWords.first (CircuitWords.rest (CircuitWords.rest tape))

/-- One comparator bit per output, with false denoting an affine gate. -/
def kindFlags (tape : List Bool) : List Bool :=
  CircuitWords.first (CircuitWords.rest (CircuitWords.rest (CircuitWords.rest tape)))

/-- Output-major concatenation of fixed-width signed coefficient fields. -/
def coefficientTape (tape : List Bool) : List Bool :=
  CircuitWords.rest (CircuitWords.rest (CircuitWords.rest (CircuitWords.rest tape)))

/-- The baseline is an integer parameter separate from the gate data. -/
def baseline (tape : List Bool) : ℤ := binarySignedValue (baselineWord tape)

/-- Decode directly to canonical gates, including empty and truncated tapes. -/
def decode (tape : List Bool) : Fin (dimension tape).length → Gate (dimension tape).length :=
  fun i => {
    coefficients := fun r => binarySignedRowValue (width tape) (coefficientTape tape)
      (i.val * ((dimension tape).length * 2) + r.val)
    kind := if (kindFlags tape).getD i.val false then .comparator else .affine }

/-- Extract a coefficient using output and action ruler lengths. -/
def coefficientField (tape output action : List Bool) : List Bool :=
  ((coefficientTape tape).drop
    ((output.length * ((dimension tape).length * 2) + action.length) * (width tape).length)).take
    (width tape).length

/-- Read a comparator-kind bit, defaulting to affine. -/
def kindFlag (tape output : List Bool) : Bool :=
  (kindFlags tape).getD output.length false

/-- Packing preserves every supplied header and payload exactly. -/
theorem encode_fields (d w h kinds coeff : List Bool) :
    dimension (encode d w h kinds coeff) = d ∧
    width (encode d w h kinds coeff) = w ∧
    baselineWord (encode d w h kinds coeff) = h ∧
    kindFlags (encode d w h kinds coeff) = kinds ∧
    coefficientTape (encode d w h kinds coeff) = coeff := by
  simp [dimension, width, baselineWord, kindFlags, coefficientTape, encode]

/-- Truncated and out-of-range fields never exceed the supplied coefficient width. -/
theorem coefficientField_length (tape output action : List Bool) :
    (coefficientField tape output action).length ≤ (width tape).length :=
  List.length_take_le _ _

/-- The executable field query has exactly the canonical output-major interpretation. -/
theorem coefficientField_value (tape output action : List Bool) :
    binarySignedValue (coefficientField tape output action) =
      binarySignedRowValue (width tape) (coefficientTape tape)
        (output.length * ((dimension tape).length * 2) + action.length) := rfl

/-- Canonical fixed blocks are recovered without normalization or padding changes. -/
theorem coefficientField_encode (d w h kinds : List Bool) (fields : List (List Bool))
    (hf : ∀ f ∈ fields, f.length = w.length) (output action : List Bool)
    (hi : output.length * (d.length * 2) + action.length < fields.length) :
    coefficientField (encode d w h kinds fields.flatten) output action =
      fields[output.length * (d.length * 2) + action.length] := by
  have hb := GameTheory.Math.FixedBlockList.block_flatMap_fixed fields id w.length hf _ hi
  simpa [coefficientField, dimension, width, coefficientTape, encode] using hb

/-- Bounded output and action rulers recover the corresponding semantic coefficient. -/
theorem decode_coefficientField (tape output action : List Bool)
    (i : Fin (dimension tape).length) (r : Fin ((dimension tape).length * 2))
    (hi : output.length = i.val) (hr : action.length = r.val) :
    binarySignedValue (coefficientField tape output action) = (decode tape i).coefficients r := by
  rw [coefficientField_value, hi, hr]
  rfl

/-- The native Boolean lookup agrees with the decoded gate kind, including missing bits. -/
theorem decode_kindFlag (tape output : List Bool) (i : Fin (dimension tape).length)
    (hi : output.length = i.val) :
    kindFlag tape output = decide ((decode tape i).kind = .comparator) := by
  unfold kindFlag
  rw [hi]
  cases h : (kindFlags tape)[i.val]?.getD false <;> simp [decode, h]

/-- Exact coefficient values and kind flags recover the canonical gate program. -/
theorem decode_eq_of_fields (tape : List Bool)
    (g : Fin (dimension tape).length → Gate (dimension tape).length)
    (hc : ∀ i r, binarySignedRowValue (width tape) (coefficientTape tape)
      (i.val * ((dimension tape).length * 2) + r.val) = (g i).coefficients r)
    (hk : ∀ i, (if (kindFlags tape).getD i.val false then GateKind.comparator
      else GateKind.affine) = (g i).kind) : decode tape = g := by
  funext i
  exact congrArg₂ Gate.mk (funext (hc i)) (hk i)

/-- Decode the dimension header under any efficiently produced tape encoding. -/
@[fun_prop] theorem dimension_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => dimension (tape a)) input encBits :=
  CircuitWords.first_polyTime.comp ht

/-- Decode the coefficient-width header under the original input encoding. -/
@[fun_prop] theorem width_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => width (tape a)) input encBits :=
  CircuitWords.first_polyTime.comp (CircuitWords.rest_polyTime.comp ht)

/-- Decode the baseline word without changing its signed padding. -/
@[fun_prop] theorem baselineWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => baselineWord (tape a)) input encBits :=
  CircuitWords.first_polyTime.comp
    (CircuitWords.rest_polyTime.comp (CircuitWords.rest_polyTime.comp ht))

/-- Decode the raw kind-bit word, retaining every supplied bit. -/
@[fun_prop] theorem kindFlags_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => kindFlags (tape a)) input encBits :=
  CircuitWords.first_polyTime.comp (CircuitWords.rest_polyTime.comp
    (CircuitWords.rest_polyTime.comp (CircuitWords.rest_polyTime.comp ht)))

/-- Decode the packed coefficient payload on every input word. -/
@[fun_prop] theorem coefficientTape_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape : Input → List Bool} (ht : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => coefficientTape (tape a)) input encBits :=
  CircuitWords.rest_polyTime.comp (CircuitWords.rest_polyTime.comp
    (CircuitWords.rest_polyTime.comp (CircuitWords.rest_polyTime.comp ht)))

/-- The public byte framing composes polynomially with all five field producers. -/
@[fun_prop] theorem encode_polyTime {Input : Type} {input : Input ↪ List Bool}
    {dimension width baseline kinds coefficients : Input → List Bool}
    (hd : ComputableInPolyTime dimension input encBits)
    (hw : ComputableInPolyTime width input encBits)
    (hb : ComputableInPolyTime baseline input encBits)
    (hk : ComputableInPolyTime kinds input encBits)
    (hc : ComputableInPolyTime coefficients input encBits) :
    ComputableInPolyTime
      (fun a => encode (dimension a) (width a) (baseline a) (kinds a) (coefficients a))
      input encBits :=
  CircuitWords.encodePair_polyTime.comp (hd.prod
    (CircuitWords.encodePair_polyTime.comp (hw.prod
      (CircuitWords.encodePair_polyTime.comp (hb.prod
        (CircuitWords.encodePair_polyTime.comp (hk.prod hc)))))))

/-- Total coefficient queries charge the tape and both explicit ordinal rulers. -/
@[fun_prop] theorem coefficientField_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape output action : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits)
    (ho : ComputableInPolyTime output input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime
      (fun a => coefficientField (tape a) (output a) (action a)) input encBits := by
  have hdimension := ComputableInPolyTime.length_bits_comp (dimension_polyTime ht)
  have hactions := ComputableInPolyTime.unary_mul' hdimension (ComputableInPolyTime.const 2)
  have hrow := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.length_bits_comp ho) hactions
  have hindex := ComputableInPolyTime.unary_add.comp
    (hrow.prod (ComputableInPolyTime.length_bits_comp ha))
  have hwidth := ComputableInPolyTime.length_bits_comp (width_polyTime ht)
  have hoffset := ComputableInPolyTime.unary_mul' hindex hwidth
  exact ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput (coefficientTape_polyTime ht) hoffset) hwidth

/-- A total comparator-kind lookup charges its tape and ordinal ruler. -/
@[fun_prop] theorem kindFlag_polyTime {Input : Type} {input : Input ↪ List Bool}
    {tape output : Input → List Bool}
    (ht : ComputableInPolyTime tape input encBits)
    (ho : ComputableInPolyTime output input encBits) :
    ComputableInPolyTime (fun a => kindFlag (tape a) (output a)) input encBool :=
  ComputableInPolyTime.bitsGetDWithInput (kindFlags_polyTime ht)
    (ComputableInPolyTime.length_bits_comp ho) false

end GameTheory.Complexity.Backend.BimatrixProgramCodec
