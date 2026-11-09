module

public import GameTheoryComplexity.Backend.BimatrixProgramCodec
public import GameTheoryComplexity.Backend.BinarySignedFixedWidth

@[expose] public section

/-! Coefficient-table emission uses the canonical mixed-gate program byte codec.
Output and action ordinals are supplied to the callback as suffix rulers from
the original dimension word, retaining every callback-observable bit.
Each signed coefficient is normalized immediately to the advertised width. -/

namespace GameTheory.Complexity.Backend.BimatrixProgramEmission

open Turing.MultiTapeTM
open GameTheory.Finite.BimatrixGateProgram

/-- Materialize one output's coefficients in increasing action order. -/
def row {Source : Type} (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width output : List Bool) : List Bool :=
  (List.range (dimension.length * 2)).flatMap fun j =>
    binarySignedFixed width
      (query source output ((dimension ++ dimension).drop (dimension.length * 2 - j)))

/-- Materialize all coefficients in output-major order with exact signed field widths. -/
def coefficients {Source : Type} (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width : List Bool) : List Bool :=
  (List.range dimension.length).flatMap fun i =>
    row query source dimension width (dimension.drop (dimension.length - i))

/-- Pack source-dependent headers and the concretely emitted coefficient table. -/
def programWord {Source : Type} (dimension width baseline kinds : Source → List Bool)
    (query : Source → List Bool → List Bool → List Bool) (source : Source) : List Bool :=
  BimatrixProgramCodec.encode (dimension source) (width source) (baseline source) (kinds source)
    (coefficients query source (dimension source) (width source))

/-- Every coefficient row contains exactly two actions per decoded output block. -/
@[simp] theorem row_length {Source : Type} (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width output : List Bool) :
    (row query source dimension width output).length =
      (dimension.length * 2) * width.length := by
  have h := GameTheory.Math.FixedBlockList.length_flatMap_fixed
    (List.range (dimension.length * 2))
    (fun j => binarySignedFixed width
      (query source output ((dimension ++ dimension).drop (dimension.length * 2 - j))))
    width.length (fun _ _ => binarySignedFixed_length _ _)
  rw [List.length_range] at h
  exact h

/-- Output-major coefficient emission has its exact advertised fixed-block size. -/
@[simp] theorem coefficients_length {Source : Type}
    (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width : List Bool) :
    (coefficients query source dimension width).length =
      dimension.length * ((dimension.length * 2) * width.length) := by
  have h := GameTheory.Math.FixedBlockList.length_flatMap_fixed
    (List.range dimension.length)
    (fun i => row query source dimension width (dimension.drop (dimension.length - i)))
    ((dimension.length * 2) * width.length) (fun _ _ => row_length _ _ _ _ _)
  rw [List.length_range] at h
  exact h

/-- A row field contains the normalized callback output at the original action suffix ruler. -/
theorem row_field {Source : Type} (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width output : List Bool) (j : ℕ)
    (hj : j < dimension.length * 2) :
    ((row query source dimension width output).drop (j * width.length)).take width.length =
      binarySignedFixed width
        (query source output ((dimension ++ dimension).drop (dimension.length * 2 - j))) := by
  have h := GameTheory.Math.FixedBlockList.block_flatMap_fixed
    (List.range (dimension.length * 2))
    (fun j => binarySignedFixed width
      (query source output ((dimension ++ dimension).drop (dimension.length * 2 - j))))
    width.length (fun _ _ => binarySignedFixed_length _ _)
    j (by simpa only [List.length_range] using hj)
  simpa only [row, List.getElem_range] using h

/-- Every emitted output row retains its exact original output suffix ruler. -/
theorem coefficients_row {Source : Type}
    (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width : List Bool) (i : ℕ) (hi : i < dimension.length) :
    ((coefficients query source dimension width).drop
      (i * ((dimension.length * 2) * width.length))).take
      ((dimension.length * 2) * width.length) =
      row query source dimension width (dimension.drop (dimension.length - i)) := by
  have h := GameTheory.Math.FixedBlockList.block_flatMap_fixed
    (List.range dimension.length)
    (fun i => row query source dimension width (dimension.drop (dimension.length - i)))
    ((dimension.length * 2) * width.length) (fun _ _ => row_length _ _ _ _ _)
    i (by simpa only [List.length_range] using hi)
  simpa only [coefficients, List.getElem_range] using h

/-- Each output/action block preserves the callback's precise suffix-ruler inputs. -/
theorem coefficients_field {Source : Type}
    (query : Source → List Bool → List Bool → List Bool)
    (source : Source) (dimension width : List Bool) (i j : ℕ)
    (hi : i < dimension.length) (hj : j < dimension.length * 2) :
    ((coefficients query source dimension width).drop
      ((i * (dimension.length * 2) + j) * width.length)).take width.length =
      binarySignedFixed width
        (query source (dimension.drop (dimension.length - i))
          ((dimension ++ dimension).drop (dimension.length * 2 - j))) := by
  have h := congrArg (fun x : List Bool => (x.drop (j * width.length)).take width.length)
    (coefficients_row query source dimension width i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : width.length ≤ dimension.length * 2 * width.length - j * width.length := by
    have hb := Nat.mul_le_mul_right width.length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (row_field query source dimension width
    (dimension.drop (dimension.length - i)) j hj)

/-- Canonical framing preserves all supplied source-dependent headers and coefficient bytes. -/
theorem programWord_fields {Source : Type} (dimension width baseline kinds : Source → List Bool)
    (query : Source → List Bool → List Bool → List Bool) (source : Source) :
    BimatrixProgramCodec.dimension (programWord dimension width baseline kinds query source) =
      dimension source ∧
    BimatrixProgramCodec.width (programWord dimension width baseline kinds query source) =
      width source ∧
    BimatrixProgramCodec.baselineWord (programWord dimension width baseline kinds query source) =
      baseline source ∧
    BimatrixProgramCodec.kindFlags (programWord dimension width baseline kinds query source) =
      kinds source ∧
    BimatrixProgramCodec.coefficientTape (programWord dimension width baseline kinds query source) =
      coefficients query source (dimension source) (width source) :=
  BimatrixProgramCodec.encode_fields _ _ _ _ _

/-- Representable callback values and exact kind flags recover the canonical gate program. -/
theorem programWord_decode {Source : Type} (dimension width baseline kinds : Source → List Bool)
    (query : Source → List Bool → List Bool → List Bool) (source : Source)
    (g : Fin (BimatrixProgramCodec.dimension
      (programWord dimension width baseline kinds query source)).length →
      Gate (BimatrixProgramCodec.dimension
        (programWord dimension width baseline kinds query source)).length)
    (hw : 0 < (width source).length)
    (hq : ∀ i r, binarySignedValue
      (query source ((dimension source).drop ((dimension source).length - i.val))
        ((dimension source ++ dimension source).drop ((dimension source).length * 2 - r.val))) =
        (g i).coefficients r)
    (hb : ∀ i r, ((g i).coefficients r).natAbs < 2 ^ ((width source).length - 1))
    (hk : ∀ i, (if (kinds source).getD i.val false then GateKind.comparator
      else GateKind.affine) = (g i).kind) :
    BimatrixProgramCodec.decode (programWord dimension width baseline kinds query source) = g := by
  have hf := programWord_fields dimension width baseline kinds query source
  apply BimatrixProgramCodec.decode_eq_of_fields
  · intro i r
    have hi : i.val < (dimension source).length := by rw [← hf.1]; exact i.isLt
    have hr : r.val < (dimension source).length * 2 := by rw [← hf.1]; exact r.isLt
    have hindex := congrArg (fun n : ℕ => i.val * (n * 2) + r.val)
      (congrArg List.length hf.1)
    rw [hindex, hf.2.1, hf.2.2.2.2]
    change binarySignedValue
      (((coefficients query source (dimension source) (width source)).drop
        ((i.val * ((dimension source).length * 2) + r.val) * (width source).length)).take
        (width source).length) = _
    rw [coefficients_field query source (dimension source) (width source) i.val r.val hi hr]
    exact (binarySignedFixed_value (width source) _ hw
      (by rw [hq i r]; exact hb i r)).trans (hq i r)
  · intro i
    rw [hf.2.2.2.1]
    exact hk i

/-- Row emission charges the source and both original callback-observable ruler words. -/
@[fun_prop] theorem row_polyTime {Source Input : Type}
    {sourceEncoding : Source ↪ List Bool} {input : Input ↪ List Bool}
    {query : Source → List Bool → List Bool → List Bool}
    (hq : ComputableInPolyTime (fun p : Source × (List Bool × List Bool) =>
      query p.1 p.2.1 p.2.2) (encPair sourceEncoding (encPair encBits encBits)) encBits)
    {source : Input → Source} {dimension width output : Input → List Bool}
    (hs : ComputableInPolyTime source input sourceEncoding)
    (hd : ComputableInPolyTime dimension input encBits)
    (hw : ComputableInPolyTime width input encBits)
    (ho : ComputableInPolyTime output input encBits) :
    ComputableInPolyTime
      (fun a => row query (source a) (dimension a) (width a) (output a)) input encBits := by
  have hcount := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.length_bits_comp hd) (ComputableInPolyTime.const 2)
  have hi := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp hcount
  change ComputableInPolyTime (fun a =>
    (List.range ((dimension a).length * 2)).flatMap fun j =>
      binarySignedFixed (width a) (query (source a) (output a)
        ((dimension a ++ dimension a).drop ((dimension a).length * 2 - j)))) input encBits
  refine ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (a : Input) (j : ℕ) =>
      binarySignedFixed (width a) (query (source a) (output a)
        ((dimension a ++ dimension a).drop ((dimension a).length * 2 - j)))) hi ?_
  have hcontext : ComputableInPolyTime (fun p : Input × ℕ => p.1)
      (encPair input encUnary) input := ComputableInPolyTime.fst input encUnary
  have hindex : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair input encUnary) encUnary := ComputableInPolyTime.snd input encUnary
  have hs' := hs.comp hcontext
  have hd' := hd.comp hcontext
  have hw' := hw.comp hcontext
  have ho' := ho.comp hcontext
  have hcount' := ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.length_bits_comp hd') (ComputableInPolyTime.const 2)
  have ha := ComputableInPolyTime.bitsDropWithInput
    (ComputableInPolyTime.bitsAppend hd' hd')
    (ComputableInPolyTime.unary_sub' hcount' hindex)
  exact binarySignedFixed_polyTime hw' (hq.comp (hs'.prod (ho'.prod ha)))

/-- Full coefficient emission preserves the joint source/output/action callback encoding. -/
@[fun_prop] theorem coefficients_polyTime {Source Input : Type}
    {sourceEncoding : Source ↪ List Bool} {input : Input ↪ List Bool}
    {query : Source → List Bool → List Bool → List Bool}
    (hq : ComputableInPolyTime (fun p : Source × (List Bool × List Bool) =>
      query p.1 p.2.1 p.2.2) (encPair sourceEncoding (encPair encBits encBits)) encBits)
    {source : Input → Source} {dimension width : Input → List Bool}
    (hs : ComputableInPolyTime source input sourceEncoding)
    (hd : ComputableInPolyTime dimension input encBits)
    (hw : ComputableInPolyTime width input encBits) :
    ComputableInPolyTime
      (fun a => coefficients query (source a) (dimension a) (width a)) input encBits := by
  have hi := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp
    (ComputableInPolyTime.length_bits_comp hd)
  change ComputableInPolyTime (fun a =>
    (List.range (dimension a).length).flatMap fun i =>
      row query (source a) (dimension a) (width a)
        ((dimension a).drop ((dimension a).length - i))) input encBits
  refine ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (a : Input) (i : ℕ) =>
      row query (source a) (dimension a) (width a)
        ((dimension a).drop ((dimension a).length - i))) hi ?_
  have hcontext : ComputableInPolyTime (fun p : Input × ℕ => p.1)
      (encPair input encUnary) input := ComputableInPolyTime.fst input encUnary
  have hindex : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair input encUnary) encUnary := ComputableInPolyTime.snd input encUnary
  have hs' := hs.comp hcontext
  have hd' := hd.comp hcontext
  have hw' := hw.comp hcontext
  have ho := ComputableInPolyTime.bitsDropWithInput hd'
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits_comp hd') hindex)
  exact row_polyTime hq hs' hd' hw' ho

/-- Source-dependent program packing has a native joint-input polynomial-time certificate. -/
@[fun_prop] theorem programWord_polyTime {Source : Type}
    {sourceEncoding : Source ↪ List Bool}
    {dimension width baseline kinds : Source → List Bool}
    {query : Source → List Bool → List Bool → List Bool}
    (hd : ComputableInPolyTime dimension sourceEncoding encBits)
    (hw : ComputableInPolyTime width sourceEncoding encBits)
    (hb : ComputableInPolyTime baseline sourceEncoding encBits)
    (hk : ComputableInPolyTime kinds sourceEncoding encBits)
    (hq : ComputableInPolyTime (fun p : Source × (List Bool × List Bool) =>
      query p.1 p.2.1 p.2.2) (encPair sourceEncoding (encPair encBits encBits)) encBits) :
    ComputableInPolyTime (programWord dimension width baseline kinds query)
      sourceEncoding encBits :=
  BimatrixProgramCodec.encode_polyTime hd hw hb hk
    (coefficients_polyTime hq (ComputableInPolyTime.id' (encIn := sourceEncoding)) hd hw)

end GameTheory.Complexity.Backend.BimatrixProgramEmission
