import Complexitylib.Classes.P.Pairing
import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
import GameTheory.Finite.BimatrixGateProgram

/-! A total tape decoder for the canonical mixed gate program.
Unary header lengths give the output count and signed coefficient width.
Coefficients occupy output-major fixed-width blocks; absent kind bits mean affine. -/
namespace GameTheory.Complexity.Backend.BimatrixProgramCodec
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite.BimatrixGateProgram

/-- Pack explicit headers, gate-kind flags, and signed coefficient blocks. -/
def encode (dimension width baseline kinds coefficients : List Bool) : List Bool :=
  pair dimension (pair width (pair baseline (pair kinds coefficients)))

/-- Explicit output-count ruler. -/
def dimension (tape : List Bool) : List Bool := pairFst tape
/-- Explicit signed coefficient-width ruler. -/
def width (tape : List Bool) : List Bool := pairFst (pairSnd tape)
/-- Signed matching-baseline parameter. -/
def baselineWord (tape : List Bool) : List Bool := pairFst (pairSnd (pairSnd tape))
/-- One comparator bit per output, with false denoting an affine gate. -/
def kindFlags (tape : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd tape)))
/-- Output-major concatenation of fixed-width signed coefficient fields. -/
def coefficientTape (tape : List Bool) : List Bool :=
  pairSnd (pairSnd (pairSnd (pairSnd tape)))

/-- The baseline is an integer parameter, separate from the gate data. -/
def baseline (tape : List Bool) : ℤ := binarySignedValue (baselineWord tape)

/-- Decode directly to canonical gates, including empty and truncated tapes. -/
def decode (tape : List Bool) : Fin (dimension tape).length → Gate (dimension tape).length :=
  fun i => {
    coefficients := fun r => binarySignedRowValue (width tape) (coefficientTape tape)
      (i.val * ((dimension tape).length * 2) + r.val)
    kind := if (kindFlags tape)[i.val]?.getD false then .comparator else .affine }

/-- Extract a coefficient using output and action rulers. -/
def coefficientField (v : Fin 3 → List Bool) : List Bool :=
  binarySignedRowField ![
    smash (v 1) (dimension (v 0) ++ dimension (v 0)) ++ v 2,
    width (v 0), coefficientTape (v 0)]

/-- Read a gate kind as a singleton flag, defaulting to affine. -/
def kindFlag (v : Fin 2 → List Bool) : List Bool := bitAt (v 1) (kindFlags (v 0))

private theorem fst_cobham : Cobham fun v : Fin 1 → List Bool => pairFst (v 0) :=
  FP_subset_CobhamFP pairFst_mem_FP
private theorem snd_cobham : Cobham fun v : Fin 1 → List Bool => pairSnd (v 0) :=
  FP_subset_CobhamFP pairSnd_mem_FP

/-- Header projections are actual polynomial-time string machines. -/
theorem dimension_cobham : Cobham fun v : Fin 1 → List Bool => dimension (v 0) :=
  fst_cobham

theorem width_cobham : Cobham fun v : Fin 1 → List Bool => width (v 0) :=
  Cobham.comp fst_cobham fun _ : Fin 1 => snd_cobham

theorem baselineWord_cobham : Cobham fun v : Fin 1 → List Bool => baselineWord (v 0) :=
  Cobham.comp fst_cobham fun _ : Fin 1 =>
    Cobham.comp snd_cobham fun _ : Fin 1 => snd_cobham

theorem kindFlags_cobham : Cobham fun v : Fin 1 → List Bool => kindFlags (v 0) :=
  Cobham.comp fst_cobham fun _ : Fin 1 =>
    Cobham.comp snd_cobham fun _ : Fin 1 =>
      Cobham.comp snd_cobham fun _ : Fin 1 => snd_cobham

theorem coefficientTape_cobham :
    Cobham fun v : Fin 1 → List Bool => coefficientTape (v 0) :=
  Cobham.comp snd_cobham fun _ : Fin 1 =>
    Cobham.comp snd_cobham fun _ : Fin 1 =>
      Cobham.comp snd_cobham fun _ : Fin 1 => snd_cobham

/-- Packed coefficient lookup has a uniform polynomial-time machine. -/
theorem coefficientField_cobham : Cobham coefficientField := by
  have hd : Cobham fun v : Fin 3 → List Bool => dimension (v 0) :=
    Cobham.comp dimension_cobham fun _ : Fin 1 => .proj 0
  have hw : Cobham fun v : Fin 3 → List Bool => width (v 0) :=
    Cobham.comp width_cobham fun _ : Fin 1 => .proj 0
  have hc : Cobham fun v : Fin 3 → List Bool => coefficientTape (v 0) :=
    Cobham.comp coefficientTape_cobham fun _ : Fin 1 => .proj 0
  exact Cobham.comp₃ binarySignedRowField_cobham
    (appendFn (Cobham.comp₂ Cobham.smash (.proj 1) (appendFn hd hd)) (.proj 2)) hw hc

theorem coefficientField_mem_FPn : FPn coefficientField :=
  cobham_iff_FPn.mp coefficientField_cobham

/-- Gate-kind lookup has a uniform polynomial-time machine. -/
theorem kindFlag_cobham : Cobham kindFlag :=
  Cobham.comp₂ Cobham.bitAtFn (.proj 1)
    (Cobham.comp kindFlags_cobham fun _ : Fin 1 => .proj 0)

theorem kindFlag_mem_FPn : FPn kindFlag := cobham_iff_FPn.mp kindFlag_cobham

/-- Encoding preserves every supplied header and payload exactly. -/
theorem encode_fields (d w h kinds coeff : List Bool) :
    dimension (encode d w h kinds coeff) = d ∧
    width (encode d w h kinds coeff) = w ∧
    baselineWord (encode d w h kinds coeff) = h ∧
    kindFlags (encode d w h kinds coeff) = kinds ∧
    coefficientTape (encode d w h kinds coeff) = coeff := by
  simp [dimension, width, baselineWord, kindFlags, coefficientTape, encode,
    pairFst_pair, pairSnd_pair]

/-- The executable query agrees with the canonical coefficient interpretation. -/
theorem coefficientField_value (v : Fin 3 → List Bool) :
    binarySignedValue (coefficientField v) =
      binarySignedRowValue (width (v 0)) (coefficientTape (v 0))
        ((v 1).length * ((dimension (v 0)).length * 2) + (v 2).length) := by
  change binarySignedValue (((coefficientTape (v 0)).drop
    ((smash (v 1) (dimension (v 0) ++ dimension (v 0)) ++ v 2).length *
      (width (v 0)).length)).take (width (v 0)).length) = _
  have hl : (smash (v 1) (dimension (v 0) ++ dimension (v 0)) ++ v 2).length =
      (v 1).length * ((dimension (v 0)).length * 2) + (v 2).length := by
    simp only [List.length_append, smash_length]
    ring
  rw [hl]
  rfl

/-- The kind query agrees with the total kind-bit interpretation. -/
theorem kindFlag_value (v : Fin 2 → List Bool) :
    kindFlag v = [((kindFlags (v 0))[(v 1).length]?).getD false] :=
  bitAt_getElem? _ _

/-- Exact fixed blocks are recovered without normalization or padding changes. -/
theorem coefficientField_encode (d w h kinds : List Bool) (fields : List (List Bool))
    (hf : ∀ f ∈ fields, f.length = w.length) (out action : List Bool)
    (hi : out.length * (d.length * 2) + action.length < fields.length) :
    coefficientField ![encode d w h kinds (fields.flatten), out, action] =
      fields[out.length * (d.length * 2) + action.length] := by
  have hl : (smash out (d ++ d) ++ action).length =
      out.length * (d.length * 2) + action.length := by
    simp only [List.length_append, smash_length]
    ring
  have hb := GameTheory.Math.FixedBlockList.block_flatMap_fixed fields id w.length hf _ hi
  simpa [coefficientField, binarySignedRowField, dimension, width, coefficientTape,
    encode, pairFst_pair, pairSnd_pair, hl] using hb

/-- Querying a canonical output and action recovers its semantic coefficient. -/
theorem decode_coefficientField (tape out action : List Bool)
    (i : Fin (dimension tape).length) (r : Fin ((dimension tape).length * 2))
    (hi : out.length = i.val) (hr : action.length = r.val) :
    binarySignedValue (coefficientField ![tape, out, action]) =
      (decode tape i).coefficients r := by
  rw [coefficientField_value]
  change binarySignedRowValue (width tape) (coefficientTape tape)
    (out.length * ((dimension tape).length * 2) + action.length) = _
  rw [hi, hr]
  rfl

/-- The queried kind agrees with the decoded gate, including missing false flags. -/
theorem decode_kindFlag (tape out : List Bool) (i : Fin (dimension tape).length)
    (hi : out.length = i.val) :
    kindFlag ![tape, out] = [decide ((decode tape i).kind = .comparator)] := by
  rw [kindFlag_value]
  change [(kindFlags tape)[out.length]?.getD false] = _
  rw [hi]
  cases h : (kindFlags tape)[i.val]?.getD false <;> simp [decode, h]

/-- Exact coefficient values and kind flags suffice to recover the canonical program. -/
theorem decode_eq_of_fields (tape : List Bool)
    (g : Fin (dimension tape).length → Gate (dimension tape).length)
    (hc : ∀ i r, binarySignedRowValue (width tape) (coefficientTape tape)
      (i.val * ((dimension tape).length * 2) + r.val) = (g i).coefficients r)
    (hk : ∀ i, (if (kindFlags tape)[i.val]?.getD false then GateKind.comparator
      else GateKind.affine) = (g i).kind) : decode tape = g := by
  funext i
  exact congrArg₂ Gate.mk (funext (hc i)) (hk i)

end GameTheory.Complexity.Backend.BimatrixProgramCodec
