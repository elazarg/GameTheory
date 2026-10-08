import Complexitylib.Circuits.Encoding.Fragment
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Internal.PolyLen
import Complexitylib.Classes.P.Composition

/-! Polynomial-time serialization of constant and live-input circuit prefixes. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open _root_.Complexity.CircuitCode

/-- Serialized constant gates, each anchored to live input wire zero. -/
def seedGateCodes (seed : List Bool) : List Bool :=
  (seed.map (RawGate.constant 0)).flatMap RawGate.encode

/-- Serialized copies of the live inputs, with width supplied by a ruler. -/
def liveCopyGateCodes (ruler : List Bool) : List Bool :=
  ((List.range ruler.length).map fun i => RawGate.copy i).flatMap RawGate.encode

private theorem seedGateCodes_cons (b : Bool) (seed : List Bool) :
    seedGateCodes (b :: seed) = (RawGate.constant 0 b).encode ++ seedGateCodes seed := by
  simp [seedGateCodes]

private theorem seedGateCodes_length (seed : List Bool) :
    (seedGateCodes seed).length = 5 * seed.length := by
  induction seed with
  | nil => simp [seedGateCodes]
  | cons b seed ih =>
    rw [seedGateCodes_cons, List.length_append, RawGate.length_encode, ih]
    cases b <;> simp [RawGate.constant] <;> omega

private theorem seedGateCodes_rec (seed : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => [])
      (fun w : Fin 2 → List Bool => (RawGate.constant 0 false).encode ++ w 1)
      (fun w : Fin 2 → List Bool => (RawGate.constant 0 true).encode ++ w 1) seed v =
      seedGateCodes seed := by
  induction seed with
  | nil => rfl
  | cons b seed ih => cases b <;> simp [recNotation_cons, ih, seedGateCodes_cons]

/-- Constant-prefix serialization has an actual polynomial-time machine. -/
theorem seedGateCodes_mem_FP : seedGateCodes ∈ FP := by
  apply CobhamFP_subset_FP
  have hstep (b : Bool) :
      Cobham fun w : Fin 2 → List Bool => (RawGate.constant 0 b).encode ++ w 1 :=
    appendFn (Cobham.const _) (Cobham.proj 1)
  refine (Cobham.boundedRec Cobham.empty (hstep false) (hstep true)
    (repeatFn (Cobham.proj 0) 5) ?_).of_eq fun v => ?_
  · intro seed v
    rw [seedGateCodes_rec, seedGateCodes_length]
    simp
    omega
  · exact seedGateCodes_rec _ _

private theorem liveCopyGateCodes_succ (b : Bool) (ruler : List Bool) :
    liveCopyGateCodes (b :: ruler) =
      liveCopyGateCodes ruler ++ (RawGate.copy ruler.length).encode := by
  simp [liveCopyGateCodes, List.range_succ, List.map_append, List.flatMap_append]

private theorem liveCopyGateCodes_length (ruler : List Bool) :
    (liveCopyGateCodes ruler).length = ruler.length * (ruler.length + 4) := by
  induction ruler with
  | nil => simp [liveCopyGateCodes]
  | cons b ruler ih =>
    rw [liveCopyGateCodes_succ, List.length_append, ih, RawGate.length_encode]
    simp only [RawGate.copy, List.length_cons]
    ring

private def copyStep (w : Fin 2 → List Bool) : List Bool :=
  w 1 ++ (RawGate.copy (w 0).length).encode

private theorem copyStep_mem : Cobham copyStep := by
  have hr : Cobham fun w : Fin 2 → List Bool => List.replicate (w 0).length true :=
    (comp₂ Cobham.smash (Cobham.const [true]) (Cobham.proj 0)).of_eq fun w => by
      simp [_root_.Complexity.smash]
  exact (appendFn (Cobham.proj 1)
    (appendFn (Cobham.const [true, false, false])
      (appendFn hr (appendFn (Cobham.const [false])
        (appendFn hr (Cobham.const [false])))))).of_eq fun w => by
          simp [copyStep, RawGate.encode, RawGate.copy, RawGate.opBit, NatCode.encode,
            List.append_assoc]

private theorem liveCopyGateCodes_rec (ruler : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => []) copyStep copyStep ruler v =
      liveCopyGateCodes ruler := by
  induction ruler with
  | nil => rfl
  | cons b ruler ih =>
    cases b <;> simp [recNotation_cons, copyStep, ih, liveCopyGateCodes_succ]

/-- Live-input copy serialization has an actual polynomial-time machine. -/
theorem liveCopyGateCodes_mem_FP : liveCopyGateCodes ∈ FP := by
  apply CobhamFP_subset_FP
  let q : Polynomial ℕ := Polynomial.X * Polynomial.X + Polynomial.C 4 * Polynomial.X
  refine (Cobham.boundedRec Cobham.empty copyStep_mem copyStep_mem
    (polyLen_mem q (Cobham.proj 0)) ?_).of_eq fun v => ?_
  · intro ruler v
    rw [liveCopyGateCodes_rec, liveCopyGateCodes_length, polyLen_length]
    simp only [q, Fin.cons_zero, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    exact le_of_eq (by ring)
  · exact liveCopyGateCodes_rec _ _

/-- Serialize both prefixes from a paired seed and live-width ruler. -/
theorem circuitPrefixCodes_pair_mem_FP :
    (fun z => seedGateCodes (pairFst z) ++ liveCopyGateCodes (pairSnd z)) ∈ FP :=
  CobhamFP_subset_FP (appendFn
    (FP_subset_CobhamFP (mem_FP_comp pairFst_mem_FP seedGateCodes_mem_FP))
    (FP_subset_CobhamFP (mem_FP_comp pairSnd_mem_FP liveCopyGateCodes_mem_FP)))

end GameTheory.Complexity.Backend
