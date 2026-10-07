import Complexitylib.Circuits.Encoding.Shift
import Complexitylib.Circuits.Encoding
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.Cobham.Internal.PolyLen

/-! Serialized raw circuit relocation. Unary references are shifted by inserting
one ruler before each reference; the scanner processes only the declared gate
count. Its execution is certified by bounded polynomial-time iteration. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- The leading unary field, excluding its terminator. -/
def circuitUnaryPrefix : List Bool → List Bool
  | true :: rest => true :: circuitUnaryPrefix rest
  | _ => []

/-- A scanned unary field never exceeds its containing word. -/
theorem circuitUnaryPrefix_length_le (bits : List Bool) :
    (circuitUnaryPrefix bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all [circuitUnaryPrefix]

private theorem circuitUnaryPrefix_rec (x : List Bool) (v : Fin 0 → List Bool) :
    recNotation (fun _ : Fin 0 → List Bool => [])
      (fun _ : Fin 2 → List Bool => []) (fun w : Fin 2 → List Bool => true :: w 1) x v =
      circuitUnaryPrefix x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [recNotation, circuitUnaryPrefix, ih]

/-- Unary field scanning has an actual polynomial-time string machine. -/
theorem circuitUnaryPrefix_mem_FP : circuitUnaryPrefix ∈ FP := by
  apply CobhamFP_subset_FP
  have h := Cobham.boundedRec (n := 0) Cobham.empty Cobham.empty
    (Cobham.comp (Cobham.bit true) fun _ : Fin 1 => Cobham.proj (1 : Fin 2))
    (Cobham.proj (0 : Fin 1)) (fun x v => by
      rw [circuitUnaryPrefix_rec]
      exact circuitUnaryPrefix_length_le x)
  exact h.of_eq fun v => circuitUnaryPrefix_rec (v 0) (Fin.tail v)

/-- Skip one unary reference and its terminator. -/
def circuitUnaryRest (bits : List Bool) : List Bool :=
  bits.drop ((circuitUnaryPrefix bits).length + 1)

/-- Scanning a canonical unary field recovers its ruler. -/
theorem circuitUnaryPrefix_encode (n : ℕ) (rest : List Bool) :
    circuitUnaryPrefix (CircuitCode.NatCode.encode n ++ rest) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [CircuitCode.NatCode.encode, List.replicate_succ,
      circuitUnaryPrefix] using congrArg (List.cons true) ih

/-- Skipping a canonical unary field recovers its unconsumed suffix. -/
theorem circuitUnaryRest_encode (n : ℕ) (rest : List Bool) :
    circuitUnaryRest (CircuitCode.NatCode.encode n ++ rest) = rest := by
  rw [circuitUnaryRest, circuitUnaryPrefix_encode]
  simp [CircuitCode.NatCode.encode, List.drop_append]

/-- The shifted serialization of the first gate in a stream. -/
def circuitShiftGate (ruler bits : List Bool) : List Bool :=
  let first := bits.drop 3
  let second := circuitUnaryRest first
  bits.take 3 ++ List.replicate ruler.length true ++
    first.take ((circuitUnaryPrefix first).length + 1) ++
    List.replicate ruler.length true ++
    second.take ((circuitUnaryPrefix second).length + 1)

/-- The unconsumed stream after its first gate. -/
def circuitGateRest (bits : List Bool) : List Bool :=
  circuitUnaryRest (circuitUnaryRest (bits.drop 3))

/-- One scanner step keeps its ruler, consumes a gate and appends shifted code. -/
def circuitShiftStep (state : List Bool) : List Bool :=
  let ruler := pairFst state
  let stream := pairFst (pairSnd state)
  let output := pairSnd (pairSnd state)
  pair ruler (pair (circuitGateRest stream) (output ++ circuitShiftGate ruler stream))

/-- Relocate a declared serialized circuit using a unary wire-offset ruler. -/
def shiftCircuitCode (ruler code : List Bool) : List Bool :=
  let count := circuitUnaryPrefix code
  let stream := circuitUnaryRest code
  count ++ [false] ++ pairSnd (pairSnd
    (circuitShiftStep^[count.length] (pair ruler (pair stream []))))

private theorem unaryPrefixFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitUnaryPrefix (f v) :=
  (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP)
    fun _ : Fin 1 => hf).of_eq fun _ => rfl

private theorem unaryRestFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitUnaryRest (f v) :=
  (dropFn (appendFn (unaryPrefixFn hf) (Cobham.const [false])) hf).of_eq fun _ => by
    simp [circuitUnaryRest]

/-- Skipping a unary field is polynomial time, including unterminated fields. -/
theorem circuitUnaryRest_mem_FP : circuitUnaryRest ∈ FP :=
  CobhamFP_subset_FP (unaryRestFn (Cobham.proj (0 : Fin 1)))

private theorem gateRestFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitGateRest (f v) :=
  unaryRestFn (unaryRestFn (dropFn (Cobham.const [false, false, false]) hf))

private theorem shiftGateFn {n : ℕ} {r f : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) (hf : Cobham f) : Cobham fun v => circuitShiftGate (r v) (f v) := by
  have hfirst := dropFn (Cobham.const [false, false, false]) hf
  have hsecond := unaryRestFn hfirst
  have hu : Cobham fun v => List.replicate (r v).length true :=
    (comp₂ Cobham.smash (Cobham.const [true]) hr).of_eq fun v => by
    simp [_root_.Complexity.smash]
  exact (appendFn (appendFn (appendFn (appendFn
    (takeFn (Cobham.const [false, false, false]) hf) hu)
    (takeFn (appendFn (unaryPrefixFn hfirst) (Cobham.const [false])) hfirst)) hu)
    (takeFn (appendFn (unaryPrefixFn hsecond) (Cobham.const [false])) hsecond)).of_eq
      fun _ => by simp [circuitShiftGate, circuitUnaryRest]

/-- Each relocation scanner step is polynomial time on arbitrary words. -/
theorem circuitShiftStep_mem_FP : circuitShiftStep ∈ FP := by
  apply CobhamFP_subset_FP
  have hr := FP_subset_CobhamFP pairFst_mem_FP
  have hs := FP_subset_CobhamFP pairSnd_mem_FP
  have hstream := Cobham.comp hr fun _ : Fin 1 => hs
  have hout := Cobham.comp hs fun _ : Fin 1 => hs
  exact (comp₂ Cobham.pairing hr (comp₂ Cobham.pairing (gateRestFn hstream)
    (appendFn hout (shiftGateFn hr hstream)))).of_eq fun _ => rfl

private theorem unaryRest_length_le (bits : List Bool) :
    (circuitUnaryRest bits).length ≤ bits.length := by
  simp only [circuitUnaryRest, List.length_drop]
  omega

private theorem gateRest_length_le (bits : List Bool) :
    (circuitGateRest bits).length ≤ bits.length :=
  (unaryRest_length_le _).trans
    ((unaryRest_length_le _).trans (by simp only [List.length_drop]; omega))

private theorem shiftGate_length_le (ruler bits : List Bool) :
    (circuitShiftGate ruler bits).length ≤ 3 + 2 * ruler.length + 2 * bits.length := by
  have hfirst : (bits.drop 3).length ≤ bits.length := by simp only [List.length_drop]; omega
  have hsecond := (unaryRest_length_le (bits.drop 3)).trans hfirst
  have hhead := List.length_take_le (l := bits) (i := 3)
  have ha : ((bits.drop 3).take ((circuitUnaryPrefix (bits.drop 3)).length + 1)).length ≤
      (bits.drop 3).length := by simp only [List.length_take]; exact min_le_right _ _
  have hb : ((circuitUnaryRest (bits.drop 3)).take
      ((circuitUnaryPrefix (circuitUnaryRest (bits.drop 3))).length + 1)).length ≤
      (circuitUnaryRest (bits.drop 3)).length := by
    simp only [List.length_take]; exact min_le_right _ _
  simp only [circuitShiftGate, List.length_append, List.length_replicate]
  omega

private theorem shiftStep_iterate_bound (ruler stream : List Bool) (i : ℕ) :
    ∃ rest output,
      circuitShiftStep^[i] (pair ruler (pair stream [])) = pair ruler (pair rest output) ∧
      rest.length ≤ stream.length ∧
      output.length ≤ i * (3 + 2 * ruler.length + 2 * stream.length) := by
  induction i with
  | zero => exact ⟨stream, [], rfl, le_rfl, by simp⟩
  | succ i ih =>
    obtain ⟨rest, output, heq, hrest, hout⟩ := ih
    refine ⟨circuitGateRest rest, output ++ circuitShiftGate ruler rest, ?_,
      (gateRest_length_le rest).trans hrest, ?_⟩
    · rw [Function.iterate_succ_apply', heq]
      simp only [circuitShiftStep, pairFst_pair, pairSnd_pair]
    · have hg := shiftGate_length_le ruler rest
      rw [List.length_append, Nat.succ_mul]
      omega

private def shiftScanInit (z : List Bool) : List Bool :=
  pair (pairFst z) (pair (circuitUnaryRest (pairSnd z)) [])

private def shiftScanWidth (z : List Bool) : List Bool :=
  let r := pairFst z
  let c := pairSnd z
  (r ++ r ++ c ++ c ++ [false, false, false, false]) ++
    smash c ([false, false, false] ++ r ++ r ++ c ++ c)

/-- Uniform serialized relocation is polynomial time, including arbitrary codes. -/
theorem shiftCircuitCode_pair_mem_FP :
    (fun z => shiftCircuitCode (pairFst z) (pairSnd z)) ∈ FP := by
  have hr := FP_subset_CobhamFP pairFst_mem_FP
  have hc := FP_subset_CobhamFP pairSnd_mem_FP
  have hinit : shiftScanInit ∈ FP := CobhamFP_subset_FP
    ((comp₂ Cobham.pairing hr (comp₂ Cobham.pairing (unaryRestFn hc) Cobham.empty)).of_eq
      fun _ => rfl)
  have hclock : (fun z => circuitUnaryPrefix (pairSnd z)) ∈ FP :=
    mem_FP_comp pairSnd_mem_FP circuitUnaryPrefix_mem_FP
  have hwidth : shiftScanWidth ∈ FP := CobhamFP_subset_FP
    ((appendFn (appendFn (appendFn (appendFn (appendFn hr hr) hc) hc)
      (Cobham.const [false, false, false, false]))
      (comp₂ Cobham.smash hc (appendFn (appendFn (appendFn (appendFn
        (Cobham.const [false, false, false]) hr) hr) hc) hc))).of_eq fun _ => rfl)
  have hscan := iterate_mem_FP circuitShiftStep_mem_FP hinit hclock hwidth
    (fun z i hi => by
      obtain ⟨rest, output, heq, hrest, hout⟩ :=
        shiftStep_iterate_bound (pairFst z) (circuitUnaryRest (pairSnd z)) i
      change (circuitShiftStep^[i]
        (pair (pairFst z) (pair (circuitUnaryRest (pairSnd z)) []))).length ≤ _
      rw [heq]
      have hs := unaryRest_length_le (pairSnd z)
      have ht := circuitUnaryPrefix_length_le (pairSnd z)
      have hm : i * (3 + 2 * (pairFst z).length +
          2 * (circuitUnaryRest (pairSnd z)).length) ≤
          (pairSnd z).length * (3 + 2 * (pairFst z).length + 2 * (pairSnd z).length) :=
        Nat.mul_le_mul (hi.trans ht) (by omega)
      have hout' := hout.trans hm
      simp only [pair_length, List.length_nil, shiftScanWidth, List.length_append,
        smash_length, List.length_cons]
      ring_nf at hout' ⊢
      omega)
  exact (appendFn_mem_FP (appendFn_mem_FP hclock (constFn_mem_FP [false]))
    (mem_FP_comp (mem_FP_comp hscan pairSnd_mem_FP) pairSnd_mem_FP))

end GameTheory.Complexity.Backend
