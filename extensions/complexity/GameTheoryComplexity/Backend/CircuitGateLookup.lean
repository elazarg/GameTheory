import GameTheoryComplexity.Backend.CircuitCodeShiftCorrectness

/-! Bounded lookup of serialized raw gates. The scanner returns the suffix beginning
at the requested gate, strips the count header, and remains total on malformed words. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham _root_.Complexity.CircuitCode

/-- Skipping a serialized gate is polynomial time on arbitrary words. -/
theorem circuitGateRest_mem_FP : circuitGateRest ∈ FP := by
  have hu := FP_subset_CobhamFP circuitUnaryRest_mem_FP
  have hd := dropFn (Cobham.const [false, false, false]) (Cobham.proj (0 : Fin 1))
  exact CobhamFP_subset_FP ((Cobham.comp hu fun _ : Fin 1 =>
    Cobham.comp hu fun _ : Fin 1 => hd).of_eq fun _ => rfl)

/-- Skipping a gate only consumes input, including truncated encodings. -/
theorem circuitGateRest_length_le (bits : List Bool) :
    (circuitGateRest bits).length ≤ bits.length := by
  simp only [circuitGateRest, circuitUnaryRest, List.length_drop]
  omega

/-- Return the serialized suffix at an ordinal supplied by ruler length.
The clock bits are ignored; missing fields and exhausted streams yield the empty word. -/
def circuitGateSuffix (code indexRuler : List Bool) : List Bool :=
  recNotation (fun v : Fin 1 → List Bool => circuitUnaryRest (v 0))
    (fun v : Fin 3 → List Bool => circuitGateRest (v 1))
    (fun v : Fin 3 → List Bool => circuitGateRest (v 1)) indexRuler ![code]

/-- The lookup performs exactly one consuming step per ruler bit. -/
theorem circuitGateSuffix_eq_iterate (code indexRuler : List Bool) :
    circuitGateSuffix code indexRuler =
      circuitGateRest^[indexRuler.length] (circuitUnaryRest code) := by
  induction indexRuler with
  | nil => rfl
  | cons b r ih =>
    simp only [circuitGateSuffix, recNotation_cons, Bool.cond_self]
    change circuitGateRest (circuitGateSuffix code r) = _
    rw [ih, List.length_cons, Function.iterate_succ_apply']

/-- The state is bounded by the original source length on all inputs. -/
theorem circuitGateSuffix_length_le (code indexRuler : List Bool) :
    (circuitGateSuffix code indexRuler).length ≤ code.length := by
  induction indexRuler with
  | nil =>
    simp only [circuitGateSuffix, recNotation, circuitUnaryRest,
      List.length_drop, Matrix.cons_val_zero]
    omega
  | cons b r ih =>
    simp only [circuitGateSuffix, recNotation_cons, Bool.cond_self]
    exact (circuitGateRest_length_le _).trans ih

/-- Uniform gate suffix lookup has an actual bounded string machine. -/
theorem circuitGateSuffix_cobham :
    Cobham fun v : Fin 2 → List Bool => circuitGateSuffix (v 0) (v 1) := by
  have hu := FP_subset_CobhamFP circuitUnaryRest_mem_FP
  have hg := FP_subset_CobhamFP circuitGateRest_mem_FP
  have hb := Cobham.comp hu fun _ : Fin 1 => Cobham.proj (0 : Fin 1)
  have hs := Cobham.comp hg fun _ : Fin 1 => Cobham.proj (1 : Fin 3)
  have hr := Cobham.boundedRec hb hs hs (Cobham.proj (1 : Fin 2)) (fun r p => by
    have hp : p = ![p 0] := by ext i; fin_cases i; rfl
    rw [hp]
    exact circuitGateSuffix_length_le _ _)
  let args : Fin 2 → (Fin 2 → List Bool) → List Bool := ![fun v => v 1, fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by intro i; fin_cases i <;> exact Cobham.proj _
  exact (Cobham.comp hr ha).of_eq fun v => by
    have hv : Fin.tail (fun i => args i v) = ![v 0] := by
      ext i
      fin_cases i
      rfl
    rw [hv]
    rfl

/-- Lookup with a paired source and ordinal ruler. -/
def circuitGateLookup (z : List Bool) : List Bool :=
  circuitGateSuffix (pairFst z) (pairSnd z)

/-- Paired serialized gate lookup is polynomial time. -/
theorem circuitGateLookup_mem_FP : circuitGateLookup ∈ FP := by
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool :=
    ![fun v => pairFst (v 0), fun v => pairSnd (v 0)]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · exact FP_subset_CobhamFP pairFst_mem_FP
    · exact FP_subset_CobhamFP pairSnd_mem_FP
  exact CobhamFP_subset_FP ((Cobham.comp circuitGateSuffix_cobham ha).of_eq fun _ => rfl)

private theorem gateRest_iterate_encode (n : ℕ) (raw : RawCircuit) :
    circuitGateRest^[n] (raw.flatMap RawGate.encode) =
      (raw.drop n).flatMap RawGate.encode := by
  induction n generalizing raw with
  | zero => rfl
  | succ n ih =>
    cases raw with
    | nil =>
      rw [Function.iterate_succ_apply]
      change circuitGateRest^[n] [] = []
      simpa only [List.flatMap_nil, List.drop_nil] using ih []
    | cons g raw =>
      rw [Function.iterate_succ_apply]
      simp only [List.flatMap_cons, circuitGateRest_encode]
      simpa only [List.drop_succ_cons] using ih raw

/-- Canonical lookup returns the exact suffix, even beyond the declared gate count. -/
theorem circuitGateSuffix_encode (raw : RawCircuit) (indexRuler : List Bool) :
    circuitGateSuffix raw.encode indexRuler =
      (raw.drop indexRuler.length).flatMap RawGate.encode := by
  rw [circuitGateSuffix_eq_iterate]
  simp only [RawCircuit.encode, circuitUnaryRest_encode]
  exact gateRest_iterate_encode _ _

/-- A canonical out-of-range lookup returns the empty stream. -/
theorem circuitGateSuffix_encode_of_length_le (raw : RawCircuit) (ruler : List Bool)
    (h : raw.length ≤ ruler.length) : circuitGateSuffix raw.encode ruler = [] := by
  rw [circuitGateSuffix_encode, List.drop_eq_nil_iff.mpr h]
  rfl

end GameTheory.Complexity.Backend
