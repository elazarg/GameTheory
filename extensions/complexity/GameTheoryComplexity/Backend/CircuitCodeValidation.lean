import GameTheoryComplexity.Backend.CircuitCodeShift

/-! Polynomial-time exact syntax validation for serialized raw circuits. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open _root_.Complexity.CircuitCode

private theorem unaryDecode (bits : List Bool) :
    NatCode.decodePrefix? bits =
      if (circuitUnaryPrefix bits).length < bits.length then
        some ((circuitUnaryPrefix bits).length, circuitUnaryRest bits) else none := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b with
    | false => simp [NatCode.decodePrefix?, NatCode.decodeAux?, circuitUnaryPrefix,
        circuitUnaryRest]
    | true =>
      have aux (bits : List Bool) (n : ℕ) :
          NatCode.decodeAux? bits n =
            (NatCode.decodePrefix? bits).map (fun p => (n + p.1, p.2)) := by
        induction bits generalizing n with
        | nil => rfl
        | cons b bits ih =>
          cases b with
          | false => simp [NatCode.decodeAux?, NatCode.decodePrefix?]
          | true =>
            change NatCode.decodeAux? bits (n + 1) =
              (NatCode.decodeAux? bits 1).map (fun p => (n + p.1, p.2))
            rw [ih (n + 1), ih 1]
            cases NatCode.decodePrefix? bits <;> simp [Nat.add_assoc]
      rw [NatCode.decodePrefix?, NatCode.decodeAux?, aux, ih]
      simp only [circuitUnaryPrefix, List.length_cons, Nat.add_lt_add_iff_right]
      split_ifs <;> simp_all [circuitUnaryRest, circuitUnaryPrefix,
        List.drop_succ_cons]
      omega

private def unaryFlag (bits : List Bool) : List Bool :=
  lenLeFlag bits (circuitUnaryPrefix bits ++ [false])

private theorem unaryFlag_flag (bits : List Bool) :
    unaryFlag bits = [true] ∨ unaryFlag bits = [false] := lenLeFlag_flag _ _

private theorem unaryFlag_accept (bits : List Bool) :
    unaryFlag bits = [true] ↔ (circuitUnaryPrefix bits).length < bits.length := by
  simp only [unaryFlag, lenLeFlag_eq_true_iff, List.length_append,
    List.length_cons, List.length_nil]
  omega

private def gateFlag (bits : List Bool) : List Bool :=
  andBit (lenLeFlag bits [false, false, false])
    (andBit (unaryFlag (bits.drop 3)) (unaryFlag (circuitUnaryRest (bits.drop 3))))

private theorem gateFlag_flag (bits : List Bool) :
    gateFlag bits = [true] ∨ gateFlag bits = [false] := andBit_flag _ _

private theorem gateFlag_accept (bits : List Bool) :
    gateFlag bits = [true] ↔
      3 ≤ bits.length ∧
      (circuitUnaryPrefix (bits.drop 3)).length < (bits.drop 3).length ∧
      (circuitUnaryPrefix (circuitUnaryRest (bits.drop 3))).length <
        (circuitUnaryRest (bits.drop 3)).length := by
  rw [gateFlag, andBit_eq_true_iff (lenLeFlag_flag _ _) (andBit_flag _ _),
    andBit_eq_true_iff (unaryFlag_flag _) (unaryFlag_flag _),
    unaryFlag_accept, unaryFlag_accept, lenLeFlag_eq_true_iff]
  simp

private theorem gateFlag_parse (bits : List Bool) :
    gateFlag bits = [true] ↔ ∃ g rest, RawGate.decodePrefix? bits = some (g, rest) := by
  rw [gateFlag_accept]
  cases bits with
  | nil => simp [RawGate.decodePrefix?]
  | cons a bits =>
    cases bits with
    | nil => simp [RawGate.decodePrefix?]
    | cons b bits =>
      cases bits with
      | nil => simp [RawGate.decodePrefix?]
      | cons c bits =>
        simp only [List.length_cons, List.drop_succ_cons, List.drop_zero]
        rw [RawGate.decodePrefix?, unaryDecode]
        split_ifs with hfirst
        · dsimp only
          rw [unaryDecode]
          have hlen : 3 ≤ bits.length + 1 + 1 + 1 := by omega
          split_ifs with hsecond <;> simp [hfirst, hsecond, hlen]
        · simp [hfirst]

private theorem gateRest_parse {bits : List Bool} {gate : RawGate} {rest : List Bool}
    (h : RawGate.decodePrefix? bits = some (gate, rest)) : circuitGateRest bits = rest := by
  rw [(RawGate.decodePrefix?_eq_some_iff _ _ _).mp h]
  simp [circuitGateRest, RawGate.encode, circuitUnaryRest_encode, List.append_assoc]

private def validationStep (state : List Bool) : List Bool :=
  pair (andBit (pairFst state) (gateFlag (pairSnd state)))
    (circuitGateRest (pairSnd state))

private def validationFinish (state : List Bool) : List Bool :=
  andBit (pairFst state) (lenEqFlag (pairSnd state) [])

private theorem validationScan_correct (count : ℕ) (flag bits : List Bool)
    (hflag : flag = [true] ∨ flag = [false]) :
    validationFinish (validationStep^[count] (pair flag bits)) = [true] ↔
      flag = [true] ∧ ∃ c, RawCircuit.decodeGates? count bits = some (c, []) := by
  induction count generalizing flag bits with
  | zero =>
    simp only [Function.iterate_zero, id_eq, validationFinish, pairFst_pair, pairSnd_pair]
    rw [andBit_eq_true_iff hflag (lenEqFlag_flag _ _), lenEqFlag_eq_true_iff]
    simp [RawCircuit.decodeGates?]
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    simp only [validationStep, pairFst_pair, pairSnd_pair]
    rw [ih _ _ (andBit_flag _ _), andBit_eq_true_iff hflag (gateFlag_flag _)]
    cases hparse : RawGate.decodePrefix? bits with
    | none =>
      have hbad : gateFlag bits ≠ [true] := by
        intro h
        obtain ⟨g, rest, hg⟩ := (gateFlag_parse bits).mp h
        simp [hparse] at hg
      simp [hbad, RawCircuit.decodeGates?, hparse]
    | some parsed =>
      obtain ⟨g, rest⟩ := parsed
      have hgood := (gateFlag_parse bits).mpr ⟨g, rest, hparse⟩
      rw [hgood, gateRest_parse hparse]
      cases htail : RawCircuit.decodeGates? count rest with
      | none => simp [RawCircuit.decodeGates?, hparse, htail]
      | some parsed =>
        obtain ⟨c, suffix⟩ := parsed
        simp [RawCircuit.decodeGates?, hparse, htail]

/-- A one-bit test for exact raw circuit syntax, including the empty gate list. -/
def circuitCodeSyntaxFlag (code : List Bool) : List Bool :=
  validationFinish (validationStep^[(circuitUnaryPrefix code).length]
    (pair (unaryFlag code) (circuitUnaryRest code)))

/-- Syntax validation always produces one Boolean bit. -/
theorem circuitCodeSyntaxFlag_flag (code : List Bool) :
    circuitCodeSyntaxFlag code = [true] ∨ circuitCodeSyntaxFlag code = [false] :=
  andBit_flag _ _

/-- The syntax flag accepts exactly the words decoded as one complete raw circuit. -/
theorem circuitCodeSyntaxFlag_accept (code : List Bool) :
    circuitCodeSyntaxFlag code = [true] ↔ ∃ c, RawCircuit.decode? code = some c := by
  rw [circuitCodeSyntaxFlag, validationScan_correct _ _ _ (unaryFlag_flag _),
    unaryFlag_accept]
  rw [RawCircuit.decode?, RawCircuit.decodePrefix?, unaryDecode]
  split_ifs with h
  · dsimp only
    cases htail : RawCircuit.decodeGates? (circuitUnaryPrefix code).length
        (circuitUnaryRest code) with
    | none => simp [h]
    | some parsed =>
      obtain ⟨c, rest⟩ := parsed
      cases rest <;> simp [h]
  · simp [h]

private theorem unaryPrefixFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitUnaryPrefix (f v) :=
  (Cobham.comp (FP_subset_CobhamFP circuitUnaryPrefix_mem_FP)
    fun _ : Fin 1 => hf).of_eq fun _ => rfl

private theorem unaryRestFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitUnaryRest (f v) :=
  (Cobham.comp (FP_subset_CobhamFP circuitUnaryRest_mem_FP)
    fun _ : Fin 1 => hf).of_eq fun _ => rfl

private theorem unaryFlagFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => unaryFlag (f v) :=
  lenLeFlag_mem hf (appendFn (unaryPrefixFn hf) (Cobham.const [false]))

private theorem gateFlagFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => gateFlag (f v) := by
  have hfirst := dropFn (Cobham.const [false, false, false]) hf
  exact andFn (lenLeFlag_mem hf (Cobham.const [false, false, false]))
    (andFn (unaryFlagFn hfirst) (unaryFlagFn (unaryRestFn hfirst)))

private theorem gateRestFn {n : ℕ} {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Cobham fun v => circuitGateRest (f v) :=
  unaryRestFn (unaryRestFn (dropFn (Cobham.const [false, false, false]) hf))

private theorem validationStep_mem_FP : validationStep ∈ FP := by
  apply CobhamFP_subset_FP
  have hf := FP_subset_CobhamFP pairFst_mem_FP
  have hs := FP_subset_CobhamFP pairSnd_mem_FP
  exact comp₂ Cobham.pairing (andFn hf (gateFlagFn hs)) (gateRestFn hs)

private theorem validationFinish_mem_FP : validationFinish ∈ FP :=
  CobhamFP_subset_FP (andFn (FP_subset_CobhamFP pairFst_mem_FP)
    (lenEqFlag_mem (FP_subset_CobhamFP pairSnd_mem_FP) Cobham.empty))

private theorem gateRest_length_le (bits : List Bool) :
    (circuitGateRest bits).length ≤ bits.length := by
  simp only [circuitGateRest, circuitUnaryRest, List.length_drop]
  omega

private theorem validationScan_bound (i : ℕ) (flag bits : List Bool)
    (hflag : flag = [true] ∨ flag = [false]) :
    (validationStep^[i] (pair flag bits)).length ≤ 2 * bits.length + 4 := by
  induction i generalizing flag bits with
  | zero => rcases hflag with rfl | rfl <;> simp [pair_length] <;> omega
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    simp only [validationStep, pairFst_pair, pairSnd_pair]
    have h := ih (andBit flag (gateFlag bits)) (circuitGateRest bits)
      (andBit_flag flag (gateFlag bits))
    have hrest := gateRest_length_le bits
    omega

/-- Exact syntax validation has an actual polynomial-time machine on all words. -/
theorem circuitCodeSyntaxFlag_mem_FP : circuitCodeSyntaxFlag ∈ FP := by
  have hinit : (fun z => pair (unaryFlag z) (circuitUnaryRest z)) ∈ FP :=
    CobhamFP_subset_FP (comp₂ Cobham.pairing (unaryFlagFn (Cobham.proj 0))
      (unaryRestFn (Cobham.proj 0)))
  have hwidth : (fun z : List Bool => z ++ z ++ [false, false, false, false]) ∈ FP :=
    CobhamFP_subset_FP (appendFn (appendFn (Cobham.proj 0) (Cobham.proj 0))
      (Cobham.const [false, false, false, false]))
  have hscan := iterate_mem_FP validationStep_mem_FP hinit circuitUnaryPrefix_mem_FP hwidth
    (fun z i _ => by
      have h := validationScan_bound i (unaryFlag z) (circuitUnaryRest z)
        (unaryFlag_flag z)
      have hrest : (circuitUnaryRest z).length ≤ z.length := by
        simp only [circuitUnaryRest, List.length_drop]
        omega
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  exact mem_FP_comp hscan validationFinish_mem_FP

end GameTheory.Complexity.Backend
