module

public import GameTheoryComplexity.Backend.BrouwerNashProgram
public import GameTheoryComplexity.Backend.BimatrixCoordinateColor
public import GameTheoryComplexity.Backend.BimatrixRawCircuit
public import Complexity.Foundations.Data.BitString.Binary
public import GameTheory.Math.BinaryExtraction
public import GameTheoryComplexity.Backend.BimatrixRawGate
public import GameTheory.Math.ClippedArithmetic
public import GameTheory.Finite.BimatrixArithmeticGate

@[expose] public section
/-! Exact prefix digits drive Boolean ripple increments and all four extended corner inputs.
The canonical program copies those bits into its relocated raw color circuits; every valid
certificate then approximates each evaluated color flag without accumulating circuit depth. -/
namespace GameTheory.Complexity.Backend.BrouwerNashColor
open Cslib.BitString Turing.MultiTapeTM Cslib.Circuits
private theorem ofBits_eq_lsbValue (bits : List Bool) : ofBits bits = Cslib.BitString.lsbValue bits := by
  unfold ofBits
  exact (Cslib.BitString.lsbValue_eq_foldr_bit bits).symm
private theorem ofBits_cons (bit : Bool) (bits : List Bool) :
    ofBits (bit :: bits) = bit.toNat + 2 * ofBits bits := by
  simp only [ofBits, List.foldr_cons, Nat.bit_val]
  omega
private theorem lowBits_ofBits_self (bits : List Bool) :
    lowBits bits.length (ofBits bits) = bits := by
  rw [ofBits_eq_lsbValue]
  exact Cslib.BitString.lowBits_lsbValue bits
private def rippleBits : List Bool → Bool → List Bool
  | [], carry => [carry]
  | bit :: bits, carry => (bit.xor carry) :: rippleBits bits (bit && carry)
private theorem rippleBits_length (bits : List Bool) (carry : Bool) :
    (rippleBits bits carry).length = bits.length + 1 := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp only [rippleBits, List.length_cons, ih]
private theorem rippleBits_value (bits : List Bool) (carry : Bool) :
    ofBits (rippleBits bits carry) = ofBits bits + if carry then 1 else 0 := by
  induction bits generalizing carry with
  | nil => cases carry <;> rfl
  | cons bit bits ih =>
    simp only [rippleBits, ofBits_cons, ih]
    cases bit <;> cases carry <;> simp <;> omega
private theorem rippleBits_eq (bits : List Bool) (carry : Bool) :
    rippleBits bits carry = lowBits (bits.length + 1)
      (ofBits bits + if carry then 1 else 0) := by
  have h := lowBits_ofBits_self (rippleBits bits carry)
  rw [rippleBits_length, rippleBits_value] at h
  exact h.symm
private def rippleCarry (bits : List Bool) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | j + 1 => bits[j]?.getD false && rippleCarry bits initial j
private theorem rippleCarry_cons (bit : Bool) (bits : List Bool) (initial : Bool) (j : ℕ) :
    rippleCarry (bit :: bits) initial (j + 1) = rippleCarry bits (bit && initial) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (bits[j]?.getD false && rippleCarry (bit :: bits) initial (j + 1)) =
      (bits[j]?.getD false && rippleCarry bits (bit && initial) j)
    rw [ih]
private theorem rippleBits_get (bits : List Bool) (carry : Bool) (j : ℕ)
    (hj : j ≤ bits.length) :
    (rippleBits bits carry)[j]?.getD false =
      (bits[j]?.getD false).xor (rippleCarry bits carry j) := by
  induction bits generalizing carry j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    cases carry <;> rfl
  | cons bit bits ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [rippleBits, List.getElem?_cons_succ, rippleCarry_cons]
      exact ih (bit && carry) j (by simp only [List.length_cons] at hj; omega)

private def prefixBits (q : ℚ) : ℕ → List Bool
  | 0 => []
  | b + 1 => GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder b q) ::
    prefixBits q b
private theorem prefixBits_length (q : ℚ) (b : ℕ) : (prefixBits q b).length = b := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [prefixBits, List.length_cons, ih]
private theorem prefixBits_value (q : ℚ) (b : ℕ) :
    ofBits (prefixBits q b) = GameTheory.Math.binaryPrefix b q := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [prefixBits, ofBits_cons, ih, GameTheory.Math.binaryPrefix]
    split <;> simp_all [Nat.add_comm]
private theorem prefixBits_get (q : ℚ) (b j : ℕ) (hj : j < b) :
    (prefixBits q b)[j]?.getD false =
      GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder (b - 1 - j) q) := by
  induction b generalizing j with
  | zero => omega
  | succ b ih =>
    cases j with
    | zero => simp only [prefixBits, List.getElem?_cons_zero, Option.getD_some,
        Nat.add_sub_cancel, Nat.sub_zero]
    | succ j =>
      simp only [prefixBits, List.getElem?_cons_succ]
      rw [ih j (by omega), show b + 1 - 1 - (j + 1) = b - 1 - j by omega]

private theorem prefixBits_pad_eq (q : ℚ) (b : ℕ) :
    prefixBits q b ++ [false] = lowBits (b + 1) (GameTheory.Math.binaryPrefix b q) := by
  have h := lowBits_ofBits_self (prefixBits q b ++ [false])
  rw [List.length_append, List.length_singleton, prefixBits_length] at h
  have happend : ofBits (prefixBits q b ++ [false]) = ofBits (prefixBits q b) := by
    calc
      ofBits (prefixBits q b ++ [false]) = Cslib.BitString.lsbValue
          (prefixBits q b ++ [false]) := ofBits_eq_lsbValue _
      _ = Cslib.BitString.lsbValue (prefixBits q b) := by
        rw [Cslib.BitString.lsbValue_append]
        simp
      _ = ofBits (prefixBits q b) := (ofBits_eq_lsbValue _).symm
  have hn : ofBits (prefixBits q b ++ [false]) =
      GameTheory.Math.binaryPrefix b q := by
    rw [happend, prefixBits_value]
  rw [hn] at h
  exact h.symm

section Game
open Cslib.Circuits
open GameTheory.Finite GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixGateProgram
variable {k : ℕ} (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
  (c : BimatrixCertificate (k * 2) (k * 2))
  (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
  (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
  (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
  (ε : ℚ) (hε : ε < 1 / 4)
  (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)

private theorem pair_gate_valid (op : CircuitFormat.signature.Op) (x y : Fin k) :
    Program.IsCodeFrom CircuitFormat.signature k 0 [(op, [x.val, y.val])] := by
  simp [Program.IsCodeFrom]

include hk hc hM hg hscale hε hδ in
private theorem ripple_step (input carry : Fin k) (out : Fin 4 → Fin k)
    (h0 : g (out 0) = BimatrixRawGate.gate
      ((true, false, true), [input.val, carry.val])
        (pair_gate_valid _ input carry))
    (h1 : g (out 1) = BimatrixRawGate.gate
      ((true, true, false), [input.val, carry.val])
        (pair_gate_valid _ input carry))
    (h2 : g (out 2) = BimatrixRawGate.gate
      ((false, false, false), [(out 0).val, (out 1).val])
        (pair_gate_valid _ (out 0) (out 1)))
    (h3 : g (out 3) = BimatrixRawGate.gate
      ((true, false, false), [input.val, carry.val])
        (pair_gate_valid _ input carry))
    (bit cb : Bool)
    (hin : |(k : ℚ) * value c input - (if bit then 1 else 0)| ≤ ε)
    (hcarry : |(k : ℚ) * value c carry - (if cb then 1 else 0)| ≤ ε) :
    (|(k : ℚ) * value c (out 2) - (if bit.xor cb then 1 else 0)| ≤ ε) ∧
    (|(k : ℚ) * value c (out 3) - (if bit && cb then 1 else 0)| ≤ ε) := by
  have hraw0 : (⟨[input.val, carry.val].getD 0 0,
      BimatrixRawGate.reference_lt ((true, false, true), [input.val, carry.val])
        (pair_gate_valid _ input carry) 0⟩ : Fin k) = input := Fin.ext (by rfl)
  have hraw1 : (⟨[input.val, carry.val].getD 1 0,
      BimatrixRawGate.reference_lt ((true, false, true), [input.val, carry.val])
        (pair_gate_valid _ input carry) 1⟩ : Fin k) = carry := Fin.ext (by rfl)
  have hin0 : |(k : ℚ) * value c ⟨[input.val, carry.val].getD 0 0,
      BimatrixRawGate.reference_lt ((true, false, true), [input.val, carry.val])
        (pair_gate_valid _ input carry) 0⟩ -
        (if bit then 1 else 0)| ≤ ε := by simpa only [hraw0] using hin
  have hin1 : |(k : ℚ) * value c ⟨[input.val, carry.val].getD 1 0,
      BimatrixRawGate.reference_lt ((true, false, true), [input.val, carry.val])
        (pair_gate_valid _ input carry) 1⟩ -
        (if cb then 1 else 0)| ≤ ε := by simpa only [hraw1] using hcarry
  have ha := (BimatrixRawGate.gate_output_error H M
    ((true, false, true), [input.val, carry.val]) (pair_gate_valid _ input carry)
    hk g c hc hM hg hscale (out 0) h0 bit cb ε hin0 hin1 hε).trans hδ
  have ha' : |(k : ℚ) * value c (out 0) - (if bit && !cb then 1 else 0)| ≤ ε := by
    simpa [CircuitFormat.opValue] using ha
  have hb := (BimatrixRawGate.gate_output_error H M
    ((true, true, false), [input.val, carry.val]) (pair_gate_valid _ input carry)
    hk g c hc hM hg hscale (out 1) h1 bit cb ε hin0 hin1 hε).trans hδ
  have hb' : |(k : ℚ) * value c (out 1) - (if !bit && cb then 1 else 0)| ≤ ε := by
    simpa [CircuitFormat.opValue] using hb
  have hraw20 : (⟨[(out 0).val, (out 1).val].getD 0 0,
      BimatrixRawGate.reference_lt ((false, false, false), [(out 0).val, (out 1).val])
        (pair_gate_valid _ (out 0) (out 1)) 0⟩ : Fin k) = out 0 := Fin.ext (by rfl)
  have hraw21 : (⟨[(out 0).val, (out 1).val].getD 1 0,
      BimatrixRawGate.reference_lt ((false, false, false), [(out 0).val, (out 1).val])
        (pair_gate_valid _ (out 0) (out 1)) 1⟩ : Fin k) = out 1 := Fin.ext (by rfl)
  have hx := (BimatrixRawGate.gate_output_error H M
    ((false, false, false), [(out 0).val, (out 1).val]) (pair_gate_valid _ (out 0) (out 1))
    hk g c hc hM hg hscale (out 2) h2 (bit && !cb) (!bit && cb) ε
    (by simpa only [hraw20, CircuitFormat.opValue] using ha')
    (by simpa only [hraw21, CircuitFormat.opValue] using hb') hε).trans hδ
  have hx' : |(k : ℚ) * value c (out 2) - (if bit.xor cb then 1 else 0)| ≤ ε := by
    cases bit <;> cases cb <;> simpa [CircuitFormat.opValue] using hx
  have hcar := (BimatrixRawGate.gate_output_error H M
    ((true, false, false), [input.val, carry.val]) (pair_gate_valid _ input carry)
    hk g c hc hM hg hscale (out 3) h3 bit cb ε hin0 hin1 hε).trans hδ
  have hcar' : |(k : ℚ) * value c (out 3) - (if bit && cb then 1 else 0)| ≤ ε := by
    simpa [CircuitFormat.opValue] using hcar
  constructor
  · cases bit <;> cases cb <;> simpa only [Bool.false_xor, Bool.false_and,
      Bool.true_xor, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_or,
      Bool.true_or, Bool.xor_false, Bool.xor_true] using hx'
  · exact hcar'
include hk hc hM hg hscale hε hδ in
private theorem ripple_chain (bits : List Bool) (input : ℕ → Fin k)
    (out : ℕ → Fin 4 → Fin k) (one : Fin k)
    (hone : |(k : ℚ) * value c one - 1| ≤ ε)
    (hin : ∀ j < bits.length,
      |(k : ℚ) * value c (input j) - (if bits[j]?.getD false then 1 else 0)| ≤ ε)
    (h0 : ∀ j < bits.length, g (out j 0) = BimatrixRawGate.gate
      ((true, false, true), [(input j).val, (if j = 0 then one else out (j - 1) 3).val])
        (pair_gate_valid _ (input j) (if j = 0 then one else out (j - 1) 3)))
    (h1 : ∀ j < bits.length, g (out j 1) = BimatrixRawGate.gate
      ((true, true, false), [(input j).val, (if j = 0 then one else out (j - 1) 3).val])
        (pair_gate_valid _ (input j) (if j = 0 then one else out (j - 1) 3)))
    (h2 : ∀ j < bits.length, g (out j 2) = BimatrixRawGate.gate
      ((false, false, false), [(out j 0).val, (out j 1).val])
        (pair_gate_valid _ (out j 0) (out j 1)))
    (h3 : ∀ j < bits.length, g (out j 3) = BimatrixRawGate.gate
      ((true, false, false), [(input j).val, (if j = 0 then one else out (j - 1) 3).val])
        (pair_gate_valid _ (input j) (if j = 0 then one else out (j - 1) 3))) :
    (∀ j ≤ bits.length,
      |(k : ℚ) * value c (if j = 0 then one else out (j - 1) 3) -
        (if rippleCarry bits true j then 1 else 0)| ≤ ε) ∧
    (∀ j < bits.length, |(k : ℚ) * value c (out j 2) -
      (if (rippleBits bits true)[j]?.getD false then 1 else 0)| ≤ ε) := by
  have hcarry : ∀ j ≤ bits.length,
      |(k : ℚ) * value c (if j = 0 then one else out (j - 1) 3) -
        (if rippleCarry bits true j then 1 else 0)| ≤ ε := by
    intro j hj
    induction j with
    | zero => simpa only [rippleCarry, ite_true] using hone
    | succ j ih =>
      have he := ripple_step H M hk g c hc hM hg hscale ε hε hδ
        (input j) (if j = 0 then one else out (j - 1) 3) (out j)
        (h0 j (by omega)) (h1 j (by omega)) (h2 j (by omega)) (h3 j (by omega))
        (bits[j]?.getD false) (rippleCarry bits true j) (hin j (by omega)) (ih (by omega))
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
        Nat.add_sub_cancel]
      exact he.2
  refine ⟨hcarry, ?_⟩
  intro j hj
  rw [rippleBits_get bits true j hj.le]
  exact (ripple_step H M hk g c hc hM hg hscale ε hε hδ
    (input j) (if j = 0 then one else out (j - 1) 3) (out j)
    (h0 j hj) (h1 j hj) (h2 j hj) (h3 j hj)
    (bits[j]?.getD false) (rippleCarry bits true j) (hin j hj) (hcarry j hj.le)).1

include hk hc hM hg hscale hδ in
private theorem copy_error (input out : Fin k)
    (hout : g out = BimatrixArithmeticGate.gate
      (fun j => if j = input then 2 * (k : ℤ) else 0) 0)
    (bit : Bool) (hin : |(k : ℚ) * value c input - (if bit then 1 else 0)| ≤ ε) :
    |(k : ℚ) * value c out - (if bit then 1 else 0)| ≤ 2 * ε := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have he := (BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (fun j => if j = input then 2 * (k : ℤ) else 0) 0
    g c hc hC hM hg hscale out hout).trans hδ
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hs : (∑ j, ((if j = input then 2 * (k : ℤ) else 0 : ℤ) : ℚ) /
      ((2 * (k : ℤ) : ℤ) : ℚ) * ((k : ℚ) * value c j)) +
      (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) = (k : ℚ) * value c input := by
    push_cast
    simp only [ite_div, zero_div, ite_mul, zero_mul, mul_zero, add_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  rw [hs] at he
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    ((k : ℚ) * value c input) (if bit then 1 else 0)
  have hfixed : max (0 : ℚ) (min 1 (if bit then 1 else 0)) = (if bit then 1 else 0) := by
    cases bit <;> norm_num
  rw [hfixed] at hcl
  exact (abs_sub_le _ _ _).trans ((add_le_add he (hcl.trans hin)).trans_eq (by ring))

end Game

section Concrete
open Cslib.Circuits
open BrouwerNashLayout BrouwerNashProgram
private theorem program_increment_raw (b : ℕ)
    (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ)) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (hj : j < b) (stage : Fin 4) :
    let input := sampleRef b raw₀.length raw₁.length t (primaryBit b axis j)
    let carry := if j = 0 then slot b raw₀.length raw₁.length one
      else sampleRef b raw₀.length raw₁.length t (increment b axis (j - 1) 3)
    let out := fun stage => sampleRef b raw₀.length raw₁.length t (increment b axis j stage)
    program b raw₀ raw₁ (out stage) = guardedRaw (match stage.val with
      | 0 => ((true, false, true), [input.val, carry.val])
      | 1 => ((true, true, false), [input.val, carry.val])
      | 2 => ((false, false, false), [(out 0).val, (out 1).val])
      | _ => ((true, false, false), [input.val, carry.val])) := by
  dsimp only
  rw [program_sample _ _ _ _ _ (increment_lt_sampleWidth _ _ _ axis j hj stage),
    sampleGate_increment _ _ _ _ axis j hj stage]
  have hcarry : (if j = 0 then one else
      (sampleRef b raw₀.length raw₁.length t (increment b axis (j - 1) 3)).val) =
      (if j = 0 then slot b raw₀.length raw₁.length one else
        sampleRef b raw₀.length raw₁.length t (increment b axis (j - 1) 3)).val := by
    by_cases hz : j = 0
    · simp only [hz, ite_true, slot_val _ _ _ _ (one_lt_dimension _ _ _)]
    · simp only [hz, ite_false]
  unfold incrementGate
  rw [hcarry]
  rfl
variable (b : ℕ) (raw₀ raw₁ : List (CircuitFormat.signature.Op × List ℕ))
local notation "K" => dimension b raw₀.length raw₁.length
local notation "programG" => program b raw₀ raw₁
open GameTheory.Finite GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixGateProgram

/-- Concrete ripple slots represent prefix plus one, retaining the extra overflow bit. -/
theorem increment_error (H M : ℤ) (c : BimatrixCertificate (K * 2) (K * 2))
    (hc : c.Valid (rowPayoff H (2 * (K : ℤ))) (columnPayoff H (2 * (K : ℤ)) programG))
    (hM : 0 ≤ M) (hg : ∀ i r, |(programG i).coefficients r| ≤ M)
    (hscale : (K : ℤ) * (M + 2 * (K : ℤ)) < H) (ε : ℚ) (hε : ε < 1 / 4)
    (hδ : (K : ℚ) * (((M + 2 * (K : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (t : Fin 41) (axis : Fin 2) (q : ℚ)
    (hone : |(K : ℚ) * value c (slot b raw₀.length raw₁.length one) - 1| ≤ ε)
    (hdigit : ∀ j < b, |(K : ℚ) * value c
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
      (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j q)
        then 1 else 0)| ≤ ε) (j : ℕ) (hj : j ≤ b) :
    |(K : ℚ) * value c (if j = b then
      if b = 0 then slot b raw₀.length raw₁.length one else
        sampleRef b raw₀.length raw₁.length t (increment b axis (b - 1) 3)
      else sampleRef b raw₀.length raw₁.length t (increment b axis j 2)) -
      (if (lowBits (b + 1) (GameTheory.Math.binaryPrefix b q + 1))[j]?.getD false
        then 1 else 0)| ≤ ε := by
  let input := fun j => sampleRef b raw₀.length raw₁.length t (primaryBit b axis j)
  let out := fun j stage => sampleRef b raw₀.length raw₁.length t (increment b axis j stage)
  let oneSlot := slot b raw₀.length raw₁.length one
  have hstep (j : ℕ) (hj : j < (prefixBits q b).length) (stage : Fin 4) :
      programG (out j stage) = guardedRaw (match stage.val with
        | 0 => ((true, false, true), [(input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val])
        | 1 => ((true, true, false), [(input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val])
        | 2 => ((false, false, false), [(out j 0).val, (out j 1).val])
        | _ => ((true, false, false), [(input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val])) :=
    program_increment_raw b raw₀ raw₁ t axis j (by rw [prefixBits_length] at hj; exact hj) stage
  have hin (j : ℕ) (hj : j < (prefixBits q b).length) :
      |(K : ℚ) * value c (input j) - (if (prefixBits q b)[j]?.getD false then 1 else 0)| ≤ ε := by
    have hjb : j < b := by rwa [prefixBits_length] at hj
    rw [prefixBits_get q b j hjb]
    exact hdigit (b - 1 - j) (by omega)
  have hr := ripple_chain H M (dimension_pos _ _ _) programG c hc hM hg hscale ε hε hδ
    (prefixBits q b) input out oneSlot hone hin
    (fun j hj => by
      rw [hstep j hj 0]
      exact guardedRaw_eq _ (pair_gate_valid _ (input j)
        (if j = 0 then oneSlot else out (j - 1) 3)))
    (fun j hj => by
      rw [hstep j hj 1]
      exact guardedRaw_eq _ (pair_gate_valid _ (input j)
        (if j = 0 then oneSlot else out (j - 1) 3)))
    (fun j hj => by
      rw [hstep j hj 2]
      exact guardedRaw_eq _ (pair_gate_valid _ (out j 0) (out j 1)))
    (fun j hj => by
      rw [hstep j hj 3]
      exact guardedRaw_eq _ (pair_gate_valid _ (input j)
        (if j = 0 then oneSlot else out (j - 1) 3)))
  have he : rippleBits (prefixBits q b) true =
      lowBits (b + 1) (GameTheory.Math.binaryPrefix b q + 1) := by
    rw [rippleBits_eq, prefixBits_length, prefixBits_value]
    rfl
  rw [← he]
  by_cases hlast : j = b
  · subst j
    simp only [ite_true]
    rw [rippleBits_get _ _ _ (by rw [prefixBits_length])]
    have hn : (prefixBits q b)[b]?.getD false = false := by
      simp [prefixBits_length]
    rw [hn, Bool.false_xor]
    exact hr.1 b (by rw [prefixBits_length])
  · simp only [hlast, ite_false]
    exact hr.2 j (by rw [prefixBits_length]; omega)

/-- Copied corner coordinates use the exact prefix or prefix-plus-one bit field. -/
theorem cornerBit_error (H M : ℤ) (c : BimatrixCertificate (K * 2) (K * 2))
    (hc : c.Valid (rowPayoff H (2 * (K : ℤ))) (columnPayoff H (2 * (K : ℤ)) programG))
    (hM : 0 ≤ M) (hg : ∀ i r, |(programG i).coefficients r| ≤ M)
    (hscale : (K : ℤ) * (M + 2 * (K : ℤ)) < H) (ε : ℚ) (hε : ε < 1 / 4)
    (hδ : (K : ℚ) * (((M + 2 * (K : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (t : Fin 41) (axis : Fin 2) (q : ℚ)
    (hone : |(K : ℚ) * value c (slot b raw₀.length raw₁.length one) - 1| ≤ ε)
    (hzero : |(K : ℚ) * value c (slot b raw₀.length raw₁.length zero)| ≤ ε)
    (hdigit : ∀ j < b, |(K : ℚ) * value c
        (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
      (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j q)
        then 1 else 0)| ≤ ε) (corner : Fin 4) (j : ℕ) (hj : j ≤ b) :
    let upper := if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
      else corner.val = 1 ∨ corner.val = 3
    |(K : ℚ) * value c (cornerBit b raw₀.length raw₁.length t corner axis j) -
      (if (lowBits (b + 1)
        (GameTheory.Math.binaryPrefix b q + if upper then 1 else 0))[j]?.getD false
        then 1 else 0)| ≤ ε := by
  dsimp only
  by_cases hu : if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
    else corner.val = 1 ∨ corner.val = 3
  · simpa only [cornerBit, hu, ite_true] using
      increment_error b raw₀ raw₁ H M c hc hM hg hscale ε hε hδ t axis q hone hdigit j hj
  · simp only [cornerBit, hu, ite_false, add_zero]
    rw [← prefixBits_pad_eq]
    by_cases hlast : j = b
    · subst j
      simp only [ite_true]
      have hn : (prefixBits q b ++ [false])[b]?.getD false = false := by
        rw [List.getElem?_append_right (by rw [prefixBits_length]), prefixBits_length,
          Nat.sub_self]
        rfl
      rw [hn]
      simpa only [Bool.false_eq_true, ite_false, sub_zero] using hzero
    · simp only [hlast, ite_false]
      have hjb : j < b := by omega
      rw [List.getElem?_append_left (by rw [prefixBits_length]; exact hjb),
        prefixBits_get q b j hjb]
      exact hdigit (b - 1 - j) (by omega)

private theorem color_end_lt (corner : Fin 4) (flag : Fin 2) :
    colorInput b raw₀.length raw₁.length corner flag + arity b +
      (if flag.val = 0 then raw₀ else raw₁).length < sampleWidth b raw₀.length raw₁.length := by
  have hc : corner.val + 1 ≤ 4 := by have hh := corner.isLt; omega
  have hm := Nat.mul_le_mul_right (cornerWidth b raw₀.length raw₁.length) hc
  simp only [Nat.add_mul, Nat.one_mul] at hm
  fin_cases flag <;>
    simp only [colorInput, cornerWidth, colorBase, weightBase, sampleWidth,
      ite_true, Nat.one_ne_zero, ite_false] at hm ⊢ <;> omega

private theorem program_colorRegion (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : ℕ) (hj : (if flag.val = 0 then 0 else arity b + raw₀.length) + j <
      cornerWidth b raw₀.length raw₁.length) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner flag + j)) =
      colorRegionGate b raw₀ raw₁ t corner
        ((if flag.val = 0 then 0 else arity b + raw₀.length) + j) := by
  have hc : corner.val + 1 ≤ 4 := by have hh := corner.isLt; omega
  have hm := Nat.mul_le_mul_right (cornerWidth b raw₀.length raw₁.length) hc
  simp only [Nat.add_mul, Nat.one_mul] at hm
  have hlocal : colorInput b raw₀.length raw₁.length corner flag + j <
      sampleWidth b raw₀.length raw₁.length := by
    simp only [colorInput, sampleWidth, colorBase, weightBase] at hj hm ⊢
    omega
  rw [program_sample _ _ _ _ _ hlocal]
  have he : colorInput b raw₀.length raw₁.length corner flag + j =
      colorBase b + corner.val * cornerWidth b raw₀.length raw₁.length +
        ((if flag.val = 0 then 0 else arity b + raw₀.length) + j) := by
    simp only [colorInput, Nat.add_assoc]
  rw [he, sampleGate_colorRegion _ _ _ _ _ _ hj]

private theorem copy_lt_region (flag : Fin 2) (j : ℕ) (hj : j < arity b) :
    (if flag.val = 0 then 0 else arity b + raw₀.length) + j <
      cornerWidth b raw₀.length raw₁.length := by
  fin_cases flag <;>
    simp only [cornerWidth, ite_true, Nat.one_ne_zero, ite_false] <;> omega

private theorem program_copy (t : Fin 41) (corner : Fin 4) (flag : Fin 2)
    (j : ℕ) (hj : j < arity b) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner flag + j)) =
      BimatrixArithmeticGate.gate (fun a => if a =
        cornerBit b raw₀.length raw₁.length t corner
          ⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩ (j % (b + 1))
        then 2 * (K : ℤ) else 0) 0 := by
  rw [program_colorRegion _ _ _ _ _ _ j (copy_lt_region _ _ _ flag j hj),
    colorRegionGate_copy _ _ _ _ _ _ j hj]
  simp only [affine₂, ite_self, add_zero]

/-- Canonical extended coordinate fields for origin, diagonal, horizontal and vertical corners. -/
def cornerVertex (b : ℕ) (qx qy : ℚ) (corner : Fin 4) : List Bool :=
  lowBits (b + 1) (GameTheory.Math.binaryPrefix b qx +
    if corner.val = 1 ∨ corner.val = 2 then 1 else 0) ++
  lowBits (b + 1) (GameTheory.Math.binaryPrefix b qy +
    if corner.val = 1 ∨ corner.val = 3 then 1 else 0)

private theorem cornerVertex_length (qx qy : ℚ) (corner : Fin 4) :
    (cornerVertex b qx qy corner).length = arity b := by
  simp only [cornerVertex, List.length_append, Cslib.BitString.length_lowBits, arity]
  omega

private theorem corner_input_error (c : GameTheory.Finite.BimatrixCertificate (K * 2) (K * 2))
    (t : Fin 41) (corner : Fin 4) (qx qy ε : ℚ)
    (hcorner : ∀ axis : Fin 2, ∀ j ≤ b,
      |(K : ℚ) * GameTheory.Finite.BimatrixAffineGate.value c
        (cornerBit b raw₀.length raw₁.length t corner axis j) -
        (if (lowBits (b + 1) (GameTheory.Math.binaryPrefix b
          (if axis.val = 0 then qx else qy) +
          if (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
            else corner.val = 1 ∨ corner.val = 3) then 1 else 0))[j]?.getD false
          then 1 else 0)| ≤ ε)
    (j : ℕ) (hj : j < arity b) :
    |(K : ℚ) * GameTheory.Finite.BimatrixAffineGate.value c
      (cornerBit b raw₀.length raw₁.length t corner
        ⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩ (j % (b + 1))) -
      (if (cornerVertex b qx qy corner)[j]?.getD false then 1 else 0)| ≤ ε := by
  by_cases hlow : j < b + 1
  · have ha : (⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := by
      apply Fin.ext
      simp only [Nat.div_eq_of_lt hlow, Nat.zero_mod, Fin.val_zero]
    rw [ha, Nat.mod_eq_of_lt hlow]
    have h := hcorner 0 j (by omega)
    simp only [Fin.val_zero, ite_true] at h
    unfold cornerVertex
    rw [List.getElem?_append_left (by rw [Cslib.BitString.length_lowBits]; exact hlow)]
    exact h
  · have hjhigh : j - (b + 1) < b + 1 := by simp only [arity] at hj; omega
    have hjform : j = (b + 1) * 1 + (j - (b + 1)) := by omega
    have hd : j / (b + 1) = 1 := by
      rw [hjform, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hjhigh]
    have hm : j % (b + 1) = j - (b + 1) := by
      conv_lhs => rw [hjform]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hjhigh]
    have ha : (⟨(j / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 := by
      apply Fin.ext
      rw [hd]
      rfl
    rw [ha, hm]
    have h := hcorner 1 (j - (b + 1)) (by omega)
    simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at h
    unfold cornerVertex
    rw [List.getElem?_append_right (by rw [Cslib.BitString.length_lowBits]; omega),
      Cslib.BitString.length_lowBits]
    exact h

private theorem program_raw₀ (t : Fin 41) (corner : Fin 4) (j : Fin raw₀.length)
    (href : Program.IsCodeFrom CircuitFormat.signature K 0
      [((raw₀.get j).1, (raw₀.get j).2.map
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 0 + ·))]) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner 0 + arity b + j.val)) =
      BimatrixRawGate.gate ((raw₀.get j).1, (raw₀.get j).2.map
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 0 + ·))
        href := by
  have ho : arity b + j.val < cornerWidth b raw₀.length raw₁.length := by
    have hj := j.isLt
    simp only [cornerWidth]
    omega
  have he := program_colorRegion b raw₀ raw₁ t corner 0 (arity b + j.val)
    (by simpa only [Fin.val_zero, ite_true, zero_add] using ho)
  simp only [Fin.val_zero, ite_true, zero_add] at he
  rw [colorRegionGate_raw₀ _ _ _ _ _ j, guardedRaw_eq _ href] at he
  simpa only [Nat.add_assoc] using he

private theorem program_raw₁ (t : Fin 41) (corner : Fin 4) (j : Fin raw₁.length)
    (href : Program.IsCodeFrom CircuitFormat.signature K 0
      [((raw₁.get j).1, (raw₁.get j).2.map
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 1 + ·))]) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner 1 + arity b + j.val)) =
      BimatrixRawGate.gate ((raw₁.get j).1, (raw₁.get j).2.map
        (sampleBase b raw₀.length raw₁.length t +
          colorInput b raw₀.length raw₁.length corner 1 + ·))
        href := by
  have ho : (arity b + raw₀.length) + (arity b + j.val) <
      cornerWidth b raw₀.length raw₁.length := by
    have hj := j.isLt
    simp only [cornerWidth]
    omega
  have he := program_colorRegion b raw₀ raw₁ t corner 1 (arity b + j.val)
    (by simpa only [Fin.val_one, Nat.one_ne_zero, ite_false] using ho)
  have hp : (arity b + raw₀.length) + (arity b + j.val) =
      2 * arity b + raw₀.length + j.val := by omega
  simp only [Fin.val_one, Nat.one_ne_zero, ite_false] at he
  rw [hp, colorRegionGate_raw₁ _ _ _ _ _ j, guardedRaw_eq _ href] at he
  simpa only [Nat.add_assoc] using he

/-- Actual copied inputs and relocated raw gates approximate every canonical corner color bit. -/
theorem colorOutput_error (H M : ℤ) (c : BimatrixCertificate (K * 2) (K * 2))
    (hc : c.Valid (rowPayoff H (2 * (K : ℤ))) (columnPayoff H (2 * (K : ℤ)) programG))
    (hM : 0 ≤ M) (hg : ∀ i r, |(programG i).coefficients r| ≤ M)
    (hscale : (K : ℤ) * (M + 2 * (K : ℤ)) < H) (ε : ℚ) (hε : 2 * ε < 1 / 4)
    (hδ : (K : ℚ) * (((M + 2 * (K : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (t : Fin 41) (corner : Fin 4) (qx qy : ℚ)
    (hcorner : ∀ axis : Fin 2, ∀ j ≤ b,
      |(K : ℚ) * value c (cornerBit b raw₀.length raw₁.length t corner axis j) -
        (if (lowBits (b + 1) (GameTheory.Math.binaryPrefix b
          (if axis.val = 0 then qx else qy) +
          if (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
            else corner.val = 1 ∨ corner.val = 3) then 1 else 0))[j]?.getD false
          then 1 else 0)| ≤ ε)
    (flag : Fin 2) (bit : Bool)
    (hraw : Program.IsCodeFrom CircuitFormat.signature (arity b) 0
      (if flag.val = 0 then raw₀ else raw₁))
    (hne : (if flag.val = 0 then raw₀ else raw₁) ≠ [])
    (hquery : CircuitFormat.evalOutput (cornerVertex b qx qy corner)
      (if flag.val = 0 then raw₀ else raw₁)
      (arity b + (if flag.val = 0 then raw₀ else raw₁).length - 1) = bit) :
    |(K : ℚ) * value c (sampleRef b raw₀.length raw₁.length t
      (colorGate b raw₀.length raw₁.length corner flag +
        ((if flag.val = 0 then raw₀ else raw₁).length - 1))) -
      (if bit then 1 else 0)| ≤ 2 * ε := by
  let raw := if flag.val = 0 then raw₀ else raw₁
  let offset := sampleBase b raw₀.length raw₁.length t +
    colorInput b raw₀.length raw₁.length corner flag
  have hend := color_end_lt b raw₀ raw₁ corner flag
  have hsize : offset + (cornerVertex b qx qy corner).length + raw.length ≤ K := by
    have ha := sample_lt_dimension b raw₀.length raw₁.length t _ hend
    rw [cornerVertex_length]
    dsimp only [offset, raw]
    omega
  have hlen : 0 < raw.length := List.length_pos_iff.mpr hne
  have he0 : 0 ≤ ε := by
    have hh := hcorner 0 0 (Nat.zero_le b)
    exact (abs_nonneg _).trans hh
  have hplace : ∀ j : Fin raw.length, ∀ href : Program.IsCodeFrom CircuitFormat.signature K 0
      [((raw.get j).1, (raw.get j).2.map (offset + ·))],
      programG ⟨offset + (cornerVertex b qx qy corner).length + j.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get j).1, (raw.get j).2.map (offset + ·)) href := by
    intro j href
    have hshift : Program.IsCodeFrom CircuitFormat.signature K 0
        [((raw.get j).1, (raw.get j).2.map (offset + ·))] := by
      change ((((raw.get j).2.map (offset + ·)).length =
          CircuitFormat.signature.Arity (raw.get j).1 ∧
        ∀ q ∈ (raw.get j).2.map (offset + ·), q < K) ∧
        Program.IsCodeFrom CircuitFormat.signature K 1 [])
      have hrawList : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 raw := hraw
      have hentry : ((raw.get j).2.length = 2 ∧
          ∀ r ∈ (raw.get j).2, r < arity b + j.val) := by
        simpa only [List.get_eq_getElem, Fin.getElem_fin, Nat.add_zero] using
          hrawList.getElem j.val j.isLt
      constructor
      · constructor
        · simpa only [List.length_map] using hentry.1
        · intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have href := hentry.2 r hr
          have hlast : offset + arity b + j.val < K := by
            rw [cornerVertex_length] at hsize
            have hj := j.isLt
            omega
          omega
      · trivial
    have hlocal : colorInput b raw₀.length raw₁.length corner flag + arity b + j.val <
        sampleWidth b raw₀.length raw₁.length := by have hj := j.isLt; dsimp [raw] at hj; omega
    have ha := sample_lt_dimension b raw₀.length raw₁.length t _ hlocal
    have heq : (⟨offset + (cornerVertex b qx qy corner).length + j.val, by omega⟩ : Fin K) =
        sampleRef b raw₀.length raw₁.length t
          (colorInput b raw₀.length raw₁.length corner flag + arity b + j.val) := by
      apply Fin.ext
      simp only [sampleRef, slot_val _ _ _ _ ha, cornerVertex_length]
      dsimp only [offset]
      omega
    rw [heq]
    fin_cases flag
    · exact program_raw₀ b raw₀ raw₁ t corner j hshift
    · exact program_raw₁ b raw₀ raw₁ t corner j hshift
  have hinput : ∀ j : Fin K, ∀ hj0 : offset ≤ j.val,
      ∀ hj : j.val < offset + (cornerVertex b qx qy corner).length,
      |(K : ℚ) * value c j -
        (if (cornerVertex b qx qy corner).getD (j.val - offset) false then 1 else 0)| ≤ 2 * ε := by
    intro j hj0 hj
    have hjlocal : j.val - offset < arity b := by rw [cornerVertex_length] at hj; omega
    have hbit := corner_input_error b raw₀ raw₁ c t corner qx qy ε hcorner
      (j.val - offset) hjlocal
    have hcopy := copy_error H M (dimension_pos _ _ _) programG c hc hM hg hscale ε hδ
      (cornerBit b raw₀.length raw₁.length t corner
        ⟨((j.val - offset) / (b + 1)) % 2, Nat.mod_lt _ (by decide)⟩
          ((j.val - offset) % (b + 1)))
      (sampleRef b raw₀.length raw₁.length t
        (colorInput b raw₀.length raw₁.length corner flag + (j.val - offset)))
      (program_copy b raw₀ raw₁ t corner flag _ hjlocal)
      ((cornerVertex b qx qy corner)[j.val - offset]?.getD false) hbit
    have hlocal : colorInput b raw₀.length raw₁.length corner flag + (j.val - offset) <
        sampleWidth b raw₀.length raw₁.length := by dsimp only [raw] at *; omega
    have ha := sample_lt_dimension b raw₀.length raw₁.length t _ hlocal
    have heq : sampleRef b raw₀.length raw₁.length t
        (colorInput b raw₀.length raw₁.length corner flag + (j.val - offset)) = j := by
      apply Fin.ext
      rw [show (sampleRef b raw₀.length raw₁.length t _).val =
        sampleBase b raw₀.length raw₁.length t +
          (colorInput b raw₀.length raw₁.length corner flag + (j.val - offset)) from
          slot_val _ _ _ _ ha]
      dsimp only [offset] at hj0 ⊢
      omega
    rw [heq] at hcopy
    have hiList : j.val - offset < (cornerVertex b qx qy corner).length := by
      rw [cornerVertex_length]
      exact hjlocal
    simpa only [← List.getD_eq_getElem?_getD] using hcopy
  let output : Fin ((cornerVertex b qx qy corner).length + raw.length) :=
    ⟨arity b + raw.length - 1, by rw [cornerVertex_length]; omega⟩
  have htopo : Program.IsCodeFrom CircuitFormat.signature
      (cornerVertex b qx qy corner).length 0 raw := by
    rw [cornerVertex_length]
    exact hraw
  have herr := BimatrixRawCircuit.evalOutput_correct_at H M
    (dimension_pos _ _ _) programG c hc hM hg hscale (2 * ε) hε (by linarith) offset raw
    (cornerVertex b qx qy corner) htopo (by simpa only [cornerVertex_length] using hsize)
    hplace hinput output
  have hbit : CircuitFormat.evalOutput (cornerVertex b qx qy corner) raw output.val = bit := by
    simpa only [output, cornerVertex_length] using hquery
  rw [hbit] at herr
  have hlocal : colorGate b raw₀.length raw₁.length corner flag + (raw.length - 1) <
      sampleWidth b raw₀.length raw₁.length := by dsimp only [colorGate, raw] at *; omega
  have ha := sample_lt_dimension b raw₀.length raw₁.length t _ hlocal
  have heq : (⟨offset + output.val, by omega⟩ :
      Fin K) = sampleRef b raw₀.length raw₁.length t
        (colorGate b raw₀.length raw₁.length corner flag + (raw.length - 1)) := by
    apply Fin.ext
    simp only [sampleRef, slot_val _ _ _ _ ha, output]
    dsimp only [offset, colorGate]
    omega
  rw [heq] at herr
  exact herr

open GameTheory.Math BrouwerNashLayout in
/-- A native color query remains exact at each extended corner of the selected binary cell. -/
theorem cornerVertex_eval (color : ℕ → ℕ → Fin 3) (b : ℕ)
    (gates : List (CircuitFormat.signature.Op × List ℕ)) (flag : Fin 2)
    (_hraw : Program.IsCodeFrom CircuitFormat.signature (arity b) 0 gates)
    (_hne : gates ≠ [])
    (hquery : ∀ x y, x ≤ 2 ^ b → y ≤ 2 ^ b →
      CircuitFormat.evalOutput (lowBits (b + 1) x ++ lowBits (b + 1) y) gates
        (arity b + gates.length - 1) = (encodeGridColor (color x y)).getD flag.val false)
    (qx qy : ℚ) (corner : Fin 4) :
    CircuitFormat.evalOutput (cornerVertex b qx qy corner) gates
        (arity b + gates.length - 1) =
      (encodeGridColor (color
        (binaryPrefix b qx + if corner.val = 1 ∨ corner.val = 2 then 1 else 0)
        (binaryPrefix b qy + if corner.val = 1 ∨ corner.val = 3 then 1 else 0))).getD flag.val false := by
  let x := binaryPrefix b qx + if corner.val = 1 ∨ corner.val = 2 then 1 else 0
  let y := binaryPrefix b qy + if corner.val = 1 ∨ corner.val = 3 then 1 else 0
  have hx : x ≤ 2 ^ b := by
    dsimp only [x]
    have hp := binaryPrefix_lt b qx
    split_ifs <;> omega
  have hy : y ≤ 2 ^ b := by
    dsimp only [y]
    have hp := binaryPrefix_lt b qy
    split_ifs <;> omega
  have he := hquery x y hx hy
  simpa only [cornerVertex, x, y] using he


/-- Exact extracted digits discharge every input premise of concrete corner color evaluation. -/
theorem colorOutput_error_of_digits (H M : ℤ) (c : BimatrixCertificate (K * 2) (K * 2))
    (hc : c.Valid (rowPayoff H (2 * (K : ℤ))) (columnPayoff H (2 * (K : ℤ)) programG))
    (hM : 0 ≤ M) (hg : ∀ i r, |(programG i).coefficients r| ≤ M)
    (hscale : (K : ℤ) * (M + 2 * (K : ℤ)) < H) (ε : ℚ) (hε : 2 * ε < 1 / 4)
    (hδ : (K : ℚ) * (((M + 2 * (K : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (color : ℕ → ℕ → Fin 3) (t : Fin 41) (corner : Fin 4) (qx qy : ℚ)
    (hone : |(K : ℚ) * value c (slot b raw₀.length raw₁.length one) - 1| ≤ ε)
    (hzero : |(K : ℚ) * value c (slot b raw₀.length raw₁.length zero)| ≤ ε)
    (hdigit : ∀ axis : Fin 2, ∀ j < b,
      |(K : ℚ) * value c (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
        (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j
          (if axis.val = 0 then qx else qy)) then 1 else 0)| ≤ ε)
    (flag : Fin 2)
    (hraw : ∀ flag : Fin 2, Program.IsCodeFrom CircuitFormat.signature (arity b) 0
      (if flag.val = 0 then raw₀ else raw₁))
    (hne : ∀ flag : Fin 2, (if flag.val = 0 then raw₀ else raw₁) ≠ [])
    (hquery : ∀ flag : Fin 2, ∀ x y, x ≤ 2 ^ b → y ≤ 2 ^ b →
      CircuitFormat.evalOutput (lowBits (b + 1) x ++ lowBits (b + 1) y)
        (if flag.val = 0 then raw₀ else raw₁)
        (arity b + (if flag.val = 0 then raw₀ else raw₁).length - 1) =
          (encodeGridColor (color x y)).getD flag.val false) :
    let x := GameTheory.Math.binaryPrefix b qx +
      if corner.val = 1 ∨ corner.val = 2 then 1 else 0
    let y := GameTheory.Math.binaryPrefix b qy +
      if corner.val = 1 ∨ corner.val = 3 then 1 else 0
    |(K : ℚ) * value c (sampleRef b raw₀.length raw₁.length t
      (colorGate b raw₀.length raw₁.length corner flag +
        ((if flag.val = 0 then raw₀ else raw₁).length - 1))) -
      (if (encodeGridColor (color x y)).getD flag.val false then 1 else 0)| ≤ 2 * ε := by
  have hcornerQuery := cornerVertex_eval color b
    (if flag.val = 0 then raw₀ else raw₁) flag
    (hraw flag) (hne flag) (hquery flag) qx qy corner
  let queryBit := (encodeGridColor (color
    (GameTheory.Math.binaryPrefix b qx + if corner.val = 1 ∨ corner.val = 2 then 1 else 0)
    (GameTheory.Math.binaryPrefix b qy + if corner.val = 1 ∨ corner.val = 3 then 1 else 0))).getD
      flag.val false
  have hbit : CircuitFormat.evalOutput (cornerVertex b qx qy corner)
      (if flag.val = 0 then raw₀ else raw₁)
      (arity b + (if flag.val = 0 then raw₀ else raw₁).length - 1) =
      queryBit := by
    simpa only [queryBit] using hcornerQuery
  refine colorOutput_error b raw₀ raw₁ H M c hc hM hg hscale ε hε hδ
    t corner qx qy ?_ flag queryBit (hraw flag) (hne flag) hbit
  intro axis j hj
  exact cornerBit_error b raw₀ raw₁ H M c hc hM hg hscale ε (by linarith) hδ
    t axis (if axis.val = 0 then qx else qy) hone hzero (hdigit axis) corner j hj

end Concrete


end GameTheory.Complexity.Backend.BrouwerNashColor
