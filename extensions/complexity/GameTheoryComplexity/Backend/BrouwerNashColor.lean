import GameTheoryComplexity.Backend.BrouwerNashProgram
import GameTheoryComplexity.Backend.BimatrixCoordinateColor
import GameTheoryComplexity.Backend.BimatrixRawCircuit
import Complexitylib.Mathlib.NatBits
import GameTheory.Math.BinaryExtraction
import GameTheoryComplexity.Backend.BimatrixRawGate
import GameTheory.Math.ClippedArithmetic
import GameTheory.Finite.BimatrixArithmeticGate
/-! Exact prefix digits drive Boolean ripple increments and all four extended corner inputs.
The canonical program copies those bits into its relocated raw color circuits; every valid
certificate then approximates each evaluated color flag without accumulating circuit depth. -/
namespace GameTheory.Complexity.Backend.BrouwerNashColor
private def rippleBits : List Bool → Bool → List Bool
  | [], carry => [carry]
  | bit :: bits, carry => (bit.xor carry) :: rippleBits bits (bit && carry)
private theorem rippleBits_length (bits : List Bool) (carry : Bool) :
    (rippleBits bits carry).length = bits.length + 1 := by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih => simp only [rippleBits, List.length_cons, ih]
private theorem rippleBits_value (bits : List Bool) (carry : Bool) :
    Nat.fromBitsLE (rippleBits bits carry) = Nat.fromBitsLE bits + if carry then 1 else 0 := by
  induction bits generalizing carry with
  | nil => cases carry <;> rfl
  | cons bit bits ih =>
    simp only [rippleBits, Nat.fromBitsLE_cons, ih]
    cases bit <;> cases carry <;> simp <;> omega
private theorem rippleBits_eq (bits : List Bool) (carry : Bool) :
    rippleBits bits carry = Nat.toBitsLE (bits.length + 1)
      (Nat.fromBitsLE bits + if carry then 1 else 0) := by
  have h := Nat.toBitsLE_fromBitsLE (rippleBits bits carry)
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
    Nat.fromBitsLE (prefixBits q b) = GameTheory.Math.binaryPrefix b q := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [prefixBits, Nat.fromBitsLE_cons, ih, GameTheory.Math.binaryPrefix]
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
    prefixBits q b ++ [false] = Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b q) := by
  have h := Nat.toBitsLE_fromBitsLE (prefixBits q b ++ [false])
  have hn : Nat.fromBitsLE (prefixBits q b ++ [false]) =
      GameTheory.Math.binaryPrefix b q := by
    simpa only [Nat.fromBitsLE, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, Nat.fromBits,
      Bool.false_eq_true, ite_false, zero_mul, zero_add] using prefixBits_value q b
  rw [List.length_append, List.length_singleton, prefixBits_length, hn] at h
  exact h.symm

section Game
open _root_.Complexity.CircuitCode
open GameTheory.Finite GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixGateProgram
variable {k : ℕ} (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
  (c : BimatrixCertificate (k * 2) (k * 2))
  (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
  (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
  (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
  (ε : ℚ) (hε : ε < 1 / 4)
  (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)

include hk hc hM hg hscale hε hδ in
private theorem ripple_step (input carry : Fin k) (out : Fin 4 → Fin k)
    (h0 : g (out 0) = BimatrixRawGate.gate
      ⟨.and, input.val, carry.val, false, true⟩ ⟨input.isLt, carry.isLt⟩)
    (h1 : g (out 1) = BimatrixRawGate.gate
      ⟨.and, input.val, carry.val, true, false⟩ ⟨input.isLt, carry.isLt⟩)
    (h2 : g (out 2) = BimatrixRawGate.gate
      ⟨.or, (out 0).val, (out 1).val, false, false⟩ ⟨(out 0).isLt, (out 1).isLt⟩)
    (h3 : g (out 3) = BimatrixRawGate.gate
      ⟨.and, input.val, carry.val, false, false⟩ ⟨input.isLt, carry.isLt⟩)
    (bit cb : Bool)
    (hin : |(k : ℚ) * value c input - (if bit then 1 else 0)| ≤ ε)
    (hcarry : |(k : ℚ) * value c carry - (if cb then 1 else 0)| ≤ ε) :
    (|(k : ℚ) * value c (out 2) - (if bit.xor cb then 1 else 0)| ≤ ε) ∧
    (|(k : ℚ) * value c (out 3) - (if bit && cb then 1 else 0)| ≤ ε) := by
  have ha := (BimatrixRawGate.gate_output_error H M
    ⟨.and, input.val, carry.val, false, true⟩ ⟨input.isLt, carry.isLt⟩
    hk g c hc hM hg hscale (out 0) h0 bit cb ε hin hcarry hε).trans hδ
  have hb := (BimatrixRawGate.gate_output_error H M
    ⟨.and, input.val, carry.val, true, false⟩ ⟨input.isLt, carry.isLt⟩
    hk g c hc hM hg hscale (out 1) h1 bit cb ε hin hcarry hε).trans hδ
  have hx := (BimatrixRawGate.gate_output_error H M
    ⟨.or, (out 0).val, (out 1).val, false, false⟩ ⟨(out 0).isLt, (out 1).isLt⟩
    hk g c hc hM hg hscale (out 2) h2 (bit && !cb) (!bit && cb) ε
    (by simpa only [RawGate.eval, Bool.false_xor, Bool.true_xor] using ha)
    (by simpa only [RawGate.eval, Bool.false_xor, Bool.true_xor] using hb) hε).trans hδ
  have hcar := (BimatrixRawGate.gate_output_error H M
    ⟨.and, input.val, carry.val, false, false⟩ ⟨input.isLt, carry.isLt⟩
    hk g c hc hM hg hscale (out 3) h3 bit cb ε hin hcarry hε).trans hδ
  constructor
  · cases bit <;> cases cb <;> simpa only [RawGate.eval, Bool.false_xor, Bool.false_and,
      Bool.true_xor, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_or,
      Bool.true_or, Bool.xor_false, Bool.xor_true] using hx
  · simpa only [RawGate.eval, Bool.false_xor] using hcar
include hk hc hM hg hscale hε hδ in
private theorem ripple_chain (bits : List Bool) (input : ℕ → Fin k)
    (out : ℕ → Fin 4 → Fin k) (one : Fin k)
    (hone : |(k : ℚ) * value c one - 1| ≤ ε)
    (hin : ∀ j < bits.length,
      |(k : ℚ) * value c (input j) - (if bits[j]?.getD false then 1 else 0)| ≤ ε)
    (h0 : ∀ j < bits.length, g (out j 0) = BimatrixRawGate.gate
      ⟨.and, (input j).val, (if j = 0 then one else out (j - 1) 3).val, false, true⟩
        ⟨(input j).isLt, (if j = 0 then one else out (j - 1) 3).isLt⟩)
    (h1 : ∀ j < bits.length, g (out j 1) = BimatrixRawGate.gate
      ⟨.and, (input j).val, (if j = 0 then one else out (j - 1) 3).val, true, false⟩
        ⟨(input j).isLt, (if j = 0 then one else out (j - 1) 3).isLt⟩)
    (h2 : ∀ j < bits.length, g (out j 2) = BimatrixRawGate.gate
      ⟨.or, (out j 0).val, (out j 1).val, false, false⟩ ⟨(out j 0).isLt, (out j 1).isLt⟩)
    (h3 : ∀ j < bits.length, g (out j 3) = BimatrixRawGate.gate
      ⟨.and, (input j).val, (if j = 0 then one else out (j - 1) 3).val, false, false⟩
        ⟨(input j).isLt, (if j = 0 then one else out (j - 1) 3).isLt⟩) :
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
open _root_.Complexity.CircuitCode
open BrouwerNashLayout BrouwerNashProgram
private theorem program_increment_raw (b : ℕ) (raw₀ raw₁ : RawCircuit) (t : Fin 41)
    (axis : Fin 2) (j : ℕ) (hj : j < b) (stage : Fin 4) :
    let input := sampleRef b raw₀.length raw₁.length t (primaryBit b axis j)
    let carry := if j = 0 then slot b raw₀.length raw₁.length one
      else sampleRef b raw₀.length raw₁.length t (increment b axis (j - 1) 3)
    let out := fun stage => sampleRef b raw₀.length raw₁.length t (increment b axis j stage)
    program b raw₀ raw₁ (out stage) = guardedRaw (match stage.val with
      | 0 => ⟨.and, input.val, carry.val, false, true⟩
      | 1 => ⟨.and, input.val, carry.val, true, false⟩
      | 2 => ⟨.or, (out 0).val, (out 1).val, false, false⟩
      | _ => ⟨.and, input.val, carry.val, false, false⟩) := by
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
variable (b : ℕ) (raw₀ raw₁ : RawCircuit)
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
      (if (Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b q + 1))[j]?.getD false
        then 1 else 0)| ≤ ε := by
  let input := fun j => sampleRef b raw₀.length raw₁.length t (primaryBit b axis j)
  let out := fun j stage => sampleRef b raw₀.length raw₁.length t (increment b axis j stage)
  let oneSlot := slot b raw₀.length raw₁.length one
  have hstep (j : ℕ) (hj : j < (prefixBits q b).length) (stage : Fin 4) :
      programG (out j stage) = guardedRaw (match stage.val with
        | 0 => ⟨.and, (input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val,
            false, true⟩
        | 1 => ⟨.and, (input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val,
            true, false⟩
        | 2 => ⟨.or, (out j 0).val, (out j 1).val, false, false⟩
        | _ => ⟨.and, (input j).val, (if j = 0 then oneSlot else out (j - 1) 3).val,
            false, false⟩) :=
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
      exact guardedRaw_eq _ ⟨(input j).isLt,
        (if j = 0 then oneSlot else out (j - 1) 3).isLt⟩)
    (fun j hj => by
      rw [hstep j hj 1]
      exact guardedRaw_eq _ ⟨(input j).isLt,
        (if j = 0 then oneSlot else out (j - 1) 3).isLt⟩)
    (fun j hj => by
      rw [hstep j hj 2]
      exact guardedRaw_eq _ ⟨(out j 0).isLt, (out j 1).isLt⟩)
    (fun j hj => by
      rw [hstep j hj 3]
      exact guardedRaw_eq _ ⟨(input j).isLt,
        (if j = 0 then oneSlot else out (j - 1) 3).isLt⟩)
  have he : rippleBits (prefixBits q b) true =
      Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b q + 1) := by
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
      (if (Nat.toBitsLE (b + 1)
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
  Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b qx +
    if corner.val = 1 ∨ corner.val = 2 then 1 else 0) ++
  Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b qy +
    if corner.val = 1 ∨ corner.val = 3 then 1 else 0)

private theorem cornerVertex_length (qx qy : ℚ) (corner : Fin 4) :
    (cornerVertex b qx qy corner).length = arity b := by
  simp only [cornerVertex, List.length_append, Nat.length_toBitsLE, arity]
  omega

private theorem corner_input_error (c : GameTheory.Finite.BimatrixCertificate (K * 2) (K * 2))
    (t : Fin 41) (corner : Fin 4) (qx qy ε : ℚ)
    (hcorner : ∀ axis : Fin 2, ∀ j ≤ b,
      |(K : ℚ) * GameTheory.Finite.BimatrixAffineGate.value c
        (cornerBit b raw₀.length raw₁.length t corner axis j) -
        (if (Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b
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
    rw [List.getElem?_append_left (by rw [Nat.length_toBitsLE]; exact hlow)]
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
    rw [List.getElem?_append_right (by rw [Nat.length_toBitsLE]; omega), Nat.length_toBitsLE]
    exact h

private theorem program_raw₀ (t : Fin 41) (corner : Fin 4) (j : Fin raw₀.length)
    (href : RawGate.WellFormedAt
      ((raw₀.get j).shift (sampleBase b raw₀.length raw₁.length t +
        colorInput b raw₀.length raw₁.length corner 0)) K) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner 0 + arity b + j.val)) =
      BimatrixRawGate.gate ((raw₀.get j).shift
        (sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner 0))
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
    (href : RawGate.WellFormedAt
      ((raw₁.get j).shift (sampleBase b raw₀.length raw₁.length t +
        colorInput b raw₀.length raw₁.length corner 1)) K) :
    programG (sampleRef b raw₀.length raw₁.length t
      (colorInput b raw₀.length raw₁.length corner 1 + arity b + j.val)) =
      BimatrixRawGate.gate ((raw₁.get j).shift
        (sampleBase b raw₀.length raw₁.length t + colorInput b raw₀.length raw₁.length corner 1))
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
        (if (Nat.toBitsLE (b + 1) (GameTheory.Math.binaryPrefix b
          (if axis.val = 0 then qx else qy) +
          if (if axis.val = 0 then corner.val = 1 ∨ corner.val = 2
            else corner.val = 1 ∨ corner.val = 3) then 1 else 0))[j]?.getD false
          then 1 else 0)| ≤ ε)
    (flag : Fin 2) (bit : Bool)
    (hraw : (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : (if flag.val = 0 then raw₀ else raw₁).eval? (cornerVertex b qx qy corner) =
      some bit) :
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
  have he0 : 0 ≤ ε := by
    have hh := hcorner 0 0 (Nat.zero_le b)
    exact (abs_nonneg _).trans hh
  have hplace : ∀ j : Fin raw.length, ∀ href : ((raw.get j).shift offset).WellFormedAt K,
      programG ⟨offset + (cornerVertex b qx qy corner).length + j.val, by omega⟩ =
        BimatrixRawGate.gate ((raw.get j).shift offset) href := by
    intro j href
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
    · exact program_raw₀ b raw₀ raw₁ t corner j href
    · exact program_raw₁ b raw₀ raw₁ t corner j href
  have hinput : ∀ j : Fin K, ∀ hj0 : offset ≤ j.val,
      ∀ hj : j.val < offset + (cornerVertex b qx qy corner).length,
      |(K : ℚ) * value c j -
        (if (cornerVertex b qx qy corner)[j.val - offset] then 1 else 0)| ≤ 2 * ε := by
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
    rw [List.getElem?_eq_getElem hiList, Option.getD_some] at hcopy
    exact hcopy
  obtain ⟨outbit, heval, hlast, herr⟩ := BimatrixRawCircuit.eval_correct_at H M
    (dimension_pos _ _ _) programG c hc hM hg hscale (2 * ε) hε (by linarith) offset raw
    (cornerVertex b qx qy corner) (by rwa [cornerVertex_length]) hsize hplace hinput
  have hbit : outbit = bit := Option.some.inj (heval.symm.trans hquery)
  subst outbit
  have hlen : 0 < raw.length := List.length_pos_iff.mpr hraw.1
  have hlocal : colorGate b raw₀.length raw₁.length corner flag + (raw.length - 1) <
      sampleWidth b raw₀.length raw₁.length := by dsimp only [colorGate, raw] at *; omega
  have ha := sample_lt_dimension b raw₀.length raw₁.length t _ hlocal
  have heq : (⟨offset + ((cornerVertex b qx qy corner).length + raw.length - 1), hlast⟩ :
      Fin K) = sampleRef b raw₀.length raw₁.length t
        (colorGate b raw₀.length raw₁.length corner flag + (raw.length - 1)) := by
    apply Fin.ext
    simp only [sampleRef, slot_val _ _ _ _ ha, cornerVertex_length]
    dsimp only [offset, colorGate]
    omega
  rw [heq] at herr
  exact herr

/-- Exact extracted digits discharge every input premise of concrete corner color evaluation. -/
theorem colorOutput_error_of_digits (H M : ℤ) (c : BimatrixCertificate (K * 2) (K * 2))
    (hc : c.Valid (rowPayoff H (2 * (K : ℤ))) (columnPayoff H (2 * (K : ℤ)) programG))
    (hM : 0 ≤ M) (hg : ∀ i r, |(programG i).coefficients r| ≤ M)
    (hscale : (K : ℤ) * (M + 2 * (K : ℤ)) < H) (ε : ℚ) (hε : 2 * ε < 1 / 4)
    (hδ : (K : ℚ) * (((M + 2 * (K : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (t : Fin 41) (corner : Fin 4) (qx qy : ℚ)
    (hone : |(K : ℚ) * value c (slot b raw₀.length raw₁.length one) - 1| ≤ ε)
    (hzero : |(K : ℚ) * value c (slot b raw₀.length raw₁.length zero)| ≤ ε)
    (hdigit : ∀ axis : Fin 2, ∀ j < b,
      |(K : ℚ) * value c (sampleRef b raw₀.length raw₁.length t (digit b axis j)) -
        (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j
          (if axis.val = 0 then qx else qy)) then 1 else 0)| ≤ ε)
    (flag : Fin 2) (bit : Bool)
    (hraw : (if flag.val = 0 then raw₀ else raw₁).WellFormed (arity b))
    (hquery : (if flag.val = 0 then raw₀ else raw₁).eval? (cornerVertex b qx qy corner) =
      some bit) :
    |(K : ℚ) * value c (sampleRef b raw₀.length raw₁.length t
      (colorGate b raw₀.length raw₁.length corner flag +
        ((if flag.val = 0 then raw₀ else raw₁).length - 1))) -
      (if bit then 1 else 0)| ≤ 2 * ε := by
  apply colorOutput_error b raw₀ raw₁ H M c hc hM hg hscale ε hε hδ
    t corner qx qy _ flag bit hraw hquery
  intro axis j hj
  exact cornerBit_error b raw₀ raw₁ H M c hc hM hg hscale ε (by linarith) hδ
    t axis (if axis.val = 0 then qx else qy) hone hzero (hdigit axis) corner j hj

end Concrete

open _root_.Complexity GameTheory.Math GameTheory.Math.Sperner in
/-- Compiled grid-color queries evaluate all four corners of the exact binary-selected cell. -/
theorem cornerVertex_eval (source : List Bool) (raw : _root_.Complexity.CircuitCode.RawCircuit)
    (flag : Fin 2)
    (hquery : ∀ x y, x ≤ 2 ^ (pairFst source).length → y ≤ 2 ^ (pairFst source).length →
      raw.eval? (Nat.toBitsLE ((pairFst source).length + 1) x ++
        Nat.toBitsLE ((pairFst source).length + 1) y) =
        some (bitOf (encodeGridColor (spernerColor source x y)) flag))
    (qx qy : ℚ) (corner : Fin 4) :
    raw.eval? (cornerVertex (pairFst source).length qx qy corner) =
      some (bitOf (encodeGridColor ((![
        spernerColor source (binaryPrefix (pairFst source).length qx)
          (binaryPrefix (pairFst source).length qy),
        spernerColor source (binaryPrefix (pairFst source).length qx + 1)
          (binaryPrefix (pairFst source).length qy + 1),
        spernerColor source (binaryPrefix (pairFst source).length qx + 1)
          (binaryPrefix (pairFst source).length qy),
        spernerColor source (binaryPrefix (pairFst source).length qx)
          (binaryPrefix (pairFst source).length qy + 1)] : Fin 4 → Fin 3) corner)) flag) := by
  have hx := binaryPrefix_lt (pairFst source).length qx
  have hy := binaryPrefix_lt (pairFst source).length qy
  have hcx : binaryPrefix (pairFst source).length qx +
      (if corner.val = 1 ∨ corner.val = 2 then 1 else 0) ≤ 2 ^ (pairFst source).length := by
    split_ifs <;> omega
  have hcy : binaryPrefix (pairFst source).length qy +
      (if corner.val = 1 ∨ corner.val = 3 then 1 else 0) ≤ 2 ^ (pairFst source).length := by
    split_ifs <;> omega
  rw [cornerVertex, hquery _ _ hcx hcy]
  fin_cases corner <;> rfl

end GameTheory.Complexity.Backend.BrouwerNashColor
