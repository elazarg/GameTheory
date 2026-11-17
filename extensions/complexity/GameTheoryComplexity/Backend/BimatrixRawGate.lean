module

public import GameTheoryComplexity.Backend.CircuitFormat
public import Mathlib.Data.List.GetD
public import GameTheory.Finite.BimatrixBooleanGate

@[expose] public section

/-! Raw circuit gates translate to comparator blocks with inline input negation.
Input references remain absolute, and aliased references retain both coefficient
contributions. No additional blocks are allocated for negation. -/
namespace GameTheory.Complexity.Backend.BimatrixRawGate
open Cslib.Circuits
open GameTheory.Finite GameTheory.Finite.BimatrixCertificate
open GameTheory.Finite.BimatrixBlockGame GameTheory.Finite.BimatrixAffineGate
open GameTheory.Finite.BimatrixGateProgram
open scoped BigOperators
variable {k : ℕ}

/-- Each argument of a checked binary gate refers to a game block. -/
theorem reference_lt (raw : CircuitFormat.signature.Op × List ℕ)
    (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw]) (i : Fin 2) :
    raw.2.getD i.val 0 < k := by
  have hlength : raw.2.length = 2 := href.1.1
  have hi : i.val < raw.2.length := by omega
  rw [List.getD_eq_getElem raw.2 0 hi]
  exact href.1.2 _ (List.getElem_mem _)

private def signedIndicator (a : Fin k) (neg : Bool) (r : Fin (k * 2)) : ℤ :=
  (if neg then -1 else 1) * (if r = finProdFinEquiv (a, 1) then 1 else 0)

/-- The doubled threshold distinguishes conjunction from disjunction. -/
def threshold (raw : CircuitFormat.signature.Op × List ℕ) : ℤ := if raw.1.1 then 3 else 1

/-- Signed indicators and constant offsets implement free input negation. -/
def coefficients (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw]) (r : Fin (k * 2)) : ℤ :=
  2 * (k : ℤ) *
    (((if raw.1.2.1 then -1 else 1) *
      (if r = finProdFinEquiv (⟨raw.2.getD 0 0, reference_lt raw href 0⟩, 1) then 1 else 0)) +
     ((if raw.1.2.2 then -1 else 1) *
      (if r = finProdFinEquiv (⟨raw.2.getD 1 0, reference_lt raw href 1⟩, 1) then 1 else 0))) +
    (if raw.1.2.1 then 2 else 0) + (if raw.1.2.2 then 2 else 0) - threshold raw

/-- One comparator block implements a raw gate, including both negation flags. -/
def gate (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw]) : Gate k :=
  ⟨coefficients raw href, .comparator⟩

/-- The normalized signal is the possibly negated input sum minus its threshold. -/
theorem signal_eq (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw])
    (c : BimatrixCertificate (k * 2) (k * 2)) (hk : 0 < k)
    (hd : 0 < c.rowDenominator) (hs : (∑ r, c.rowWeights r) = c.rowDenominator)
    (g : Fin k → Gate k) (i : Fin k) (hi : g i = gate raw href) :
    (k : ℚ) * signal c (2 * (k : ℤ)) g i =
      (if raw.1.2.1 then 1 - (k : ℚ) * value c ⟨raw.2.getD 0 0, reference_lt raw href 0⟩
        else (k : ℚ) * value c ⟨raw.2.getD 0 0, reference_lt raw href 0⟩) +
      (if raw.1.2.2 then 1 - (k : ℚ) * value c ⟨raw.2.getD 1 0, reference_lt raw href 1⟩
        else (k : ℚ) * value c ⟨raw.2.getD 1 0, reference_lt raw href 1⟩) - (threshold raw : ℚ) / 2 := by
  have hsum : (∑ r, (g i).coefficients r * (c.rowWeights r : ℤ)) =
      2 * (k : ℤ) * ((if raw.1.2.1 then -1 else 1) *
        (c.rowWeights (finProdFinEquiv (⟨raw.2.getD 0 0, reference_lt raw href 0⟩, 1)) : ℤ) +
        (if raw.1.2.2 then -1 else 1) *
        (c.rowWeights (finProdFinEquiv (⟨raw.2.getD 1 0, reference_lt raw href 1⟩, 1)) : ℤ)) +
      ((if raw.1.2.1 then 2 else 0) + (if raw.1.2.2 then 2 else 0) - threshold raw) *
        c.rowDenominator := by
    simp only [hi, gate, coefficients, sub_mul, add_mul, mul_assoc,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [ite_mul, ← Nat.cast_sum, hs]
    ring
  unfold signal value
  rw [hsum]
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdq : (c.rowDenominator : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  cases raw.1.2.1 <;> cases raw.1.2.2 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    push_cast <;> field_simp <;> ring

private theorem negated_error (neg bit : Bool) (x ε : ℚ)
    (hx : |x - (if bit then 1 else 0)| ≤ ε) :
    |(if neg then 1 - x else x) - (if neg.xor bit then 1 else 0)| ≤ ε := by
  cases neg <;> cases bit <;> simp only [Bool.false_xor, Bool.true_xor,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, sub_zero] at hx ⊢
  · exact hx
  · exact hx
  · simpa only [sub_sub_cancel_left, abs_neg] using hx
  · simpa only [abs_sub_comm] using hx

/-- Small input representation errors preserve the strict sign of the canonical gate result. -/
theorem sign_eval (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw])
    (c : BimatrixCertificate (k * 2) (k * 2)) (hk : 0 < k)
    (hd : 0 < c.rowDenominator) (hs : (∑ r, c.rowWeights r) = c.rowDenominator)
    (g : Fin k → Gate k) (i : Fin k) (hi : g i = gate raw href)
    (b₀ b₁ : Bool) (ε : ℚ)
    (h₀ : |(k : ℚ) * value c ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ - (if b₀ then 1 else 0)| ≤ ε)
    (h₁ : |(k : ℚ) * value c ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ - (if b₁ then 1 else 0)| ≤ ε)
    (hε : ε < 1 / 4) :
    (0 < signal c (2 * (k : ℤ)) g i ↔ CircuitFormat.opValue raw.1 b₀ b₁ = true) ∧
      (signal c (2 * (k : ℤ)) g i < 0 ↔ CircuitFormat.opValue raw.1 b₀ b₁ = false) := by
  have ha := negated_error raw.1.2.1 b₀ _ ε h₀
  have hb := negated_error raw.1.2.2 b₁ _ ε h₁
  have hn : (0 < (k : ℚ) * signal c (2 * (k : ℤ)) g i ↔ CircuitFormat.opValue raw.1 b₀ b₁ = true) ∧
      ((k : ℚ) * signal c (2 * (k : ℤ)) g i < 0 ↔ CircuitFormat.opValue raw.1 b₀ b₁ = false) := by
    rw [signal_eq raw href c hk hd hs g i hi]
    cases hop : raw.1.1
    · simpa only [threshold, hop, CircuitFormat.opValue, Bool.false_eq_true, ite_false,
        Int.cast_one] using
        GameTheory.Math.booleanThreshold_or (raw.1.2.1.xor b₀) (raw.1.2.2.xor b₁)
          _ _ ε ha hb hε
    · simpa only [threshold, hop, CircuitFormat.opValue, ite_true, Int.cast_ofNat] using
        GameTheory.Math.booleanThreshold_and (raw.1.2.1.xor b₀) (raw.1.2.2.xor b₁)
          _ _ ε ha hb hε
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hneg : (k : ℚ) * signal c (2 * (k : ℤ)) g i < 0 ↔
      signal c (2 * (k : ℤ)) g i < 0 := by
    constructor <;> intro hh <;> nlinarith
  simpa only [mul_pos_iff_of_pos_left hkq, hneg] using hn
/-- A linear coefficient bound covers all flags and aliased input references. -/
theorem coefficients_bound (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw]) (r : Fin (k * 2)) :
    |coefficients raw href r| ≤ 4 * (k : ℤ) + 3 := by
  have hterm (a : Fin k) (neg : Bool) : |signedIndicator a neg r| ≤ 1 := by
    unfold signedIndicator
    split_ifs <;> norm_num
  have hsum : |signedIndicator ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ raw.1.2.1 r +
      signedIndicator ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ raw.1.2.2 r| ≤ 2 :=
    (abs_add_le _ _).trans (by
      have ha := hterm ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ raw.1.2.1
      have hb := hterm ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ raw.1.2.2
      linarith)
  have hoff : |(if raw.1.2.1 then (2 : ℤ) else 0) +
      (if raw.1.2.2 then 2 else 0) - threshold raw| ≤ 3 := by
    cases h₀ : raw.1.2.1 <;> cases h₁ : raw.1.2.2 <;> cases hop : raw.1.1 <;>
      norm_num [threshold, hop, h₀, h₁]
  have hc : coefficients raw href r =
      2 * (k : ℤ) * (signedIndicator ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ raw.1.2.1 r +
        signedIndicator ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ raw.1.2.2 r) +
      ((if raw.1.2.1 then 2 else 0) + (if raw.1.2.2 then 2 else 0) - threshold raw) := by
    dsimp only [coefficients, signedIndicator]
    ring
  have hk : 0 ≤ 2 * (k : ℤ) := mul_nonneg (by decide) (Nat.cast_nonneg _)
  rw [hc]
  calc
    _ ≤ |2 * (k : ℤ) * (signedIndicator ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ raw.1.2.1 r +
        signedIndicator ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ raw.1.2.2 r)| +
        |(if raw.1.2.1 then 2 else 0) + (if raw.1.2.2 then 2 else 0) - threshold raw| :=
      abs_add_le _ _
    _ ≤ 2 * (k : ℤ) * 2 + 3 := by
      rw [abs_mul, abs_of_nonneg hk]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum hk) hoff
    _ = 4 * (k : ℤ) + 3 := by ring

/-- Every valid game certificate selects the endpoint prescribed by the raw gate evaluator. -/
theorem gate_value (H M : ℤ) (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw])
    (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i : Fin k) (hi : g i = gate raw href) (b₀ b₁ : Bool) (ε : ℚ)
    (h₀ : |(k : ℚ) * value c ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ - (if b₀ then 1 else 0)| ≤ ε)
    (h₁ : |(k : ℚ) * value c ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ - (if b₁ then 1 else 0)| ≤ ε)
    (hε : ε < 1 / 4) :
    value c i = if CircuitFormat.opValue raw.1 b₀ b₁ then blockMass c.rowWeights c.rowDenominator i else 0 := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have he := (all_gate_equations H (2 * (k : ℤ)) M g c hc hC hM hg hscale i).2
    (by simp [hi, gate])
  have hsign := sign_eval raw href c hk hc.1 hc.2.2.1 g i hi b₀ b₁ ε h₀ h₁ hε
  cases hbit : CircuitFormat.opValue raw.1 b₀ b₁
  · simp only [Bool.false_eq_true, ite_false]
    exact he.2 (hsign.2.mpr hbit)
  · simp only [ite_true]
    exact he.1 (hsign.1.mpr hbit)

/-- The raw gate output inherits only the common block normalization error. -/
theorem gate_output_error (H M : ℤ) (raw : CircuitFormat.signature.Op × List ℕ) (href : Program.IsCodeFrom CircuitFormat.signature k 0 [raw])
    (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (i : Fin k) (hi : g i = gate raw href) (b₀ b₁ : Bool) (ε : ℚ)
    (h₀ : |(k : ℚ) * value c ⟨raw.2.getD 0 0, reference_lt raw href 0⟩ - (if b₀ then 1 else 0)| ≤ ε)
    (h₁ : |(k : ℚ) * value c ⟨raw.2.getD 1 0, reference_lt raw href 1⟩ - (if b₁ then 1 else 0)| ≤ ε)
    (hε : ε < 1 / 4) :
    |(k : ℚ) * value c i - (if CircuitFormat.opValue raw.1 b₀ b₁ then 1 else 0)| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) :=
  GameTheory.Finite.BimatrixBooleanGate.normalized_output_error H M hk g c hc hM hg hscale
    i (CircuitFormat.opValue raw.1 b₀ b₁) (gate_value H M raw href hk g c hc hM hg hscale i hi b₀ b₁ ε h₀ h₁ hε)
end GameTheory.Complexity.Backend.BimatrixRawGate
