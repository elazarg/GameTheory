import GameTheory.Finite.BimatrixArithmeticGate
import GameTheory.Finite.BimatrixBooleanGate
import GameTheory.Math.BinaryGridClearance
import GameTheory.Math.ClippedArithmetic

/-!
# Binary extraction by canonical comparator and affine game gates

A comparator reads the sign of a normalized residual minus one half. An affine block doubles
that residual and subtracts the extracted digit, retaining aggregated coefficients for aliases.
Every accepted certificate implements these steps with explicit matching-block errors. Clearance
from interior dyadic grid lines controls all stages without assuming a program generator.
-/

namespace GameTheory.Finite.BimatrixBinaryExtraction
open BimatrixCertificate BimatrixAffineGate BimatrixGateProgram BimatrixBlockGame
open scoped BigOperators
variable {k : ℕ}

/-- A comparator at one half of the normalized remainder. -/
def digitGate (r : Fin k) : Gate k :=
  ⟨fun a => 2 * (k : ℤ) * (if a = finProdFinEquiv (r, 1) then 1 else 0) - 1,
    .comparator⟩

/-- Aggregation retains both contributions when remainder and digit inputs coincide. -/
def remainderCoefficients (r digit : Fin k) (j : Fin k) : ℤ :=
  (if j = r then 4 * (k : ℤ) else 0) - (if j = digit then 2 * (k : ℤ) else 0)

/-- The next residual is an ordinary affine gate with no alternate semantics. -/
abbrev remainderGate (r digit : Fin k) : Gate k :=
  BimatrixArithmeticGate.gate (remainderCoefficients r digit) 0

private theorem digit_signal (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hd : 0 < c.rowDenominator) (hs : ∑ r, c.rowWeights r = c.rowDenominator)
    (r digit : Fin k) (hi : g digit = digitGate r) :
    (k : ℚ) * signal c (2 * (k : ℤ)) g digit = (k : ℚ) * value c r - 1 / 2 := by
  have hsum : (∑ a, (g digit).coefficients a * (c.rowWeights a : ℤ)) =
      2 * (k : ℤ) * c.rowWeights (finProdFinEquiv (r, 1)) - c.rowDenominator := by
    simp only [hi, digitGate, sub_mul, one_mul, mul_assoc,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [ite_mul, ← Nat.cast_sum, hs]
  unfold signal value
  rw [hsum]
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hdq : (c.rowDenominator : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  push_cast
  field_simp

/-- A separated exact threshold forces the actual digit block to its matching endpoint. -/
theorem digit_value (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (r digit : Fin k)
    (hi : g digit = digitGate r) (x E : ℚ)
    (herr : |(k : ℚ) * value c r - x| ≤ E) (hmargin : E < |x - 1 / 2|) :
    value c digit = if GameTheory.Math.binaryThreshold x then
      blockMass c.rowWeights c.rowDenominator digit else 0 := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have he := (all_gate_equations H (2 * (k : ℤ)) M g c hc hC hM hg hscale digit).2
    (by simp [hi, digitGate])
  have hsig := digit_signal hk g c hc.1 hc.2.2.1 r digit hi
  have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
  rw [abs_le] at herr
  simp only [GameTheory.Math.binaryThreshold, decide_eq_true_eq]
  split_ifs with hx
  · rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hmargin
    apply he.1
    have hp : 0 < (k : ℚ) * signal c (2 * (k : ℤ)) g digit := by linarith [herr.1]
    exact (mul_pos_iff_of_pos_left hkq).mp hp
  · rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)] at hmargin
    apply he.2
    have hp : (k : ℚ) * signal c (2 * (k : ℤ)) g digit < 0 := by linarith [herr.2]
    nlinarith

/-- The actual normalized digit has only the matching-block error. -/
theorem digit_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (r digit : Fin k)
    (hi : g digit = digitGate r) (x E : ℚ)
    (herr : |(k : ℚ) * value c r - x| ≤ E) (hmargin : E < |x - 1 / 2|) :
    |(k : ℚ) * value c digit - (if GameTheory.Math.binaryThreshold x then 1 else 0)| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  apply BimatrixBooleanGate.normalized_output_error H M hk g c hc hM hg hscale digit
  exact digit_value H M hk g c hc hM hg hscale r digit hi x E herr hmargin

private theorem remainder_signal (hk : 0 < k)
    (c : BimatrixCertificate (k * 2) (k * 2)) (r digit : Fin k) :
    (∑ j, ((remainderCoefficients r digit j : ℤ) : ℚ) / ((2 * (k : ℤ) : ℤ) : ℚ) *
      ((k : ℚ) * value c j)) + (k : ℚ) * (0 : ℤ) / ((2 * (k : ℤ) : ℤ) : ℚ) =
      2 * ((k : ℚ) * value c r) - (k : ℚ) * value c digit := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [remainderCoefficients, sub_div, sub_mul, Finset.sum_sub_distrib,
    ite_div, ite_mul, hkq]
  field_simp
  norm_num

/-- The actual affine block approximates the clipped recurrence on its actual inputs. -/
theorem remainder_gate_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (r digit out : Fin k)
    (hi : g out = remainderGate r digit) :
    |(k : ℚ) * value c out -
      max 0 (min 1 (2 * ((k : ℚ) * value c r) - (k : ℚ) * value c digit))| ≤
      (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) := by
  have hC : 0 < 2 * (k : ℤ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hk
  have h := BimatrixArithmeticGate.normalized_value_error H (2 * (k : ℤ)) M
    (remainderCoefficients r digit) 0 g c hc hC hM hg hscale out hi
  rw [remainder_signal hk c r digit] at h
  exact h

/-- Comparator and affine errors add twice the game error to the doubled input error. -/
theorem nextRemainder_error (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (r digit out : Fin k)
    (hi : g digit = digitGate r) (ho : g out = remainderGate r digit) (x E : ℚ)
    (herr : |(k : ℚ) * value c r - x| ≤ E) (hmargin : E < |x - 1 / 2|) :
    |(k : ℚ) * value c out -
      max 0 (min 1 (2 * x - if GameTheory.Math.binaryThreshold x then 1 else 0))| ≤
      2 * ((k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H)) + 2 * E := by
  have hd := digit_error H M hk g c hc hM hg hscale r digit hi x E herr hmargin
  have ha := remainder_gate_error H M hk g c hc hM hg hscale r digit out ho
  have hcl := GameTheory.Math.unitClamp_nonexpansive
    (2 * ((k : ℚ) * value c r) - (k : ℚ) * value c digit)
    (2 * x - if GameTheory.Math.binaryThreshold x then 1 else 0)
  have he : (2 * ((k : ℚ) * value c r) - (k : ℚ) * value c digit) -
      (2 * x - if GameTheory.Math.binaryThreshold x then 1 else 0) =
      2 * ((k : ℚ) * value c r - x) -
        ((k : ℚ) * value c digit - if GameTheory.Math.binaryThreshold x then 1 else 0) := by
    ring
  rw [he] at hcl
  have hab := abs_sub_le (2 * ((k : ℚ) * value c r - x)) (0 : ℚ)
    ((k : ℚ) * value c digit - if GameTheory.Math.binaryThreshold x then 1 else 0)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul,
    abs_of_pos (by norm_num : (0 : ℚ) < 2)] at hab
  have ht := abs_sub_le ((k : ℚ) * value c out)
    (max 0 (min 1 (2 * ((k : ℚ) * value c r) - (k : ℚ) * value c digit)))
    (max 0 (min 1 (2 * x - if GameTheory.Math.binaryThreshold x then 1 else 0)))
  linarith

/-- Every separated stage of an actual program satisfies the geometric extraction bound. -/
theorem trajectory_errors (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (r digits : ℕ → Fin k) (b : ℕ) (q ε δ : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hdigit : ∀ j < b, g (digits j) = digitGate (r j))
    (hnext : ∀ j < b, g (r (j + 1)) = remainderGate (r j) (digits j))
    (hinit : |(k : ℚ) * value c (r 0) - q| ≤ ε)
    (hmargin : ∀ j < b, (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ) <
      |GameTheory.Math.binaryRemainder j q - 1 / 2|) :
    (∀ j ≤ b, |(k : ℚ) * value c (r j) - GameTheory.Math.binaryRemainder j q| ≤
      (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ)) ∧
    (∀ j < b, |(k : ℚ) * value c (digits j) -
      (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j q) then 1 else 0)|
      ≤ δ) := by
  have he : ∀ j ≤ b,
      |(k : ℚ) * value c (r j) - GameTheory.Math.binaryRemainder j q| ≤
        (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ) := by
    intro j hj
    induction j with
    | zero => simpa [GameTheory.Math.binaryRemainder] using hinit
    | succ j ih =>
      have hjb : j < b := by omega
      have hi := ih (by omega)
      have hs := nextRemainder_error H M hk g c hc hM hg hscale
        (r j) (digits j) (r (j + 1)) (hdigit j hjb) (hnext j hjb)
        (GameTheory.Math.binaryRemainder j q)
        ((2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ)) hi (hmargin j hjb)
      have hr := GameTheory.Math.binaryRemainder_bounds hq0 hq1 (j + 1)
      change |(k : ℚ) * value c (r (j + 1)) -
        max 0 (min 1 (GameTheory.Math.binaryRemainder (j + 1) q))| ≤ _ at hs
      rw [GameTheory.Math.unitClamp_eq_self hr.1 hr.2] at hs
      calc
        _ ≤ 2 * ((k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H)) +
            2 * ((2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ)) := hs
        _ ≤ 2 * δ + 2 * ((2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ)) := by
          linarith only [hδ]
        _ = _ := by rw [pow_succ]; ring
  refine ⟨he, ?_⟩
  intro j hj
  exact (digit_error H M hk g c hc hM hg hscale (r j) (digits j) (hdigit j hj)
    (GameTheory.Math.binaryRemainder j q)
    ((2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ))
    (he j (by omega)) (hmargin j hj)).trans hδ

/-- Interior dyadic-grid clearance discharges all exact threshold-margin obligations. -/
theorem trajectory_errors_of_grid_clearance (H M : ℤ) (hk : 0 < k)
    (g : Fin k → Gate k) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ i a, |(g i).coefficients a| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H)
    (r digits : ℕ → Fin k) (b : ℕ) (q ε δ β : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ0 : 0 ≤ δ)
    (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ δ)
    (hdigit : ∀ j < b, g (digits j) = digitGate (r j))
    (hnext : ∀ j < b, g (r (j + 1)) = remainderGate (r j) (digits j))
    (hinit : |(k : ℚ) * value c (r 0) - q| ≤ ε) (hbudget : ε + 2 * δ ≤ β)
    (hgrid : ∀ l : ℕ, 0 < l → l < 2 ^ b → β < |q - (l : ℚ) / (2 : ℚ) ^ b|) :
    (∀ j ≤ b, |(k : ℚ) * value c (r j) - GameTheory.Math.binaryRemainder j q| ≤
      (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ)) ∧
    (∀ j < b, |(k : ℚ) * value c (digits j) -
      (if GameTheory.Math.binaryThreshold (GameTheory.Math.binaryRemainder j q) then 1 else 0)|
      ≤ δ) := by
  apply trajectory_errors H M hk g c hc hM hg hscale r digits b q ε δ
    hq0 hq1 hδ hdigit hnext hinit
  intro j hj
  have hm := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) j)
  have he : (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * (2 * δ) ≤ (2 : ℚ) ^ j * β := by
    nlinarith only [hm, hδ0]
  exact he.trans_lt (GameTheory.Math.binaryRemainder_grid_clearance b q β hgrid j hj)

end GameTheory.Finite.BimatrixBinaryExtraction
