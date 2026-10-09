import GameTheory.Finite.BimatrixAffineGate
import Mathlib.Algebra.Order.Group.MinMax

/-! A single paired-action game implements both affine and comparator gates.
Each output occupies its own row block. Signed coefficients are split into
nonnegative signals, and comparator gates add their output as affine feedback.
The canonical affine payoff factory therefore enforces every gate simultaneously. -/
namespace GameTheory.Finite.BimatrixGateProgram
open BimatrixCertificate BimatrixBlockGame
open scoped BigOperators

/-- The equation enforced by one paired output block. -/
inductive GateKind where
  | affine
  | comparator
  deriving DecidableEq

/-- A gate reads aggregated signed coefficients of actual row actions. -/
structure Gate (k : ℕ) where
  /-- Aggregate coefficient of each action, including repeated or aliased inputs. -/
  coefficients : Fin (k * 2) → ℤ
  /-- Affine saturation or strict-sign comparison. -/
  kind : GateKind

variable {k : ℕ}

/-- Positive coefficients include output feedback exactly for comparator gates. -/
def positiveCoefficients (C : ℤ) (g : Fin k → Gate k) (i : Fin k)
    (r : Fin (k * 2)) : ℤ :=
  max ((g i).coefficients r) 0 +
    if (g i).kind = .comparator ∧ r = finProdFinEquiv (i, 1) then C else 0

/-- The negative part of each signed input coefficient. -/
def negativeCoefficients (g : Fin k → Gate k) (i : Fin k) (r : Fin (k * 2)) : ℤ :=
  max (-((g i).coefficients r)) 0

/-- All gate signals share the canonical affine column payoff factory. -/
def columnPayoff (H C : ℤ) (g : Fin k → Gate k) : Fin (k * 2) → Fin (k * 2) → ℤ :=
  BimatrixAffineGate.columnPayoff H C (positiveCoefficients C g) (negativeCoefficients g)

/-- The signed input signal evaluated against normalized row probabilities. -/
def signal (c : BimatrixCertificate (k * 2) (k * 2)) (C : ℤ)
    (g : Fin k → Gate k) (i : Fin k) : ℚ :=
  ((∑ r, (g i).coefficients r * (c.rowWeights r : ℤ) : ℤ) : ℚ) /
    ((C : ℚ) * c.rowDenominator)

/-- Splitting a signed coefficient preserves its value and explicit comparator feedback. -/
theorem coefficients_sub (C : ℤ) (g : Fin k → Gate k) (i : Fin k) (r : Fin (k * 2)) :
    positiveCoefficients C g i r - negativeCoefficients g i r =
      (g i).coefficients r +
        if (g i).kind = .comparator ∧ r = finProdFinEquiv (i, 1) then C else 0 := by
  unfold positiveCoefficients negativeCoefficients
  rw [add_sub_right_comm, max_zero_sub_max_neg_zero_eq_self]

/-- Affine blocks use their signed input signal directly. -/
theorem target_affine (c : BimatrixCertificate (k * 2) (k * 2)) (C : ℤ)
    (g : Fin k → Gate k) (i : Fin k) (hi : (g i).kind = .affine) :
    BimatrixAffineGate.target c C (positiveCoefficients C g) (negativeCoefficients g) i =
      signal c C g i := by
  simp [BimatrixAffineGate.target, signal, coefficients_sub, hi]

/-- Comparator blocks use their signed input signal plus their current output. -/
theorem target_comparator (c : BimatrixCertificate (k * 2) (k * 2)) (C : ℤ)
    (hC : 0 < C) (g : Fin k → Gate k) (i : Fin k) (hi : (g i).kind = .comparator) :
    BimatrixAffineGate.target c C (positiveCoefficients C g) (negativeCoefficients g) i =
      signal c C g i + BimatrixAffineGate.value c i := by
  simp only [BimatrixAffineGate.target, coefficients_sub, hi, true_and, add_mul,
    Finset.sum_add_distrib]
  have hsum : (∑ r, (if r = finProdFinEquiv (i, 1) then C else 0) *
      (c.rowWeights r : ℤ)) = C * (c.rowWeights (finProdFinEquiv (i, 1)) : ℤ) := by
    simp [ite_mul]
  rw [hsum]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, add_div,
    signal, BimatrixAffineGate.value]
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  congr 1
  exact mul_div_mul_left _ _ hCq

private theorem clamp_self_add_endpoints (X x t : ℚ) (hX : 0 ≤ X)
    (he : x = max 0 (min X (x + t))) :
    (0 < t → x = X) ∧ (t < 0 → x = 0) := by
  have hx0 : 0 ≤ x := by rw [he]; exact le_max_left _ _
  have hxX : x ≤ X := by rw [he]; exact max_le hX (min_le_left _ _)
  constructor
  · intro ht
    by_contra hne
    have hlt : x < min X (x + t) := lt_min (lt_of_le_of_ne hxX hne) (by linarith)
    have hle : min X (x + t) ≤ x :=
      (le_max_right 0 (min X (x + t))).trans_eq he.symm
    exact (not_lt_of_ge hle) hlt
  · intro ht
    by_contra hne
    have hx : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
    have hlt : max 0 (min X (x + t)) < x := max_lt hx
      (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    exact (not_lt_of_ge he.le) hlt

/-- A common coefficient bound covers positive inputs and comparator feedback. -/
theorem positiveCoefficients_bounds (C M : ℤ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (g : Fin k → Gate k) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (i : Fin k) (r : Fin (k * 2)) :
    0 ≤ positiveCoefficients C g i r ∧ positiveCoefficients C g i r ≤ M + C := by
  have hq := abs_le.mp (hg i r)
  unfold positiveCoefficients
  have hm : max ((g i).coefficients r) 0 ≤ M := max_le hq.2 hM
  have hp : 0 ≤ max ((g i).coefficients r) 0 := le_max_right _ _
  split_ifs <;> constructor <;> linarith

/-- Negative inputs and the affine output penalty share the same coefficient cap. -/
theorem negativeCoefficients_bounds (C M : ℤ) (hM : 0 ≤ M)
    (g : Fin k → Gate k) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (i : Fin k) (r : Fin (k * 2)) :
    0 ≤ negativeCoefficients g i r ∧ negativeCoefficients g i r + C ≤ M + C := by
  have hq := abs_le.mp (hg i r)
  unfold negativeCoefficients
  have hm : max (-((g i).coefficients r)) 0 ≤ M := max_le (by linarith) hM
  exact ⟨le_max_right _ _, by linarith⟩

/-- A dominant matching baseline enforces every gate equation in every valid certificate. -/
theorem all_gate_equations (H C M : ℤ) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H C) (columnPayoff H C g))
    (hC : 0 < C) (hM : 0 ≤ M) (hg : ∀ i r, |(g i).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + C) < H) :
    ∀ i, ((g i).kind = .affine →
      BimatrixAffineGate.value c i = max 0
        (min (blockMass c.rowWeights c.rowDenominator i) (signal c C g i))) ∧
      ((g i).kind = .comparator →
        (0 < signal c C g i →
          BimatrixAffineGate.value c i = blockMass c.rowWeights c.rowDenominator i) ∧
        (signal c C g i < 0 → BimatrixAffineGate.value c i = 0)) := by
  have h := BimatrixAffineGate.all_values_eq_clamp H C (M + C)
    (positiveCoefficients C g) (negativeCoefficients g) c hc hC (by linarith)
    (positiveCoefficients_bounds C M hC.le hM g hg)
    (negativeCoefficients_bounds C M hM g hg) hscale
  intro i
  constructor
  · intro hi
    have he := h i
    rw [target_affine c C g i hi] at he
    exact he
  · intro hi
    have he := h i
    rw [target_comparator c C hC g i hi, add_comm] at he
    have hmass : 0 ≤ blockMass c.rowWeights c.rowDenominator i :=
      Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact clamp_self_add_endpoints _ _ _ hmass he
end GameTheory.Finite.BimatrixGateProgram
