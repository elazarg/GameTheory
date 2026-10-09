import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Binary threshold extraction on the closed unit interval

Thresholding each residual at one half and subtracting its extracted bit gives an exact
binary prefix decomposition. The right endpoint is represented by all-one bits with residual
one, selecting the last cell rather than an out-of-range grid index. A strict threshold margin
also ensures that bounded perturbations preserve a bit.
-/

namespace GameTheory.Math

/-- The next most significant bit, assigning a threshold tie to one. -/
def binaryThreshold (x : ℚ) : Bool := decide ((1 : ℚ) / 2 ≤ x)

/-- The residual after repeated doubling and subtraction of the threshold bit. -/
def binaryRemainder : ℕ → ℚ → ℚ
  | 0, x => x
  | n + 1, x =>
      2 * binaryRemainder n x - if binaryThreshold (binaryRemainder n x) then 1 else 0

/-- The natural-number prefix read from most significant to least significant bit. -/
def binaryPrefix : ℕ → ℚ → ℕ
  | 0, _ => 0
  | n + 1, x =>
      2 * binaryPrefix n x + if binaryThreshold (binaryRemainder n x) then 1 else 0

/-- The prefix and residual reconstruct the scaled input exactly. -/
theorem binary_decomposition (n : ℕ) (x : ℚ) :
    (2 : ℚ) ^ n * x = (binaryPrefix n x : ℚ) + binaryRemainder n x := by
  induction n with
  | zero => simp [binaryPrefix, binaryRemainder]
  | succ n ih =>
    rw [pow_succ, binaryPrefix, binaryRemainder]
    cases h : binaryThreshold (binaryRemainder n x) <;> simp only [Bool.false_eq_true,
      ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] <;>
      nlinarith [ih]

theorem binaryRemainder_bounds {x : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ binaryRemainder n x ∧ binaryRemainder n x ≤ 1 := by
  induction n with
  | zero => exact ⟨hx, hx1⟩
  | succ n ih =>
    simp only [binaryRemainder, binaryThreshold, decide_eq_true_eq]
    split_ifs with h <;> constructor <;> linarith [ih.1, ih.2]

theorem binaryRemainder_lt_one {x : ℚ} (hx : x < 1) (n : ℕ) :
    binaryRemainder n x < 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    simp only [binaryRemainder, binaryThreshold, decide_eq_true_eq]
    split_ifs with h <;> linarith

theorem binaryPrefix_lt (n : ℕ) (x : ℚ) : binaryPrefix n x < 2 ^ n := by
  induction n with
  | zero => simp [binaryPrefix]
  | succ n ih =>
    rw [binaryPrefix, pow_succ]
    cases binaryThreshold (binaryRemainder n x) <;> simp <;> omega

theorem binaryRemainder_one (n : ℕ) : binaryRemainder n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => norm_num [binaryRemainder, ih, binaryThreshold]

/-- The endpoint one selects the last cell at every extraction width. -/
theorem binaryPrefix_one (n : ℕ) : binaryPrefix n 1 = 2 ^ n - 1 := by
  have h := binary_decomposition n 1
  rw [binaryRemainder_one] at h
  simp only [mul_one] at h
  have hnat : binaryPrefix n 1 + 1 = 2 ^ n := by exact_mod_cast h.symm
  omega

theorem binaryPrefix_cell {x : ℚ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (binaryPrefix n x : ℚ) ≤ (2 : ℚ) ^ n * x ∧
      (2 : ℚ) ^ n * x ≤ (binaryPrefix n x : ℚ) + 1 := by
  have h := binary_decomposition n x
  have hr := binaryRemainder_bounds hx hx1 n
  constructor <;> linarith [hr.1, hr.2]

theorem binaryPrefix_cell_strict {x : ℚ} (hx : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (binaryPrefix n x : ℚ) ≤ (2 : ℚ) ^ n * x ∧
      (2 : ℚ) ^ n * x < (binaryPrefix n x : ℚ) + 1 := by
  have h := binary_decomposition n x
  have hr := binaryRemainder_bounds hx hx1.le n
  have ht := binaryRemainder_lt_one hx1 n
  constructor <;> linarith [hr.1]

/-- A perturbation smaller than the distance to the threshold preserves the extracted bit. -/
theorem binaryThreshold_stable {x y ε : ℚ} (he : 0 ≤ ε)
    (hd : |x - y| ≤ ε) (hs : ε < |x - 1 / 2|) : binaryThreshold y = binaryThreshold x := by
  rw [abs_le] at hd
  simp only [binaryThreshold]
  congr 1
  apply propext
  by_cases hx : 1 / 2 ≤ x
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - 1 / 2)] at hs
    constructor <;> intro h <;> linarith [hd.1, hd.2]
  · rw [abs_of_nonpos (by linarith : x - 1 / 2 ≤ 0)] at hs
    constructor <;> intro h <;> linarith [hd.1, hd.2]

/-- Matching digits amplify initial and per-step residual errors by the exact geometric bound. -/
theorem binaryRemainder_trajectory_error (x : ℚ) (y : ℕ → ℚ) (d : ℕ → Bool)
    (ε η : ℚ) (n : ℕ) (hinit : |y 0 - x| ≤ ε)
    (hstep : ∀ j < n, |y (j + 1) - (2 * y j - if d j then 1 else 0)| ≤ η)
    (hdigit : ∀ j < n, d j = binaryThreshold (binaryRemainder j x)) :
    ∀ j ≤ n, |y j - binaryRemainder j x| ≤
      (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * η := by
  intro j hj
  induction j with
  | zero => simpa [binaryRemainder] using hinit
  | succ j ih =>
    have hjn : j < n := by omega
    have hi := ih (by omega)
    have hs := hstep j hjn
    rw [hdigit j hjn] at hs
    have he : y (j + 1) - binaryRemainder (j + 1) x =
        (y (j + 1) - (2 * y j - if binaryThreshold (binaryRemainder j x) then 1 else 0)) +
          2 * (y j - binaryRemainder j x) := by
      rw [binaryRemainder]
      ring
    rw [he]
    calc
      _ ≤ |y (j + 1) - (2 * y j - if binaryThreshold (binaryRemainder j x) then 1 else 0)| +
          |2 * (y j - binaryRemainder j x)| := abs_add_le _ _
      _ ≤ η + 2 * ((2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * η) := by
        rw [abs_mul]
        norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
        linarith
      _ = _ := by rw [pow_succ]; ring

/-- Threshold margins force every perturbed digit to agree with exact extraction. -/
theorem binaryThreshold_trajectory_stable (x : ℚ) (y : ℕ → ℚ) (ε η : ℚ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hinit : |y 0 - x| ≤ ε)
    (hstep : ∀ j < n,
      |y (j + 1) - (2 * y j - if binaryThreshold (y j) then 1 else 0)| ≤ η)
    (hmargin : ∀ j < n, (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * η <
      |binaryRemainder j x - 1 / 2|) :
    ∀ j < n, binaryThreshold (y j) = binaryThreshold (binaryRemainder j x) := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have he := binaryRemainder_trajectory_error x y (fun k => binaryThreshold (y k))
      ε η j hinit (fun k hk => hstep k (by omega))
      (fun k hk => ih k hk (by omega)) j le_rfl
    have hp : (1 : ℚ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have he0 : 0 ≤ (2 : ℚ) ^ j * ε + ((2 : ℚ) ^ j - 1) * η :=
      add_nonneg (mul_nonneg (pow_nonneg (by norm_num) j) hε)
        (mul_nonneg (sub_nonneg.mpr hp) hη)
    apply binaryThreshold_stable he0
    · simpa only [abs_sub_comm] using he
    · exact hmargin j hj

/-- Equal extracted digits give the same natural-number prefix. -/
theorem binaryPrefix_eq_trajectory (x : ℚ) (d : ℕ → Bool) (n : ℕ)
    (hdigit : ∀ j < n, d j = binaryThreshold (binaryRemainder j x)) :
    Nat.rec 0 (fun j p => 2 * p + if d j then 1 else 0) n = binaryPrefix n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (Nat.rec 0 (fun j p => 2 * p + if d j then 1 else 0) n) +
      (if d n then 1 else 0) = binaryPrefix (n + 1) x
    rw [ih (fun j hj => hdigit j (by omega)), binaryPrefix, hdigit n (by omega)]

end GameTheory.Math
