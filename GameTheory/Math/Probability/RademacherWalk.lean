/-
# The fair `±σ` walk

`signLaw σ` takes the values `σ` and `-σ` with probability one half each; it is
symmetric, centred, and has second moment `σ ^ 2`. A sum of `m` independent
copies is `σ` times the fair `±1` walk, whose value `2 k - m` carries the
binomial mass `C(m, k) / 2 ^ m`.

Every binomial mass is at most the central one, and the square of the central
mass is at most `1 / m`. Hence the walk lands in any window of `H + 1`
consecutive values with probability at most `(H + 1) / √m`: a sum of symmetric
summands is not concentrated near zero.
-/
import GameTheory.Math.Probability.SampleSum
import GameTheory.Math.Probability.Uniform
import Mathlib.Data.Nat.Choose.Central

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

/-! ## The `±σ` law -/

/-- The law taking the values `σ` and `-σ` with probability one half each. -/
def signLaw (σ : ℝ) : PMF ℝ :=
  (PMF.uniformOfFintype Bool).map fun b => if b then σ else -σ

theorem expect_signLaw (σ : ℝ) (f : ℝ → ℝ) :
    expect (signLaw σ) f = (f σ + f (-σ)) / 2 := by
  rw [signLaw, expect_map, expect_uniformOfFintype]
  simp

theorem abs_le_of_mem_support_signLaw (σ : ℝ) :
    ∀ x ∈ (signLaw σ).support, |x| ≤ |σ| := by
  intro x hx
  rw [signLaw, PMF.mem_support_map_iff] at hx
  obtain ⟨b, _, rfl⟩ := hx
  cases b <;> simp

private theorem uniform_bool_map_not :
    (PMF.uniformOfFintype Bool).map (fun b => !b) = PMF.uniformOfFintype Bool := by
  ext b
  cases b <;> simp [PMF.map_apply, tsum_fintype]

theorem signLaw_map_neg (σ : ℝ) : (signLaw σ).map Neg.neg = signLaw σ := by
  rw [signLaw, PMF.map_comp]
  have hswap : (Neg.neg ∘ fun b : Bool => if b then σ else -σ) =
      (fun b : Bool => if b then σ else -σ) ∘ fun b => !b := by
    funext b
    cases b <;> simp
  rw [hswap, ← PMF.map_comp, uniform_bool_map_not]

theorem signLaw_eq_map_mul (σ : ℝ) : signLaw σ = (signLaw 1).map (σ * ·) := by
  rw [signLaw, signLaw, PMF.map_comp]
  congr 1
  funext b
  cases b <;> simp

/-! ## Counting heads -/

/-- The number of heads in `m` fair coin flips. -/
def headCount : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | m + 1 => (headCount m).bind fun k =>
      (PMF.uniformOfFintype Bool).map fun b => if b then k + 1 else k

private theorem coinStep_apply (j k : ℕ) :
    (PMF.uniformOfFintype Bool).map (fun b => if b then j + 1 else j) k =
      (if k = j + 1 then 2⁻¹ else 0) + (if k = j then 2⁻¹ else 0) := by
  simp [PMF.map_apply, tsum_fintype]

private theorem headCount_succ_apply (m k : ℕ) :
    headCount (m + 1) k =
      (∑' j, headCount m j * if k = j + 1 then 2⁻¹ else 0) + headCount m k * 2⁻¹ := by
  rw [headCount, PMF.bind_apply]
  simp only [coinStep_apply, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  simp [mul_ite]

/-- The binomial masses of the head count. -/
theorem headCount_apply (m k : ℕ) : headCount m k = (m.choose k : ℝ≥0∞) * 2⁻¹ ^ m := by
  induction m generalizing k with
  | zero =>
    rcases k with _ | k
    · simp [headCount]
    · simp [headCount, PMF.pure_apply]
  | succ m ih =>
    rw [headCount_succ_apply]
    rcases k with _ | k
    · simp [ih, pow_succ]
    · have hshift : (∑' j, headCount m j * if k + 1 = j + 1 then (2⁻¹ : ℝ≥0∞) else 0) =
          headCount m k * 2⁻¹ := by
        simp [mul_ite]
      rw [hshift, ih, ih, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
      ring

/-- The fair `±1` walk after `m` steps is `2 k - m` for `k` heads. -/
theorem sampleSum_signLaw_one (m : ℕ) :
    sampleSum (signLaw 1) m = (headCount m).map fun k : ℕ => 2 * (k : ℝ) - m := by
  induction m with
  | zero => simp [headCount, PMF.pure_map]
  | succ m ih =>
    rw [sampleSum_succ, ih, headCount, addLaw, PMF.bind_map, PMF.map_bind]
    congr 1
    funext k
    rw [Function.comp_apply, signLaw, PMF.map_comp, PMF.map_comp]
    congr 1
    funext b
    cases b <;> simp <;> ring

/-! ## Central binomial bound -/

private theorem centralBinom_sq_mul_le (j : ℕ) :
    j.centralBinom ^ 2 * (2 * j + 1) ≤ 16 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have key := Nat.succ_mul_centralBinom_succ j
    have hpos : 0 < (j + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc
      (j + 1) ^ 2 * ((j + 1).centralBinom ^ 2 * (2 * (j + 1) + 1)) =
          ((j + 1) * (j + 1).centralBinom) ^ 2 * (2 * j + 3) := by ring
      _ = 4 * (2 * j + 1) * (2 * j + 3) * (j.centralBinom ^ 2 * (2 * j + 1)) := by
        rw [key]
        ring
      _ ≤ 4 * (2 * j + 1) * (2 * j + 3) * 16 ^ j := Nat.mul_le_mul_left _ ih
      _ ≤ 4 * (2 * j + 2) ^ 2 * 16 ^ j := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = (j + 1) ^ 2 * 16 ^ (j + 1) := by ring

/-- The square of the central binomial mass is at most `1 / m`. -/
theorem choose_middle_sq_mul_le (m : ℕ) : m.choose (m / 2) ^ 2 * m ≤ 4 ^ m := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have h := centralBinom_sq_mul_le j
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have hdiv : 2 * j / 2 = j := by omega
    rw [hdiv, show 4 ^ (2 * j) = 16 ^ j by rw [pow_mul]; norm_num]
    calc
      (2 * j).choose j ^ 2 * (2 * j) ≤ (2 * j).choose j ^ 2 * (2 * j + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ _)
      _ ≤ 16 ^ j := h
  · have h := centralBinom_sq_mul_le (j + 1)
    have hdiv : (2 * j + 1) / 2 = j := by omega
    have hsplit : (j + 1).centralBinom = 2 * (2 * j + 1).choose j := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (j + 1) = (2 * j + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    rw [hdiv]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc
      4 * ((2 * j + 1).choose j ^ 2 * (2 * j + 1)) =
          (j + 1).centralBinom ^ 2 * (2 * j + 1) := by rw [hsplit]; ring
      _ ≤ (j + 1).centralBinom ^ 2 * (2 * (j + 1) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ (j + 1) := h
      _ = 4 * 4 ^ (2 * j + 1) := by
        rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]
        ring

/-! ## Anti-concentration -/

/-- The fair `±1` walk lands in `[-H, H]` with probability at most `H + 1`
central binomial masses. -/
theorem signWalk_window_le (m H : ℕ) :
    ((sampleSum (signLaw 1) m).toOuterMeasure {x | |x| ≤ H}).toReal ≤
      (H + 1) * ((m.choose (m / 2) : ℝ) / 2 ^ m) := by
  classical
  rw [sampleSum_signLaw_one, PMF.toOuterMeasure_map_apply]
  set window := Finset.Icc ((m - H) / 2) ((m + H) / 2)
  have hsubset : (fun k : ℕ => 2 * (k : ℝ) - m) ⁻¹' {x | |x| ≤ H} ∩ (headCount m).support ⊆
      (window : Set ℕ) := by
    rintro k ⟨hk, _⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, abs_le] at hk
    have hlow : m ≤ 2 * k + H := by exact_mod_cast (show (m : ℝ) ≤ 2 * k + H by linarith)
    have hhigh : 2 * k ≤ m + H := by exact_mod_cast (show (2 * k : ℝ) ≤ m + H by linarith)
    simp only [window, Finset.coe_Icc, Set.mem_Icc]
    omega
  have hcard : window.card ≤ H + 1 := by
    simp only [window, Nat.card_Icc]
    omega
  have hle : (headCount m).toOuterMeasure
      ((fun k : ℕ => 2 * (k : ℝ) - m) ⁻¹' {x | |x| ≤ H}) ≤
        ((H + 1 : ℕ) : ℝ≥0∞) * ((m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m) := by
    calc
      _ ≤ (headCount m).toOuterMeasure (window : Set ℕ) := PMF.toOuterMeasure_mono _ hsubset
      _ = ∑ k ∈ window, headCount m k := PMF.toOuterMeasure_apply_finset _ _
      _ ≤ ∑ _k ∈ window, (m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m := by
        apply Finset.sum_le_sum
        intro k _
        rw [headCount_apply]
        gcongr
        exact_mod_cast Nat.choose_le_middle k m
      _ = (window.card : ℝ≥0∞) * ((m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((H + 1 : ℕ) : ℝ≥0∞) * ((m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m) := by
        gcongr
  have hfin : ((H + 1 : ℕ) : ℝ≥0∞) * ((m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m) ≠ ∞ := by
    simp [ENNReal.mul_eq_top]
  calc
    _ ≤ (((H + 1 : ℕ) : ℝ≥0∞) * ((m.choose (m / 2) : ℝ≥0∞) * 2⁻¹ ^ m)).toReal :=
      ENNReal.toReal_mono hfin hle
    _ = (H + 1) * ((m.choose (m / 2) : ℝ) / 2 ^ m) := by
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
        ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      push_cast
      rw [inv_pow, div_eq_mul_inv]

/-- After `n ^ 8` steps the fair `±1` walk lies in `[-n ^ 3, n ^ 3]` with
probability at most `2 / n`. -/
theorem signWalk_window_pow_eight_le (n : ℕ) (hn : 1 ≤ n) :
    ((sampleSum (signLaw 1) (n ^ 8)).toOuterMeasure {x | |x| ≤ (n ^ 3 : ℕ)}).toReal ≤
      2 / n := by
  have hwin := signWalk_window_le (n ^ 8) (n ^ 3)
  set a := ((n ^ 8).choose (n ^ 8 / 2) : ℝ) / 2 ^ (n ^ 8)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 ≤ a := by positivity
  have hsq : a ^ 2 * (n : ℝ) ^ 8 ≤ 1 := by
    have h := choose_middle_sq_mul_le (n ^ 8)
    have hcast : ((n ^ 8).choose (n ^ 8 / 2) : ℝ) ^ 2 * (n : ℝ) ^ 8 ≤ 4 ^ (n ^ 8) := by
      exact_mod_cast h
    have h4 : (4 : ℝ) ^ (n ^ 8) = (2 ^ (n ^ 8)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4] at hcast
    have h2pos : (0 : ℝ) < (2 ^ (n ^ 8)) ^ 2 := by positivity
    simp only [a, div_pow]
    rw [div_mul_eq_mul_div, div_le_one h2pos]
    exact hcast
  clear_value a
  have ha : a ≤ 1 / (n : ℝ) ^ 4 := by
    have hb : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
    have h8 : a ^ 2 ≤ (1 / (n : ℝ) ^ 4) ^ 2 := by
      rw [show (1 / (n : ℝ) ^ 4) ^ 2 = 1 / (n : ℝ) ^ 8 by
        rw [div_pow, one_pow, ← pow_mul]]
      rw [le_div_iff₀ (by positivity)]
      exact hsq
    exact (pow_le_pow_iff_left₀ ha0 hb two_ne_zero).mp h8
  calc
    _ ≤ ((n ^ 3 : ℕ) + 1) * a := by exact_mod_cast hwin
    _ ≤ ((n : ℝ) ^ 3 + 1) * (1 / (n : ℝ) ^ 4) := by
      push_cast
      exact mul_le_mul_of_nonneg_left ha (by positivity)
    _ ≤ (2 * (n : ℝ) ^ 3) * (1 / (n : ℝ) ^ 4) := by
      gcongr
      have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
      linarith
    _ = 2 / n := by
      field_simp

end GameTheory.Math.Probability
