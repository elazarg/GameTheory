/-
# Mean dominance of fixed laws is comparison of expectations

For laws of bounded support that do not vary with the size parameter,
computational mean dominance is exactly the order of expectations.

* If `E X > E Y`, Chebyshev's inequality makes the `m`-sample mean of `X - Y`
  nonpositive with probability `O(1 / m)`, so the gap vanishes polynomially.
* If `E X = E Y`, the sum of `m` draws of `X - Y` has expected sign
  `O(m ^ (-1 / 8))` (sign balance), so again the gap vanishes polynomially.
* If `E X < E Y`, the sample mean of `X - Y` is eventually negative with
  probability near one, so the gap tends to one and dominance fails.
-/
import GameTheory.Math.Probability.MeanComparison
import GameTheory.Math.Probability.SignBalance

noncomputable section

namespace GameTheory.Math.Probability

open Filter

private theorem abs_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]

theorem abs_le_of_mem_support_differenceLaw {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R) :
    ∀ z ∈ (differenceLaw X Y).support, |z| ≤ R + R := by
  intro z hz
  rw [differenceLaw, mem_support_addLaw] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  rw [PMF.mem_support_map_iff] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  calc
    |a + -y| ≤ |a| + |-y| := abs_add_le _ _
    _ ≤ R + R := add_le_add (hX a ha) (by rw [abs_neg]; exact hY y hy)

theorem lawMean_differenceLaw {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R) :
    lawMean (differenceLaw X Y) = lawMean X - lawMean Y := by
  have hYneg : ∀ y ∈ (Y.map Neg.neg).support, |y| ≤ R := by
    intro y hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    rw [abs_neg]
    exact hY y hy
  have hint : PayoffIntegrable (differenceLaw X Y) id :=
    payoffIntegrable_of_support_abs_le (abs_le_of_mem_support_differenceLaw hX hY) id
      fun x hx => hx
  have hXint : PayoffIntegrable X id := payoffIntegrable_of_support_abs_le hX id fun x hx => hx
  have hYint : PayoffIntegrable (Y.map Neg.neg) id :=
    payoffIntegrable_of_support_abs_le hYneg id fun x hx => hx
  have hnegMean : expect (Y.map Neg.neg) id = -lawMean Y := by
    rw [expect_map]
    exact expect_neg
  rw [lawMean, differenceLaw, expect_addLaw _ _ _ hint]
  have hinner : ∀ a, expect (Y.map Neg.neg) (fun b => id (a + b)) = a - lawMean Y := by
    intro a
    change expect (Y.map Neg.neg) (fun b => a + id b) = _
    rw [expect_add (payoffIntegrable_constant _ _) hYint, expect_constant, hnegMean]
    ring
  simp only [hinner]
  change expect X (fun a => id a - lawMean Y) = _
  rw [expect_sub hXint (payoffIntegrable_constant _ _), expect_constant]

/-- Chebyshev's bound on the gap when `X` has the larger expectation. -/
private theorem meanComparisonGap_le_of_lt {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R)
    (hlt : lawMean Y < lawMean X) {m : ℕ} (hm : 1 ≤ m) :
    meanComparisonGap X Y m ≤
      lawVariance (differenceLaw X Y) / (m * (lawMean X - lawMean Y) ^ 2) := by
  classical
  set D := differenceLaw X Y
  have hDbound := abs_le_of_mem_support_differenceLaw hX hY
  have hmean : lawMean D = lawMean X - lawMean Y := lawMean_differenceLaw hX hY
  set e := lawMean D
  have he : 0 < e := by rw [hmean]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < (m : ℝ) * e := mul_pos hmpos he
  have hcheb := sampleSum_deviation_le hDbound m ht
  have hsupp := abs_le_of_mem_support_sampleSum hDbound m
  rw [meanComparisonGap_eq_neg_expect_sign, ← expect_neg, ← expect_indicator] at *
  have hmono : expect (sampleSum D m) (fun s => -Real.sign s) ≤
      expect (sampleSum D m)
        (fun s => if s ∈ {s | (m : ℝ) * e ≤ |s - m * lawMean D|} then (1 : ℝ) else 0) := by
    refine expect_mono (fun s _ => ?_)
      (payoffIntegrable_of_bounded _ _ (C := 1) fun s => by
        rw [abs_neg]
        exact abs_sign_le_one s)
      (payoffIntegrable_of_bounded _ _ (C := 1) fun s => by split_ifs <;> simp)
    rcases le_or_gt s 0 with hs | hs
    · have hfar : (m : ℝ) * e ≤ |s - m * lawMean D| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      simp only [Set.mem_ofPred_eq, hfar, ite_true]
      have := abs_sign_le_one s
      rw [abs_le] at this
      linarith
    · rw [Real.sign_of_pos hs]
      split_ifs <;> norm_num
  calc
    _ ≤ _ := hmono
    _ ≤ m * lawVariance D / (m * e) ^ 2 := hcheb
    _ = lawVariance D / (m * (lawMean X - lawMean Y) ^ 2) := by
      rw [← hmean]
      field_simp

/-- The gap tends to one when `Y` has the larger expectation. -/
private theorem one_sub_le_meanComparisonGap_of_lt {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R)
    (hlt : lawMean X < lawMean Y) {m : ℕ} (hm : 1 ≤ m) :
    1 - 2 * (lawVariance (differenceLaw X Y) / (m * (lawMean Y - lawMean X) ^ 2)) ≤
      meanComparisonGap X Y m := by
  classical
  set D := differenceLaw X Y
  have hDbound := abs_le_of_mem_support_differenceLaw hX hY
  have hmean : lawMean D = lawMean X - lawMean Y := lawMean_differenceLaw hX hY
  set e := lawMean D
  have he : e < 0 := by rw [hmean]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < (m : ℝ) * -e := mul_pos hmpos (by linarith)
  have hcheb := sampleSum_deviation_le hDbound m ht
  rw [← expect_indicator] at hcheb
  set far : ℝ → ℝ := fun s => if s ∈ {s | (m : ℝ) * -e ≤ |s - m * lawMean D|} then 1 else 0
  have hfarInt : PayoffIntegrable (sampleSum D m) far :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun s => by
      simp only [far]
      split_ifs <;> simp
  have hmono : expect (sampleSum D m) (fun s => 1 + -2 * far s) ≤
      expect (sampleSum D m) (fun s => -Real.sign s) := by
    refine expect_mono (fun s _ => ?_)
      (payoffIntegrable_add (payoffIntegrable_constant _ _)
        (payoffIntegrable_const_mul hfarInt))
      (payoffIntegrable_of_bounded _ _ (C := 1) fun s => by
        rw [abs_neg]
        exact abs_sign_le_one s)
    rcases lt_or_ge s 0 with hs | hs
    · rw [Real.sign_of_neg hs]
      simp only [far]
      split_ifs <;> norm_num
    · have hfar : (m : ℝ) * -e ≤ |s - m * lawMean D| := by
        rw [abs_of_nonneg (by nlinarith)]
        linarith
      simp only [far, Set.mem_ofPred_eq, hfar, ite_true]
      have := abs_sign_le_one s
      rw [abs_le] at this
      linarith
  rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_const_mul hfarInt),
    expect_constant, expect_const_mul, expect_neg, ← meanComparisonGap_eq_neg_expect_sign]
    at hmono
  have hvar : m * lawVariance D / (m * -e) ^ 2 =
      lawVariance D / (m * (lawMean Y - lawMean X) ^ 2) := by
    rw [show -e = lawMean Y - lawMean X by rw [hmean]; ring]
    field_simp
  rw [hvar] at hcheb
  linarith

/-- Laws with equal expectations have polynomially vanishing gaps. -/
private theorem meanComparisonGap_le_of_eq {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R)
    (heq : lawMean X = lawMean Y) :
    ∃ C, ∀ m : ℕ, |meanComparisonGap X Y m| ^ 8 * m ≤ C := by
  have hmean : expect (differenceLaw X Y) id = 0 := by
    rw [← lawMean, lawMean_differenceLaw hX hY, heq, sub_self]
  obtain ⟨C, hC⟩ := exists_abs_expect_sign_sampleSum_pow_mul_le
    (abs_le_of_mem_support_differenceLaw hX hY) hmean
  refine ⟨C, fun m => ?_⟩
  rw [meanComparisonGap_eq_neg_expect_sign, abs_neg]
  exact hC m

private theorem eventually_div_lt_inv_pow {C : ℝ} (c : ℕ) :
    ∀ᶠ κ : ℕ in atTop, C / (κ : ℝ) ^ (c + 1) < ((κ : ℝ) ^ c)⁻¹ := by
  filter_upwards [eventually_gt_atTop ⌈C⌉₊, eventually_ge_atTop 1] with κ hκ hκ1
  have hpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hCκ : C < κ := Nat.lt_of_ceil_lt hκ
  rw [div_lt_iff₀ (by positivity), pow_succ, ← mul_assoc, inv_mul_cancel₀ (by positivity),
    one_mul]
  exact hCκ

/-- For laws of bounded support that do not vary with the size parameter,
computational mean dominance is the order of expectations. -/
theorem computationallyMeanDominates_const_iff {X Y : PMF ℝ} {R : ℝ}
    (hX : ∀ x ∈ X.support, |x| ≤ R) (hY : ∀ y ∈ Y.support, |y| ≤ R) :
    ComputationallyMeanDominates (fun _ => X) (fun _ => Y) ↔ lawMean Y ≤ lawMean X := by
  constructor
  · intro hdom
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨d, hd, hev⟩ := hdom 1 le_rfl
    set V := lawVariance (differenceLaw X Y)
    set Δ := lawMean Y - lawMean X
    have hΔ : 0 < Δ := by simp only [Δ]; linarith
    obtain ⟨κ, hgap, hκ⟩ := (hev.and (eventually_ge_atTop (4 + ⌈4 * V / Δ ^ 2⌉₊))).exists
    have hκ4 : (4 : ℝ) ≤ κ := by exact_mod_cast (show 4 ≤ κ by omega)
    have hκV : 4 * V / Δ ^ 2 ≤ κ :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 * V / Δ ^ 2⌉₊ ≤ κ by omega))
    have hκpos : (0 : ℝ) < κ := by linarith
    have hm1 : 1 ≤ κ ^ d := Nat.one_le_pow _ _ (by omega)
    have hmκ : (κ : ℝ) ≤ ((κ ^ d : ℕ) : ℝ) := by
      push_cast
      exact le_self_pow₀ (by linarith) (by omega)
    have hlower := one_sub_le_meanComparisonGap_of_lt hX hY hlt hm1
    have hsmall : V / (((κ ^ d : ℕ) : ℝ) * Δ ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * V ≤ κ * Δ ^ 2 := by
        have := (div_le_iff₀ (by positivity)).mp hκV
        linarith
      nlinarith [sq_nonneg Δ]
    have hinv : ((κ : ℝ) ^ 1)⁻¹ ≤ 1 / 4 := by
      rw [pow_one, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hκ4
    linarith
  · intro hle
    rcases hle.lt_or_eq with hlt | heq
    · intro c hc
      refine ⟨c + 1, by omega, ?_⟩
      filter_upwards [eventually_div_lt_inv_pow (C := lawVariance (differenceLaw X Y) /
          (lawMean X - lawMean Y) ^ 2) c, eventually_ge_atTop 1] with κ hκ hκ1
      have hm1 : 1 ≤ κ ^ (c + 1) := Nat.one_le_pow _ _ (by omega)
      refine (meanComparisonGap_le_of_lt hX hY hlt hm1).trans_lt ?_
      convert hκ using 1
      push_cast
      field_simp
    · obtain ⟨C, hC⟩ := meanComparisonGap_le_of_eq hX hY heq.symm
      intro c hc
      refine ⟨8 * c + 1, by omega, ?_⟩
      filter_upwards [eventually_gt_atTop ⌈C⌉₊, eventually_ge_atTop 1] with κ hκC hκ1
      have hpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
      have hCκ : C < κ := Nat.lt_of_ceil_lt hκC
      set gap := meanComparisonGap X Y (κ ^ (8 * c + 1))
      have hbound := hC (κ ^ (8 * c + 1))
      push_cast at hbound
      have hscaled : (|gap| * (κ : ℝ) ^ c) ^ 8 < 1 := by
        have hsplit : (|gap| * (κ : ℝ) ^ c) ^ 8 * κ = |gap| ^ 8 * (κ : ℝ) ^ (8 * c + 1) := by
          ring
        have hlt : (|gap| * (κ : ℝ) ^ c) ^ 8 * κ < 1 * κ := by
          rw [hsplit, one_mul]
          linarith
        exact lt_of_mul_lt_mul_right hlt hpos.le
      have hsmall : |gap| * (κ : ℝ) ^ c < 1 := by
        by_contra hge
        rw [not_lt] at hge
        exact absurd (one_le_pow₀ hge) (not_le.mpr hscaled)
      have hκc : (0 : ℝ) < (κ : ℝ) ^ c := by positivity
      calc
        gap ≤ |gap| := le_abs_self _
        _ < ((κ : ℝ) ^ c)⁻¹ := by
          rw [← one_div, lt_div_iff₀ hκc]
          exact hsmall

end GameTheory.Math.Probability
