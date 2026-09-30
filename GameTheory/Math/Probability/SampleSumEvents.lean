/-
# Events of sums of draws

Probabilities of events are expectations of indicators (`probOf`). For the sum
of `m` independent draws, the file bounds the events that decide a comparison
with a sure total:

* the sum is nonzero only if some draw is (a union bound), and a sum of
  nonnegative draws vanishes only if every draw does;
* the sum exceeds `m t` only if some draw exceeds `t`, and it reaches `m t`
  only if some draw exceeds `t` or every draw equals `t`.
-/
import GameTheory.Math.Probability.SampleSum

noncomputable section

namespace GameTheory.Math.Probability

/-- The probability of an event, as the expectation of its indicator. -/
abbrev probOf (μ : PMF ℝ) (event : ℝ → Prop) [DecidablePred event] : ℝ :=
  expect μ fun x => if event x then 1 else 0

/-- An indicator has absolute value at most one. -/
theorem abs_indicator_le (p : Prop) [Decidable p] :
    |(if p then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- Indicators are nonnegative. -/
theorem indicator_nonneg (p : Prop) [Decidable p] : 0 ≤ (if p then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

/-- Indicators are integrable. -/
theorem payoffIntegrable_eventIndicator (μ : PMF ℝ) (event : ℝ → Prop) [DecidablePred event] :
    PayoffIntegrable μ fun x => if event x then (1 : ℝ) else 0 :=
  payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _

/-- A probability has absolute value at most one. -/
theorem abs_probOf_le (μ : PMF ℝ) (event : ℝ → Prop) [DecidablePred event] :
    |probOf μ event| ≤ 1 :=
  expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _

/-- Bound an event of a sum by bounding it for each value of the first
summand. -/
theorem probOf_addLaw_le (ν μ : PMF ℝ) (event : ℝ → Prop) [DecidablePred event]
    (F : ℝ → ℝ) {C : ℝ} (hF : ∀ s, |F s| ≤ C)
    (h : ∀ s, expect μ (fun y => if event (s + y) then (1 : ℝ) else 0) ≤ F s) :
    probOf (addLaw ν μ) event ≤ expect ν F := by
  rw [probOf, expect_addLaw _ _ _ (payoffIntegrable_eventIndicator _ _)]
  exact expect_mono (fun s _ => h s)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
      expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
    (payoffIntegrable_of_bounded _ _ hF)

/-- The sum of `m` draws exceeds `m t` only if some draw exceeds `t`. -/
theorem probOf_sampleSum_gt_le (μ : PMF ℝ) (t : ℝ) (m : ℕ) :
    probOf (sampleSum μ m) (fun s => m * t < s) ≤ m * probOf μ (t < ·) := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    have hp := abs_probOf_le μ (t < ·)
    rw [sampleSum_succ]
    refine (probOf_addLaw_le _ _ _
      (fun s => (if (m : ℝ) * t < s then (1 : ℝ) else 0) + probOf μ (t < ·)) (C := 2)
      (fun s => (abs_add_le _ _).trans (by linarith [abs_indicator_le ((m : ℝ) * t < s)]))
      (fun s => ?_)).trans ?_
    · rw [← expect_constant μ (if (m : ℝ) * t < s then (1 : ℝ) else 0),
        ← expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_eventIndicator _ _)]
      refine expect_mono (fun y _ => ?_) (payoffIntegrable_eventIndicator _ _)
        (payoffIntegrable_add (payoffIntegrable_constant _ _) (payoffIntegrable_eventIndicator _ _))
      push_cast
      split_ifs <;> linarith
    · rw [expect_add (payoffIntegrable_eventIndicator _ _) (payoffIntegrable_constant _ _),
        expect_constant]
      push_cast
      linarith

/-- The sum of `m` draws reaches `m t` only if some draw exceeds `t` or every
draw equals `t`. -/
theorem probOf_sampleSum_ge_le (μ : PMF ℝ) (t : ℝ) (m : ℕ) :
    probOf (sampleSum μ m) (fun s => m * t ≤ s) ≤
      m * probOf μ (t < ·) + probOf μ (· = t) ^ m := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    set p := probOf μ (t < ·)
    set q := probOf μ (· = t)
    set r := probOf μ (· < t)
    have hp : 0 ≤ p := expect_nonneg _ _ fun _ _ => indicator_nonneg _
    have hq : 0 ≤ q := expect_nonneg _ _ fun _ _ => indicator_nonneg _
    have hr : 0 ≤ r := expect_nonneg _ _ fun _ _ => indicator_nonneg _
    have hqr : q + r ≤ 1 := by
      rw [← expect_add (payoffIntegrable_eventIndicator _ _) (payoffIntegrable_eventIndicator _ _)]
      refine expect_le_const _ _ (payoffIntegrable_add (payoffIntegrable_eventIndicator _ _)
        (payoffIntegrable_eventIndicator _ _)) 1 fun y _ => ?_
      split_ifs <;> first | (exfalso; linarith) | norm_num
    have hgt := probOf_sampleSum_gt_le μ t m
    have habs : |p| ≤ 1 := abs_probOf_le μ _
    have habsq : |q| ≤ 1 := abs_probOf_le μ _
    have habsr : |r| ≤ 1 := abs_probOf_le μ _
    rw [sampleSum_succ]
    refine (probOf_addLaw_le _ _ _
      (fun s => p + q * (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0) +
        r * (if (m : ℝ) * t < s then (1 : ℝ) else 0)) (C := 3) (fun s => ?_)
      (fun s => ?_)).trans ?_
    · have h1 := abs_indicator_le ((m : ℝ) * t ≤ s)
      have h2 := abs_indicator_le ((m : ℝ) * t < s)
      have hb : |q * (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0)| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg q, abs_nonneg (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0)]
      have hc : |r * (if (m : ℝ) * t < s then (1 : ℝ) else 0)| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg r, abs_nonneg (if (m : ℝ) * t < s then (1 : ℝ) else 0)]
      have hab := abs_add_le p (q * (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0))
      have habc := abs_add_le (p + q * (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0))
        (r * (if (m : ℝ) * t < s then (1 : ℝ) else 0))
      linarith
    · calc
        expect μ (fun y => if (((m + 1 : ℕ) : ℝ) * t ≤ s + y) then (1 : ℝ) else 0) ≤
            expect μ (fun y => (if t < y then (1 : ℝ) else 0) +
              ((if (m : ℝ) * t ≤ s then (1 : ℝ) else 0) * (if y = t then (1 : ℝ) else 0) +
                (if (m : ℝ) * t < s then (1 : ℝ) else 0) *
                  (if y < t then (1 : ℝ) else 0))) := by
          refine expect_mono (fun y _ => ?_) (payoffIntegrable_eventIndicator _ _)
            (payoffIntegrable_add (payoffIntegrable_eventIndicator _ _)
              (payoffIntegrable_add
                (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _))
                (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _))))
          push_cast
          split_ifs <;> first | (exfalso; linarith) |
            (exfalso; apply ‹¬y = t›; linarith) | norm_num
        _ = p + q * (if (m : ℝ) * t ≤ s then (1 : ℝ) else 0) +
            r * (if (m : ℝ) * t < s then (1 : ℝ) else 0) := by
          rw [expect_add (payoffIntegrable_eventIndicator _ _)
            (payoffIntegrable_add (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _))
              (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _))),
            expect_add (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _))
              (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _)),
            expect_const_mul, expect_const_mul]
          ring
    · rw [expect_add (payoffIntegrable_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _)))
          (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _)),
        expect_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_const_mul (payoffIntegrable_eventIndicator _ _)),
        expect_constant, expect_const_mul, expect_const_mul]
      have hge := ih
      change _ ≤ _ at hge
      push_cast
      have hqm : 0 ≤ q ^ m := pow_nonneg hq m
      have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg m) hp
      calc
        p + q * probOf (sampleSum μ m) (fun s => (m : ℝ) * t ≤ s) +
            r * probOf (sampleSum μ m) (fun s => (m : ℝ) * t < s) ≤
            p + q * ((m : ℝ) * p + q ^ m) + r * ((m : ℝ) * p) := by
          gcongr
        _ ≤ ((m : ℝ) + 1) * p + q ^ (m + 1) := by
          rw [pow_succ]
          nlinarith

/-- The sum of `m` draws is nonzero only if some draw is: a union bound. -/
theorem probOf_sampleSum_ne_zero_le (μ : PMF ℝ) (m : ℕ) :
    probOf (sampleSum μ m) (· ≠ 0) ≤ m * probOf μ (· ≠ 0) := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    rw [sampleSum_succ, probOf, expect_addLaw _ _ _
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
    have hpoint : ∀ s, expect μ (fun y => if s + y ≠ 0 then (1 : ℝ) else 0) ≤
        (if s ≠ 0 then 1 else 0) + probOf μ (· ≠ 0) := by
      intro s
      rw [← expect_constant μ (if s ≠ 0 then (1 : ℝ) else 0),
        ← expect_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
      refine expect_mono (fun y _ => ?_)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
        (payoffIntegrable_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _))
      by_cases hs : s = 0
      · subst hs
        simp only [zero_add, ne_eq, not_true_eq_false, ite_false]
        rfl
      · have := indicator_nonneg (y ≠ 0)
        split_ifs <;> simp_all
    calc
      _ ≤ expect (sampleSum μ m) (fun s => (if s ≠ 0 then (1 : ℝ) else 0) + probOf μ (· ≠ 0)) :=
        expect_mono (fun s _ => hpoint s)
          (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
            expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
          (payoffIntegrable_add (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
            (payoffIntegrable_constant _ _))
      _ = probOf (sampleSum μ m) (· ≠ 0) + probOf μ (· ≠ 0) := by
        rw [expect_add (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
          (payoffIntegrable_constant _ _), expect_constant]
      _ ≤ m * probOf μ (· ≠ 0) + probOf μ (· ≠ 0) := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * probOf μ (· ≠ 0) := by push_cast; ring

/-- A sum of nonnegative draws vanishes only if every draw does. -/
theorem probOf_sampleSum_eq_zero_le {μ : PMF ℝ} (hμ : ∀ x ∈ μ.support, 0 ≤ x)
    (m : ℕ) : probOf (sampleSum μ m) (· = 0) ≤ probOf μ (· = 0) ^ m := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    have hnonneg := fun s hs => nonneg_of_mem_support_sampleSum hμ m s hs
    rw [sampleSum_succ, probOf, expect_addLaw _ _ _
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
    have hpoint : ∀ s ∈ (sampleSum μ m).support,
        expect μ (fun y => if s + y = 0 then (1 : ℝ) else 0) ≤
          (if s = 0 then 1 else 0) * probOf μ (· = 0) := by
      intro s hs
      rw [← expect_const_mul]
      refine expect_mono (fun y hy => ?_)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
        (payoffIntegrable_const_mul (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _))
      have h0 := hnonneg s hs
      have h1 := hμ y hy
      by_cases hsy : s + y = 0
      · have hs0 : s = 0 := by linarith
        have hy0 : y = 0 := by linarith
        simp [hs0, hy0]
      · simp only [hsy, ite_false]
        exact mul_nonneg (indicator_nonneg _) (indicator_nonneg _)
    have hprob0 : 0 ≤ probOf μ (· = 0) := expect_nonneg _ _ fun _ _ => indicator_nonneg _
    calc
      _ ≤ expect (sampleSum μ m) (fun s => (if s = 0 then (1 : ℝ) else 0) * probOf μ (· = 0)) :=
        expect_mono hpoint
          (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
            expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
          (payoffIntegrable_of_bounded _ _ (C := |probOf μ (· = 0)|) fun _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_le _))
      _ = probOf (sampleSum μ m) (· = 0) * probOf μ (· = 0) := by
        simp only [mul_comm _ (probOf μ (· = 0))]
        rw [expect_const_mul, mul_comm]
      _ ≤ probOf μ (· = 0) ^ m * probOf μ (· = 0) := mul_le_mul_of_nonneg_right ih hprob0
      _ = probOf μ (· = 0) ^ (m + 1) := (pow_succ _ _).symm

end GameTheory.Math.Probability
