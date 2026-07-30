/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability

/-!
# Finite adaptive PMF histories

A small horizon-indexed history process for predictable-score arguments. At depth `n`, histories
are functions `Fin n → Ω`. A step kernel may depend on the whole previous history. If every
predictable one-step score has conditional expectation zero, then its cumulative score has
expectation zero at every finite horizon.
-/

namespace Math.Probability

noncomputable section

variable {Ω : Type*}

/-- Law of an adaptive finite history. -/
noncomputable def adaptiveHistoryLaw
    (step : ∀ n, (Fin n → Ω) → PMF Ω) : (n : ℕ) → PMF (Fin n → Ω)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | n + 1 => (adaptiveHistoryLaw step n).bind fun history =>
      (step n history).map (Fin.snoc history)

@[simp] theorem adaptiveHistoryLaw_zero
    (step : ∀ n, (Fin n → Ω) → PMF Ω) :
    adaptiveHistoryLaw step 0 = PMF.pure (fun i => Fin.elim0 i) := rfl

theorem adaptiveHistoryLaw_succ
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (n : ℕ) :
    adaptiveHistoryLaw step (n + 1) =
      (adaptiveHistoryLaw step n).bind fun history =>
        (step n history).map (Fin.snoc history) := rfl

/-- Sum of predictable scores along a finite history. -/
noncomputable def predictableScoreSum
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ) :
    (n : ℕ) → (Fin n → Ω) → ℝ
  | 0, _ => 0
  | n + 1, history =>
      predictableScoreSum score n (Fin.init history) +
        score n (Fin.init history) (history (Fin.last n))

@[simp] theorem predictableScoreSum_zero
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (history : Fin 0 → Ω) :
    predictableScoreSum score 0 history = 0 := rfl

@[simp] theorem predictableScoreSum_snoc
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (n : ℕ) (history : Fin n → Ω) (x : Ω) :
    predictableScoreSum score (n + 1) (Fin.snoc history x) =
      predictableScoreSum score n history + score n history x := by
  simp [predictableScoreSum]

/-- Along a full observation stream, the recursively defined predictable
score is the ordinary sum of its prefix-selected one-step scores. -/
theorem predictableScoreSum_restrict_eq_sum
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (observation : ℕ → Ω) (T : ℕ) :
    predictableScoreSum score T (fun i => observation i) =
      ∑ t ∈ Finset.range T,
        score t (fun i => observation i) (observation t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hinit :
          Fin.init (fun i : Fin (T + 1) => observation i) =
            (fun i : Fin T => observation i) := by
        rfl
      rw [← Fin.snoc_init_self
        (fun i : Fin (T + 1) => observation i)]
      rw [predictableScoreSum_snoc, hinit, Finset.sum_range_succ, ih]
      simp

/-- Sum of the conditional means of a predictable score along a finite history. -/
noncomputable def predictableConditionalMeanSum
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ) :
    (n : ℕ) → (Fin n → Ω) → ℝ
  | 0, _ => 0
  | n + 1, history =>
      predictableConditionalMeanSum step score n (Fin.init history) +
        expect (step n (Fin.init history)) (score n (Fin.init history))

@[simp] theorem predictableConditionalMeanSum_zero
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (history : Fin 0 → Ω) :
    predictableConditionalMeanSum step score 0 history = 0 := rfl

@[simp] theorem predictableConditionalMeanSum_snoc
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (n : ℕ) (history : Fin n → Ω) (x : Ω) :
    predictableConditionalMeanSum step score (n + 1) (Fin.snoc history x) =
      predictableConditionalMeanSum step score n history +
        expect (step n history) (score n history) := by
  simp [predictableConditionalMeanSum]

/-- Finite-horizon compensator identity: expected cumulative predictable score equals the
    expected sum of its historywise conditional means. -/
theorem expect_predictableScoreSum_eq_expect_conditionalMeanSum [Finite Ω]
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (T : ℕ) :
    expect (adaptiveHistoryLaw step T) (predictableScoreSum score T) =
      expect (adaptiveHistoryLaw step T)
        (predictableConditionalMeanSum step score T) := by
  induction T with
  | zero =>
      simp [adaptiveHistoryLaw, predictableScoreSum, predictableConditionalMeanSum]
  | succ T ih =>
      rw [adaptiveHistoryLaw_succ, expect_bind, expect_bind]
      have hraw : (fun history =>
          expect ((step T history).map (Fin.snoc history))
            (predictableScoreSum score (T + 1))) =
          fun history => predictableScoreSum score T history +
            expect (step T history) (score T history) := by
        funext history
        rw [expect_map]
        simp_rw [predictableScoreSum_snoc]
        rw [expect_add, expect_const]
      have hmean : (fun history =>
          expect ((step T history).map (Fin.snoc history))
            (predictableConditionalMeanSum step score (T + 1))) =
          fun history => predictableConditionalMeanSum step score T history +
            expect (step T history) (score T history) := by
        funext history
        rw [expect_map]
        simp_rw [predictableConditionalMeanSum_snoc]
        rw [expect_const]
      rw [hraw, hmean, expect_add, expect_add, ih]

/-- A uniform per-round conditional-mean lower bound accumulates linearly along every history. -/
theorem mul_le_predictableConditionalMeanSum
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    {δ : ℝ} (hdrift : ∀ n history, δ ≤ expect (step n history) (score n history))
    (T : ℕ) (history : Fin T → Ω) :
    T * δ ≤ predictableConditionalMeanSum step score T history := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [predictableConditionalMeanSum]
      have hprev := ih (Fin.init history)
      have hstep := hdrift T (Fin.init history)
      push_cast
      nlinarith

/-- Persistent positive conditional drift yields a linear expected cumulative-score lower bound. -/
theorem mul_le_expect_predictableScoreSum [Finite Ω]
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    {δ : ℝ} (hdrift : ∀ n history, δ ≤ expect (step n history) (score n history))
    (T : ℕ) :
    T * δ ≤ expect (adaptiveHistoryLaw step T) (predictableScoreSum score T) := by
  rw [expect_predictableScoreSum_eq_expect_conditionalMeanSum]
  calc
    (T : ℝ) * δ =
        expect (adaptiveHistoryLaw step T) (fun _ => (T : ℝ) * δ) := by
          rw [expect_const]
    _ ≤ expect (adaptiveHistoryLaw step T)
          (predictableConditionalMeanSum step score T) :=
      expect_mono _ _ _ fun history =>
        mul_le_predictableConditionalMeanSum step score hdrift T history

/-- Finite-horizon martingale identity for a predictable score with zero conditional mean. -/
theorem expect_predictableScoreSum_eq_zero [Finite Ω]
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0)
    (T : ℕ) :
    expect (adaptiveHistoryLaw step T) (predictableScoreSum score T) = 0 := by
  induction T with
  | zero => simp [adaptiveHistoryLaw, predictableScoreSum]
  | succ T ih =>
      rw [adaptiveHistoryLaw_succ, expect_bind]
      have hstep : (fun history =>
          expect ((step T history).map (Fin.snoc history))
            (predictableScoreSum score (T + 1))) =
          fun history => predictableScoreSum score T history := by
        funext history
        rw [expect_map]
        simp_rw [predictableScoreSum_snoc]
        rw [expect_add, expect_const, hcenter, add_zero]
      rw [hstep, ih]

end

end Math.Probability
