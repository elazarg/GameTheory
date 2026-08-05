/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.Adaptive

/-!
# A weak-L² maximal inequality for adaptive decision processes

Here `Ω` is one *decision step's* observation: the action chosen at the current state
together with the next state. The kernel `step n history` is the law of that observation
given the past, so the filtration carried by `adaptiveHistoryLaw step` is exactly
"everything known immediately before the `n`-th decision", and a predictable score
`score n history ω` is the decision increment `D_n = v(Y_n) - v(X_n)` of that step.

Two hypotheses drive the whole file:

* `hcenter` is the half-step martingale property `E[D_n | F_n] = 0`;
* `hbalanced` is δ-balancedness `|D_n| ≤ δ`.

Writing `S_T = ∑_{k < T} D_k` for the cumulative score and `w̄_T = ∑_{k < T} |D_k|` for the
pathwise decision variation, the results are:

* `expect_predictableScoreSum_eq_sum_expect_conditionalMean` — the compensator identity
  `E[S_T] = ∑_{k < T} E[E[D_k | F_k]]`, with no centering hypothesis;
* `expectedDecisionVariation` — the expected decision variation `E[w̄_T]`, monotone in `T`
  and nonnegative;
* `expect_predictableScoreSum_sq_eq_sum` — orthogonality of centered increments,
  `E[S_T²] = ∑_{k < T} E[E[D_k² | F_k]]`;
* `sq_mul_expect_indicator_le_mul_expectedDecisionVariation` — the maximal inequality
  `ε² · P(max_{m ≤ T} |S_m| ≥ ε) ≤ δ · E[w̄_T]`, and its uniform-in-`T` corollary
  `expect_indicator_le_div_of_expectedDecisionVariation_le`;
* `expect_indicator_scoreRunningMax_le_div` — the one-sided strengthening
  `P(max_{m ≤ T} S_m ≥ ε) ≤ V / (ε² + V)` for `V = δ · E[w̄_T]`.

The infinite-horizon form `P(sup_m |S_m| ≥ ε) ≤ δ · E[w̄] / ε²` follows from the
uniform-in-`T` corollary by continuity from below. It is *not* formalized here, because the
infinite path measure is not constructed in this repository.

The observation alphabet is assumed finite (`[Finite Ω]`), which is a restriction relative to
the countable-alphabet statement of the result. Every integrand appearing below is bounded, so
the countable case would go through `expect_bind_of_bounded` and `expect_add_of_summable` in
place of `expect_bind` and `expect_add`; that generalization is not carried out here.
-/

set_option autoImplicit false

namespace Math.Probability

noncomputable section

variable {Ω : Type*} [Finite Ω]

/-! ### The compensator identity as a sum over rounds -/

/-- **Compensator sum identity.** The expected cumulative predictable score at horizon `T` is
the sum over rounds `k < T` of the expected historywise conditional mean of the `k`-th
increment. No centering hypothesis is needed. -/
theorem expect_predictableScoreSum_eq_sum_expect_conditionalMean
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (T : ℕ) :
    expect (adaptiveHistoryLaw step T) (predictableScoreSum score T) =
      ∑ k ∈ Finset.range T,
        expect (adaptiveHistoryLaw step k)
          (fun history => expect (step k history) (score k history)) := by
  induction T with
  | zero => simp [adaptiveHistoryLaw, predictableScoreSum]
  | succ T ih =>
      have hstep : (fun history : Fin T → Ω =>
          expect ((step T history).map (Fin.snoc history))
            (predictableScoreSum score (T + 1))) =
          fun history => predictableScoreSum score T history +
            expect (step T history) (score T history) := by
        funext history
        rw [expect_map]
        simp_rw [predictableScoreSum_snoc]
        rw [expect_add, expect_const]
      rw [Finset.sum_range_succ, ← ih, adaptiveHistoryLaw_succ, expect_bind, hstep,
        expect_add]

/-! ### The expected decision variation -/

/-- The **expected decision variation** up to horizon `T`: the expectation of the pathwise
decision variation `w̄_T = ∑_{k < T} |D_k|`, written as a sum of historywise conditional
mean absolute increments. -/
noncomputable def expectedDecisionVariation
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T,
    expect (adaptiveHistoryLaw step k)
      (fun history => expect (step k history) (fun ω => |score k history ω|))

omit [Finite Ω] in
/-- Each round contributes a nonnegative amount to the expected decision variation. -/
theorem expect_expect_abs_score_nonneg
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (k : ℕ) :
    0 ≤ expect (adaptiveHistoryLaw step k)
      (fun history => expect (step k history) (fun ω => |score k history ω|)) :=
  expect_nonneg _ _ fun _ => expect_nonneg _ _ fun _ => abs_nonneg _

omit [Finite Ω] in
/-- The expected decision variation is nonnegative. -/
theorem expectedDecisionVariation_nonneg
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (T : ℕ) :
    0 ≤ expectedDecisionVariation step score T :=
  Finset.sum_nonneg fun k _ => expect_expect_abs_score_nonneg step score k

omit [Finite Ω] in
/-- The expected decision variation is monotone in the horizon. -/
theorem expectedDecisionVariation_mono
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    {T T' : ℕ} (hle : T ≤ T') :
    expectedDecisionVariation step score T ≤ expectedDecisionVariation step score T' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun k _ _ => expect_expect_abs_score_nonneg step score k
  exact fun k hk => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hle)

/-- The expected decision variation really is `E[w̄_T]`: the expectation of the cumulative
absolute increment along a history. -/
theorem expectedDecisionVariation_eq_expect_predictableScoreSum_abs
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (T : ℕ) :
    expectedDecisionVariation step score T =
      expect (adaptiveHistoryLaw step T)
        (predictableScoreSum (fun n history ω => |score n history ω|) T) :=
  (expect_predictableScoreSum_eq_sum_expect_conditionalMean step
    (fun n history ω => |score n history ω|) T).symm

/-! ### Orthogonality of centered increments -/

/-- **Isometry.** For a centered predictable score the second moment of the cumulative score
is the sum over rounds of the expected historywise conditional second moments: the cross
terms vanish by `hcenter`. -/
theorem expect_predictableScoreSum_sq_eq_sum
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0) (T : ℕ) :
    expect (adaptiveHistoryLaw step T)
        (fun history => predictableScoreSum score T history ^ 2) =
      ∑ k ∈ Finset.range T,
        expect (adaptiveHistoryLaw step k)
          (fun history => expect (step k history) (fun ω => score k history ω ^ 2)) := by
  induction T with
  | zero => simp [adaptiveHistoryLaw, predictableScoreSum]
  | succ T ih =>
      have hstep : (fun history : Fin T → Ω =>
          expect ((step T history).map (Fin.snoc history))
            (fun path => predictableScoreSum score (T + 1) path ^ 2)) =
          fun history => predictableScoreSum score T history ^ 2 +
            expect (step T history) (fun ω => score T history ω ^ 2) := by
        funext history
        rw [expect_map]
        simp_rw [predictableScoreSum_snoc]
        have hexpand : ∀ x : Ω,
            (predictableScoreSum score T history + score T history x) ^ 2 =
              predictableScoreSum score T history ^ 2 +
                (2 * predictableScoreSum score T history * score T history x +
                  score T history x ^ 2) := fun x => by ring
        simp_rw [hexpand]
        rw [expect_add, expect_const, expect_add, expect_const_mul, hcenter T history,
          mul_zero, zero_add]
      rw [Finset.sum_range_succ, ← ih, adaptiveHistoryLaw_succ, expect_bind, hstep,
        expect_add]

/-! ### Running maxima and stopped scores -/

/-- The running maximum of a *readout* of the cumulative score:
`readRunningMax readout score n history` is `max_{m ≤ n} readout (S_m)` along the history.
The two readouts used below are `fun x => |x|` (two-sided) and `id` (one-sided); for both of
them the base value `0` is `readout (S_0)`. -/
noncomputable def readRunningMax (readout : ℝ → ℝ) (score : ∀ n, (Fin n → Ω) → Ω → ℝ) :
    (n : ℕ) → (Fin n → Ω) → ℝ
  | 0, _ => 0
  | n + 1, history =>
      max (readRunningMax readout score n (Fin.init history))
        (readout (predictableScoreSum score (n + 1) history))

omit [Finite Ω] in
/-- The empty history carries running maximum `0`. -/
@[simp] theorem readRunningMax_zero (readout : ℝ → ℝ) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (history : Fin 0 → Ω) : readRunningMax readout score 0 history = 0 := rfl

omit [Finite Ω] in
/-- One more step raises the running maximum to the readout of the new cumulative score. -/
theorem readRunningMax_succ (readout : ℝ → ℝ) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (n : ℕ) (history : Fin (n + 1) → Ω) :
    readRunningMax readout score (n + 1) history =
      max (readRunningMax readout score n (Fin.init history))
        (readout (predictableScoreSum score (n + 1) history)) := rfl

/-- `max_{0 ≤ m ≤ n} |S_m|` along a history. -/
noncomputable def scoreRunningMaxAbs (score : ∀ n, (Fin n → Ω) → Ω → ℝ) :
    (n : ℕ) → (Fin n → Ω) → ℝ :=
  readRunningMax (fun x => |x|) score

/-- `max_{0 ≤ m ≤ n} S_m` along a history; it is nonnegative because `S_0 = 0`. -/
noncomputable def scoreRunningMax (score : ∀ n, (Fin n → Ω) → Ω → ℝ) :
    (n : ℕ) → (Fin n → Ω) → ℝ :=
  readRunningMax id score

/-- The increment, switched off once the running maximum of the readout has reached `ε`.
The switch is history-measurable, so the stopped score is still predictable. -/
noncomputable def readStoppedScore (readout : ℝ → ℝ) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (ε : ℝ) : ∀ n, (Fin n → Ω) → Ω → ℝ :=
  fun n history ω =>
    if readRunningMax readout score n history < ε then score n history ω else 0

/-- The increment, switched off once `max_{m ≤ n} |S_m|` has reached `ε`. -/
noncomputable def stoppedScore (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (ε : ℝ) :
    ∀ n, (Fin n → Ω) → Ω → ℝ :=
  readStoppedScore (fun x => |x|) score ε

/-- The increment, switched off once `max_{m ≤ n} S_m` has reached `ε`. -/
noncomputable def oneSidedStoppedScore (score : ∀ n, (Fin n → Ω) → Ω → ℝ) (ε : ℝ) :
    ∀ n, (Fin n → Ω) → Ω → ℝ :=
  readStoppedScore id score ε

/-- Switching an integrand off on an event that does not depend on the sample preserves a
zero expectation. -/
theorem expect_ite_eq_zero {α : Type*} (d : PMF α) (f : α → ℝ) (p : Prop) [Decidable p]
    (hf : expect d f = 0) : expect d (fun ω => if p then f ω else 0) = 0 := by
  by_cases hp : p
  · simpa [hp] using hf
  · simp [hp]

/-- Switching a real number off never increases its absolute value. -/
theorem abs_ite_le_abs (p : Prop) [Decidable p] (x : ℝ) : |if p then x else 0| ≤ |x| := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]

omit [Finite Ω] in
/-- The stopped score is still centered: the switch is history-measurable. -/
theorem expect_readStoppedScore_eq_zero (readout : ℝ → ℝ)
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0) (ε : ℝ)
    (n : ℕ) (history : Fin n → Ω) :
    expect (step n history) (readStoppedScore readout score ε n history) = 0 :=
  expect_ite_eq_zero _ _ _ (hcenter n history)

omit [Finite Ω] in
/-- The stopped score is pointwise dominated by the raw score. -/
theorem abs_readStoppedScore_le (readout : ℝ → ℝ) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (ε : ℝ) (n : ℕ) (history : Fin n → Ω) (ω : Ω) :
    |readStoppedScore readout score ε n history ω| ≤ |score n history ω| :=
  abs_ite_le_abs _ _

omit [Finite Ω] in
/-- **First-crossing dichotomy.** Before the running maximum reaches `ε` the stopped sum
agrees with the raw sum; once the running maximum has reached `ε` the stopped sum has already
recorded a readout of size at least `ε`. The two halves are proved simultaneously because the
induction step of each uses the other. -/
theorem readStoppedScore_dichotomy (readout : ℝ → ℝ)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ (n : ℕ) (history : Fin n → Ω),
      (readRunningMax readout score n history < ε →
          predictableScoreSum (readStoppedScore readout score ε) n history =
            predictableScoreSum score n history) ∧
        (ε ≤ readRunningMax readout score n history →
          ε ≤ readout (predictableScoreSum (readStoppedScore readout score ε) n history)) := by
  intro n
  induction n with
  | zero =>
      intro history
      refine ⟨fun _ => rfl, fun hcross => ?_⟩
      rw [readRunningMax_zero] at hcross
      linarith
  | succ n ih =>
      intro history
      obtain ⟨ihagree, ihcross⟩ := ih (Fin.init history)
      have hmax : readRunningMax readout score (n + 1) history =
          max (readRunningMax readout score n (Fin.init history))
            (readout (predictableScoreSum score (n + 1) history)) := rfl
      have hraw : predictableScoreSum score (n + 1) history =
          predictableScoreSum score n (Fin.init history) +
            score n (Fin.init history) (history (Fin.last n)) := by
        rw [predictableScoreSum]
      have hstopped :
          predictableScoreSum (readStoppedScore readout score ε) (n + 1) history =
            predictableScoreSum (readStoppedScore readout score ε) n (Fin.init history) +
              readStoppedScore readout score ε n (Fin.init history)
                (history (Fin.last n)) := by
        rw [predictableScoreSum]
      by_cases hbefore : readRunningMax readout score n (Fin.init history) < ε
      · have hgate : readStoppedScore readout score ε n (Fin.init history)
            (history (Fin.last n)) = score n (Fin.init history) (history (Fin.last n)) :=
          if_pos hbefore
        have hagree :
            predictableScoreSum (readStoppedScore readout score ε) (n + 1) history =
              predictableScoreSum score (n + 1) history := by
          rw [hstopped, hgate, ihagree hbefore, hraw]
        refine ⟨fun _ => hagree, fun hcross => ?_⟩
        rw [hagree]
        rw [hmax] at hcross
        rcases le_max_iff.mp hcross with hle | hle
        · linarith
        · exact hle
      · have hgate : readStoppedScore readout score ε n (Fin.init history)
            (history (Fin.last n)) = 0 := if_neg hbefore
        have hfrozen :
            predictableScoreSum (readStoppedScore readout score ε) (n + 1) history =
              predictableScoreSum (readStoppedScore readout score ε) n (Fin.init history) := by
          rw [hstopped, hgate, add_zero]
        have hmono : readRunningMax readout score n (Fin.init history) ≤
            readRunningMax readout score (n + 1) history := by
          rw [hmax]
          exact le_max_left _ _
        refine ⟨fun hlt => absurd (lt_of_le_of_lt hmono hlt) hbefore, fun _ => ?_⟩
        rw [hfrozen]
        exact ihcross (not_lt.mp hbefore)

/-! ### The second moment of a stopped score -/

/-- A centered predictable score dominated by a δ-balanced score has second moment at most
`δ · E[w̄_T]`. This is the common engine of both maximal inequalities below. -/
theorem expect_predictableScoreSum_sq_le_mul_expectedDecisionVariation
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score minor : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (minor n history) = 0)
    (hdominated : ∀ n history ω, |minor n history ω| ≤ |score n history ω|)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbalanced : ∀ n history ω, |score n history ω| ≤ δ) (T : ℕ) :
    expect (adaptiveHistoryLaw step T)
        (fun history => predictableScoreSum minor T history ^ 2) ≤
      δ * expectedDecisionVariation step score T := by
  rw [expect_predictableScoreSum_sq_eq_sum step minor hcenter T, expectedDecisionVariation,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← expect_const_mul]
  refine expect_mono _ _ _ fun history => ?_
  rw [← expect_const_mul]
  refine expect_mono _ _ _ fun ω => ?_
  have h1 : |minor k history ω| ≤ |score k history ω| := hdominated k history ω
  have h2 : |score k history ω| ≤ δ := hbalanced k history ω
  calc minor k history ω ^ 2 = |minor k history ω| ^ 2 := (sq_abs _).symm
    _ = |minor k history ω| * |minor k history ω| := pow_two _
    _ ≤ δ * |score k history ω| := mul_le_mul (h1.trans h2) h1 (abs_nonneg _) hδ

/-! ### The two-sided maximal inequality -/

/-- **Weak-L² maximal inequality (Proposition 1).** For a centered, δ-balanced decision
process, `ε² · P(max_{m ≤ T} |S_m| ≥ ε) ≤ δ · E[w̄_T]`. -/
theorem sq_mul_expect_indicator_le_mul_expectedDecisionVariation
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hbalanced : ∀ n history ω, |score n history ω| ≤ δ)
    (hε : 0 < ε) (T : ℕ) :
    ε ^ 2 * expect (adaptiveHistoryLaw step T)
        (fun history => if ε ≤ scoreRunningMaxAbs score T history then 1 else 0) ≤
      δ * expectedDecisionVariation step score T := by
  have hpointwise : ∀ history : Fin T → Ω,
      ε ^ 2 * (if ε ≤ scoreRunningMaxAbs score T history then (1 : ℝ) else 0) ≤
        predictableScoreSum (stoppedScore score ε) T history ^ 2 := by
    intro history
    by_cases hcross : ε ≤ scoreRunningMaxAbs score T history
    · rw [if_pos hcross, mul_one]
      have hge : ε ≤ |predictableScoreSum (stoppedScore score ε) T history| :=
        (readStoppedScore_dichotomy (fun x => |x|) score hε T history).2 hcross
      calc ε ^ 2 = ε * ε := pow_two ε
        _ ≤ |predictableScoreSum (stoppedScore score ε) T history| *
              |predictableScoreSum (stoppedScore score ε) T history| :=
            mul_self_le_mul_self hε.le hge
        _ = |predictableScoreSum (stoppedScore score ε) T history| ^ 2 := (pow_two _).symm
        _ = predictableScoreSum (stoppedScore score ε) T history ^ 2 := sq_abs _
    · rw [if_neg hcross, mul_zero]
      exact sq_nonneg _
  calc ε ^ 2 * expect (adaptiveHistoryLaw step T)
          (fun history => if ε ≤ scoreRunningMaxAbs score T history then 1 else 0)
      = expect (adaptiveHistoryLaw step T)
          (fun history =>
            ε ^ 2 * (if ε ≤ scoreRunningMaxAbs score T history then (1 : ℝ) else 0)) :=
        (expect_const_mul _ _ _).symm
    _ ≤ expect (adaptiveHistoryLaw step T)
          (fun history => predictableScoreSum (stoppedScore score ε) T history ^ 2) :=
        expect_mono _ _ _ hpointwise
    _ ≤ δ * expectedDecisionVariation step score T :=
        expect_predictableScoreSum_sq_le_mul_expectedDecisionVariation step score
          (stoppedScore score ε)
          (fun n history =>
            expect_readStoppedScore_eq_zero (fun x => |x|) step score hcenter ε n history)
          (fun n history ω =>
            abs_readStoppedScore_le (fun x => |x|) score ε n history ω) hδ hbalanced T

/-- **Uniform-in-`T` maximal bound.** With a decision-variation budget `B` valid at every
horizon, `P(max_{m ≤ T} |S_m| ≥ ε) ≤ δ · B / ε²` uniformly in `T`. Letting `T → ∞` in this
bound gives `P(sup_m |S_m| ≥ ε) ≤ δ · E[w̄] / ε²` by continuity from below; that step is not
formalized here because the infinite path measure is not constructed in this repository. -/
theorem expect_indicator_le_div_of_expectedDecisionVariation_le
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0)
    {δ ε B : ℝ} (hδ : 0 ≤ δ) (hbalanced : ∀ n history ω, |score n history ω| ≤ δ)
    (hε : 0 < ε) (hbudget : ∀ T, expectedDecisionVariation step score T ≤ B) (T : ℕ) :
    expect (adaptiveHistoryLaw step T)
        (fun history => if ε ≤ scoreRunningMaxAbs score T history then 1 else 0) ≤
      δ * B / ε ^ 2 := by
  have hmain := sq_mul_expect_indicator_le_mul_expectedDecisionVariation step score hcenter
    hδ hbalanced hε T
  have hbud : δ * expectedDecisionVariation step score T ≤ δ * B :=
    mul_le_mul_of_nonneg_left (hbudget T) hδ
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  rw [le_div_iff₀ hε2]
  linarith

/-! ### The one-sided strengthening -/

/-- **Shifted second moment.** If `Z` is centered with second moment at most `V`, and `Z ≥ ε`
on an event `A`, then `(ε + a)² · P(A) ≤ V + a²` for every shift `a ≥ 0`. -/
theorem sq_add_mul_expect_indicator_le {ι : Type*} [Finite ι] (law : PMF ι) (Z : ι → ℝ)
    (A : ι → Prop) [DecidablePred A] {V ε a : ℝ}
    (hzero : expect law Z = 0) (hsecond : expect law (fun i => Z i ^ 2) ≤ V)
    (hge : ∀ i, A i → ε ≤ Z i) (hε : 0 ≤ ε) (ha : 0 ≤ a) :
    (ε + a) ^ 2 * expect law (fun i => if A i then 1 else 0) ≤ V + a ^ 2 := by
  have hpointwise : ∀ i, (ε + a) ^ 2 * (if A i then (1 : ℝ) else 0) ≤ (Z i + a) ^ 2 := by
    intro i
    by_cases hA : A i
    · rw [if_pos hA, mul_one]
      have hshift : ε + a ≤ Z i + a := by linarith [hge i hA]
      calc (ε + a) ^ 2 = (ε + a) * (ε + a) := pow_two _
        _ ≤ (Z i + a) * (Z i + a) := mul_self_le_mul_self (by linarith) hshift
        _ = (Z i + a) ^ 2 := (pow_two _).symm
    · rw [if_neg hA, mul_zero]
      exact sq_nonneg _
  have hexpand : ∀ i, (Z i + a) ^ 2 = Z i ^ 2 + (2 * a * Z i + a ^ 2) := fun i => by ring
  calc (ε + a) ^ 2 * expect law (fun i => if A i then (1 : ℝ) else 0)
      = expect law (fun i => (ε + a) ^ 2 * (if A i then (1 : ℝ) else 0)) :=
        (expect_const_mul _ _ _).symm
    _ ≤ expect law (fun i => (Z i + a) ^ 2) := expect_mono _ _ _ hpointwise
    _ = expect law (fun i => Z i ^ 2) + a ^ 2 := by
        simp_rw [hexpand]
        rw [expect_add, expect_add, expect_const, expect_const_mul, hzero, mul_zero, zero_add]
    _ ≤ V + a ^ 2 := by linarith

/-- Optimizing the shift in the Chebyshev–Cantelli bound: the family of bounds
`(ε + a)² P ≤ V + a²`, `a ≥ 0`, is strongest at `a = V / ε`, where it gives
`P ≤ V / (ε² + V)`. The degenerate case `V = 0` is covered by the shift `a = 0`. -/
theorem le_div_of_forall_sq_add_mul_le {P V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε)
    (h : ∀ a : ℝ, 0 ≤ a → (ε + a) ^ 2 * P ≤ V + a ^ 2) :
    P ≤ V / (ε ^ 2 + V) := by
  rcases eq_or_lt_of_le hV with rfl | hVpos
  · have h0 := h 0 le_rfl
    rw [zero_div]
    nlinarith [mul_pos hε hε]
  · have hεne : ε ≠ 0 := ne_of_gt hε
    obtain ⟨u, hupos, rfl⟩ : ∃ u : ℝ, 0 < u ∧ u * ε = V :=
      ⟨V / ε, div_pos hVpos hε, by field_simp⟩
    have hc : (0 : ℝ) < ε ^ 2 + u * ε := by nlinarith
    rw [le_div_iff₀ hc]
    have hk := h u hupos.le
    have hsum : (0 : ℝ) < ε + u := by linarith
    have hfactored : (ε + u) * ((ε + u) * P - u) ≤ 0 := by nlinarith
    have hcore : (ε + u) * P - u ≤ 0 :=
      le_of_mul_le_mul_left (by linarith) hsum
    nlinarith

/-- **One-sided maximal inequality.** For a centered, δ-balanced decision process and
`V = δ · E[w̄_T]`, the one-sided running maximum satisfies
`P(max_{m ≤ T} S_m ≥ ε) ≤ V / (ε² + V)`. This is strictly stronger than the two-sided bound
`V / ε²` of `sq_mul_expect_indicator_le_mul_expectedDecisionVariation`. -/
theorem expect_indicator_scoreRunningMax_le_div
    (step : ∀ n, (Fin n → Ω) → PMF Ω) (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (hcenter : ∀ n history, expect (step n history) (score n history) = 0)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hbalanced : ∀ n history ω, |score n history ω| ≤ δ)
    (hε : 0 < ε) (T : ℕ) :
    expect (adaptiveHistoryLaw step T)
        (fun history => if ε ≤ scoreRunningMax score T history then 1 else 0) ≤
      δ * expectedDecisionVariation step score T /
        (ε ^ 2 + δ * expectedDecisionVariation step score T) := by
  have hstoppedCentered : ∀ n (history : Fin n → Ω),
      expect (step n history) (oneSidedStoppedScore score ε n history) = 0 :=
    fun n history => expect_readStoppedScore_eq_zero id step score hcenter ε n history
  have hzero : expect (adaptiveHistoryLaw step T)
      (predictableScoreSum (oneSidedStoppedScore score ε) T) = 0 :=
    expect_predictableScoreSum_eq_zero step (oneSidedStoppedScore score ε) hstoppedCentered T
  have hsecond : expect (adaptiveHistoryLaw step T)
      (fun history => predictableScoreSum (oneSidedStoppedScore score ε) T history ^ 2) ≤
        δ * expectedDecisionVariation step score T :=
    expect_predictableScoreSum_sq_le_mul_expectedDecisionVariation step score
      (oneSidedStoppedScore score ε) hstoppedCentered
      (fun n history ω => abs_readStoppedScore_le id score ε n history ω) hδ hbalanced T
  have hge : ∀ history : Fin T → Ω, ε ≤ scoreRunningMax score T history →
      ε ≤ predictableScoreSum (oneSidedStoppedScore score ε) T history :=
    fun history hcross =>
      (readStoppedScore_dichotomy id score hε T history).2 hcross
  refine le_div_of_forall_sq_add_mul_le
    (mul_nonneg hδ (expectedDecisionVariation_nonneg step score T)) hε fun a ha => ?_
  exact sq_add_mul_expect_indicator_le (adaptiveHistoryLaw step T)
    (predictableScoreSum (oneSidedStoppedScore score ε) T)
    (fun history => ε ≤ scoreRunningMax score T history) hzero hsecond hge hε.le ha

end

end Math.Probability
