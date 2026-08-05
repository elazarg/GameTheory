/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.Adaptive
import Math.Probability.CoreShadowCompiler

/-!
# Predictable finite-history core shadows

This file recursively assembles one-step maximal fiber couplings on the
finite history tree.  The controlled kernel may depend on the complete
full-state history.  The legal core family and its selected mixture weights
may depend on the complete core history.  Their maximal fiber coupling is
therefore predictable from the joint history.

The resulting joint history law has exactly the prescribed controlled and
legal history marginals.  Its expected accumulated projection mismatch is
bounded by the sum of the one-step total-variation tolerances.  A final
interface theorem converts any one-step comparison dominated by mismatch
plus an implementation error into a finite-horizon continuation bound.

The construction does not assert that the chosen legal core continuation is
the strategically correct continuation after entering a recurrent core
component.  That core-entry compatibility is a separate game-theoretic
interface condition.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace Probability

variable {S R L : Type*}

/-- Apply a state map pointwise to a finite history. -/
def mapFiniteHistory (f : S → R) {n : ℕ}
    (history : Fin n → S) : Fin n → R :=
  f ∘ history

@[simp]
theorem mapFiniteHistory_apply (f : S → R) {n : ℕ}
    (history : Fin n → S) (i : Fin n) :
    mapFiniteHistory f history i = f (history i) :=
  rfl

theorem mapFiniteHistory_snoc (f : S → R) {n : ℕ}
    (history : Fin n → S) (x : S) :
    mapFiniteHistory f (Fin.snoc history x) =
      Fin.snoc (mapFiniteHistory f history) (f x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mapFiniteHistory]
  · simp [mapFiniteHistory]

/-- Adaptive history laws commute with a pointwise state map whenever the
one-step kernels do. -/
theorem adaptiveHistoryLaw_map
    [Finite S] [Finite R]
    (f : S → R)
    (stepS : ∀ n, (Fin n → S) → PMF S)
    (stepR : ∀ n, (Fin n → R) → PMF R)
    (hstep :
      ∀ n history,
        (stepS n history).map f =
          stepR n (mapFiniteHistory f history))
    (T : ℕ) :
    (adaptiveHistoryLaw stepS T).map (mapFiniteHistory f) =
      adaptiveHistoryLaw stepR T := by
  induction T with
  | zero =>
      rw [adaptiveHistoryLaw_zero, adaptiveHistoryLaw_zero, PMF.pure_map]
      congr
      funext i
      exact Fin.elim0 i
  | succ T ih =>
      rw [adaptiveHistoryLaw_succ, adaptiveHistoryLaw_succ, PMF.map_bind]
      calc
        (adaptiveHistoryLaw stepS T).bind
            (fun history =>
              ((stepS T history).map (Fin.snoc history)).map
                (mapFiniteHistory f)) =
            (adaptiveHistoryLaw stepS T).bind
              (fun history =>
                (stepR T (mapFiniteHistory f history)).map
                  (Fin.snoc (mapFiniteHistory f history))) := by
            apply ProbabilityMassFunction.bind_congr_on_support
            intro history _
            rw [PMF.map_comp]
            have hfun :
                mapFiniteHistory f ∘ Fin.snoc history =
                  (fun r : R =>
                    Fin.snoc
                      (α := fun _ : Fin (T + 1) => R)
                      (mapFiniteHistory f history) r) ∘ f := by
              funext x
              exact mapFiniteHistory_snoc f history x
            rw [hfun]
            have hmap :=
              congrArg
                (fun μ : PMF R =>
                  μ.map (fun r : R =>
                    Fin.snoc
                      (α := fun _ : Fin (T + 1) => R)
                      (mapFiniteHistory f history) r))
                (hstep T history)
            rw [PMF.map_comp] at hmap
            exact hmap
        _ =
            ((adaptiveHistoryLaw stepS T).map
              (mapFiniteHistory f)).bind
              (fun history =>
                (stepR T history).map (Fin.snoc history)) := by
            symm
            rw [PMF.bind_map]
            rfl
        _ = adaptiveHistoryLaw stepR (T + 1) := by
            rw [ih]
            rfl

/-- The legal core kernel selected predictably from a core history. -/
noncomputable def selectedLegalCoreStep
    [Fintype L]
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L) :
    ∀ n, (Fin n → R) → PMF R :=
  fun n history =>
    legalMixture (legal n history) (weights n history)

/-- The predictable joint step obtained by maximally coupling the projected
controlled law with the selected legal core law. -/
noncomputable def predictableCoreShadowStep
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L) :
    ∀ n, (Fin n → S × R) → PMF (S × R) :=
  fun n history =>
    maximalFiberCoupling
        (controlled n (mapFiniteHistory Prod.fst history))
        π
        (selectedLegalCoreStep legal weights n
          (mapFiniteHistory Prod.snd history))

theorem predictableCoreShadowStep_map_fst
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (n : ℕ) (history : Fin n → S × R) :
    (predictableCoreShadowStep π controlled legal weights n history).map
        Prod.fst =
      controlled n (mapFiniteHistory Prod.fst history) :=
  maximalFiberCoupling_map_fst _ _ _

theorem predictableCoreShadowStep_map_snd
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (n : ℕ) (history : Fin n → S × R) :
    (predictableCoreShadowStep π controlled legal weights n history).map
        Prod.snd =
      selectedLegalCoreStep legal weights n
        (mapFiniteHistory Prod.snd history) :=
  maximalFiberCoupling_map_snd _ _ _

/-- The first trajectory marginal of the recursively assembled shadow is the
prescribed adaptive controlled history law. -/
theorem adaptiveHistoryLaw_predictableCoreShadow_map_fst
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (T : ℕ) :
    (adaptiveHistoryLaw
        (predictableCoreShadowStep π controlled legal weights) T).map
        (mapFiniteHistory Prod.fst) =
      adaptiveHistoryLaw controlled T := by
  apply adaptiveHistoryLaw_map
  exact predictableCoreShadowStep_map_fst π controlled legal weights

/-- The second trajectory marginal is exactly the adaptive legal core
history law selected by `weights`. -/
theorem adaptiveHistoryLaw_predictableCoreShadow_map_snd
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (T : ℕ) :
    (adaptiveHistoryLaw
        (predictableCoreShadowStep π controlled legal weights) T).map
        (mapFiniteHistory Prod.snd) =
      adaptiveHistoryLaw (selectedLegalCoreStep legal weights) T := by
  apply adaptiveHistoryLaw_map
  exact predictableCoreShadowStep_map_snd π controlled legal weights

/-- One-step projection mismatch indicator. -/
noncomputable def projectionMismatchScore (π : S → R) :
    ∀ n, (Fin n → S × R) → S × R → ℝ :=
  by
    classical
    exact fun _ _ next => if π next.1 ≠ next.2 then 1 else 0

/-- The conditional mismatch probability of the predictable joint step is
exactly the total variation distance between its two projected laws. -/
theorem expect_predictableCoreShadow_projectionMismatchScore
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (n : ℕ) (history : Fin n → S × R) :
    expect
        (predictableCoreShadowStep π controlled legal weights n history)
        (projectionMismatchScore π n history) =
      pmfTV
        ((controlled n
          (mapFiniteHistory Prod.fst history)).map π)
        (selectedLegalCoreStep legal weights n
          (mapFiniteHistory Prod.snd history)) := by
  simp only [predictableCoreShadowStep]
  change
    projectionMismatchProbability π
        (maximalFiberCoupling
          (controlled n (mapFiniteHistory Prod.fst history))
          π
          (selectedLegalCoreStep legal weights n
            (mapFiniteHistory Prod.snd history))) =
      pmfTV
        ((controlled n
          (mapFiniteHistory Prod.fst history)).map π)
        (selectedLegalCoreStep legal weights n
          (mapFiniteHistory Prod.snd history))
  exact maximalFiberCoupling_mismatchProbability _ _ _

/-- A deterministic bound on every one-step conditional mean bounds the
entire compensator along every finite history. -/
theorem predictableConditionalMeanSum_le_sum
    {Ω : Type*} [Finite Ω]
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (budget : ℕ → ℝ)
    (hbudget :
      ∀ n history, expect (step n history) (score n history) ≤ budget n)
    (T : ℕ) (history : Fin T → Ω) :
    predictableConditionalMeanSum step score T history ≤
      ∑ n ∈ Finset.range T, budget n := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [predictableConditionalMeanSum, Finset.sum_range_succ]
      exact add_le_add (ih (Fin.init history)) (hbudget T (Fin.init history))

/-- Expected cumulative predictable cost is bounded by the sum of uniform
one-step conditional-mean budgets. -/
theorem expect_predictableScoreSum_le_sum
    {Ω : Type*} [Finite Ω]
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (budget : ℕ → ℝ)
    (hbudget :
      ∀ n history, expect (step n history) (score n history) ≤ budget n)
    (T : ℕ) :
    expect (adaptiveHistoryLaw step T) (predictableScoreSum score T) ≤
      ∑ n ∈ Finset.range T, budget n := by
  rw [expect_predictableScoreSum_eq_expect_conditionalMeanSum]
  calc
    expect (adaptiveHistoryLaw step T)
          (predictableConditionalMeanSum step score T) ≤
        expect (adaptiveHistoryLaw step T)
          (fun _ => ∑ n ∈ Finset.range T, budget n) :=
      expect_mono _ _ _ fun history =>
        predictableConditionalMeanSum_le_sum
          step score budget hbudget T history
    _ = ∑ n ∈ Finset.range T, budget n := by
      rw [expect_const]

/-- The expected accumulated projection mismatch is at most the sum of the
one-step total-variation tolerances. -/
theorem expect_projectionMismatchSum_le
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (tolerance : ℕ → ℝ)
    (hclose :
      ∀ n history,
        pmfTV
            ((controlled n
              (mapFiniteHistory Prod.fst history)).map π)
            (selectedLegalCoreStep legal weights n
              (mapFiniteHistory Prod.snd history)) ≤
          tolerance n)
    (T : ℕ) :
    expect
        (adaptiveHistoryLaw
          (predictableCoreShadowStep π controlled legal weights) T)
        (predictableScoreSum (projectionMismatchScore π) T) ≤
      ∑ n ∈ Finset.range T, tolerance n := by
  apply expect_predictableScoreSum_le_sum
  intro n history
  rw [expect_predictableCoreShadow_projectionMismatchScore]
  exact hclose n history

/-- Interface-ready continuation comparison.

Any predictable one-step comparison cost dominated by `L` times the
projection mismatch plus an implementation error inherits the corresponding
finite-horizon expected bound. -/
theorem expect_interfaceScoreSum_le
    [Finite S] [Fintype R] [Fintype L]
    (π : S → R)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (legal : ∀ n, (Fin n → R) → L → PMF R)
    (weights : ∀ n, (Fin n → R) → stdSimplex ℝ L)
    (tolerance implementationError : ℕ → ℝ)
    (interfaceScore :
      ∀ n, (Fin n → S × R) → S × R → ℝ)
    (Lipschitz : ℝ) (hLipschitz : 0 ≤ Lipschitz)
    (hclose :
      ∀ n history,
        pmfTV
            ((controlled n
              (mapFiniteHistory Prod.fst history)).map π)
            (selectedLegalCoreStep legal weights n
              (mapFiniteHistory Prod.snd history)) ≤
          tolerance n)
    (hinterface :
      ∀ n history next,
        interfaceScore n history next ≤
          Lipschitz * projectionMismatchScore π n history next +
            implementationError n)
    (T : ℕ) :
    expect
        (adaptiveHistoryLaw
          (predictableCoreShadowStep π controlled legal weights) T)
        (predictableScoreSum interfaceScore T) ≤
      ∑ n ∈ Finset.range T,
        (Lipschitz * tolerance n + implementationError n) := by
  apply expect_predictableScoreSum_le_sum
  intro n history
  let step :=
    predictableCoreShadowStep π controlled legal weights n history
  calc
    expect step (interfaceScore n history) ≤
        expect step
          (fun next =>
            Lipschitz * projectionMismatchScore π n history next +
              implementationError n) :=
      expect_mono _ _ _ (hinterface n history)
    _ =
        Lipschitz *
            expect step (projectionMismatchScore π n history) +
          implementationError n := by
      rw [expect_add, expect_const_mul, expect_const]
    _ ≤
        Lipschitz * tolerance n + implementationError n := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hLipschitz
        rw [expect_predictableCoreShadow_projectionMismatchScore]
        exact hclose n history
      · exact le_rfl

end Probability
end Math
