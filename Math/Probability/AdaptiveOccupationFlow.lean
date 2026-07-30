/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.Adaptive
import Math.Probability.AnalyticOccupationFlow
import Math.Probability.MarkovOccupation

/-!
# Adaptive use budgets from occupation separators

A bounded potential which has nonnegative drift under every available
transition and drift at least `eta > 0` under one distinguished transition
gives an expected-use budget for that transition. The transition selected at
each step may depend on the complete finite state history.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

/-- The accumulated state charge of the zero function is zero. -/
@[simp]
theorem markovHistoryStateChargeSum_zero_function
    (T : ℕ) (history : Fin (T + 1) → S) :
    markovHistoryStateChargeSum (fun _ => (0 : ℝ)) T history = 0 := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [← Fin.snoc_init_self history,
        markovHistoryStateChargeSum_snoc, ih]
      simp

/-- Number of uses of a distinguished transition during the transitions of
a finite state history. The choice at step `n` sees the first `n + 1`
states, before the next state is sampled. -/
def selectedTransitionUseCount
    [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I) (i₀ : I) :
    ∀ T, (Fin (T + 1) → S) → ℝ
  | 0, _ => 0
  | T + 1, history =>
      selectedTransitionUseCount choice i₀ T (Fin.init history) +
        if choice T (Fin.init history) = i₀ then 1 else 0

@[simp]
theorem selectedTransitionUseCount_zero
    [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I) (i₀ : I)
    (history : Fin 1 → S) :
    selectedTransitionUseCount choice i₀ 0 history = 0 := rfl

@[simp]
theorem selectedTransitionUseCount_snoc
    [DecidableEq I]
    (choice : ∀ n, (Fin (n + 1) → S) → I) (i₀ : I)
    (T : ℕ) (history : Fin (T + 1) → S) (successor : S) :
    selectedTransitionUseCount choice i₀ (T + 1)
        (Fin.snoc history successor) =
      selectedTransitionUseCount choice i₀ T history +
        if choice T history = i₀ then 1 else 0 := by
  simp [selectedTransitionUseCount]

/-- Adaptive comparison law obtained by applying the history-selected
transition kernel. -/
def selectedTransitionComparison
    (kernel : I → PMF S)
    (choice : ∀ n, (Fin (n + 1) → S) → I) :
    ∀ n, (Fin (n + 1) → S) → PMF S :=
  fun n history => kernel (choice n history)

/-- Every finite-history conditional-mean sum pays `eta` for each use of
the distinguished transition. -/
theorem selectedTransitionUseCount_mul_margin_le_conditionalMeanSum
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (i₀ : I) (potential : S → ℝ) {eta : ℝ}
    (hsource :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      eta ≤ expect (kernel i₀) potential - potential (source i₀))
    (T : ℕ) (history : Fin (T + 1) → S) :
    eta * selectedTransitionUseCount choice i₀ T history ≤
      predictableConditionalMeanSum
        (adaptiveMarkovStep initial
          (selectedTransitionComparison kernel choice))
        (adaptiveMarkovDiscrepancyScore
          (fun s => PMF.pure s) potential)
        (T + 1) history := by
  induction T with
  | zero =>
      simp [predictableConditionalMeanSum,
        adaptiveMarkovDiscrepancyScore]
  | succ T ih =>
      rw [← Fin.snoc_init_self history]
      simp only [selectedTransitionUseCount_snoc,
        predictableConditionalMeanSum_snoc]
      have hprevious := ih (Fin.init history)
      let chosen := choice T (Fin.init history)
      have hmean :
          expect
              (adaptiveMarkovStep initial
                (selectedTransitionComparison kernel choice)
                (T + 1) (Fin.init history))
              (adaptiveMarkovDiscrepancyScore
                (fun s => PMF.pure s) potential
                (T + 1) (Fin.init history)) =
            expect (kernel chosen) potential -
              potential (source chosen) := by
        rw [expect_adaptiveMarkovDiscrepancyScore_succ]
        simp only [selectedTransitionComparison, expect_pure]
        rw [hsource T (Fin.init history)]
      rw [hmean]
      by_cases hchosen : chosen = i₀
      · have hstep :
            eta ≤
              expect (kernel chosen) potential -
                potential (source chosen) := by
          simpa [hchosen] using hmargin
        simp only [chosen, hchosen, if_true]
        linarith
      · have hstep :
            0 ≤
              expect (kernel chosen) potential -
                potential (source chosen) :=
          hdrift chosen
        simp only [chosen, hchosen, if_false, add_zero]
        linarith

/-- Under arbitrary history-dependent switching among source-compatible
available kernels, a `[0,1]`-valued separator permits at most `1 / eta`
expected uses of the distinguished transition. The division-free form is
stated to avoid an unnecessary normalization step. -/
theorem margin_mul_expect_selectedTransitionUseCount_le_one
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (i₀ : I) (potential : S → ℝ) {eta : ℝ}
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      eta ≤ expect (kernel i₀) potential - potential (source i₀))
    (T : ℕ) :
    eta *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison kernel choice))
            (T + 1))
          (selectedTransitionUseCount choice i₀ T) ≤
      1 := by
  let comparison := selectedTransitionComparison kernel choice
  let step := adaptiveMarkovStep initial comparison
  let score :=
    adaptiveMarkovDiscrepancyScore
      (fun s => PMF.pure s) potential
  let law := adaptiveHistoryLaw step (T + 1)
  have hcount :
      expect law
          (fun history =>
            eta *
              selectedTransitionUseCount choice i₀ T history) ≤
        expect law
          (predictableConditionalMeanSum step score (T + 1)) := by
    apply expect_mono
    intro history
    exact
      selectedTransitionUseCount_mul_margin_le_conditionalMeanSum
        initial kernel source choice i₀ potential hsource hdrift
        hmargin T history
  have hcompensator :
      expect law
          (predictableConditionalMeanSum step score (T + 1)) =
        expect law (predictableScoreSum score (T + 1)) := by
    symm
    exact
      expect_predictableScoreSum_eq_expect_conditionalMeanSum
        step score (T + 1)
  have hscore :
      expect law (predictableScoreSum score (T + 1)) ≤ 1 := by
    calc
      expect law (predictableScoreSum score (T + 1)) ≤
          expect law (fun _ => (1 : ℝ)) := by
        apply expect_mono
        intro history
        have htelescope :=
          markovHistoryStateChargeSum_eq_potential_sub_add_score
            (fun s => PMF.pure s) potential (fun _ => 0)
            (fun s => by rw [expect_pure, sub_self]) T history
        have hfirst : 0 ≤ potential (history 0) :=
          (hpotential (history 0)).1
        have hlast : potential (history (Fin.last T)) ≤ 1 :=
          (hpotential (history (Fin.last T))).2
        rw [markovHistoryStateChargeSum_zero_function] at htelescope
        change
          predictableScoreSum
              (adaptiveMarkovDiscrepancyScore
                (fun s => PMF.pure s) potential)
              (T + 1) history ≤
            1
        linarith
      _ = 1 := expect_const _ _
  calc
    eta *
        expect law
          (selectedTransitionUseCount choice i₀ T) =
        expect law
          (fun history =>
            eta *
              selectedTransitionUseCount choice i₀ T history) := by
      symm
      exact expect_const_mul law eta _
    _ ≤
        expect law
          (predictableConditionalMeanSum step score (T + 1)) :=
      hcount
    _ =
        expect law (predictableScoreSum score (T + 1)) :=
      hcompensator
    _ ≤ 1 := hscore

end Probability
end Math
