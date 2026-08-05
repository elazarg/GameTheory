/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AdaptiveTransitionAccount

/-!
# Potentials pay dominated predictable transition costs

A fixed state potential pays every predictable, source-compatible mixed
transition cost which is pointwise dominated by its transition drift.  The
resulting bound is independent of both the horizon and the selector.
-/

noncomputable section

open Filter Set Topology

namespace Math
namespace Probability

variable {S I : Type*}

/-- A fixed potential pays every predictable source-compatible mixed cost
which is pointwise dominated by its transition drift.  The bound is
independent of the horizon and of the selector. -/
theorem expected_mixedTransitionCostSum_le_two_potentialBound
    [Fintype S] [Finite I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (potential : S → ℝ)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          source index = history (Fin.last n))
    (cost : I → ℝ)
    (cost_le_drift :
      ∀ index,
        cost index ≤
          transitionPotentialDrift kernel source potential index)
    (T : ℕ) :
    expect
        (adaptiveHistoryLaw
          (adaptiveMarkovStep initial
            (mixedTransitionComparison kernel selection))
          (T + 1))
        (mixedTransitionCostSum selection cost T) ≤
      2 * finiteStatePotentialBound potential := by
  let comparison := mixedTransitionComparison kernel selection
  let step := adaptiveMarkovStep initial comparison
  let score :=
    adaptiveMixedTransitionCenteredScore kernel potential selection
  let law := adaptiveHistoryLaw step (T + 1)
  have hcost :
      expect law (mixedTransitionCostSum selection cost T) ≤
        expect law
          (mixedTransitionCostSum selection
            (transitionPotentialDrift kernel source potential) T) := by
    apply expect_mono
    intro history
    exact mixedTransitionCostSum_mono
      selection cost_le_drift T history
  have hcenter :
      ∀ n history,
        expect (step n history) (score n history) = 0 := by
    intro n history
    cases n with
    | zero =>
        simp [step, score]
    | succ n =>
        simpa [step, comparison, score] using
          expect_adaptiveMixedTransitionCenteredScore_succ
            kernel potential selection n history
  have hscore_zero :
      expect law (predictableScoreSum score (T + 1)) = 0 :=
    expect_predictableScoreSum_eq_zero step score hcenter (T + 1)
  have haccount :
      expect law
          (mixedTransitionCostSum selection
            (transitionPotentialDrift kernel source potential) T) =
        expect law
          (fun history =>
            potential (history (Fin.last T)) -
              potential (history 0)) := by
    calc
      expect law
          (mixedTransitionCostSum selection
            (transitionPotentialDrift kernel source potential) T) =
          expect law (predictableScoreSum score (T + 1)) +
            expect law
              (mixedTransitionCostSum selection
                (transitionPotentialDrift kernel source potential) T) := by
            rw [hscore_zero, zero_add]
      _ =
          expect law
            (fun history =>
              predictableScoreSum score (T + 1) history +
                mixedTransitionCostSum selection
                  (transitionPotentialDrift
                    kernel source potential) T history) := by
            rw [expect_add]
      _ =
          expect law
            (fun history =>
              potential (history (Fin.last T)) -
                potential (history 0)) := by
            apply congrArg
            funext history
            exact mixedTransitionCenteredScore_add_drift_eq_accountIncrement
              kernel source potential selection source_compatible T history
  calc
    expect law (mixedTransitionCostSum selection cost T) ≤
        expect law
          (mixedTransitionCostSum selection
            (transitionPotentialDrift kernel source potential) T) :=
      hcost
    _ =
        expect law
          (fun history =>
            potential (history (Fin.last T)) -
              potential (history 0)) := haccount
    _ ≤ expect law (fun _ =>
          2 * finiteStatePotentialBound potential) := by
      apply expect_mono
      intro history
      have hlast :
          |potential (history (Fin.last T))| ≤
            finiteStatePotentialBound potential := by
        simpa [statePotentialAccount] using
          abs_statePotentialAccount_le_finiteStatePotentialBound
            potential (fun _ => history (Fin.last T)) 0
      have hfirst :
          |potential (history 0)| ≤
            finiteStatePotentialBound potential := by
        simpa [statePotentialAccount] using
          abs_statePotentialAccount_le_finiteStatePotentialBound
            potential (fun _ => history 0) 0
      calc
        potential (history (Fin.last T)) -
            potential (history 0) ≤
            |potential (history (Fin.last T)) -
              potential (history 0)| := le_abs_self _
        _ ≤ |potential (history (Fin.last T))| +
              |potential (history 0)| := abs_sub _ _
        _ ≤ finiteStatePotentialBound potential +
              finiteStatePotentialBound potential :=
          add_le_add hlast hfirst
        _ = 2 * finiteStatePotentialBound potential := by ring
    _ = 2 * finiteStatePotentialBound potential := by rw [expect_const]

end Probability
end Math
