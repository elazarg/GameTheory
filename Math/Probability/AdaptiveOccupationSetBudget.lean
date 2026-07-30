/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AdaptiveOccupationFlow

/-!
# Adaptive occupation budgets for a finite set of transitions

The one-column occupation bounds in `AdaptiveOccupationFlow` aggregate over
any finite family on which one common positive drift margin is available.
The resulting constant is the cardinality of the family.  This deliberately
coarse bound is enough to show that the total expected use, or total
predictable mixed mass, of every strictly separated transition is uniformly
bounded in the horizon.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

variable {S I : Type*}

/-- A common positive drift margin on a finite transition set gives a
horizon-uniform bound for the sum of the expected pure use counts. -/
theorem margin_mul_expect_transitionSetUseCount_le_card
    [Finite S] [DecidableEq I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (choice : ∀ n, (Fin (n + 1) → S) → I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history,
        source (choice n history) = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i))
    (T : ℕ) :
    eta *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison kernel choice))
            (T + 1))
          (fun history =>
            ∑ i : {i // i ∈ active},
              selectedTransitionUseCount choice i.1 T history) ≤
      active.card := by
  let law :=
    adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (selectedTransitionComparison kernel choice))
      (T + 1)
  have hcoordinate :
      ∀ i : {i // i ∈ active},
        eta *
            expect law
              (selectedTransitionUseCount choice i.1 T) ≤
          1 := by
    intro i
    exact margin_mul_expect_selectedTransitionUseCount_le_one
      initial kernel source choice i.1 potential hpotential hsource
      hdrift (hmargin i.1 i.2) T
  calc
    eta *
        expect law
          (fun history =>
            ∑ i : {i // i ∈ active},
              selectedTransitionUseCount choice i.1 T history) =
        ∑ i : {i // i ∈ active},
          eta *
            expect law
              (selectedTransitionUseCount choice i.1 T) := by
      rw [← expect_sum_comm]
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : {i // i ∈ active}, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => hcoordinate i
    _ = active.card := by simp

/-- A common positive drift margin on a finite transition set gives a
horizon-uniform bound for the sum of its expected predictable mixed masses. -/
theorem margin_mul_expect_transitionSetMassSum_le_card
    [Finite S] [Finite I]
    (initial : S) (kernel : I → PMF S) (source : I → S)
    (selection : ∀ n, (Fin (n + 1) → S) → PMF I)
    (active : Finset I) (potential : S → ℝ) {eta : ℝ}
    (hpotential :
      ∀ s, 0 ≤ potential s ∧ potential s ≤ 1)
    (hsource :
      ∀ n history i,
        selection n history i ≠ 0 →
          source i = history (Fin.last n))
    (hdrift :
      ∀ i,
        0 ≤ expect (kernel i) potential - potential (source i))
    (hmargin :
      ∀ i ∈ active,
        eta ≤ expect (kernel i) potential - potential (source i))
    (T : ℕ) :
    eta *
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison kernel selection))
            (T + 1))
          (fun history =>
            ∑ i : {i // i ∈ active},
              selectedTransitionMassSum selection i.1 T history) ≤
      active.card := by
  let law :=
    adaptiveHistoryLaw
      (adaptiveMarkovStep initial
        (mixedTransitionComparison kernel selection))
      (T + 1)
  have hcoordinate :
      ∀ i : {i // i ∈ active},
        eta *
            expect law
              (selectedTransitionMassSum selection i.1 T) ≤
          1 := by
    intro i
    exact margin_mul_expect_selectedTransitionMassSum_le_one
      initial kernel source selection i.1 potential hpotential hsource
      hdrift (hmargin i.1 i.2) T
  calc
    eta *
        expect law
          (fun history =>
            ∑ i : {i // i ∈ active},
              selectedTransitionMassSum selection i.1 T history) =
        ∑ i : {i // i ∈ active},
          eta *
            expect law
              (selectedTransitionMassSum selection i.1 T) := by
      rw [← expect_sum_comm]
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : {i // i ∈ active}, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => hcoordinate i
    _ = active.card := by simp

end Probability
end Math
