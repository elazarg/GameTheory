/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityHolonomy
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffineIteration

/-!
# Nonempty repetition of complete quitting holonomy

This module lifts affine and max-affine repetition to the common playerwise
holonomy.  A strategically self-similar block remains self-similar under every
finite nonempty repetition.
-/

noncomputable section

namespace GameTheory
namespace QuittingBoundaryHolonomy

/-- `extra + 1` chronological copies of one complete holonomy. -/
def selfComposeNonempty
    (holonomy : QuittingBoundaryHolonomy ι) : ℕ →
      QuittingBoundaryHolonomy ι
  | 0 => holonomy
  | extra + 1 => holonomy * holonomy.selfComposeNonempty extra

@[simp] theorem selfComposeNonempty_zero
    (holonomy : QuittingBoundaryHolonomy ι) :
    holonomy.selfComposeNonempty 0 = holonomy := rfl

@[simp] theorem selfComposeNonempty_succ
    (holonomy : QuittingBoundaryHolonomy ι) (extra : ℕ) :
    holonomy.selfComposeNonempty (extra + 1) =
      holonomy * holonomy.selfComposeNonempty extra := rfl

/-- The prescribed component is the ordinary affine self-composition with one
more copy than `extra`. -/
theorem prescribed_selfComposeNonempty
    (holonomy : QuittingBoundaryHolonomy ι) (extra : ℕ) (who : ι) :
    (holonomy.selfComposeNonempty extra).prescribed who =
      (holonomy.prescribed who).selfCompose (extra + 1) := by
  induction extra with
  | zero =>
      simp [QuittingAffineSummary.selfCompose]
  | succ extra ih =>
      rw [selfComposeNonempty_succ, prescribed_mul, ih,
        QuittingAffineSummary.selfCompose_succ]

/-- The unilateral component is the corresponding nonempty max-affine
self-composition. -/
theorem bestResponse_selfComposeNonempty
    (holonomy : QuittingBoundaryHolonomy ι) (extra : ℕ) (who : ι) :
    (holonomy.selfComposeNonempty extra).bestResponse who =
      (holonomy.bestResponse who).selfComposeNonempty extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [selfComposeNonempty_succ, bestResponse_mul, ih,
        QuittingMaxAffineSummary.selfComposeNonempty_succ]

/-- Strategic self-similarity is stable under every finite nonempty
repetition. -/
theorem IsSelfSimilarAt.selfComposeNonempty
    {holonomy : QuittingBoundaryHolonomy ι} {target : Payoff ι}
    (hself : holonomy.IsSelfSimilarAt target) :
    ∀ extra, (holonomy.selfComposeNonempty extra).IsSelfSimilarAt target := by
  intro extra
  induction extra with
  | zero => exact hself
  | succ extra ih =>
      rw [selfComposeNonempty_succ]
      exact hself.mul ih

/-- Every repeated self-similar holonomy has nonpositive zero-relative-debt
gap. -/
theorem IsSelfSimilarAt.gap_selfComposeNonempty_nonpos
    {holonomy : QuittingBoundaryHolonomy ι} {target : Payoff ι}
    (hself : holonomy.IsSelfSimilarAt target)
    (extra : ℕ) (who : ι) :
    (holonomy.selfComposeNonempty extra).gap who 0 (target who) ≤ 0 :=
  (hself.selfComposeNonempty extra).gap_nonpos who

/-- A coefficient-idempotent complete holonomy is unchanged by every nonempty
repetition. -/
theorem selfComposeNonempty_eq_of_isIdempotent
    {holonomy : QuittingBoundaryHolonomy ι}
    (hidempotent : holonomy.IsIdempotent) :
    ∀ extra, holonomy.selfComposeNonempty extra = holonomy := by
  intro extra
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [selfComposeNonempty_succ, ih]
      exact hidempotent

end QuittingBoundaryHolonomy
end GameTheory
