/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingBoundaryHolonomyMaxAffineResidual

/-!
# Playerwise self-similarity of complete quitting holonomy

The complete holonomy combines prescribed affine transport and every player's
max-affine unilateral stopping value.  Exact self-similarity at a target means
that prescribed play reproduces the target and unilateral stopping is capped
there.  The property is semialgebraic and closed under chronological
composition; complete coefficient idempotents have explicit normal forms. This
is not a producer of strategically returning blocks.
-/

noncomputable section

namespace GameTheory

namespace QuittingBoundaryHolonomy

/-- Exact strategic self-similarity at `target`: prescribed play reproduces
the target, while every unilateral stopping value is already capped by it. -/
structure IsSelfSimilarAt
    (holonomy : QuittingBoundaryHolonomy ι) (target : Payoff ι) : Prop where
  prescribed_fixed : ∀ who,
    (holonomy.prescribed who).IsFixedAt (target who)
  bestResponse_safe : ∀ who,
    (holonomy.bestResponse who).eval (target who) ≤ target who

/-- Strategic self-similarity is a finite family of affine equations and
halfspaces in the five holonomy coordinates. -/
theorem isSelfSimilarAt_iff
    (holonomy : QuittingBoundaryHolonomy ι) (target : Payoff ι) :
    holonomy.IsSelfSimilarAt target ↔
      (∀ who,
        (holonomy.prescribed who).intercept =
          (holonomy.prescribed who).absorptionMass * target who) ∧
      ∀ who,
        (holonomy.bestResponse who).early ≤ target who ∧
          (holonomy.bestResponse who).tail ≤
            (holonomy.bestResponse who).absorptionMass * target who := by
  constructor
  · intro h
    constructor
    · intro who
      exact (QuittingAffineSummary.isFixedAt_iff_intercept_eq
        (holonomy.prescribed who) (target who)).mp
          (h.prescribed_fixed who)
    · intro who
      exact (QuittingMaxAffineSummary.eval_le_target_iff
        (holonomy.bestResponse who) (target who)).mp
          (h.bestResponse_safe who)
  · rintro ⟨hprescribed, hbest⟩
    constructor
    · intro who
      exact (QuittingAffineSummary.isFixedAt_iff_intercept_eq
        (holonomy.prescribed who) (target who)).mpr
          (hprescribed who)
    · intro who
      exact (QuittingMaxAffineSummary.eval_le_target_iff
        (holonomy.bestResponse who) (target who)).mpr
          (hbest who)

/-- Target-self-similar holonomies are closed under chronological
composition. -/
theorem IsSelfSimilarAt.mul
    {outer inner : QuittingBoundaryHolonomy ι} {target : Payoff ι}
    (houter : outer.IsSelfSimilarAt target)
    (hinner : inner.IsSelfSimilarAt target) :
    (outer * inner).IsSelfSimilarAt target := by
  constructor
  · intro who
    change (outer.prescribed who * inner.prescribed who).IsFixedAt
      (target who)
    unfold QuittingAffineSummary.IsFixedAt
    rw [QuittingAffineSummary.eval_mul]
    have hinnerFixed :
        (inner.prescribed who).eval (target who) = target who :=
      hinner.prescribed_fixed who
    rw [hinnerFixed]
    exact houter.prescribed_fixed who
  · intro who
    change (outer.bestResponse who * inner.bestResponse who).eval
      (target who) ≤ target who
    rw [QuittingMaxAffineSummary.eval_mul]
    exact (QuittingMaxAffineSummary.eval_mono (outer.bestResponse who)
      (hinner.bestResponse_safe who)).trans
        (houter.bestResponse_safe who)

/-- A self-similar block has nonpositive zero-boundary strategic gap. -/
theorem IsSelfSimilarAt.gap_nonpos
    {holonomy : QuittingBoundaryHolonomy ι} {target : Payoff ι}
    (hself : holonomy.IsSelfSimilarAt target) (who : ι) :
    holonomy.gap who 0 (target who) ≤ 0 := by
  unfold gap
  rw [add_zero]
  have hfixed :
      (holonomy.prescribed who).eval (target who) = target who :=
    hself.prescribed_fixed who
  rw [hfixed]
  exact sub_nonpos.mpr (hself.bestResponse_safe who)

/-- Coefficient-semigroup idempotence of the complete playerwise holonomy. -/
def IsIdempotent (holonomy : QuittingBoundaryHolonomy ι) : Prop :=
  holonomy * holonomy = holonomy

/-- Complete holonomy idempotence is componentwise idempotence. -/
theorem isIdempotent_iff
    (holonomy : QuittingBoundaryHolonomy ι) :
    holonomy.IsIdempotent ↔
      (∀ who, holonomy.prescribed who * holonomy.prescribed who =
        holonomy.prescribed who) ∧
      ∀ who, holonomy.bestResponse who * holonomy.bestResponse who =
        holonomy.bestResponse who := by
  constructor
  · intro h
    unfold IsIdempotent at h
    constructor
    · intro who
      have hp := congrArg
        (fun H : QuittingBoundaryHolonomy ι => H.prescribed who) h
      simpa [QuittingBoundaryHolonomy.compose] using hp
    · intro who
      have hb := congrArg
        (fun H : QuittingBoundaryHolonomy ι => H.bestResponse who) h
      simpa [QuittingBoundaryHolonomy.compose] using hb
  · rintro ⟨hprescribed, hbest⟩
    unfold IsIdempotent
    apply QuittingBoundaryHolonomy.ext
    · funext who
      exact hprescribed who
    · funext who
      exact hbest who

/-- An idempotent which is strategically self-similar at `target` has only the
expected projector/identity and safe constant/threshold forms. -/
theorem normalForm_of_isIdempotent_of_isSelfSimilarAt
    {holonomy : QuittingBoundaryHolonomy ι} {target : Payoff ι}
    (hidempotent : holonomy.IsIdempotent)
    (hself : holonomy.IsSelfSimilarAt target) (who : ι) :
    (((holonomy.prescribed who).survival = 0 ∧
        (holonomy.prescribed who).intercept = target who) ∨
      ((holonomy.prescribed who).survival = 1 ∧
        (holonomy.prescribed who).intercept = 0)) ∧
    (((holonomy.bestResponse who).survival = 0 ∧
        (holonomy.bestResponse who).tail ≤
          (holonomy.bestResponse who).early ∧
        (holonomy.bestResponse who).early ≤ target who) ∨
      ((holonomy.bestResponse who).survival = 1 ∧
        (holonomy.bestResponse who).tail = 0 ∧
        (holonomy.bestResponse who).early ≤ target who)) := by
  obtain ⟨hprescribedIdem, hbestIdem⟩ :=
    (isIdempotent_iff holonomy).mp hidempotent
  have hfixed :=
    (QuittingAffineSummary.isFixedAt_iff_intercept_eq
      (holonomy.prescribed who) (target who)).mp
        (hself.prescribed_fixed who)
  have hsafe :=
    (QuittingMaxAffineSummary.eval_le_target_iff
      (holonomy.bestResponse who) (target who)).mp
        (hself.bestResponse_safe who)
  constructor
  · rcases (QuittingAffineSummary.mul_self_eq_self_iff
      (holonomy.prescribed who)).mp (hprescribedIdem who) with
      hzero | ⟨hone, hintercept⟩
    · left
      refine ⟨hzero, ?_⟩
      simpa [QuittingAffineSummary.absorptionMass, hzero] using hfixed
    · exact Or.inr ⟨hone, hintercept⟩
  · rcases (QuittingMaxAffineSummary.mul_self_eq_self_iff
      (holonomy.bestResponse who)).mp (hbestIdem who) with
      ⟨hzero, htail⟩ | ⟨hone, htail⟩
    · exact Or.inl ⟨hzero, htail, hsafe.1⟩
    · exact Or.inr ⟨hone, htail, hsafe.1⟩

end QuittingBoundaryHolonomy


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
       simp [QuittingAffineSummary.selfCompose,
         QuittingAffineSummary.identitySummary, QuittingAffineSummary.compose]
  | succ extra ih =>
       rw [selfComposeNonempty_succ, prescribed_mul, ih]
       rw [QuittingAffineSummary.selfCompose_succ]
       rfl

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
