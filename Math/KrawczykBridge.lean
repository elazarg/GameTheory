/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A small Krawczyk-to-existence bridge

This file isolates the analytic consumer needed by finite exact certificates
for periodic quitting profiles.  It deliberately does not implement a broad
interval-arithmetic library.  A certificate may compute, over exact rational
intervals, a Lipschitz constant for the preconditioned map

`T x = x - A (F x)`

on a closed ball.  If the center correction fits inside the remaining radius
and `A` is injective, Banach's fixed-point theorem supplies an exact zero of
`F` in that ball.
-/

namespace Math

open Function Metric Set

open scoped NNReal

/-- If a square preconditioned derivative is within operator norm one of the
identity, then the preconditioner is injective.

The finite-dimensional hypothesis is essential for this conclusion.  The
norm bound first makes `preconditioner.comp derivative` injective.  In finite
dimension that composite is therefore surjective, so `preconditioner` is
surjective and hence injective.  Without finite dimensionality, a surjective
noninjective bounded operator can have a bounded right inverse, making the
composite exactly the identity. -/
theorem preconditioner_injective_of_norm_one_sub_comp_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (preconditioner derivative : E →L[ℝ] E)
    (hnear : ‖1 - preconditioner.comp derivative‖ < 1) :
    Injective preconditioner := by
  have hcompInjective : Injective (preconditioner.comp derivative) := by
    intro first second heq
    have hzero :
        (preconditioner.comp derivative) (first - second) = 0 := by
      rw [map_sub, heq, sub_self]
    have hfixed :
        (1 - preconditioner.comp derivative) (first - second) =
          first - second := by
      change (first - second) -
          (preconditioner.comp derivative) (first - second) = first - second
      rw [hzero, sub_zero]
    have hopNorm :=
      (1 - preconditioner.comp derivative).le_opNorm (first - second)
    rw [hfixed] at hopNorm
    by_cases hdifference : first - second = 0
    · exact sub_eq_zero.mp hdifference
    · have hnormPositive : 0 < ‖first - second‖ :=
        norm_pos_iff.mpr hdifference
      have hstrict :
          ‖1 - preconditioner.comp derivative‖ * ‖first - second‖ <
            ‖first - second‖ :=
        (mul_lt_iff_lt_one_left hnormPositive).mpr hnear
      exact False.elim (not_lt_of_ge hopNorm hstrict)
  have hcompSurjective : Surjective (preconditioner.comp derivative) :=
    LinearMap.injective_iff_surjective.mp hcompInjective
  have hpreconditionerSurjective : Surjective preconditioner := by
    intro target
    obtain ⟨source, hsource⟩ := hcompSurjective target
    change preconditioner (derivative source) = target at hsource
    exact ⟨derivative source, hsource⟩
  exact LinearMap.injective_iff_surjective.mpr hpreconditionerSurjective

/-- A contracting preconditioned residual map whose center correction fits
inside a closed ball has an exact residual zero in that ball.

This is the proof-theoretic core of a Krawczyk certificate.  Exact interval
arithmetic is only needed to discharge `hlipschitz` and `hcorrection`; the
root itself is obtained inside Lean from Banach's fixed-point theorem. -/
theorem exists_zero_in_closedBall_of_preconditioned_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (residual : E → E) (preconditioner : E →ₗ[ℝ] E)
    (center : E) (radius : ℝ) (contraction : ℝ≥0)
    (hradius : 0 ≤ radius) (hcontraction : contraction < 1)
    (hpreconditioner : Injective preconditioner)
    (hlipschitz : LipschitzOnWith contraction
      (fun x ↦ x - preconditioner (residual x))
      (closedBall center radius))
    (hcorrection : norm (preconditioner (residual center)) ≤
      (1 - (contraction : ℝ)) * radius) :
    ∃ root ∈ closedBall center radius, residual root = 0 := by
  let step : E → E := fun x ↦ x - preconditioner (residual x)
  let ball : Set E := closedBall center radius
  have hcenter : center ∈ ball := by
    exact mem_closedBall_self hradius
  have hmaps : MapsTo step ball ball := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    calc
      dist (step x) center ≤ dist (step x) (step center) +
          dist (step center) center := dist_triangle _ _ _
      _ ≤ (contraction : ℝ) * dist x center +
          dist (step center) center := by
        exact add_le_add
          (hlipschitz.dist_le_mul x hx center hcenter) le_rfl
      _ = (contraction : ℝ) * dist x center +
          norm (preconditioner (residual center)) := by
        congr 1
        simp only [step, dist_eq_norm]
        rw [sub_sub_cancel_left, norm_neg]
      _ ≤ (contraction : ℝ) * radius +
          (1 - (contraction : ℝ)) * radius := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hx contraction.coe_nonneg)
          hcorrection
      _ = radius := by ring
  have hrestricted : ContractingWith contraction
      (hmaps.restrict step ball ball) :=
    ⟨hcontraction, hlipschitz.mapsToRestrict hmaps⟩
  have hcomplete : IsComplete ball := isClosed_closedBall.isComplete
  have hfinite : edist center (step center) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨root, hrootBall, hrootFixed, _⟩ :=
    hrestricted.exists_fixedPoint' hcomplete hmaps hcenter hfinite
  refine ⟨root, hrootBall, ?_⟩
  have hzero : preconditioner (residual root) = 0 := by
    dsimp only [step] at hrootFixed
    exact sub_eq_self.mp hrootFixed
  exact hpreconditioner (hzero.trans preconditioner.map_zero.symm)

end Math
