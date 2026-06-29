/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Learning.Approachability
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Approachability ⇒ no external regret (the nonpositive orthant)

The loop-closer between Blackwell approachability (`Approachability`) and the no-regret learning of
Tier A: external-regret minimization is exactly approachability of the **nonpositive orthant** in
`ℝ^ι`. A learner's average regret vector approaches the orthant iff its external regret against
every fixed action vanishes.

This file develops the orthant geometry. The full reduction (orthant is a B-set with the
regret-matching witness `p* ∝ (x)₊`, hence external regret minimization is approachable) builds on
`blackwell_approaches`.
-/

namespace Math.Approachability

variable {ι : Type*}

/-- The nonpositive orthant `{x : ‖x i ≤ 0 for all i}` in `ℝ^ι`. Approaching it is exactly having
    nonpositive external regret against every coordinate. -/
def nonposOrthant : Set (EuclideanSpace ℝ ι) := {x | ∀ i, x.ofLp i ≤ 0}

theorem mem_nonposOrthant {x : EuclideanSpace ℝ ι} :
    x ∈ nonposOrthant ↔ ∀ i, x.ofLp i ≤ 0 := Iff.rfl

theorem nonposOrthant_nonempty : (nonposOrthant (ι := ι)).Nonempty :=
  ⟨0, fun i => by simp⟩

theorem isClosed_nonposOrthant : IsClosed (nonposOrthant (ι := ι)) := by
  have hset : (nonposOrthant (ι := ι)) = ⋂ i, {x : EuclideanSpace ℝ ι | x.ofLp i ≤ 0} := by
    ext x; simp [nonposOrthant, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter (fun i => ?_)
  have hc : Continuous (fun x : EuclideanSpace ℝ ι => x.ofLp i) := by
    simpa [EuclideanSpace.coe_proj] using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  exact isClosed_le hc continuous_const

/-! ### The orthant projection -/

/-- Projection onto the nonpositive orthant: clamp each coordinate at `0`. -/
noncomputable def orthantProj (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => min (x.ofLp i) 0)

@[simp] theorem orthantProj_ofLp (x : EuclideanSpace ℝ ι) (i : ι) :
    (orthantProj x).ofLp i = min (x.ofLp i) 0 := rfl

theorem orthantProj_mem (x : EuclideanSpace ℝ ι) : orthantProj x ∈ nonposOrthant :=
  fun i => by rw [orthantProj_ofLp]; exact min_le_right _ _

/-- The displacement from the projection is the coordinatewise positive part `(x)₊`. -/
theorem sub_orthantProj_ofLp (x : EuclideanSpace ℝ ι) (i : ι) :
    (x - orthantProj x).ofLp i = max (x.ofLp i) 0 := by
  rw [WithLp.ofLp_sub, Pi.sub_apply, orthantProj_ofLp]
  rcases le_total (x.ofLp i) 0 with h | h
  · rw [min_eq_left h, max_eq_right h, sub_self]
  · rw [min_eq_right h, max_eq_left h, sub_zero]

variable [Fintype ι]

/-- The squared Euclidean norm as a coordinate sum. -/
theorem norm_sq_eq_sum (z : EuclideanSpace ℝ ι) : ‖z‖ ^ 2 = ∑ i, (z.ofLp i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- `orthantProj x` is the nearest point of the orthant to `x`: the distance to the orthant is
    realised by clamping at `0`. -/
theorem infDist_eq_norm_sub_orthantProj (x : EuclideanSpace ℝ ι) :
    Metric.infDist x nonposOrthant = ‖x - orthantProj x‖ := by
  refine le_antisymm ?_ ?_
  · rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (orthantProj_mem x)
  · rw [Metric.le_infDist nonposOrthant_nonempty]
    intro y hy
    rw [dist_eq_norm]
    have hsq : ‖x - orthantProj x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [norm_sq_eq_sum, norm_sq_eq_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hyi : y.ofLp i ≤ 0 := hy i
      rw [sub_orthantProj_ofLp, WithLp.ofLp_sub, Pi.sub_apply]
      rcases le_total (x.ofLp i) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (x.ofLp i - y.ofLp i)]
      · rw [max_eq_left h]; nlinarith [hyi, h]
    nlinarith [hsq, norm_nonneg (x - orthantProj x), norm_nonneg (x - y)]

end Math.Approachability
