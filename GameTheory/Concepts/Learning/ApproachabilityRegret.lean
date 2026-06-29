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

end Math.Approachability
