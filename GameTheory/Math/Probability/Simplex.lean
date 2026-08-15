/-
# Finite-support laws as points of the standard simplex

The analytic presentation of a finite-support probability law on a finite
carrier.
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Analysis.Convex.StdSimplex

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {α : Type*} [Fintype α]

/-- A law's probability vector is a point of the standard simplex. -/
theorem prob_mem_stdSimplex (μ : FinDist α) : μ.prob ∈ stdSimplex ℝ α :=
  ⟨fun a => μ.prob_nonneg a, μ.sum_prob⟩

/-- Every point of the standard simplex determines a finite-support law. -/
def ofSimplex {x : α → ℝ} (hx : x ∈ stdSimplex ℝ α) : FinDist α :=
  ofWeights x hx.1 hx.2

@[simp]
theorem prob_ofSimplex {x : α → ℝ} (hx : x ∈ stdSimplex ℝ α) :
    (ofSimplex hx).prob = x := by
  funext _
  exact prob_ofWeights ..

@[simp]
theorem ofSimplex_prob (μ : FinDist α) : ofSimplex μ.prob_mem_stdSimplex = μ :=
  ext_of_prob fun _ => prob_ofWeights ..

/-- A nonempty finite carrier has a nonempty simplex: a point mass is in it. -/
theorem stdSimplex_nonempty [Nonempty α] : (stdSimplex ℝ α).Nonempty :=
  ⟨(pure (Classical.arbitrary α)).prob, prob_mem_stdSimplex _⟩

end GameTheory.Math.Probability.FinDist
