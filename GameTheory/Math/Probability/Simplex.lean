/-
# Finite-support laws as points of the standard simplex

The analytic presentation of a finite-support probability law on a finite
carrier. The ambient function space is the coordinate image of Mathlib's
canonical finitely supported simplex.
-/

import GameTheory.Math.Probability.FinDist
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

noncomputable section

namespace GameTheory.Math.Probability

/-- The canonical standard simplex, viewed in its ambient space of real
coordinate functions. This is a range of the existing simplex's weights,
rather than another representation of finite probability laws. -/
def simplexWeights (α : Type*) : Set (α → ℝ) :=
  Set.range (fun t ↦ t.weights : Convexity.StdSimplex ℝ α → α → ℝ)

variable {α : Type*}

/-- On a finite carrier, the coordinate image consists exactly of the
nonnegative functions with total weight one. -/
theorem mem_simplexWeights [Fintype α] {x : α → ℝ} :
    x ∈ simplexWeights α ↔ (∀ a, 0 ≤ x a) ∧ ∑ a, x a = 1 := by
  unfold simplexWeights
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The simplex's finite coordinate image is convex in its ambient space. -/
theorem convex_simplexWeights (α : Type*) [Fintype α] : Convex ℝ (simplexWeights α) := by
  intro x hx y hy a b ha hb hab
  rw [mem_simplexWeights] at hx hy ⊢
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hy.2, mul_one]
    exact hab

/-- The finite coordinate image is closed by the canonical weight embedding. -/
theorem isClosed_simplexWeights (α : Type*) [Finite α] : IsClosed (simplexWeights α) :=
  (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ α).isClosed_range

/-- Compactness of Mathlib's simplex passes through its coordinate embedding. -/
theorem isCompact_simplexWeights (α : Type*) [Finite α] : IsCompact (simplexWeights α) :=
  isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ α).continuous

namespace FinDist

variable [Fintype α]

/-- A law's probability vector is a point of the standard simplex. -/
theorem prob_mem_simplexWeights (μ : FinDist α) : μ.prob ∈ simplexWeights α :=
  mem_simplexWeights.mpr ⟨μ.prob_nonneg, μ.sum_prob⟩

/-- Every point of the standard simplex determines a finite-support law. -/
def ofSimplex {x : α → ℝ} (hx : x ∈ simplexWeights α) : FinDist α :=
  ofWeights x (mem_simplexWeights.mp hx).1 (mem_simplexWeights.mp hx).2

@[simp]
theorem prob_ofSimplex {x : α → ℝ} (hx : x ∈ simplexWeights α) :
    (ofSimplex hx).prob = x := by
  funext _
  exact prob_ofWeights ..

@[simp]
theorem ofSimplex_prob (μ : FinDist α) : ofSimplex μ.prob_mem_simplexWeights = μ :=
  ext_of_prob fun _ => prob_ofWeights ..

/-- A nonempty finite carrier has a nonempty simplex: a point mass is in it. -/
theorem simplexWeights_nonempty [Nonempty α] : (simplexWeights α).Nonempty :=
  ⟨(pure (Classical.arbitrary α)).prob, prob_mem_simplexWeights _⟩

end FinDist
end GameTheory.Math.Probability
