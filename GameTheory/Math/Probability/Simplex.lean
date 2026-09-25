/-
# Finite-carrier PMFs as points of the standard simplex

The analytic presentation of an ordinary probability law on a finite
carrier. The ambient function space is the coordinate image of Mathlib's
canonical finitely supported simplex.
-/

import GameTheory.Math.Probability.Expectation
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

namespace PMF

variable [Fintype α]

/-- A PMF's real weight vector is a point of the standard simplex. -/
theorem toReal_mem_simplexWeights (μ : PMF α) :
    (fun value => (μ value).toReal) ∈ simplexWeights α := by
  apply mem_simplexWeights.mpr
  refine ⟨(fun _ => ENNReal.toReal_nonneg), ?_⟩
  have hmass : (∑' value, (μ value).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun value => μ.apply_ne_top value), PMF.tsum_coe]
    rfl
  simpa only [tsum_fintype] using hmass

/-- Every real point of the finite standard simplex determines an ordinary
PMF through Mathlib's finite-carrier constructor. -/
def ofSimplex {x : α → ℝ} (hx : x ∈ simplexWeights α) : PMF α :=
  PMF.ofFintype (fun value => ENNReal.ofReal (x value)) (by
    have hcoords := mem_simplexWeights.mp hx
    rw [← ENNReal.ofReal_sum_of_nonneg (fun value _ => hcoords.1 value), hcoords.2]
    norm_num)

theorem ofSimplex_toReal {x : α → ℝ} (hx : x ∈ simplexWeights α) :
    (fun value => (ofSimplex hx value).toReal) = x := by
  funext value
  simp [ofSimplex, ENNReal.toReal_ofReal ((mem_simplexWeights.mp hx).1 value)]

theorem ofSimplex_toReal_weights (μ : PMF α) :
    ofSimplex (toReal_mem_simplexWeights μ) = μ := by
  ext value
  simp [ofSimplex, ENNReal.ofReal_toReal (μ.apply_ne_top value)]

/-- A nonempty finite carrier has a nonempty simplex: a point mass is in it. -/
theorem simplexWeights_nonempty [Nonempty α] : (simplexWeights α).Nonempty :=
  ⟨(fun value => ((pure (Classical.arbitrary α) : PMF α) value).toReal),
    toReal_mem_simplexWeights _⟩

end PMF
end GameTheory.Math.Probability
