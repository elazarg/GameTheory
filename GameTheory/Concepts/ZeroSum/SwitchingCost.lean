/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AffineLowerEnvelope
import GameTheory.Concepts.ZeroSum.MatrixGame.Rectangular
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

/-!
# Static minimax values with switching costs

This file formalizes the history-independent layer of finite zero-sum games with
switching costs.  For a stage-payoff matrix `A`, a switching-cost matrix `S`, and
a cost weight `c`, the auxiliary payoff is

`xᵀ A y + c * yᵀ S y`.

Only its minimax value is considered: the column player minimizes the maximum
over the row player.  No minimax equality is asserted because the switching-cost
term is quadratic in the column strategy.

The regularity argument is Proposition 2 of the arXiv version
*Repeated Games with Switching Costs: Stationary vs History-Independent
Strategies* (arXiv:2103.00045), and the analytic part of Theorem 2 in the
published *The Regularity of the Value Function of Repeated Games with Switching
Costs*, Mathematics of Operations Research 48(4), 2023,
doi:10.1287/moor.2022.1325.  The static-strategy comparison is developed further
in *The Price of History-Independent Strategies in Games with Inter-Temporal
Externalities*, Dynamic Games and Applications 14(5), 2024,
doi:10.1007/s13235-024-00555-w.

The key observation is abstracted as `Math.IsAffineLowerEnvelope`: an attained
pointwise minimum of affine functions is concave; nonnegative, uniformly bounded
slopes additionally make it monotone and Lipschitz.
-/

noncomputable section

open scoped BigOperators NNReal
open Set

namespace GameTheory

/-! ## Switching-cost games -/

/-- A switching-cost matrix on a finite action type.  Costs are nonnegative and
remaining at the same action costs zero. -/
structure SwitchingCostMatrix (α : Type*) [Fintype α] where
  /-- Cost of changing from the first action to the second. -/
  cost : α → α → ℝ
  /-- Switching costs are nonnegative. -/
  nonneg : ∀ k j, 0 ≤ cost k j
  /-- Remaining at an action has no switching cost. -/
  diag_zero : ∀ j, cost j j = 0

namespace SwitchingCostMatrix

variable {m α : Type*} [Fintype m] [Nonempty m] [Fintype α] [Nonempty α]

/-- The quadratic expected switching cost `yᵀ S y`. -/
def quadCost (S : SwitchingCostMatrix α) (y : α → ℝ) : ℝ :=
  ∑ k, ∑ j, y k * S.cost k j * y j

/-- The largest entry of a switching-cost matrix. -/
def supCost (S : SwitchingCostMatrix α) : ℝ :=
  (Finset.univ.product Finset.univ).sup'
    (Finset.univ_nonempty.product Finset.univ_nonempty) fun p => S.cost p.1 p.2

/-- Every switching cost is bounded by `supCost`. -/
theorem cost_le_supCost (S : SwitchingCostMatrix α) (k j : α) :
    S.cost k j ≤ S.supCost := by
  have hmem : (k, j) ∈ (Finset.univ : Finset α).product Finset.univ := by simp
  exact Finset.le_sup' (fun p : α × α => S.cost p.1 p.2) hmem

/-- The largest switching cost is nonnegative. -/
theorem supCost_nonneg (S : SwitchingCostMatrix α) : 0 ≤ S.supCost :=
  (S.nonneg (Classical.arbitrary α) (Classical.arbitrary α)).trans
    (S.cost_le_supCost (Classical.arbitrary α) (Classical.arbitrary α))

omit [Nonempty α] in
/-- Expected switching cost is nonnegative on the simplex. -/
theorem quadCost_nonneg (S : SwitchingCostMatrix α) {y : α → ℝ}
    (hy : y ∈ stdSimplex ℝ α) : 0 ≤ S.quadCost y := by
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hy.1 k) (S.nonneg k j)) (hy.1 j)

/-- Expected switching cost is at most the largest matrix entry. -/
theorem quadCost_le_supCost (S : SwitchingCostMatrix α) {y : α → ℝ}
    (hy : y ∈ stdSimplex ℝ α) : S.quadCost y ≤ S.supCost := by
  calc
    S.quadCost y ≤ ∑ k, ∑ j, y k * S.supCost * y j := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (S.cost_le_supCost k j) (hy.1 k)) (hy.1 j)
    _ = ∑ k, y k * S.supCost * (∑ j, y j) := by
      simp_rw [Finset.mul_sum]
    _ = S.supCost := by rw [hy.2]; simp [← Finset.sum_mul, hy.2]

/-- The auxiliary payoff for static strategies. -/
def auxPayoff (A : MatrixGame.Rectangular m α) (S : SwitchingCostMatrix α) (c : ℝ)
    (x : m → ℝ) (y : α → ℝ) : ℝ :=
  MatrixGame.bilinearPayoff A x y + c * S.quadCost y

/-- The attained inner maximum, written as an affine function of the cost weight. -/
def innerMax (A : MatrixGame.Rectangular m α) (S : SwitchingCostMatrix α) (c : ℝ)
    (y : α → ℝ) : ℝ :=
  MatrixGame.maxRowPayoff A y + c * S.quadCost y

omit [Nonempty α] in
/-- The inner maximum is affine in the cost weight. -/
theorem innerMax_eq_zero_add (A : MatrixGame.Rectangular m α) (S : SwitchingCostMatrix α)
    (c : ℝ) (y : α → ℝ) :
    innerMax A S c y = innerMax A S 0 y + c * S.quadCost y := by
  simp [innerMax]

omit [Nonempty α] in
/-- The row player's inner maximum over the simplex is attained. -/
theorem exists_isMaxOn_auxPayoff (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α)
    (c : ℝ) (y : α → ℝ) :
    ∃ x ∈ stdSimplex ℝ m,
      auxPayoff A S c x y = innerMax A S c y ∧
      IsMaxOn (fun z => auxPayoff A S c z y) (stdSimplex ℝ m) x := by
  obtain ⟨x, hx, hmax⟩ := MatrixGame.exists_bilinearPayoff_eq_maxRowPayoff A y
  refine ⟨x, hx, ?_, ?_⟩
  · unfold auxPayoff innerMax
    rw [hmax]
  · intro z hz
    change MatrixGame.bilinearPayoff A z y + c * S.quadCost y ≤
      MatrixGame.bilinearPayoff A x y + c * S.quadCost y
    rw [hmax]
    simpa only [add_comm] using
      add_le_add_right (MatrixGame.bilinearPayoff_le_maxRowPayoff A hz)
        (c * S.quadCost y)

omit [Nonempty α] in
open Classical in
/-- The expected switching cost is continuous in the mixed action. -/
theorem continuous_quadCost (S : SwitchingCostMatrix α) : Continuous S.quadCost := by
  unfold quadCost
  fun_prop

omit [Nonempty α] in
/-- The attained inner maximum is continuous in the column vector. -/
theorem continuous_innerMax (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) (c : ℝ) :
    Continuous (innerMax A S c) := by
  exact (MatrixGame.continuous_maxRowPayoff A).add
    (continuous_const.mul S.continuous_quadCost)

open Classical in
/-- The outer minimum defining the static minimax value is attained. -/
theorem exists_isMinOn_innerMax (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) (c : ℝ) :
    ∃ y ∈ stdSimplex ℝ α,
      IsMinOn (innerMax A S c) (stdSimplex ℝ α) y := by
  apply (isCompact_stdSimplex ℝ α).exists_isMinOn
  · exact ⟨Pi.single (Classical.arbitrary α) 1,
      single_mem_stdSimplex ℝ (Classical.arbitrary α)⟩
  · exact (continuous_innerMax A S c).continuousOn

/-- A selected static minimizer. -/
noncomputable def staticMinimizer (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) (c : ℝ) :
    α → ℝ :=
  (exists_isMinOn_innerMax A S c).choose

/-- The selected static minimizer lies in the column simplex. -/
theorem staticMinimizer_mem (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) (c : ℝ) :
    staticMinimizer A S c ∈ stdSimplex ℝ α :=
  (exists_isMinOn_innerMax A S c).choose_spec.1

/-- The selected static minimizer minimizes the attained inner maximum. -/
theorem staticMinimizer_isMinOn (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) (c : ℝ) :
    IsMinOn (innerMax A S c) (stdSimplex ℝ α) (staticMinimizer A S c) :=
  (exists_isMinOn_innerMax A S c).choose_spec.2

/-- The static minimax value `min_y max_x g(c)(x,y)`. -/
noncomputable def staticMinimaxValue (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α)
    (c : ℝ) : ℝ :=
  innerMax A S c (staticMinimizer A S c)

/-- The static minimax value is no larger than the objective at any column mixture. -/
theorem staticMinimaxValue_le (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α)
    (c : ℝ) {y : α → ℝ} (hy : y ∈ stdSimplex ℝ α) :
    staticMinimaxValue A S c ≤ innerMax A S c y := by
  exact staticMinimizer_isMinOn A S c hy

/-- The static minimax value is an attained lower envelope of affine functions. -/
theorem staticMinimaxValue_isAffineLowerEnvelope (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    Math.IsAffineLowerEnvelope
      (fun y : stdSimplex ℝ α => MatrixGame.maxRowPayoff A y)
      (fun y : stdSimplex ℝ α => S.quadCost y)
      (staticMinimaxValue A S) := by
  intro c
  let y : stdSimplex ℝ α := ⟨staticMinimizer A S c, staticMinimizer_mem A S c⟩
  refine ⟨y, ?_, ?_⟩
  · rfl
  · intro z
    exact staticMinimaxValue_le A S c z.property

/-- The static minimax value is nondecreasing, in fact on the whole real line. -/
theorem staticMinimaxValue_monotone (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    Monotone (staticMinimaxValue A S) := by
  apply (staticMinimaxValue_isAffineLowerEnvelope A S).monotone
  intro y
  exact S.quadCost_nonneg y.property

/-- The static minimax value is nondecreasing for nonnegative cost weights. -/
theorem staticMinimaxValue_monotoneOn (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    MonotoneOn (staticMinimaxValue A S) (Ici 0) :=
  (staticMinimaxValue_monotone A S).monotoneOn (Ici 0)

/-- The static minimax value is concave, in fact on the whole real line. -/
theorem staticMinimaxValue_concaveOn_univ (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    ConcaveOn ℝ univ (staticMinimaxValue A S) :=
  (staticMinimaxValue_isAffineLowerEnvelope A S).concaveOn_univ

/-- The static minimax value is concave for nonnegative cost weights. -/
theorem staticMinimaxValue_concaveOn (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    ConcaveOn ℝ (Ici 0) (staticMinimaxValue A S) :=
  (staticMinimaxValue_concaveOn_univ A S).subset (subset_univ _) (convex_Ici 0)

/-- The static minimax value is globally Lipschitz, with largest switching cost
as a Lipschitz constant. -/
theorem staticMinimaxValue_lipschitz (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    LipschitzWith ⟨S.supCost, S.supCost_nonneg⟩ (staticMinimaxValue A S) := by
  apply (staticMinimaxValue_isAffineLowerEnvelope A S).lipschitzWith
    ⟨S.supCost, S.supCost_nonneg⟩
  intro y
  exact ⟨S.quadCost_nonneg y.property, S.quadCost_le_supCost y.property⟩

/-- The static minimax value is Lipschitz for nonnegative cost weights. -/
theorem staticMinimaxValue_lipschitzOn (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    LipschitzOnWith ⟨S.supCost, S.supCost_nonneg⟩
      (staticMinimaxValue A S) (Ici 0) :=
  (staticMinimaxValue_lipschitz A S).lipschitzOnWith

/-- The static minimax value is continuous. -/
theorem continuous_staticMinimaxValue (A : MatrixGame.Rectangular m α)
    (S : SwitchingCostMatrix α) :
    Continuous (staticMinimaxValue A S) :=
  (staticMinimaxValue_lipschitz A S).continuous

end SwitchingCostMatrix

end GameTheory
