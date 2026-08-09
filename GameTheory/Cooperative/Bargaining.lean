/-
# Finite Nash bargaining

A bargaining problem is a feasible predicate on utility profiles together with
a feasible disagreement point.  It stores no finiteness, convexity,
compactness, topology, or existence assumption.  The Nash product needs a
finite player enumeration, so that capability appears only on its predicate
and theorems.

The algebraic proof spine adapts
`reference/GameTheory-v1/GameTheory/Cooperative/Bargaining.lean` at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`, while removing its unused
logarithm and probability imports.
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GameTheory

open scoped BigOperators

universe uPlayer

/-- A feasible utility set with an explicit feasible fallback profile. -/
structure BargainingProblem (Player : Type uPlayer) where
  feasible : (Player → ℝ) → Prop
  disagreement : Player → ℝ
  disagreement_feasible : feasible disagreement

namespace BargainingProblem

variable {Player : Type uPlayer} (problem : BargainingProblem Player)

/-- Every player weakly improves on the disagreement profile. -/
def IsIndividuallyRational (utility : Player → ℝ) : Prop :=
  ∀ player, problem.disagreement player ≤ utility player

/-- No feasible profile weakly improves every coordinate and strictly improves
at least one. -/
def IsPareto (utility : Player → ℝ) : Prop :=
  problem.feasible utility ∧
    ¬ ∃ alternative, problem.feasible alternative ∧
      (∀ player, utility player ≤ alternative player) ∧
      ∃ player, utility player < alternative player

/-- No feasible profile strictly improves every coordinate. -/
def IsWeaklyPareto (utility : Player → ℝ) : Prop :=
  problem.feasible utility ∧
    ¬ ∃ alternative, problem.feasible alternative ∧
      ∀ player, utility player < alternative player

theorem isWeaklyPareto_of_isPareto
    [Nonempty Player] {utility : Player → ℝ}
    (pareto : problem.IsPareto utility) :
    problem.IsWeaklyPareto utility := by
  refine ⟨pareto.1, ?_⟩
  rintro ⟨alternative, hfeasible, hstrict⟩
  exact pareto.2 ⟨alternative, hfeasible,
    fun player => (hstrict player).le,
    Classical.arbitrary Player, hstrict _⟩

/-- A feasible individually-rational maximizer of the Nash product of gains. -/
def IsNashSolution [Fintype Player] (utility : Player → ℝ) : Prop :=
  problem.feasible utility ∧ problem.IsIndividuallyRational utility ∧
    ∀ alternative,
      problem.feasible alternative →
      problem.IsIndividuallyRational alternative →
      (∏ player, (alternative player - problem.disagreement player)) ≤
        ∏ player, (utility player - problem.disagreement player)

theorem IsNashSolution.isIndividuallyRational
    [Fintype Player] {utility : Player → ℝ}
    (solution : problem.IsNashSolution utility) :
    problem.IsIndividuallyRational utility :=
  solution.2.1

/-- A Nash-product maximizer is weakly Pareto optimal. -/
theorem IsNashSolution.isWeaklyPareto
    [Fintype Player] [Nonempty Player] {utility : Player → ℝ}
    (solution : problem.IsNashSolution utility) :
    problem.IsWeaklyPareto utility := by
  refine ⟨solution.1, ?_⟩
  rintro ⟨alternative, hfeasible, hstrict⟩
  have hir := solution.2.1
  have halternativeIR : problem.IsIndividuallyRational alternative :=
    fun player => (hir player).trans (hstrict player).le
  have hmax := solution.2.2 alternative hfeasible halternativeIR
  have haltPositive : ∀ player,
      0 < alternative player - problem.disagreement player :=
    fun player => sub_pos.mpr ((hir player).trans_lt (hstrict player))
  have haltProductPositive :
      0 < ∏ player, (alternative player - problem.disagreement player) :=
    Finset.prod_pos fun player _ => haltPositive player
  by_cases hpositive : ∀ player,
      0 < utility player - problem.disagreement player
  · have hproductStrict :
        (∏ player, (utility player - problem.disagreement player)) <
          ∏ player, (alternative player - problem.disagreement player) :=
      Finset.prod_lt_prod_of_nonempty
        (fun player _ => hpositive player)
        (fun player _ => sub_lt_sub_right (hstrict player) _)
        Finset.univ_nonempty
    linarith
  · obtain ⟨player, hnotPositive⟩ := not_forall.mp hpositive
    rw [not_lt] at hnotPositive
    have hzero : utility player - problem.disagreement player = 0 :=
      le_antisymm hnotPositive (sub_nonneg.mpr (hir player))
    have hproductZero :
        (∏ player, (utility player - problem.disagreement player)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ player) hzero
    rw [hproductZero] at hmax
    linarith

/-- A symmetric problem has a constant disagreement profile and a feasible set
closed under player permutations. -/
def IsSymmetric : Prop :=
  (∀ first second,
    problem.disagreement first = problem.disagreement second) ∧
  ∀ (permutation : Equiv.Perm Player) (utility : Player → ℝ),
    problem.feasible utility → problem.feasible (utility ∘ permutation)

/-- A unique Nash solution of a symmetric problem gives every player the same
gain over disagreement. -/
theorem IsNashSolution.equal_gain_of_symmetric
    [Fintype Player] {utility : Player → ℝ}
    (solution : problem.IsNashSolution utility)
    (symmetric : problem.IsSymmetric)
    (unique : ∀ first second,
      problem.IsNashSolution first → problem.IsNashSolution second →
        first = second) :
    ∀ first second,
      utility first - problem.disagreement first =
        utility second - problem.disagreement second := by
  classical
  obtain ⟨hdisagreement, hinvariant⟩ := symmetric
  have hpermuted : ∀ permutation : Equiv.Perm Player,
      problem.IsNashSolution (utility ∘ permutation) := by
    intro permutation
    have hproduct :
        (∏ player,
          ((utility ∘ permutation) player - problem.disagreement player)) =
        ∏ player, (utility player - problem.disagreement player) := by
      calc
        (∏ player,
            ((utility ∘ permutation) player - problem.disagreement player)) =
            ∏ player,
              (utility (permutation player) -
                problem.disagreement (permutation player)) := by
          apply Finset.prod_congr rfl
          intro player _
          simp only [Function.comp_apply]
          rw [hdisagreement player (permutation player)]
        _ = ∏ player,
            (utility player - problem.disagreement player) :=
          Equiv.prod_comp permutation
            (fun player => utility player - problem.disagreement player)
    refine ⟨hinvariant permutation utility solution.1, ?_, ?_⟩
    · intro player
      have hcurrent := solution.2.1 (permutation player)
      simpa only [Function.comp_apply,
        hdisagreement player (permutation player)] using hcurrent
    · intro alternative hfeasible hir
      rw [hproduct]
      exact solution.2.2 alternative hfeasible hir
  intro first second
  have heq : utility = utility ∘ Equiv.swap first second :=
    unique utility (utility ∘ Equiv.swap first second)
      solution (hpermuted _)
  have hutility : utility first = utility second := by
    have hcomponent := congrFun heq first
    simpa [Equiv.swap_apply_left] using hcomponent
  rw [hutility, hdisagreement first second]

/-- Positive componentwise affine image of a bargaining problem. -/
def positiveAffineMap
    (scale : Player → ℝ) (positive : ∀ player, 0 < scale player)
    (shift : Player → ℝ) : BargainingProblem Player where
  feasible transformed :=
    problem.feasible fun player =>
      (transformed player - shift player) / scale player
  disagreement player :=
    scale player * problem.disagreement player + shift player
  disagreement_feasible := by
    convert problem.disagreement_feasible using 1
    funext player
    rw [add_sub_cancel_right,
      mul_div_cancel_left₀ (problem.disagreement player) (positive player).ne']

/-- The affine image of a profile is feasible exactly when the original is. -/
theorem positiveAffineMap_feasible_image
    {scale : Player → ℝ} (positive : ∀ player, 0 < scale player)
    {shift : Player → ℝ} (utility : Player → ℝ) :
    (problem.positiveAffineMap scale positive shift).feasible
        (fun player => scale player * utility player + shift player) ↔
      problem.feasible utility := by
  have heq :
      (fun player =>
        (scale player * utility player + shift player - shift player) /
          scale player) = utility := by
    funext player
    rw [add_sub_cancel_right,
      mul_div_cancel_left₀ (utility player) (positive player).ne']
  simp only [positiveAffineMap, heq]

/-- Individual rationality is preserved and reflected by the affine image. -/
theorem positiveAffineMap_isIndividuallyRational_image
    {scale : Player → ℝ} (positive : ∀ player, 0 < scale player)
    {shift : Player → ℝ} (utility : Player → ℝ) :
    (problem.positiveAffineMap scale positive shift).IsIndividuallyRational
        (fun player => scale player * utility player + shift player) ↔
      problem.IsIndividuallyRational utility := by
  simp only [positiveAffineMap, IsIndividuallyRational]
  constructor
  · intro h player
    exact le_of_mul_le_mul_left (by linarith [h player]) (positive player)
  · intro h player
    nlinarith [mul_le_mul_of_nonneg_left (h player) (positive player).le]

/-- Positive componentwise affine transformations preserve Nash solutions. -/
theorem IsNashSolution.positiveAffineMap
    [Fintype Player]
    (scale : Player → ℝ) (positive : ∀ player, 0 < scale player)
    (shift : Player → ℝ) {utility : Player → ℝ}
    (solution : problem.IsNashSolution utility) :
    (problem.positiveAffineMap scale positive shift).IsNashSolution
      (fun player => scale player * utility player + shift player) := by
  refine ⟨(problem.positiveAffineMap_feasible_image positive utility).mpr solution.1,
    (problem.positiveAffineMap_isIndividuallyRational_image positive utility).mpr
      solution.2.1, ?_⟩
  intro transformed hfeasible hir
  dsimp only [positiveAffineMap] at hfeasible hir ⊢
  have hpreimageIR : problem.IsIndividuallyRational
      (fun player =>
        (transformed player - shift player) / scale player) := by
    intro player
    rw [le_div_iff₀ (positive player)]
    have hp :
        scale player * problem.disagreement player + shift player ≤
          transformed player :=
      hir player
    calc
      problem.disagreement player * scale player =
          scale player * problem.disagreement player := mul_comm _ _
      _ ≤ transformed player - shift player := by
        linarith [hir player]
  have hmax := solution.2.2
    (fun player =>
      (transformed player - shift player) / scale player)
    hfeasible hpreimageIR
  have hleft :
      (∏ player,
        (scale player * utility player + shift player -
          (scale player * problem.disagreement player + shift player))) =
      (∏ player, scale player) *
        ∏ player, (utility player - problem.disagreement player) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun player _ => by ring
  have hright :
      (∏ player,
        (transformed player -
          (scale player * problem.disagreement player + shift player))) =
      (∏ player, scale player) *
        ∏ player,
          ((transformed player - shift player) / scale player -
            problem.disagreement player) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun player _ => ?_
    rw [mul_sub, mul_div_cancel₀ _ (positive player).ne']
    ring
  have hscaled :
      (∏ player,
        (transformed player -
          (scale player * problem.disagreement player + shift player))) ≤
        ∏ player,
          (scale player * utility player + shift player -
            (scale player * problem.disagreement player + shift player)) := by
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hmax
      (Finset.prod_nonneg fun player _ => (positive player).le)
  exact hscaled

end BargainingProblem

end GameTheory
