module

/-
# Balanced coalitional games

A balanced collection assigns nonnegative weights to coalitions so that every
agent is covered with total weight one. Any core allocation certifies that
the game is balanced by finite double counting. Conversely, finite linear
inequality duality turns failure of core feasibility into a balanced
collection violating the game's grand-coalition bound.

Primary references: O. N. Bondareva, “Some Applications of Linear Programming
Methods to the Theory of Cooperative Games,” 1963; L. S. Shapley, “On
Balanced Sets and Cores,” *Naval Research Logistics Quarterly* 14 (1967).
-/

public import GameTheory.Core.Coalitional
public import GameTheory.Math.LinearInequality
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring

@[expose] public section

namespace GameTheory

open scoped BigOperators

universe ua

namespace CoalitionalGame

variable {Agent : Type ua} [Fintype Agent] [DecidableEq Agent]

/-- Nonnegative coalition weights that cover every agent with total weight
one. -/
def IsBalancedCollection (weights : Finset Agent → ℝ) : Prop :=
  (∀ coalition, 0 ≤ weights coalition) ∧
    ∀ agent : Agent,
      ∑ coalition ∈
          (Finset.univ : Finset (Finset Agent)).filter
            (fun coalition => agent ∈ coalition),
        weights coalition = 1

/-- A coalitional game is balanced when every balanced collection's weighted
worth is at most the value of the grand coalition. -/
def IsBalanced (G : CoalitionalGame Agent) : Prop :=
  ∀ weights : Finset Agent → ℝ,
    IsBalancedCollection weights →
      ∑ coalition, weights coalition * G.value coalition ≤
        G.value Finset.univ

private theorem IsBalanced.weighted_value_le {G : CoalitionalGame Agent}
    (balanced : G.IsBalanced) (weights : Finset Agent → ℝ) (total : ℝ)
    (nonnegative : ∀ coalition, 0 ≤ weights coalition) (total_nonnegative : 0 ≤ total)
    (covers : ∀ agent : Agent,
      ∑ coalition ∈ (Finset.univ : Finset (Finset Agent)).filter
        (fun coalition => agent ∈ coalition), weights coalition = total) :
    ∑ coalition, weights coalition * G.value coalition ≤ total * G.value Finset.univ := by
  classical
  by_cases zero : total = 0
  · have vanishes (coalition : Finset Agent) : weights coalition * G.value coalition = 0 := by
      by_cases empty : coalition = ∅
      · simp [empty, G.value_empty]
      · obtain ⟨agent, member⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        have bound : weights coalition ≤ total := by
          rw [← covers agent]
          exact Finset.single_le_sum (a := coalition) (fun c _ => nonnegative c)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, member⟩)
        have weight_zero : weights coalition = 0 :=
          le_antisymm (by simpa only [zero] using bound) (nonnegative coalition)
        simp only [weight_zero, zero_mul]
    simp only [vanishes, Finset.sum_const_zero, zero, zero_mul, le_refl]
  · have positive : 0 < total := lt_of_le_of_ne total_nonnegative (Ne.symm zero)
    have normalized : IsBalancedCollection (fun coalition => weights coalition / total) := by
      refine ⟨fun coalition => div_nonneg (nonnegative coalition) total_nonnegative, ?_⟩
      intro agent
      rw [← Finset.sum_div, covers agent, div_self zero]
    have bound := balanced _ normalized
    have divided : (∑ coalition, weights coalition * G.value coalition) / total ≤
        G.value Finset.univ := by
      convert bound using 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro coalition _
      ring
    simpa only [mul_comm] using (div_le_iff₀ positive).mp divided

private def coreConstraint (row : Finset Agent ⊕ Unit) (agent : Agent) : ℝ :=
  match row with
  | .inl coalition => if agent ∈ coalition then 1 else 0
  | .inr _ => -1

private def coreBound (G : CoalitionalGame Agent) : Finset Agent ⊕ Unit → ℝ
  | .inl coalition => G.value coalition
  | .inr _ => -G.value Finset.univ

private theorem IsBalanced.no_core_certificate {G : CoalitionalGame Agent}
    (balanced : G.IsBalanced) :
    ¬ ∃ weights : Finset Agent ⊕ Unit → ℝ,
      (∀ row, 0 ≤ weights row) ∧
      (∀ agent, ∑ row, weights row * coreConstraint row agent = 0) ∧
      0 < ∑ row, weights row * coreBound G row := by
  classical
  rintro ⟨weights, nonnegative, columns, positive⟩
  have covers (agent : Agent) :
      ∑ coalition ∈ (Finset.univ : Finset (Finset Agent)).filter
        (fun coalition => agent ∈ coalition), weights (.inl coalition) = weights (.inr ()) := by
    have column := columns agent
    simp only [Fintype.sum_sum_type, coreConstraint, mul_ite, mul_one, mul_zero,
      Fintype.sum_unique, mul_neg_one] at column
    have filtered : (∑ coalition : Finset Agent,
        if agent ∈ coalition then weights (.inl coalition) else 0) =
        ∑ coalition ∈ (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∈ coalition), weights (.inl coalition) := by
      exact (Finset.sum_filter _ _).symm
    rw [filtered] at column
    linarith
  have bound := balanced.weighted_value_le (fun coalition => weights (.inl coalition))
    (weights (.inr ())) (fun coalition => nonnegative (.inl coalition))
    (nonnegative (.inr ())) covers
  simp only [Fintype.sum_sum_type, coreBound, Fintype.sum_unique, mul_neg] at positive
  linarith

/-- **Bondareva--Shapley sufficiency.** A balanced finite coalitional game has
a core allocation. The proof is algebraic finite-inequality duality and also
includes the empty player carrier. -/
theorem IsBalanced.exists_core {G : CoalitionalGame Agent} (balanced : G.IsBalanced) :
    ∃ allocation, IsInCore G allocation := by
  classical
  obtain ⟨allocation, feasible⟩ :=
    (Math.LinearInequality.exists_solution_iff_no_certificate
      (coreConstraint (Agent := Agent)) (coreBound G)).mpr balanced.no_core_certificate
  have rational (coalition : Finset Agent) : G.value coalition ≤ payout allocation coalition := by
    have row := feasible (.inl coalition)
    simpa [coreConstraint, coreBound, payout, ite_mul] using row
  have efficient_le : payout allocation Finset.univ ≤ G.value Finset.univ := by
    have row := feasible (.inr ())
    simp only [coreConstraint, coreBound, neg_one_mul, Finset.sum_neg_distrib] at row
    exact neg_le_neg_iff.mp row
  exact ⟨allocation, le_antisymm efficient_le (rational Finset.univ), rational⟩

end CoalitionalGame

/-- Every core allocation certifies balancedness.  This is the finite
double-counting direction of the Bondareva--Shapley theorem. -/
theorem IsInCore.isBalanced
    {Agent : Type ua} [Fintype Agent] [DecidableEq Agent]
    {G : CoalitionalGame Agent} {allocation : Allocation Agent}
    (hcore : IsInCore G allocation) :
    G.IsBalanced := by
  intro weights hweights
  calc
    ∑ coalition, weights coalition * G.value coalition
        ≤ ∑ coalition, weights coalition * payout allocation coalition :=
      Finset.sum_le_sum fun coalition _ =>
        mul_le_mul_of_nonneg_left
          (hcore.coalition_rational coalition) (hweights.1 coalition)
    _ = ∑ coalition, ∑ agent ∈ coalition,
          weights coalition * allocation agent := by
      simp_rw [payout, Finset.mul_sum]
    _ = ∑ agent, ∑ coalition ∈
          (Finset.univ : Finset (Finset Agent)).filter
            (fun coalition => agent ∈ coalition),
          weights coalition * allocation agent :=
      Finset.sum_comm' (fun coalition agent => by simp [Finset.mem_filter])
    _ = ∑ agent, allocation agent *
          ∑ coalition ∈
            (Finset.univ : Finset (Finset Agent)).filter
              (fun coalition => agent ∈ coalition),
            weights coalition := by
      refine Finset.sum_congr rfl fun agent _ => ?_
      rw [← Finset.sum_mul]
      exact mul_comm _ _
    _ = ∑ agent, allocation agent := by
      simp_rw [hweights.2, mul_one]
    _ = payout allocation Finset.univ := by simp [payout]
    _ = G.value Finset.univ := hcore.efficient

namespace CoalitionalGame

/-- **Bondareva--Shapley.** A finite coalitional game's core is nonempty exactly
when every balanced collection satisfies the grand-coalition bound. -/
theorem isBalanced_iff_core_nonempty
    {Agent : Type ua} [Fintype Agent] [DecidableEq Agent] (G : CoalitionalGame Agent) :
    G.IsBalanced ↔ ∃ allocation, IsInCore G allocation :=
  ⟨IsBalanced.exists_core, fun ⟨_, core⟩ => core.isBalanced⟩

end CoalitionalGame

end GameTheory
