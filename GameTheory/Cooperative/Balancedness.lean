/-
# Balanced coalitional games

A balanced collection assigns nonnegative weights to coalitions so that every
agent is covered with total weight one.  Any core allocation certifies that
the game is balanced by finite double counting.  This is the easy direction
of Bondareva--Shapley; the converse requires a separate finite-dimensional
duality argument and is not claimed here.

The definitions and theorem are adapted from
`reference/GameTheory-v1/GameTheory/Cooperative/CoalitionalGame/Bondareva.lean`
at pinned commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Core.Coalitional

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

end GameTheory
