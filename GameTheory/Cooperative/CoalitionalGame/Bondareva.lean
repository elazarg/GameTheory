/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Cooperative.CoalitionalGame.Core

/-!
# Balancedness and the Bondareva–Shapley theorem

A *balanced collection* of weights assigns each coalition a nonnegative weight so
that, for every player, the weights of the coalitions containing them sum to `1`. A
game is *balanced* if no balanced collection values the coalitions above the grand
coalition. The Bondareva–Shapley theorem states that a game has a nonempty core iff
it is balanced.

This file formalizes the **easy direction**: a game with a nonempty core is
balanced. For a core allocation `x` and balanced weights `w`,
`∑_S w_S v(S) ≤ ∑_S w_S ∑_{i∈S} x_i = ∑_i x_i ∑_{S∋i} w_S = ∑_i x_i = v(N)`
— the middle step a double-counting swap, the penultimate using balancedness.

## Main definitions

* `IsBalancedCollection` — nonnegative weights summing to `1` at every player
* `CoalGame.IsBalanced` — every balanced collection is dominated by the grand coalition

## Main results

* `IsCore.isBalanced` — a nonempty core implies the game is balanced (Bondareva–Shapley, easy
  direction)

The converse (*balanced ⇒ nonempty core*) is the hard direction; it is an LP-duality
(Farkas) argument and is not formalized here.
-/

open scoped BigOperators

namespace GameTheory

namespace CoalGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- A **balanced collection of weights**: nonnegative weights on coalitions such
that, for every player, the total weight of the coalitions containing them is `1`. -/
def IsBalancedCollection (w : Finset ι → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧ ∀ i : ι, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S = 1

/-- A game is **balanced** if every balanced collection of weights values the grand
coalition at least as highly as the weighted sum of coalition values. -/
def IsBalanced (G : CoalGame ι) : Prop :=
  ∀ w : Finset ι → ℝ, IsBalancedCollection w →
    ∑ S, w S * G.v S ≤ G.v Finset.univ

/-- **Bondareva–Shapley (easy direction): a game with a nonempty core is balanced.**
A core allocation distributes exactly `v(N)`, gives every coalition at least its
worth, and — being charged once per player via the balancing condition — dominates
the weighted coalition values. -/
theorem IsCore.isBalanced {G : CoalGame ι} {x : ι → ℝ} (hx : G.IsCore x) :
    G.IsBalanced := by
  intro w hw
  calc ∑ S, w S * G.v S
      ≤ ∑ S, w S * ∑ i ∈ S, x i :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hx.2 S) (hw.1 S)
    _ = ∑ S, ∑ i ∈ S, w S * x i := by simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S * x i :=
        Finset.sum_comm' (fun S i => by simp [Finset.mem_filter])
    _ = ∑ i, x i * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul]; ring
    _ = ∑ i, x i := by simp_rw [hw.2, mul_one]
    _ = G.v Finset.univ := hx.1

end CoalGame

end GameTheory
