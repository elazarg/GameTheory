/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.SenParetianLiberal

/-!
# Condorcet's paradox

The voting paradox of Condorcet (1785): pairwise majority rule can be
**intransitive**. With three voters whose preferences cycle,

* voter 0 ranks `0 ≻ 1 ≻ 2`,
* voter 1 ranks `1 ≻ 2 ≻ 0`,
* voter 2 ranks `2 ≻ 0 ≻ 1`,

a strict majority (two of three) prefers `0` to `1`, `1` to `2`, and `2` to `0`.
The majority relation therefore has a cycle and is not acyclic — so there is no
transitive social ranking consistent with pairwise majorities.

This is the foundational obstruction that motivates the social-choice
impossibility theorems: it is exactly the failure of `IsAcyclic` that
`sen_paretian_liberal` demands of a social decision function, and the
intransitivity that Arrow's collective-rationality axiom rules out by fiat.

## Main results

* `condorcetMajority_cycle` — the majority prefers `0 ≻ 1 ≻ 2 ≻ 0`
* `condorcetMajority_not_acyclic` — the majority relation is not acyclic
-/

namespace GameTheory

open scoped BigOperators

/-- Score that each of the three voters assigns to each of the three alternatives
(higher is more preferred). The rows are the three cyclic rankings. -/
def condorcetScore : Fin 3 → Fin 3 → ℤ :=
  ![![2, 1, 0], ![0, 2, 1], ![1, 0, 2]]

/-- Pairwise majority preference for the Condorcet profile: `a` beats `b` when
strictly more voters score `a` above `b` than score `b` above `a`. -/
def condorcetMajority (a b : Fin 3) : Prop :=
  (∑ i, if condorcetScore i b < condorcetScore i a then (1 : ℤ) else 0)
    > ∑ i, if condorcetScore i a < condorcetScore i b then (1 : ℤ) else 0

/-- **Condorcet's cycle.** The majority strictly prefers `0` to `1`, `1` to `2`,
and `2` to `0`. -/
theorem condorcetMajority_cycle :
    condorcetMajority 0 1 ∧ condorcetMajority 1 2 ∧ condorcetMajority 2 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [condorcetMajority, condorcetScore, Fin.sum_univ_three]; decide

/-- **Condorcet's paradox.** The pairwise-majority relation of the cyclic profile is
not acyclic: `0 ≻ 1 ≻ 2 ≻ 0` is a majority cycle, so no transitive social
preference extends it. -/
theorem condorcetMajority_not_acyclic : ¬ IsAcyclic condorcetMajority := by
  obtain ⟨h01, h12, h20⟩ := condorcetMajority_cycle
  exact fun h => h 0 (((Relation.TransGen.single h01).tail h12).tail h20)

end GameTheory
