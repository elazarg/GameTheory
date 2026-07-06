/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Cooperative.CoalitionalGame.Banzhaf

/-!
# Weighted majority games

The quota games of cooperative voting theory: each player carries a
nonnegative integer weight, and a coalition wins exactly when its total weight
reaches the quota. These are the canonical simple games; the Banzhaf and
Shapley–Shubik indices (`Banzhaf.lean`) applied to them quantify voting power.

## Main definitions

* `CoalGame.weightedMajority` — the quota game for weights `w` and quota `q`

## Main results

* `weightedMajority_wins_iff` — a coalition wins iff its weight meets the quota
* `weightedMajority_isSimpleGame` — with an achievable quota this is a simple
  game, so the power-index theory applies
-/

namespace GameTheory

namespace CoalGame

variable {ι : Type} [DecidableEq ι]

open Finset

/-- The weighted majority (quota) game: coalition `S` is worth `1` when its
total weight reaches the quota `q`, and `0` otherwise. The quota is positive,
so the empty coalition loses. -/
def weightedMajority (w : ι → ℕ) (q : ℕ) (hq : 0 < q) : CoalGame ι where
  v S := if q ≤ ∑ i ∈ S, w i then 1 else 0
  v_empty := by
    rw [if_neg]
    simp only [Finset.sum_empty]
    omega

theorem weightedMajority_wins_iff {w : ι → ℕ} {q : ℕ} {hq : 0 < q}
    {S : Finset ι} :
    (weightedMajority w q hq).v S = 1 ↔ q ≤ ∑ i ∈ S, w i := by
  unfold weightedMajority
  dsimp only
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A weighted majority game whose quota is achievable by the grand coalition
is a simple game. -/
theorem weightedMajority_isSimpleGame [Fintype ι] {w : ι → ℕ} {q : ℕ}
    (hq : 0 < q) (hle : q ≤ ∑ i, w i) :
    (weightedMajority w q hq).IsSimpleGame where
  boolean S := by
    unfold weightedMajority
    dsimp only
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  monotone hST hS :=
    weightedMajority_wins_iff.mpr
      (le_trans (weightedMajority_wins_iff.mp hS)
        (Finset.sum_le_sum_of_subset hST))
  grandWinning := weightedMajority_wins_iff.mpr hle

end CoalGame

end GameTheory
