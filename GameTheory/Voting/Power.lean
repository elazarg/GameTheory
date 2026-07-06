/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.LiquidDemocracy
import GameTheory.Cooperative.CoalitionalGame.WeightedMajority

/-!
# Delegation and voting power

A delegation profile equips the electorate with guru weights, and any quota
turns those weights into a weighted majority game — a coalitional simple game
over the voters. This bridges fluid democracy to cooperative game theory: the
Banzhaf and Shapley–Shubik indices of the delegation power game quantify how
delegation concentrates influence in the casters.

## Main definitions

* `Voting.delegationPowerGame` — the weighted majority game of guru weights

## Main results

* `delegationPowerGame_wins_iff` — a coalition wins exactly when the voters
  whose delegation chains end inside it meet the quota
* `delegationPowerGame_isSimpleGame` — achievable quotas (at most the number
  of participants) yield simple games, so power indices apply
-/

namespace GameTheory.Voting

open DelegationProfile

variable {ι : Type} {β : Type*} [Fintype ι]

/-- Total guru weight over the whole electorate is the number of participants
(non-casters carry weight `0`). -/
theorem sum_weight_univ (d : DelegationProfile ι β) :
    ∑ j, d.weight j = d.participants.card := by
  rw [← sum_weight_eq_card_participants]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
  exact weight_eq_zero_of_not_isCaster (fun hc => hj (mem_casters.mpr hc))

variable [DecidableEq ι]

/-- The delegation power game: coalitions of voters win when their accumulated
guru weight meets the quota `q`. -/
noncomputable def delegationPowerGame (d : DelegationProfile ι β) (q : ℕ)
    (hq : 0 < q) : CoalGame ι :=
  CoalGame.weightedMajority d.weight q hq

/-- A coalition wins the delegation power game exactly when the voters whose
delegation chains end inside it number at least the quota. -/
theorem delegationPowerGame_wins_iff {d : DelegationProfile ι β} {q : ℕ}
    {hq : 0 < q} {S : Finset ι} :
    (delegationPowerGame d q hq).v S = 1 ↔ q ≤ (S.biUnion d.guruFiber).card := by
  rw [delegationPowerGame, CoalGame.weightedMajority_wins_iff,
    card_biUnion_guruFiber]

/-- With a quota no larger than the number of participants, the delegation
power game is a simple game, so Banzhaf and Shapley–Shubik power indices
apply. -/
theorem delegationPowerGame_isSimpleGame (d : DelegationProfile ι β) {q : ℕ}
    (hq : 0 < q) (hle : q ≤ d.participants.card) :
    (delegationPowerGame d q hq).IsSimpleGame :=
  CoalGame.weightedMajority_isSimpleGame hq (by rw [sum_weight_univ]; exact hle)

end GameTheory.Voting
