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
* `Voting.delegationBanzhafPower` — probabilistic Banzhaf power in that game
* `Voting.delegationShapleyShubikPower` — Shapley--Shubik power for an
  achievable quota

## Main results

* `delegationPowerGame_wins_iff` — a coalition wins exactly when the voters
  whose delegation chains end inside it meet the quota
* `delegationPowerGame_isSimpleGame` — achievable quotas (at most the number
  of participants) yield simple games, so power indices apply
* `sum_delegationShapleyShubikPower` — Shapley--Shubik delegation power sums
  to one
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
guru weight meets the quota `q`.

Delegations are held fixed: a coalition benefits from a delegator only through
that delegator's guru, so voters who delegate are null players. This is the
guru-power reading, which measures how a delegation structure concentrates
influence; treating delegations as revocable would instead give every voter
control of one vote, a majority game independent of the delegation profile. -/
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

/-- The probabilistic Banzhaf power of voter `i` in the weighted-majority game
induced by the fixed delegation profile. This value is not normalized across
voters. -/
noncomputable def delegationBanzhafPower (d : DelegationProfile ι β)
    (q : ℕ) (hq : 0 < q) (i : ι) : ℝ :=
  (delegationPowerGame d q hq).banzhafIndex i

/-- The Shapley--Shubik power of voter `i` in the simple delegation power game.
The quota bound ensures that the grand coalition wins. -/
noncomputable def delegationShapleyShubikPower (d : DelegationProfile ι β)
    (q : ℕ) (hq : 0 < q) (hle : q ≤ d.participants.card) (i : ι) : ℝ :=
  (delegationPowerGame d q hq).shapleyShubikIndex
    (delegationPowerGame_isSimpleGame d hq hle) i

/-- Shapley--Shubik power in an achievable-quota delegation game is normalized:
the voters' powers sum to one. -/
theorem sum_delegationShapleyShubikPower (d : DelegationProfile ι β)
    (q : ℕ) (hq : 0 < q) (hle : q ≤ d.participants.card) :
    ∑ i, delegationShapleyShubikPower d q hq hle i = 1 := by
  exact CoalGame.shapleyShubikIndex_sum_eq_one
    (delegationPowerGame d q hq) (delegationPowerGame_isSimpleGame d hq hle)

end GameTheory.Voting
