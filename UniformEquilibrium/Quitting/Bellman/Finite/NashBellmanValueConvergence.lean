/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanClockReduction
import Math.SequenceVariation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Value convergence along a summable opponent clock

Exact root Nash controls every upward move of a player's continuation value:
the move is at most twice the common payoff bound times that player's
one-stage opponent-absorption mass.  Although downward moves need not obey a
pointwise clock bound, boundedness makes their total mass no larger than the
upward mass plus one endpoint span.  This yields a finite total-variation
estimate.

Consequently, along any bounded exact Nash--Bellman spine, summability of one
player's opponent clock implies absolute summability of that player's value
increments and hence convergence of the value coordinate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One-step increase -/

/-- On an exact Nash--Bellman edge, the survived successor can exceed the
current value only by twice the payoff bound times the marked player's
opponent-absorption mass. -/
theorem quittingNashBellman_successor_sub_current_le_two_mul_opponentAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor who| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root) :
    successor who - current who ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
  exact successorEscape_le_two_mul_opponentAbsorptionMass
    reward current successor root who M (-current who)
      (successor who - current who) hreward hsuccessorBound
      hbellman hnash (by simp) (by linarith)

/-- One-step increase bound in the canonical spine/clock interface. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.successor_sub_current_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι) (time : ℕ) :
    value (time + 1) who - value time who ≤
      2 * quittingRewardBound reward *
        quittingOpponentClockCharge roots who time := by
  exact
    quittingNashBellman_successor_sub_current_le_two_mul_opponentAbsorptionMass
      reward (value time) (value (time + 1)) (roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
      (hspine.1 (time + 1) who) (hspine.2.1 time) (hspine.2.2 time)

/-- Finite total variation of one value coordinate is controlled by its
finite opponent-clock mass. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.sum_abs_value_succ_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        |value (time + 1) who - value time who|) ≤
      2 * quittingRewardBound reward +
        4 * quittingRewardBound reward *
          (∑ time ∈ Finset.range horizon,
            quittingOpponentClockCharge roots who time) := by
  exact Math.sum_abs_succ_sub_le_of_bounded_of_increase_le_clock
    (fun time => value time who)
    (quittingOpponentClockCharge roots who)
    (quittingRewardBound reward)
    (fun time => hspine.1 time who)
    (quittingOpponentClockCharge_nonneg roots who)
    (hspine.successor_sub_current_le reward value roots who) horizon

/-! ## Summability and convergence -/

/-- A summable opponent clock gives absolutely summable increments of the
owner's value coordinate. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.summable_abs_value_succ_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι)
    (hclock : Summable (quittingOpponentClockCharge roots who)) :
    Summable (fun time =>
      |value (time + 1) who - value time who|) := by
  refine summable_of_sum_range_le
    (c := 2 * quittingRewardBound reward +
      4 * quittingRewardBound reward *
        ∑' time, quittingOpponentClockCharge roots who time)
    (fun _ => abs_nonneg _) ?_
  intro horizon
  calc
    (∑ time ∈ Finset.range horizon,
        |value (time + 1) who - value time who|) ≤
        2 * quittingRewardBound reward +
          4 * quittingRewardBound reward *
            (∑ time ∈ Finset.range horizon,
              quittingOpponentClockCharge roots who time) :=
      hspine.sum_abs_value_succ_sub_le reward value roots who horizon
    _ ≤ 2 * quittingRewardBound reward +
          4 * quittingRewardBound reward *
            ∑' time, quittingOpponentClockCharge roots who time := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left
      · exact hclock.sum_le_tsum (Finset.range horizon) fun time _ =>
          quittingOpponentClockCharge_nonneg roots who time
      · exact mul_nonneg (by norm_num)
          (quittingRewardBound_nonneg reward)

/-- **Summable-clock value convergence.**  Along a canonical exact
Nash--Bellman spine, a player with summable opponent clock has a convergent
value coordinate. -/
theorem IsCanonicalExactQuittingNashBellmanSpine.exists_tendsto_value_of_summableClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (who : ι)
    (hclock : Summable (quittingOpponentClockCharge roots who)) :
    ∃ limit : ℝ, Tendsto (fun time => value time who) atTop (nhds limit) := by
  have habsolute :=
    hspine.summable_abs_value_succ_sub reward value roots who hclock
  have hdist : Summable (fun time =>
      dist (value time who) (value time.succ who)) := by
    simpa [Real.dist_eq, abs_sub_comm, Nat.succ_eq_add_one] using habsolute
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

end GameTheory
