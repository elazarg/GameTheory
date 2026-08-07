/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingForwardBlockSingleSeam
import Math.CompactFiniteChargedReturn
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Finite charged forward packets produce projective lassos

This file is the payload-preserving capstone of finite charged closing.
Compactness first chooses one finite charge target from a fixed common compact
carrier.  The producer is then invoked once and returns a finite packet that
retains its roots, Bellman equations, support witnesses, rationality floors,
and charge proof.  The selected returned pair therefore belongs to the same
packet and can be reversed immediately into a single-seam projective lasso.

The compact carrier is fixed before the charge target is selected.  Merely
asking each target-dependent finite sequence to be bounded would be vacuous:
every finite sequence is bounded, with a bound that could grow with the target.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite exact forward Bellman packet inside one common compact carrier.
Only the prefix `0,...,horizon` is semantically constrained. -/
structure QuittingFiniteForwardPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι))
    (supportError chargeTarget : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  horizon : ℕ
  value_mem : ∀ time, time ≤ horizon → value time ∈ carrier
  policy : ∀ time, time < horizon →
    value (time + 1) = quittingRootSuccessorPayoff reward
      (value time) (roots time)
  support : ∀ time, time < horizon →
    IsQuittingRootSupportApproxNash reward
      (value time) supportError (roots time)
  rational : ∀ target time, time ≤ horizon →
    quittingPunishmentValue reward target - supportError ≤ value time target
  chargeTarget_le : chargeTarget ≤
    ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (roots time)

omit [DecidableEq ι] in
private theorem quittingRootAbsorptionMass_nonneg_packet
    (root : ι → PMF Bool) :
    0 ≤ quittingRootAbsorptionMass root := by
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_le_one root]

omit [DecidableEq ι] in
private theorem quittingRootAbsorptionMass_le_one_packet
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ 1 := by
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_nonneg root]

/-- **Finite charged-closing capstone.**

At local error `error / 2`, compactness selects one target-dependent packet
and one returned block with raw charge at least one.  Whole-block absorption
is at least one half, endpoint distance is below `error / 2`, and the reversed
block is therefore a single-seam projective lasso at error `error`. -/
theorem exists_singleSeamProjectiveLasso_of_finiteForwardPackets
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (hcarrier : IsCompact carrier)
    (hproducer : ∀ supportError : ℝ, 0 < supportError →
      ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
        Nonempty (QuittingFiniteForwardPacket
          reward carrier supportError chargeTarget))
    (error : ℝ) (herror : 0 < error) :
    ∃ K : ℕ,
      Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error) := by
  have hhalfError : 0 < error / 2 := by linarith
  obtain ⟨threshold, hthreshold0, hthreshold⟩ :=
    Math.exists_charge_threshold_for_close_pair_of_compact
      carrier hcarrier (error / 2) hhalfError
  obtain ⟨packet⟩ :=
    hproducer (error / 2) hhalfError threshold hthreshold0
  let state : ℕ → Payoff ι := fun time =>
    packet.value (min time packet.horizon)
  let charge : ℕ → ℝ := fun time =>
    if time < packet.horizon then
      quittingRootAbsorptionMass (packet.roots time)
    else 0
  have hstate : ∀ time, state time ∈ carrier := by
    intro time
    exact packet.value_mem _ (Nat.min_le_right _ _)
  have hcharge0 : ∀ time, 0 ≤ charge time := by
    intro time
    by_cases htime : time < packet.horizon
    · rw [show charge time =
          quittingRootAbsorptionMass (packet.roots time) by
        simp [charge, htime]]
      exact quittingRootAbsorptionMass_nonneg_packet _
    · simp [charge, htime]
  have hcharge1 : ∀ time, charge time ≤ 1 := by
    intro time
    by_cases htime : time < packet.horizon
    · rw [show charge time =
          quittingRootAbsorptionMass (packet.roots time) by
        simp [charge, htime]]
      exact quittingRootAbsorptionMass_le_one_packet _
    · simp [charge, htime]
  have hchargeSum :
      (∑ time ∈ Finset.range packet.horizon, charge time) =
        ∑ time ∈ Finset.range packet.horizon,
          quittingRootAbsorptionMass (packet.roots time) := by
    apply Finset.sum_congr rfl
    intro time htime
    have hlt := Finset.mem_range.mp htime
    simp [charge, hlt]
  have hlarge :
      threshold ≤ ∑ time ∈ Finset.range packet.horizon, charge time := by
    rw [hchargeSum]
    exact packet.chargeTarget_le
  obtain ⟨first, second, hfirst, hsecond, hdist, hgap⟩ :=
    hthreshold state charge packet.horizon
      hstate hcharge0 hcharge1 hlarge
  have hfirstLe : first ≤ packet.horizon :=
    le_trans hfirst.le hsecond
  have hfirstState : state first = packet.value first := by
    simp [state, Nat.min_eq_left hfirstLe]
  have hsecondState : state second = packet.value second := by
    simp [state, Nat.min_eq_left hsecond]
  have hdistValue :
      dist (packet.value first) (packet.value second) < error / 2 := by
    simpa only [hfirstState, hsecondState] using hdist
  let q : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (packet.roots time)
  have hprefixEq : ∀ cutoff, cutoff ≤ packet.horizon →
      (∑ time ∈ Finset.range cutoff, charge time) =
        ∑ time ∈ Finset.range cutoff, q time := by
    intro cutoff hcutoff
    apply Finset.sum_congr rfl
    intro time htime
    have hlt : time < packet.horizon :=
      lt_of_lt_of_le (Finset.mem_range.mp htime) hcutoff
    simp [charge, q, hlt]
  rw [hprefixEq second hsecond, hprefixEq first hfirstLe] at hgap
  have hsumSplit :
      (∑ time ∈ Finset.range second, q time) =
        (∑ time ∈ Finset.range first, q time) +
          ∑ offset ∈ Finset.range (second - first),
            q (first + offset) := by
    simpa [Nat.add_sub_of_le hfirstLe] using
      (Finset.sum_range_add q first (second - first))
  have hblock :
      1 ≤ ∑ offset ∈ Finset.range (second - first),
        q (first + offset) := by
    rw [hsumSplit] at hgap
    linarith
  let n : ℕ := second - first - 1
  have hlength : n + 1 = second - first := by
    dsimp only [n]
    omega
  have hend : first + n + 1 = second := by
    dsimp only [n]
    omega
  have hblockN :
      1 ≤ ∑ offset ∈ Finset.range (n + 1),
        q (first + offset) := by
    simpa only [hlength] using hblock
  have hq0 : ∀ time, 0 ≤ q time := by
    intro time
    exact quittingRootAbsorptionMass_nonneg_packet _
  have hq1 : ∀ time, q time ≤ 1 := by
    intro time
    exact quittingRootAbsorptionMass_le_one_packet _
  have hhalfRange :=
    Math.half_le_one_sub_prod_one_sub_of_one_le_sum_range
      q hq0 hq1 first (n + 1) hblockN
  have hweightedHalf :
      (1 : ℝ) / 2 ≤ quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle packet.roots first n) := by
    rw [quittingCyclicWeightedAbsorption_reversedForwardCycle]
    simpa only [q] using hhalfRange
  have hsumPos :
      0 < ∑ offset ∈ Finset.range (n + 1),
        q (first + offset) :=
    lt_of_lt_of_le zero_lt_one hblockN
  have hexists : ∃ offset ∈ Finset.range (n + 1),
      0 < q (first + offset) := by
    by_contra hno
    push_neg at hno
    have hsumNonpos :
        (∑ offset ∈ Finset.range (n + 1),
          q (first + offset)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro offset hoffset
      exact hno offset hoffset
    exact (not_lt_of_ge hsumNonpos) hsumPos
  obtain ⟨offset, hoffset, hoffsetPos⟩ := hexists
  let rawPhase : Fin (n + 1) :=
    ⟨offset, Finset.mem_range.mp hoffset⟩
  let absorbingPhase : Fin (n + 1) := rawPhase.rev
  have habsorbing :
      0 < quittingRootAbsorptionMass
        (quittingReversedForwardCycle packet.roots first n
          absorbingPhase) := by
    simpa [quittingReversedForwardCycle, absorbingPhase, rawPhase, q]
      using hoffsetPos
  have hclose : ∀ who,
      |packet.value first who - packet.value (first + n + 1) who| ≤
        error / 2 := by
    intro who
    rw [hend]
    have hcoordinate :
        dist (packet.value first who) (packet.value second who) <
          error / 2 :=
      lt_of_le_of_lt
        (dist_le_pi_dist (packet.value first) (packet.value second) who)
        hdistValue
    simpa [Real.dist_eq] using hcoordinate.le
  have hpolicy : ∀ time,
      first ≤ time → time < first + n + 1 →
      packet.value (time + 1) = quittingRootSuccessorPayoff reward
        (packet.value time) (packet.roots time) := by
    intro time _ htime
    have htimeSecond : time < second := by
      simpa only [hend] using htime
    exact packet.policy time (lt_of_lt_of_le htimeSecond hsecond)
  have hsupport : ∀ time,
      first ≤ time → time < first + n + 1 →
      IsQuittingRootSupportApproxNash reward
        (packet.value time) (error / 2) (packet.roots time) := by
    intro time _ htime
    have htimeSecond : time < second := by
      simpa only [hend] using htime
    exact packet.support time (lt_of_lt_of_le htimeSecond hsecond)
  have hrational : ∀ target time,
      first < time → time ≤ first + n + 1 →
      quittingPunishmentValue reward target -
          (error / 2 + error / 2) ≤ packet.value time target := by
    intro target time _ htime
    have htimeSecond : time ≤ second := by
      simpa only [hend] using htime
    have hpacket := packet.rational target time
      (le_trans htimeSecond hsecond)
    linarith
  have hclosingRatio :
      error / 2 ≤ (error / 2 + error / 2) *
        quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle packet.roots first n) := by
    calc
      error / 2 = (error / 2 + error / 2) * ((1 : ℝ) / 2) := by ring
      _ ≤ (error / 2 + error / 2) *
          quittingCyclicWeightedAbsorption
            (quittingReversedForwardCycle packet.roots first n) :=
        mul_le_mul_of_nonneg_left hweightedHalf (by linarith)
  let lasso :=
    quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock
      reward packet.roots packet.value first n
      (supportError := error / 2) (seamError := error / 2)
      (by linarith) (by linarith) hpolicy hsupport hclose
      hclosingRatio hrational absorbingPhase habsorbing
  refine ⟨n + 1, ?_⟩
  have herr : error / 2 + error / 2 = error := by ring
  rw [← herr]
  exact ⟨lasso⟩

/-- **Uniform-payoff corollary.**  Finite exact forward packets at every local
accuracy and every charge target, all living in one fixed compact carrier,
imply a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (hcarrier : IsCompact carrier)
    (hproducer : ∀ supportError : ℝ, 0 < supportError →
      ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
        Nonempty (QuittingFiniteForwardPacket
          reward carrier supportError chargeTarget)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    reward
  intro error herror
  exact exists_singleSeamProjectiveLasso_of_finiteForwardPackets
    reward carrier hcarrier hproducer error herror

end GameTheory
