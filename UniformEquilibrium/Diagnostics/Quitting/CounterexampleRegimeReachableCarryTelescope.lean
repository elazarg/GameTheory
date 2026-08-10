/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixConsumption
import Math.Probability.KilledTailPotential

/-!
# Reachable-prefix capacity telescope for carried dynamic debt

A chronological sequence of literally attached punishment-floor reachable
prepends runs opposite the charged relation: its current predecessor is
followed by the edge's tail.  The canonical reachable potential therefore
increases along chronological time.  Subtracting it from the regime's prefix
charge bound produces a nonnegative remaining capacity that decreases by at
least the edge's joint absorption charge.

When the same sequence carries coherent exact dynamic-debt annotations, the
aggregate diagonal seam is at most `card * rewardBound` times that charge.
Scaling remaining capacity by this constant gives an excessive killed
account for aggregate debt.  Finite telescoping consumes every seam, but it
retains one survival-weighted far-end debt boundary.  The final theorem makes
domination of that boundary the exact remaining premise; reachability and
capacity alone do not provide it.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- A chronological reachable predecessor sequence equipped with literal
exact dynamic-debt states over exactly the same Nash--Bellman points. -/
structure QuittingReachableDynamicDebtChronology
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  state : ℕ → QuittingPunishmentFloorReachableState reward
  edge : ℕ → QuittingPunishmentFloorReachableEdge reward
  edge_current : ∀ time, (edge time).current = state time
  edge_tail : ∀ time, (edge time).tail = state (time + 1)
  debtState : ℕ → QuittingDebtPoint ι
  debtPoint : ∀ time, (debtState time).1 = (state time).1.1
  debt_mem : ∀ time, debtState time ∈ quittingDebtBox reward
  debt_edge : ∀ time,
    IsQuittingDynamicDebtEdge reward (debtState time) (debtState (time + 1))

namespace QuittingReachableDynamicDebtChronology

variable (chain : QuittingReachableDynamicDebtChronology reward)

/-- Joint survival coefficient at one chronological debt edge. -/
def survival (time : ℕ) : ℝ :=
  quittingStationaryContinueMass
    (quittingRootOfSimplex (chain.debtState time).1.2)

/-- Aggregate diagonal debt seam at one chronological edge. -/
def source (time : ℕ) : ℝ :=
  ∑ who, quittingDynamicDebtSeam (chain.debtState time) who

/-- Aggregate exact dynamic debt carried by one chronological state. -/
def debt (time : ℕ) : ℝ :=
  ∑ who, (chain.debtState time).2 who

/-- Literal joint absorption charge of the corresponding reachable edge. -/
def charge (time : ℕ) : ℝ :=
  (chain.edge time).toBoxEdge.absorptionCharge

/-- Canonical reachable budget still available after the chronological
state. -/
def remainingCapacity (time : ℕ) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    quittingPunishmentFloorReachablePotential reward (chain.state time)

/-- Aggregate capacity account at the uniform singleton-debt scale. -/
def aggregateCapacityAccount (time : ℕ) : ℝ :=
  (Fintype.card ι : ℝ) * quittingRewardBound reward *
    chain.remainingCapacity time

private theorem anchoredChargeBound
    (regime : QuittingCounterexampleRegime reward) :
    HasQuittingPunishmentFloorAnchoredChargeBound reward
      (quittingPunishmentFloorPrefixChargeBound reward) :=
  QuittingCounterexampleRegime.hasAnchoredChargeBound regime

include regime

theorem remainingCapacity_nonneg (time : ℕ) :
    0 ≤ chain.remainingCapacity time := by
  unfold remainingCapacity
  have hle := quittingPunishmentFloorReachablePotential_le_chargeBound
    (anchoredChargeBound regime) (chain.state time)
  linarith

/-- Remaining capacity telescopes one reachable chronological edge. -/
theorem charge_add_remainingCapacity_succ_le (time : ℕ) :
    chain.charge time + chain.remainingCapacity (time + 1) ≤
      chain.remainingCapacity time := by
  have hdecrement :=
    quittingPunishmentFloorReachablePotential_predecessor_decrement
      (anchoredChargeBound regime) (chain.edge time)
  rw [chain.edge_current time, chain.edge_tail time] at hdecrement
  unfold charge remainingCapacity
  linarith

theorem aggregateCapacityAccount_nonneg (time : ℕ) :
    0 ≤ chain.aggregateCapacityAccount time := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward))
    (chain.remainingCapacity_nonneg (regime := regime) time)

omit regime in
/-- Aggregate diagonal seam is paid by the uniformly scaled legal charge. -/
theorem source_le_card_mul_rewardBound_mul_charge (time : ℕ) :
    chain.source time ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        chain.charge time := by
  have hroot : quittingRootOfSimplex (chain.debtState time).1.2 =
      (chain.edge time).toBoxEdge.root := by
    unfold QuittingPunishmentFloorReachableEdge.toBoxEdge
      QuittingPunishmentFloorBoxEdge.root
    rw [chain.debtPoint time, ← chain.edge_current time]
  have hpoint (who : ι) :
      quittingDynamicDebtSeam (chain.debtState time) who ≤
        quittingRewardBound reward * chain.charge time := by
    have hraw := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      (chain.debtState time) (chain.debt_mem time) who
    have hcap : quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
      (le_abs_self _).trans
        (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
    have hcharge0 : 0 ≤ chain.charge time :=
      (chain.edge time).toBoxEdge.absorptionCharge_nonneg
    rw [hroot] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_right hcap hcharge0)
  unfold source
  calc
    (∑ who, quittingDynamicDebtSeam (chain.debtState time) who) ≤
        ∑ _who : ι,
          (quittingRewardBound reward * chain.charge time) := by
      apply Finset.sum_le_sum
      intro who _
      exact hpoint who
    _ = (Fintype.card ι : ℝ) * quittingRewardBound reward *
        chain.charge time := by simp [mul_assoc]

/-- The scaled remaining capacity pays the aggregate seam and retains its
successor account. -/
theorem source_add_aggregateCapacityAccount_succ_le (time : ℕ) :
    chain.source time + chain.aggregateCapacityAccount (time + 1) ≤
      chain.aggregateCapacityAccount time := by
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  have hscale : 0 ≤ scale :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  have hsource := chain.source_le_card_mul_rewardBound_mul_charge time
  have hremaining :=
    chain.charge_add_remainingCapacity_succ_le (regime := regime) time
  calc
    chain.source time + chain.aggregateCapacityAccount (time + 1) ≤
        scale * chain.charge time +
          chain.aggregateCapacityAccount (time + 1) :=
      add_le_add_left hsource _
    _ = scale *
        (chain.charge time + chain.remainingCapacity (time + 1)) := by
      simp [aggregateCapacityAccount, scale]
      ring
    _ ≤ scale * chain.remainingCapacity time :=
      mul_le_mul_of_nonneg_left hremaining hscale
    _ = chain.aggregateCapacityAccount time := rfl

omit regime in
/-- Exact aggregate dynamic debt obeys the killed reference recursion. -/
theorem debt_step (time : ℕ) :
    chain.debt time = chain.source time +
      chain.survival time * chain.debt (time + 1) := by
  have hcoordinate (who : ι) :=
    quittingDynamicDebt_eq_continueMass_mul_add_seam
      (chain.debtState time) (chain.debtState (time + 1))
      (chain.debt_edge time) (chain.debt_mem (time + 1)).2.1 who
  unfold debt source survival
  calc
    (∑ who, (chain.debtState time).2 who) =
        ∑ who,
          (quittingDynamicDebtSeam (chain.debtState time) who +
            quittingStationaryContinueMass
                (quittingRootOfSimplex (chain.debtState time).1.2) *
              (chain.debtState (time + 1)).2 who) := by
      apply Finset.sum_congr rfl
      intro who _
      linarith [hcoordinate who]
    _ = (∑ who, quittingDynamicDebtSeam (chain.debtState time) who) +
        quittingStationaryContinueMass
            (quittingRootOfSimplex (chain.debtState time).1.2) *
          ∑ who, (chain.debtState (time + 1)).2 who := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

omit regime in
theorem survival_nonneg (time : ℕ) : 0 ≤ chain.survival time :=
  quittingStationaryContinueMass_nonneg _

/-- The aggregate remaining-capacity account is excessive for exact debt. -/
theorem aggregateCapacityAccount_isKilledExcessive :
    IsKilledExcessive chain.survival chain.source
      chain.aggregateCapacityAccount := by
  intro time
  have hadditive :=
    chain.source_add_aggregateCapacityAccount_succ_le
      (regime := regime) time
  have hsurvival : chain.survival time ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  have haccount :=
    chain.aggregateCapacityAccount_nonneg (regime := regime) (time + 1)
  calc
    chain.source time + chain.survival time *
        chain.aggregateCapacityAccount (time + 1) ≤
      chain.source time + chain.aggregateCapacityAccount (time + 1) := by
        exact add_le_add_right
          (mul_le_of_le_one_left haccount hsurvival) _
    _ ≤ chain.aggregateCapacityAccount time := hadditive

/-- **Finite carried-debt telescope.**  Once the one surviving far-end exact
debt boundary is dominated by the capacity account's boundary, all earlier
carried debt and diagonal seams are bounded by initial remaining capacity.

This boundary comparison is the precise premise not implied by reachable
attachment, exact edges, or finite prefix-charge capacity. -/
theorem debt_le_aggregateCapacityAccount_of_boundary
    (start fuel : ℕ)
    (hboundary :
      killedBoundaryRemainder chain.survival chain.debt start fuel ≤
        killedBoundaryRemainder chain.survival
          chain.aggregateCapacityAccount start fuel) :
    chain.debt start ≤ chain.aggregateCapacityAccount start := by
  have href : chain.debt start =
      killedTailAccount chain.survival chain.source chain.debt start fuel :=
    potential_eq_killedTailAccount chain.survival chain.source chain.debt
      chain.debt_step start fuel
  have haccount := killedTailAccount_le_of_excessive
    chain.survival chain.source chain.aggregateCapacityAccount
      chain.survival_nonneg
      (chain.aggregateCapacityAccount_isKilledExcessive (regime := regime))
      start fuel
  unfold killedTailAccount at href haccount
  linarith

end QuittingReachableDynamicDebtChronology

end GameTheory
