/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge

/-!
# The positive-debt all-Continue limit of the optimized tail

The optimized exact dynamic-debt tail extracted from a counterexample has
summable joint absorption.  This module completes its limit geometry.

* prescribed values have summable coordinatewise variation and converge;
* exact debt is monotone forward, bounded, and converges;
* displayed roots converge coordinatewise to all-Continue; and
* the limiting value/root/debt state is an exact dynamic-debt self-loop.

The selected debt owner retains debt at least the regime's terminal gap.  Its
limiting value consequently dominates both its solo payoff and behavioral
punishment floor.  The limit remains a phantom boundary annotation: the
self-loop statement does not identify it with the terminal payoff of an
all-Continue profile.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingDynamicDebtTail

variable (tail : ℕ → QuittingDebtPoint ι)

/-- One-stage prescribed-value motion is controlled by joint absorption. -/
theorem abs_value_succ_sub_le_two_mul_absorptionMass
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (time : ℕ) (who : ι) :
    |(tail (time + 1)).1.1 who - (tail time).1.1 who| ≤
      2 * quittingRewardBound reward *
        quittingDynamicDebtTailAbsorptionCharge tail time := by
  rw [congrFun (hedge time).1.1 who]
  simpa [abs_sub_comm, quittingDynamicDebtTailAbsorptionCharge,
      quittingDynamicDebtTailRoots] using
    (abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time) who
        (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
        (abs_le.mpr ⟨(hbox (time + 1)).1.1 who,
          (hbox (time + 1)).1.2 who⟩))

/-- Summable absorption makes every prescribed-value coordinate have
summable absolute increments. -/
theorem summable_abs_value_succ_sub
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hsummable : Summable (quittingDynamicDebtTailAbsorptionCharge tail))
    (who : ι) :
    Summable (fun time ↦
      |(tail (time + 1)).1.1 who - (tail time).1.1 who|) :=
  Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
    (fun time ↦
      QuittingDynamicDebtTail.abs_value_succ_sub_le_two_mul_absorptionMass
        tail hbox hedge time who)
    (hsummable.mul_left (2 * quittingRewardBound reward))

/-- Exact dynamic debt is monotone in chronological time. -/
theorem monotone_debt
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) :
    Monotone (fun time ↦ (tail time).2 who) := by
  apply monotone_nat_of_le_succ
  intro time
  rw [(hedge time).2 who]
  exact quittingDynamicDebtUpdate_le_successor
    reward (tail time) (tail (time + 1)) (hedge time).1
      (hbox (time + 1)).2.1 who

omit [DecidableEq ι] in
/-- Every debt coordinate is bounded above by its positive singleton cap. -/
theorem bddAbove_range_debt
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (who : ι) :
    BddAbove (Set.range fun time ↦ (tail time).2 who) := by
  refine ⟨quittingPositiveSingletonDebtCap reward who, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact (hbox time).2.2 who

/-- The pure-Quit deviation gives a uniform solo lower estimate at every
stage, with error controlled by opponent absorption. -/
theorem soloReward_sub_opponentHazard_le_value
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (time : ℕ) (who : ι) :
    quittingSoloReward reward who who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass
            (quittingDynamicDebtTailRoots tail time) who ≤
      (tail time).1.1 who := by
  have hest :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time) who
        (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
  have hnash : IsεQuittingRootNash reward (tail (time + 1)).1.1 0
      (quittingDynamicDebtTailRoots tail time) :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time)).1 (hedge time).1.2
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (tail (time + 1)).1.1
      (quittingDynamicDebtTailRoots tail time) who hnash
  have hcurrent := congrFun (hedge time).1.1 who
  have hpair := abs_le.mp hest
  simp only [quittingDynamicDebtTailRoots] at hquit hpair
  rw [← hcurrent] at hquit
  have hsolo : quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := rfl
  rw [hsolo]
  simp only [quittingDynamicDebtTailRoots]
  linarith [hpair.1, hcurrent]

end QuittingDynamicDebtTail

/-- A positive-debt all-Continue boundary state selected from an exact tail. -/
structure QuittingPositiveDebtSelfLoopLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  value : Payoff ι
  debt : Payoff ι
  owner : ι
  ownerDebt_pos : 0 < debt owner
  state_mem :
    (((value, quittingAllContinueSimplexRoot), debt) : QuittingDebtPoint ι) ∈
      quittingDebtBox reward
  exactSelfLoop :
    IsQuittingDynamicDebtEdge reward
      ((value, quittingAllContinueSimplexRoot), debt)
      ((value, quittingAllContinueSimplexRoot), debt)

namespace QuittingPositiveDebtSelfLoopLimit

/-- A positive limiting debt is bounded by the corresponding strictly
positive own singleton reward, rather than merely by its positive part. -/
theorem debt_le_soloReward_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    limit.debt who ≤ reward (quittingSingletonTerminal who) who := by
  have hdebtCap := limit.state_mem.2.2 who
  unfold quittingPositiveSingletonDebtCap at hdebtCap
  rcases lt_max_iff.mp (lt_of_lt_of_le hdebtPos hdebtCap) with
    hzero | hsolo
  · exact (lt_irrefl 0 hzero).elim
  · simpa [max_eq_right hsolo.le] using hdebtCap

/-- Every coordinate's own singleton reward is dominated by its prescribed
value at the all-Continue exact Nash self-loop.  This is a property of the
exact Nash self-loop and does not require positive debt. -/
theorem soloReward_le_value
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ limit.value who := by
  have hquit :=
    quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
      reward (limit.value, quittingAllContinueSimplexRoot)
        (limit.value, quittingAllContinueSimplexRoot)
        limit.exactSelfLoop.1 who
  simpa [quittingRootOfSimplex_allContinueSimplexRoot] using hquit

/-- Positive-debt compatibility wrapper for the general self-loop singleton
inequality. -/
theorem soloReward_le_value_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (_hdebtPos : 0 < limit.debt who) :
    reward (quittingSingletonTerminal who) who ≤ limit.value who :=
  limit.soloReward_le_value who

/-- Positive limiting debt is no larger than its phantom prescribed value. -/
theorem debt_le_value_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    limit.debt who ≤ limit.value who :=
  (limit.debt_le_soloReward_of_debt_pos who hdebtPos).trans
    (limit.soloReward_le_value_of_debt_pos who hdebtPos)

/-- Every positive-debt coordinate lies above its behavioral punishment
floor at the phantom self-loop.  The distinguished owner is only the
coordinate for which positivity is supplied by the extraction theorem. -/
theorem punishmentValue_le_value_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    quittingPunishmentValue reward who ≤ limit.value who := by
  have hsoloPos : 0 < reward (quittingSingletonTerminal who) who :=
    hdebtPos.trans_le (limit.debt_le_soloReward_of_debt_pos who hdebtPos)
  have hsoloLe := limit.soloReward_le_value_of_debt_pos who hdebtPos
  have hpunishment := quittingPunishmentValue_le_max_solo reward who
  rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
    (Finset.singleton_nonempty who) who] at hpunishment
  change quittingPunishmentValue reward who ≤
    max (reward (quittingSingletonTerminal who) who) 0 at hpunishment
  rw [max_eq_left hsoloPos.le] at hpunishment
  exact hpunishment.trans hsoloLe

/-- The marked positive-debt coordinate lies above its behavioral punishment
floor at the phantom self-loop. -/
theorem punishmentValue_le_ownerValue
    (limit : QuittingPositiveDebtSelfLoopLimit reward) :
    quittingPunishmentValue reward limit.owner ≤ limit.value limit.owner :=
  limit.punishmentValue_le_value_of_debt_pos
    limit.owner limit.ownerDebt_pos

/-- **All-date floor safety for positive debt.**  Suppose a boxed exact-D
tail converges to the supplied all-Continue self-loop in both value and debt.
At every finite date, every coordinate carrying positive debt already lies
above its behavioral punishment floor.  Otherwise floor violation persists
and the value coordinate moves only downward, while debt moves upward to a
positive limiting coordinate; the self-loop then gives the opposite floor
inequality. -/
theorem punishmentValue_le_tailValue_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hvalue : ∀ who, Tendsto (fun time ↦ (tail time).1.1 who) atTop
      (nhds (limit.value who)))
    (hdebt : ∀ who, Tendsto (fun time ↦ (tail time).2 who) atTop
      (nhds (limit.debt who)))
    (who : ι) (time : ℕ) (hdebtPos : 0 < (tail time).2 who) :
    quittingPunishmentValue reward who ≤ (tail time).1.1 who := by
  by_contra hnot
  push Not at hnot
  have hdebtMono := QuittingDynamicDebtTail.monotone_debt
    tail hbox hedge who
  have hlimitDebt : (tail time).2 who ≤ limit.debt who := by
    apply ge_of_tendsto (hdebt who)
    filter_upwards [eventually_ge_atTop time] with later hlater
    exact hdebtMono hlater
  have hlimitDebtPos : 0 < limit.debt who :=
    hdebtPos.trans_le hlimitDebt
  have hlimitFloor :=
    limit.punishmentValue_le_value_of_debt_pos who hlimitDebtPos
  have hlimitValueLe : limit.value who ≤ (tail time).1.1 who := by
    apply le_of_tendsto (hvalue who)
    filter_upwards [eventually_ge_atTop time] with later hlater
    have hgap := quittingDynamicDebtTail_punishmentGap_mono
      tail hedge who hnot later hlater
    linarith
  linarith

end QuittingPositiveDebtSelfLoopLimit

namespace QuittingCounterexampleRegime

/-- **Joint value/debt limit of the optimized tail.**  The extracted
summably absorbing exact-D tail converges coordinatewise in value and debt to
a positive-debt all-Continue exact dynamic-debt self-loop.  The original
projective subsequence and all exact-edge certificates are retained. -/
theorem exists_terminalGapDynamicDebtTail_selfLoopLimit
    (regime : QuittingCounterexampleRegime reward) [Nonempty ι] :
    ∃ (tail : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (limit : QuittingPositiveDebtSelfLoopLimit reward),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds tail) ∧
      (∀ time, tail time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (tail time) (tail (time + 1))) ∧
      regime.terminalGap ≤ (tail 0).2 limit.owner ∧
      regime.terminalGap ≤ limit.debt limit.owner ∧
      (∀ who, Tendsto (fun time ↦ (tail time).1.1 who) atTop
        (nhds (limit.value who))) ∧
      (∀ who, Tendsto (fun time ↦ (tail time).2 who) atTop
        (nhds (limit.debt who))) ∧
      (∀ who, Tendsto (fun time ↦
          (quittingDynamicDebtTailRoots tail time who true).toReal)
        atTop (nhds 0)) ∧
      (∀ who, Tendsto (fun time ↦
          (quittingDynamicDebtTailRoots tail time who false).toReal)
        atTop (nhds 1)) ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) limit.owner) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge tail) := by
  obtain ⟨tail, subseq, owner, hsubseq, hprojective, hbox, hedge,
      hownerDebt, hownerClock, habsorption⟩ :=
    regime.exists_terminalGapDynamicDebtTail_summableAbsorption
  have hvalueConverge : ∀ who : ι, ∃ coordinateLimit : ℝ,
      Tendsto (fun time ↦ (tail time).1.1 who) atTop
        (nhds coordinateLimit) := by
    intro who
    have hdist : Summable (fun time ↦
        dist ((tail time).1.1 who) ((tail (time + 1)).1.1 who)) := by
      simpa [Real.dist_eq, abs_sub_comm] using
        QuittingDynamicDebtTail.summable_abs_value_succ_sub
          tail hbox hedge habsorption who
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose valueLimit hvalueLimit using hvalueConverge
  let debtLimit : Payoff ι := fun who ↦ ⨆ time, (tail time).2 who
  have hdebtLimit : ∀ who,
      Tendsto (fun time ↦ (tail time).2 who) atTop
        (nhds (debtLimit who)) := by
    intro who
    exact tendsto_atTop_ciSup
      (QuittingDynamicDebtTail.monotone_debt tail hbox hedge who)
      (QuittingDynamicDebtTail.bddAbove_range_debt tail hbox who)
  have hvalueBox : valueLimit ∈ Set.Icc
      (fun _ : ι ↦ -quittingRewardBound reward)
      (fun _ : ι ↦ quittingRewardBound reward) := by
    constructor
    · intro who
      exact ge_of_tendsto' (hvalueLimit who)
        (fun time ↦ (hbox time).1.1 who)
    · intro who
      exact le_of_tendsto' (hvalueLimit who)
        (fun time ↦ (hbox time).1.2 who)
  have hdebtBox : debtLimit ∈ Set.Icc (0 : Payoff ι)
      (quittingPositiveSingletonDebtCap reward) := by
    constructor
    · intro who
      exact ge_of_tendsto' (hdebtLimit who)
        (fun time ↦ (hbox time).2.1 who)
    · intro who
      exact le_of_tendsto' (hdebtLimit who)
        (fun time ↦ (hbox time).2.2 who)
  have habsorptionZero : Tendsto
      (quittingDynamicDebtTailAbsorptionCharge tail) atTop (nhds 0) :=
    habsorption.tendsto_atTop_zero
  have hopponentZero : ∀ who, Tendsto (fun time ↦
      quittingRootOpponentAbsorptionMass
        (quittingDynamicDebtTailRoots tail time) who) atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg
        (quittingDynamicDebtTailRoots tail) who _
    · exact fun time ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (quittingDynamicDebtTailRoots tail time) who
    · exact habsorptionZero
  have hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ valueLimit who := by
    intro who
    have hlower : Tendsto (fun time ↦
        quittingSoloReward reward who who -
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass
              (quittingDynamicDebtTailRoots tail time) who)
        atTop (nhds (quittingSoloReward reward who who)) := by
      have hscaled := (hopponentZero who).const_mul
        (2 * quittingRewardBound reward)
      simpa using tendsto_const_nhds.sub hscaled
    have hle := le_of_tendsto_of_tendsto' hlower (hvalueLimit who)
      (fun time ↦ QuittingDynamicDebtTail.soloReward_sub_opponentHazard_le_value
        tail hedge time who)
    exact hle
  have hownerZero_le_limit : (tail 0).2 owner ≤ debtLimit owner :=
    ge_of_tendsto' (hdebtLimit owner) fun time ↦
      QuittingDynamicDebtTail.monotone_debt tail hbox hedge owner
        (Nat.zero_le time)
  have hownerLimit : regime.terminalGap ≤ debtLimit owner :=
    hownerDebt.trans hownerZero_le_limit
  have hselfNash : IsQuittingNashBellmanEdge reward
      (valueLimit, quittingAllContinueSimplexRoot)
      (valueLimit, quittingAllContinueSimplexRoot) := by
    constructor
    · change valueLimit = quittingRootSuccessorPayoff reward valueLimit
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        quittingRootSuccessorPayoff_allContinueRoot_eq]
    · change IsεQuittingRootEndpointNash reward valueLimit 0
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
      exact quittingAllContinueRoot_isZeroNash_of_singleton_le
        reward valueLimit hsolo
  have hopponentMass : ∀ who,
      quittingDebtOpponentContinueMass
          (((valueLimit, quittingAllContinueSimplexRoot), debtLimit) :
            QuittingDebtPoint ι) who = 1 := by
    intro who
    rw [quittingDebtOpponentContinueMass_eq_stationary,
      quittingRootOfSimplex_allContinueSimplexRoot]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_one
    intro player _
    by_cases hplayer : player = who
    · subst player
      simp
    · rw [Function.update_of_ne hplayer]
      simp [quittingAllContinueRoot]
  have hselfDynamic : IsQuittingDynamicDebtEdge reward
      ((valueLimit, quittingAllContinueSimplexRoot), debtLimit)
      ((valueLimit, quittingAllContinueSimplexRoot), debtLimit) := by
    refine ⟨hselfNash, fun who ↦ ?_⟩
    unfold quittingDynamicDebtUpdate
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootQuitPayoff_allContinueRoot,
      quittingRootContinuePayoff_allContinueRoot,
      hopponentMass who]
    have hdebtNonneg := hdebtBox.1 who
    rw [max_eq_right]
    · dsimp
      ring
    · dsimp only
      rw [one_mul]
      exact (hsolo who).trans (le_add_of_nonneg_right hdebtNonneg)
  let limit : QuittingPositiveDebtSelfLoopLimit reward := {
    value := valueLimit
    debt := debtLimit
    owner := owner
    ownerDebt_pos := lt_of_lt_of_le regime.terminalGap_pos hownerLimit
    state_mem := ⟨hvalueBox, hdebtBox⟩
    exactSelfLoop := hselfDynamic }
  have hquitConverge : ∀ who, Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who true).toReal)
      atTop (nhds 0) := fun who ↦
    quitProbability_tendsto_zero_of_summable_dynamicDebtTailAbsorptionCharge
      tail habsorption who
  have hcontinueConverge : ∀ who, Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who false).toReal)
      atTop (nhds 1) := fun who ↦
    continueProbability_tendsto_one_of_summable_dynamicDebtTailAbsorptionCharge
      tail habsorption who
  exact ⟨tail, subseq, limit, hsubseq, hprojective, hbox, hedge,
    hownerDebt, hownerLimit, hvalueLimit, hdebtLimit, hquitConverge,
    hcontinueConverge, hownerClock, habsorption⟩

end QuittingCounterexampleRegime

end GameTheory
