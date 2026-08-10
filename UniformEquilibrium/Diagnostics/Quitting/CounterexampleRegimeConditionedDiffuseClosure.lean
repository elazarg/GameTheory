/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Cycles.ConditionedProperFaceDeficientClock

/-!
# Counterexample exclusion on the singleton-tight diffuse boundary

The conditioned diffuse compilers no longer require the optimized source
values to dominate singleton payoffs.  Exact policy and endpoint Nash charge
that possible deficit to the deleted clock.  Consequently a counterexample
seam whose remaining absorption is positive and diffuse cannot converge to
the full singleton boundary.

The result keeps only the two genuine conditioning hypotheses explicit:
eventual absorption is positive at every date, and the normalized one-stage
mesh tends to zero.  Vanishing remaining absorption follows from the seam's
summable joint-absorption clock, while conditioned reward-box boundedness and
singleton individual rationality follow from the canonical seam itself.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

/-- **Singleton-tight diffuse closure.**  A canonical counterexample seam
cannot simultaneously have positive remaining absorption at every date,
vanishing conditioned mesh, and a phantom boundary equal to every player's
singleton payoff.  Both complete and deficient deleted clocks are consumed
by the conditioned compiler. -/
theorem not_all_limitValue_eq_singleton_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ¬ ∀ who, seam.limit.value who = quittingSoloBaseline reward who := by
  intro htight
  letI : Nonempty ι := regime.nonempty_players
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  have hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (seam.tail_edge time).1.1
  have hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time) := by
    intro time
    simpa only [value, roots, quittingDynamicDebtTailRoots] using
      (seam.tail_edge time).1.2
  have hsummable : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)) := by
    change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
    exact seam.jointAbsorption_summable
  have heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0) :=
    tendsto_quittingTailEventualAbsorption_zero_of_summable_absorption
      roots hsummable
  have hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value seam.limit.value
        time player| ≤ quittingRewardBound reward := by
    intro time player
    exact abs_quittingTailConditionedValue_le roots value seam.limit.value
      hpolicy (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) seam.value_tendsto time
      (hpositive time) player
  have hpunishment : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who := by
    intro who
    calc
      quittingPunishmentValue reward who ≤ seam.limit.value who :=
        seam.punishmentValue_le_limitValue who
      _ = quittingSoloReward reward who who := by
        rw [htight who]
        rfl
  have hexists :=
    quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseTail_punishmentIR
      reward roots value seam.limit.value hpolicy hnash hpositive
      heventualZero hconditionedBound htight hmesh hpunishment
  exact regime.not_exists_uniformEquilibriumPayoff hexists

/-- In the diffuse positive-absorption branch, a counterexample therefore
has a genuinely strict phantom plateau coordinate.  The reverse weak
inequality is already forced by exact Nash at the limiting all-Continue
self-loop. -/
theorem exists_singleton_lt_limitValue_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who, quittingSoloBaseline reward who < seam.limit.value who := by
  by_contra hnot
  push Not at hnot
  apply seam.not_all_limitValue_eq_singleton_of_diffuse hpositive hmesh
  intro who
  apply le_antisymm
  · exact hnot who
  · simpa [quittingSoloBaseline, quittingSoloReward,
      quittingSingletonTerminal] using seam.limit.soloReward_le_value who

/-- A strict phantom-plateau coordinate can appear only if that player is
eventually prescribed literal `Never` on the optimized source tail.  Indeed,
positive Quit hazards at arbitrarily late dates would pin the limiting
annotation to the singleton payoff. -/
theorem eventually_pureContinue_of_singleton_lt_limitValue
    (seam : QuittingCounterexampleSeamWitness regime) (who : ι)
    (hstrict : quittingSoloBaseline reward who < seam.limit.value who) :
    ∀ᶠ time : ℕ in atTop,
      quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false := by
  rw [Filter.eventually_atTop]
  by_contra hnot
  push Not at hnot
  choose selected hselected hnonzero using hnot
  have hselectedTendsto : Tendsto selected atTop atTop :=
    Filter.tendsto_atTop_mono hselected tendsto_id
  have hpositive : ∀ index,
      0 < (quittingDynamicDebtTailRoots seam.tail
        (selected index) who true).toReal := by
    intro index
    have hnonneg : 0 ≤ (quittingDynamicDebtTailRoots seam.tail
        (selected index) who true).toReal := ENNReal.toReal_nonneg
    have hne : (quittingDynamicDebtTailRoots seam.tail
        (selected index) who true).toReal ≠ 0 := by
      intro hzero
      apply hnonzero index
      exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hzero
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hpinned := quittingAnnotationBoundary_eq_singleton_of_activeSubsequence
    reward (quittingDynamicDebtTailRoots seam.tail)
      (fun time => (seam.tail time).1.1)
      seam.isCanonicalExactNashBellmanSpine seam.limit.value
      seam.value_tendsto
      (by
        change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
        exact seam.jointAbsorption_summable)
      who selected hselectedTendsto hpositive
  have hbaseline : quittingSoloBaseline reward who =
      reward (quittingSingletonTerminal who) who := rfl
  rw [hbaseline, ← hpinned] at hstrict
  exact (lt_irrefl _ hstrict)

/-- After one common finite cutoff, every player present in the physical
quitter support lies on a singleton-tight boundary coordinate. -/
theorem eventually_active_implies_limitValue_eq_singleton
    (seam : QuittingCounterexampleSeamWitness regime) :
    ∀ᶠ time : ℕ in atTop, ∀ who,
      quittingDynamicDebtTailRoots seam.tail time who ≠ PMF.pure false →
        seam.limit.value who = quittingSoloBaseline reward who := by
  rw [Filter.eventually_all]
  intro who
  by_cases htight : seam.limit.value who = quittingSoloBaseline reward who
  · exact Filter.Eventually.of_forall fun _ _ => htight
  · have hsoloLe : quittingSoloBaseline reward who ≤ seam.limit.value who := by
      simpa [quittingSoloBaseline, quittingSoloReward,
        quittingSingletonTerminal] using seam.limit.soloReward_le_value who
    have hstrict : quittingSoloBaseline reward who < seam.limit.value who :=
      lt_of_le_of_ne hsoloLe (Ne.symm htight)
    filter_upwards [
      seam.eventually_pureContinue_of_singleton_lt_limitValue who hstrict]
      with time hpure hactive
    exact (hactive hpure).elim

/-- **Sharp diffuse support separation.**  Every positive diffuse
counterexample seam contains a strict plateau player who is eventually absent
from the physical quitter support.  The remaining active source support is
therefore a proper subset of the player set and is singleton-tight. -/
theorem exists_strictPlateau_eventually_pureContinue_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who,
      quittingSoloBaseline reward who < seam.limit.value who ∧
        ∀ᶠ time : ℕ in atTop,
          quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false := by
  obtain ⟨who, hstrict⟩ :=
    seam.exists_singleton_lt_limitValue_of_diffuse hpositive hmesh
  exact ⟨who, hstrict,
    seam.eventually_pureContinue_of_singleton_lt_limitValue who hstrict⟩

/-- **Proper-face diffuse obstruction.**  Once the source support has settled
onto its singleton-tight face, complete player-deleted clocks would compile
unless the uniform pure-Quit defect of the absent spectators stays
nonvanishing.  Thus every diffuse counterexample has one of exactly two
remaining strategic obstructions: a deficient deleted clock, or persistent
one-stage support enlargement pressure. -/
theorem
    exists_summable_conditionedOpponentWeight_or_not_tendsto_rescaledQuitDefect
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    (∃ who start, Summable (fun offset =>
        quittingTailConditionedOpponentWeight
          (quittingDynamicDebtTailRoots seam.tail) (start + offset) who)) ∨
      ¬Tendsto
        (quittingConditionedRescaledQuitDefect reward
          (quittingDynamicDebtTailRoots seam.tail)
          (fun time => (seam.tail time).1.1) seam.limit.value hpositive)
        atTop (nhds 0) := by
  letI : Nonempty ι := regime.nonempty_players
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  by_cases hclock : ∃ who start, Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) who)
  · exact Or.inl hclock
  · right
    intro hdefect
    have hcomplete : ∀ who start,
        ¬Summable (fun offset =>
          quittingTailConditionedOpponentWeight roots (start + offset) who) := by
      push Not at hclock
      exact hclock
    obtain ⟨start, hstart⟩ := Filter.eventually_atTop.1
      seam.eventually_active_implies_limitValue_eq_singleton
    let suffixRoots := quittingRootSequenceSuffix roots start
    let suffixValue : ℕ → Payoff ι := fun time => value (start + time)
    have hsuffixPositive : ∀ time,
        0 < quittingTailEventualAbsorption suffixRoots time := by
      intro time
      simpa only [suffixRoots, quittingTailEventualAbsorption_suffix] using
        hpositive (start + time)
    have hpolicy : ∀ time, value time =
        quittingRootSuccessorPayoff reward (value (time + 1))
          (roots time) := by
      intro time
      exact (seam.tail_edge time).1.1
    have hnash : ∀ time,
        IsεQuittingRootEndpointNash reward (value (time + 1)) 0
          (roots time) := by
      intro time
      simpa only [value, roots, quittingDynamicDebtTailRoots] using
        (seam.tail_edge time).1.2
    have hconditionedBound : ∀ time player,
        |quittingTailConditionedValue roots value seam.limit.value
          time player| ≤ quittingRewardBound reward := by
      intro time player
      exact abs_quittingTailConditionedValue_le roots value seam.limit.value
        hpolicy (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) seam.value_tendsto time
        (hpositive time) player
    have hexists :=
      quittingGame_exists_uniformEquilibriumPayoff_of_conditionedProperFaceDiffuseTail
        reward suffixRoots suffixValue seam.limit.value
        (by
          intro time
          simpa only [suffixRoots, suffixValue, quittingRootSequenceSuffix,
            Nat.add_assoc] using hpolicy (start + time))
        (by
          intro time
          simpa only [suffixRoots, suffixValue, quittingRootSequenceSuffix,
            Nat.add_assoc] using hnash (start + time))
        hsuffixPositive
        (by
          intro time player
          simpa only [suffixRoots, suffixValue,
            quittingTailConditionedValue_suffix] using
              hconditionedBound (start + time) player)
        (by
          intro time who
          by_cases hinactive : suffixRoots time who = PMF.pure false
          · exact Or.inr hinactive
          · left
            exact hstart (start + time) (Nat.le_add_right start time) who
              (by simpa only [suffixRoots, quittingRootSequenceSuffix] using
                hinactive))
        (fun time =>
          quittingConditionedRescaledQuitDefect reward roots value
            seam.limit.value hpositive (start + time))
        (by
          simpa only [roots, value, Function.comp_def, Nat.add_comm] using
            hdefect.comp (tendsto_add_atTop_nat start))
        (by
          intro time who
          have hsource :=
            quittingStationaryFixedOpponentsQuitValue_le_conditionedValue_add_defect
              (reward := reward) roots value seam.limit.value hpositive
                (start + time) who
          calc
            quittingStationaryFixedOpponentsQuitValue reward
                  (quittingTailDiffuseRescaledRoot suffixRoots time
                    (hsuffixPositive time)) who =
                quittingStationaryFixedOpponentsQuitValue reward
                  (quittingTailDiffuseRescaledRoot roots (start + time)
                    (hpositive (start + time))) who := by
              rw [show quittingTailDiffuseRescaledRoot suffixRoots time
                    (hsuffixPositive time) =
                  quittingTailDiffuseRescaledRoot roots (start + time)
                    (hpositive (start + time)) by
                simpa only [suffixRoots] using
                  quittingTailDiffuseRescaledRoot_suffix roots start time
                    (hpositive (start + time))]
            _ ≤ quittingTailConditionedValue roots value seam.limit.value
                  (start + time) who +
                quittingConditionedRescaledQuitDefect reward roots value
                  seam.limit.value hpositive (start + time) := hsource
            _ = quittingTailConditionedValue suffixRoots suffixValue
                  seam.limit.value time who +
                quittingConditionedRescaledQuitDefect reward roots value
                  seam.limit.value hpositive (start + time) := by
              rw [show quittingTailConditionedValue suffixRoots suffixValue
                    seam.limit.value time =
                  quittingTailConditionedValue roots value seam.limit.value
                    (start + time) by
                simp only [suffixRoots, suffixValue,
                  quittingTailConditionedValue_suffix]])
        (by
          have hsource := hmesh.comp (tendsto_add_atTop_nat start)
          convert hsource using 1
          funext time
          simp only [suffixRoots, roots,
            quittingTailConditionedAbsorptionWeight_suffix,
            Function.comp_def, Nat.add_comm])
        (by
          intro who suffixStart
          have hsource := hcomplete who (start + suffixStart)
          simpa only [suffixRoots,
            quittingTailConditionedOpponentWeight_suffix, Nat.add_assoc] using
              hsource)
    exact regime.not_exists_uniformEquilibriumPayoff hexists

/-- **Unified proper-face obstruction.**  The deleted-clock alternative above
is not an additional counterexample branch.  If such a clock is summable,
conditioned solo extraction and a vanishing Quit defect force the deficient
owner's singleton vector above every singleton floor; punishment completion
then produces a uniform payoff.  Hence every positive diffuse counterexample
has a genuinely persistent rescaled pure-Quit defect. -/
theorem not_tendsto_rescaledQuitDefect_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ¬Tendsto
      (quittingConditionedRescaledQuitDefect reward
        (quittingDynamicDebtTailRoots seam.tail)
        (fun time => (seam.tail time).1.1) seam.limit.value hpositive)
      atTop (nhds 0) := by
  intro hdefect
  letI : Nonempty ι := regime.nonempty_players
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  have hclockOr :=
    seam.exists_summable_conditionedOpponentWeight_or_not_tendsto_rescaledQuitDefect
      hpositive hmesh
  rcases hclockOr with ⟨owner, start, hsummable⟩ | hnot
  · have hpolicy : ∀ time, value time =
        quittingRootSuccessorPayoff reward (value (time + 1))
          (roots time) := by
      intro time
      exact (seam.tail_edge time).1.1
    have hsummableAbsorption : Summable (fun time =>
        quittingRootAbsorptionMass (roots time)) := by
      change Summable (quittingDynamicDebtTailAbsorptionCharge seam.tail)
      exact seam.jointAbsorption_summable
    have heventualZero : Tendsto
        (quittingTailEventualAbsorption roots) atTop (nhds 0) :=
      tendsto_quittingTailEventualAbsorption_zero_of_summable_absorption
        roots hsummableAbsorption
    have hconditionedBound : ∀ time player,
        |quittingTailConditionedValue roots value seam.limit.value
          time player| ≤ quittingRewardBound reward := by
      intro time player
      exact abs_quittingTailConditionedValue_le roots value seam.limit.value
        hpolicy (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) seam.value_tendsto time
        (hpositive time) player
    obtain ⟨_, _, _, hownerPositiveLate⟩ :=
      conditionedDeletedClock_ownerMonopoly roots owner start hpositive
        heventualZero hmesh hsummable
    obtain ⟨supportStart, hsupport⟩ := Filter.eventually_atTop.1
      seam.eventually_active_implies_limitValue_eq_singleton
    obtain ⟨offset, hoffset, hownerPositive⟩ :=
      hownerPositiveLate supportStart
    have hownerActive : roots (start + offset) owner ≠ PMF.pure false := by
      intro hpure
      unfold quittingTailDiffuseRescaledHazard at hownerPositive
      rw [hpure] at hownerPositive
      simp at hownerPositive
    have hownerTight : seam.limit.value owner =
        quittingSoloBaseline reward owner :=
      hsupport (start + offset)
        (hoffset.trans (Nat.le_add_left offset start)) owner hownerActive
    have hpunishment : quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner := by
      calc
        quittingPunishmentValue reward owner ≤ seam.limit.value owner :=
          seam.punishmentValue_le_limitValue owner
        _ = quittingSoloBaseline reward owner := hownerTight
        _ = quittingSoloReward reward owner owner :=
          quittingSoloBaseline_apply reward owner
    let suffixRoots := quittingRootSequenceSuffix roots start
    let suffixValue : ℕ → Payoff ι := fun time => value (start + time)
    have hsuffixPositive : ∀ time,
        0 < quittingTailEventualAbsorption suffixRoots time := by
      intro time
      simpa only [suffixRoots, quittingTailEventualAbsorption_suffix] using
        hpositive (start + time)
    have hdefectSuffix : Tendsto
        (quittingConditionedRescaledQuitDefect reward suffixRoots suffixValue
          seam.limit.value hsuffixPositive) atTop (nhds 0) := by
      have hshiftRight := hdefect.comp (tendsto_add_atTop_nat start)
      have hshift : Tendsto (fun time =>
          quittingConditionedRescaledQuitDefect reward
            (quittingDynamicDebtTailRoots seam.tail)
            (fun date => (seam.tail date).1.1) seam.limit.value hpositive
            (start + time)) atTop (nhds 0) := by
        apply hshiftRight.congr'
        exact Filter.Eventually.of_forall fun time => by
          exact congrArg
            (quittingConditionedRescaledQuitDefect reward
              (quittingDynamicDebtTailRoots seam.tail)
              (fun date => (seam.tail date).1.1) seam.limit.value hpositive)
            (Nat.add_comm time start)
      convert hshift using 1
      funext time
      unfold quittingConditionedRescaledQuitDefect
      apply Finset.sum_congr rfl
      intro who _
      rw [show quittingTailDiffuseRescaledRoot suffixRoots time
            (hsuffixPositive time) =
          quittingTailDiffuseRescaledRoot roots (start + time)
            (hpositive (start + time)) by
        simpa only [suffixRoots] using
          quittingTailDiffuseRescaledRoot_suffix roots start time
            (hpositive (start + time))]
      rw [show quittingTailConditionedValue suffixRoots suffixValue
            seam.limit.value time =
          quittingTailConditionedValue roots value seam.limit.value
            (start + time) by
        simp only [suffixRoots, suffixValue,
          quittingTailConditionedValue_suffix]]
    have hexists : ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
      refine ⟨quittingSoloReward reward owner, ?_⟩
      exact
        isUniformEquilibriumPayoff_solo_of_summableClock_and_vanishingQuitDefect
          suffixRoots suffixValue seam.limit.value
          (by
            intro time
            simpa only [suffixRoots, suffixValue, quittingRootSequenceSuffix,
              Nat.add_assoc] using hpolicy (start + time))
          hsuffixPositive
          (by
            have hshift := heventualZero.comp (tendsto_add_atTop_nat start)
            convert hshift using 1
            funext time
            simp only [suffixRoots, roots,
              quittingTailEventualAbsorption_suffix,
              Function.comp_apply, Nat.add_comm])
          (by
            intro time player
            simpa only [suffixRoots, suffixValue,
              quittingTailConditionedValue_suffix] using
                hconditionedBound (start + time) player)
          (by
            have hshift := hmesh.comp (tendsto_add_atTop_nat start)
            convert hshift using 1
            funext time
            simp only [suffixRoots, roots,
              quittingTailConditionedAbsorptionWeight_suffix,
              Function.comp_apply, Nat.add_comm])
          hdefectSuffix owner
          (by
            simpa only [suffixRoots,
              quittingTailConditionedOpponentWeight_suffix] using hsummable)
          hpunishment
    exact regime.not_exists_uniformEquilibriumPayoff hexists
  · exact hnot hdefect

/-- Search-facing quantitative form of the unified obstruction.  Some fixed
positive amount of immediate-Quit pressure recurs arbitrarily late along the
diffuse rescaled chronology. -/
theorem exists_persistent_rescaledQuitDefect_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ start, ∃ time, start ≤ time ∧
      eta ≤ quittingConditionedRescaledQuitDefect reward
        (quittingDynamicDebtTailRoots seam.tail)
        (fun date => (seam.tail date).1.1) seam.limit.value hpositive time := by
  by_contra hnone
  push Not at hnone
  have htendsto : Tendsto
      (quittingConditionedRescaledQuitDefect reward
        (quittingDynamicDebtTailRoots seam.tail)
        (fun date => (seam.tail date).1.1) seam.limit.value hpositive)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨start, hstart⟩ := hnone epsilon hepsilon
    refine ⟨start, fun time htime => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg]
    · exact hstart time htime
    · exact quittingConditionedRescaledQuitDefect_nonneg
        (reward := reward) (quittingDynamicDebtTailRoots seam.tail)
          (fun date => (seam.tail date).1.1) seam.limit.value hpositive time
  exact seam.not_tendsto_rescaledQuitDefect_of_diffuse hpositive hmesh
    htendsto

end QuittingCounterexampleSeamWitness

end GameTheory
