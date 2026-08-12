/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentForcedOwnerDispatch

/-!
# Forced-owner refusal is a literal semantic-debt charge

The punishment value in an atomic-blocker refusal is not the prescribed
continuation payoff.  It is nevertheless below the literal shifted tail's
best-response envelope.  Consequently a refusal gap at an owner-forced-Quit
face is paid by the increase of the owner's semantic best-response debt after
one actual root, after subtracting the honest joint-survival transport of the
next debt.

This is the missing sign behind the observer-absent forced-owner wall.  The
charge is not assembled from independently chosen rowwise replies.  It is
part of the debt of one literal carrier profile, hence is approached by one
legal behavioral deviation.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **One-row refusal/debt inequality.**  The actual owner-Quit probability
times the positive forced-owner refusal, plus the joint-survival transport of
the shifted debt, is bounded by the current literal semantic debt. -/
theorem quittingOwnerQuitProbability_mul_forcedRefusal_add_transport_le_prefixDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (owner : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair owner)
    (hfloor : quittingPunishmentValue reward owner ≤ pair.2 owner) :
    (root owner true).toReal *
          max 0 (-quittingAtomicBlockerBalance reward
            (Function.update root owner (PMF.pure true)) owner) +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair owner ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) owner := by
  let debt := quittingTerminalSemanticDebt pair owner
  let quitValue := quittingRootQuitPayoff reward pair.1 root owner
  let continueValue := quittingRootContinuePayoff reward pair.1 root owner
  let envelopeContinue := quittingRootContinuePayoff reward
    (Function.update pair.1 owner (pair.2 owner)) root owner
  let refusal := max 0 (-quittingAtomicBlockerBalance reward
    (Function.update root owner (PMF.pure true)) owner)
  have hdebtEq : pair.2 owner = pair.1 owner + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have henvelopeContinue : envelopeContinue = continueValue +
      quittingRootOpponentContinueMass root owner * debt := by
    dsimp [envelopeContinue, continueValue]
    rw [hdebtEq, quittingRootContinuePayoff_update_add]
  have hforcedObey : quittingForcedOwnerObeyValue reward
      (Function.update root owner (PMF.pure true)) owner = quitValue := by
    dsimp [quitValue, quittingForcedOwnerObeyValue, quittingRootQuitPayoff]
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
    have hzero : quittingStationaryContinueMass
        (Function.update root owner (PMF.pure true)) = 0 :=
      quittingStationaryContinueMass_eq_zero_of_owner_eq_pure
        (Function.update_self owner (PMF.pure true) root)
    rw [hzero, zero_mul, add_zero]
  have hforcedMass : quittingForcedOwnerAllOutsidersContinueMass
      (Function.update root owner (PMF.pure true)) owner =
        quittingRootOpponentContinueMass root owner := by
    simp only [quittingForcedOwnerAllOutsidersContinueMass,
      quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingRootOpponentContinueMass, Function.update_idem]
  have hforcedReward : quittingStationaryFixedOpponentsContinueReward reward
      (Function.update root owner (PMF.pure true)) owner =
        quittingStationaryFixedOpponentsContinueReward reward root owner := by
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
    rw [Function.update_idem]
  have hrefusalRaw : -quittingAtomicBlockerBalance reward
      (Function.update root owner (PMF.pure true)) owner =
        quittingRootContinuePayoff reward
            (Function.update pair.1 owner
              (quittingPunishmentValue reward owner)) root owner -
          quitValue := by
    have hcontinuePunish : quittingRootContinuePayoff reward
          (Function.update pair.1 owner
            (quittingPunishmentValue reward owner)) root owner =
        quittingStationaryFixedOpponentsContinueReward reward root owner +
          quittingRootOpponentContinueMass root owner *
            quittingPunishmentValue reward owner := by
      unfold quittingRootContinuePayoff
      rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
      simp only [Function.update_self]
      rfl
    unfold quittingAtomicBlockerBalance quittingForcedOwnerRefusalCap
    rw [hforcedObey, hforcedMass, hforcedReward]
    rw [hcontinuePunish]
    ring
  have hpunishContinue : quittingRootContinuePayoff reward
        (Function.update pair.1 owner
          (quittingPunishmentValue reward owner)) root owner ≤
      envelopeContinue := by
    dsimp [envelopeContinue]
    unfold quittingRootContinuePayoff
    have h := quittingRootExpectedPayoff_continuation_le_add reward
      (Function.update pair.1 owner (quittingPunishmentValue reward owner))
      (Function.update pair.1 owner (pair.2 owner))
      (Function.update root owner (PMF.pure false)) owner
      (δ := 0) (by norm_num)
      (by simpa using hfloor)
    simpa using h
  have hrefusalLe : refusal ≤ max 0 (envelopeContinue - quitValue) := by
    dsimp [refusal]
    rw [hrefusalRaw]
    exact max_le_max (le_refl 0)
      (sub_le_sub_right hpunishContinue quitValue)
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  have hjoint : quittingStationaryContinueMass root =
      (root owner false).toReal *
        quittingRootOpponentContinueMass root owner := by
    rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own root owner]
    change quittingRootOpponentContinueMass root owner *
      (root owner false).toReal = _
    ring
  have hsuccessor := quittingRootSuccessorPayoff_eq_endpointMix
    reward pair.1 root owner
  change (root owner true).toReal * refusal +
      quittingStationaryContinueMass root * debt ≤
    max quitValue envelopeContinue -
      quittingRootSuccessorPayoff reward pair.1 root owner
  rw [hsuccessor, hjoint]
  change (root owner true).toReal * refusal +
      (root owner false).toReal *
          quittingRootOpponentContinueMass root owner * debt ≤
    max quitValue envelopeContinue -
      ((root owner true).toReal * quitValue +
        (root owner false).toReal * continueValue)
  have hq0 : 0 ≤ (root owner true).toReal := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ (root owner false).toReal := ENNReal.toReal_nonneg
  have hq : (root owner true).toReal =
      1 - (root owner false).toReal := by linarith
  have htransport0 : 0 ≤
      quittingRootOpponentContinueMass root owner * debt :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root owner) hdebt
  have hweightedRefusal := mul_le_mul_of_nonneg_left hrefusalLe hq0
  by_cases hsign : envelopeContinue - quitValue ≤ 0
  · rw [max_eq_left hsign, mul_zero] at hweightedRefusal
    have henvelopeLe : envelopeContinue ≤ quitValue := sub_nonpos.mp hsign
    rw [max_eq_left henvelopeLe]
    calc
      (root owner true).toReal * refusal +
          (root owner false).toReal *
            quittingRootOpponentContinueMass root owner * debt ≤
        0 + (root owner false).toReal *
            quittingRootOpponentContinueMass root owner * debt :=
          add_le_add hweightedRefusal (le_refl _)
      _ ≤ (root owner false).toReal * (quitValue - continueValue) := by
        have hinner : quittingRootOpponentContinueMass root owner * debt ≤
            quitValue - continueValue := by
          rw [henvelopeContinue] at henvelopeLe
          linarith
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinner hc0
      _ = quitValue -
          ((root owner true).toReal * quitValue +
            (root owner false).toReal * continueValue) := by
        rw [hq]
        ring
  · have hpositive : 0 ≤ envelopeContinue - quitValue := le_of_not_ge hsign
    rw [max_eq_right hpositive] at hweightedRefusal
    rw [max_eq_right (by linarith : quitValue ≤ envelopeContinue)]
    calc
      (root owner true).toReal * refusal +
          (root owner false).toReal *
            quittingRootOpponentContinueMass root owner * debt ≤
        (root owner true).toReal * (envelopeContinue - quitValue) +
          (root owner false).toReal *
            quittingRootOpponentContinueMass root owner * debt :=
        add_le_add hweightedRefusal (le_refl _)
      _ = envelopeContinue -
          ((root owner true).toReal * quitValue +
            (root owner false).toReal * continueValue) := by
        rw [henvelopeContinue, hq]
        ring

/-- The owner's literal best-response debt in the shifted carrier tail. -/
def quittingForcedOwnerSpineDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)) owner

/-- **Chronological refusal charge.**  When the displayed terminal coalition
contains the forced owner, its stage mass times the positive refusal is paid
by the exact live-weighted drop of that owner's shifted semantic debt. -/
theorem quittingStageCoalitionMass_mul_forcedRefusal_le_spineDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (time : ℕ) :
    let root := quittingProfileLiveRoot reward profile time
    let forcedRoot := Function.update root owner (PMF.pure true)
    let refusal := max 0
      (-quittingAtomicBlockerBalance reward forcedRoot owner)
    quittingStageCoalitionMass reward profile time terminal * refusal ≤
      quittingLiveMass reward profile time *
          quittingForcedOwnerSpineDebt reward profile owner time -
        quittingLiveMass reward profile (time + 1) *
          quittingForcedOwnerSpineDebt reward profile owner (time + 1) := by
  dsimp only
  let root := quittingProfileLiveRoot reward profile time
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile time)
  let refusal := max 0 (-quittingAtomicBlockerBalance reward
    (Function.update root owner (PMF.pure true)) owner)
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail owner :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) htailCarrier owner
  have hfloor : quittingPunishmentValue reward owner ≤ tail.2 owner := by
    have h := quittingPunishmentValue_le reward owner
      (quittingAllContinueProfileSpine reward profile (time + 1))
    change quittingPunishmentValue reward owner ≤
      quittingContinuationBestResponseValue reward
        (quittingAllContinueProfileSpine reward profile (time + 1)) owner
    simpa [quittingBestReplyValue, quittingContinuationBestResponseValue,
      iSup] using h
  have hrow :=
    quittingOwnerQuitProbability_mul_forcedRefusal_add_transport_le_prefixDebt
      reward tail root owner htailDebt hfloor
  have hrootMass : quittingRootCoalitionMass root terminal.val ≤
      (root owner true).toReal :=
    quittingRootCoalitionMass_le_quitProbability_of_mem root terminal.val
      owner howner
  have hrefusal0 : 0 ≤ refusal := le_max_left _ _
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hstage : quittingStageCoalitionMass reward profile time terminal *
      refusal ≤ quittingLiveMass reward profile time *
        ((root owner true).toReal * refusal) := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    calc
      (quittingLiveMass reward profile time *
          quittingRootCoalitionMass root terminal.val) * refusal =
        quittingLiveMass reward profile time *
          (quittingRootCoalitionMass root terminal.val * refusal) := by ring
      _ ≤ quittingLiveMass reward profile time *
          ((root owner true).toReal * refusal) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrootMass hrefusal0) hlive0
  have hweighted := mul_le_mul_of_nonneg_left hrow hlive0
  have hprefix : current = quittingTerminalSemanticPrefix reward root tail :=
    quittingTerminalSemanticPair_spine_eq_prefix reward profile time
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  have hliveSucc : quittingLiveMass reward profile (time + 1) =
      quittingLiveMass reward profile time *
        quittingStationaryContinueMass root := by
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot reward profile,
      quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot reward profile,
      quittingJointSurvivalWeight_succ]
    dsimp only [root]
    rw [Nat.zero_add]
  dsimp only [quittingForcedOwnerSpineDebt]
  change quittingStageCoalitionMass reward profile time terminal * refusal ≤
      quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt current owner -
        quittingLiveMass reward profile (time + 1) *
          quittingTerminalSemanticDebt tail owner
  rw [hprefix, hliveSucc]
  calc
    quittingStageCoalitionMass reward profile time terminal * refusal ≤
        quittingLiveMass reward profile time *
          ((root owner true).toReal * refusal) := hstage
    _ ≤ quittingLiveMass reward profile time *
        (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root tail) owner -
          quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt tail owner) := by
      nlinarith
    _ = quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root tail) owner -
        (quittingLiveMass reward profile time *
          quittingStationaryContinueMass root) *
            quittingTerminalSemanticDebt tail owner := by ring

private theorem sum_range_forwardDrop_eq
    (value : ℕ → ℝ) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, (value time - value (time + 1))) =
      value 0 - value cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- **Finite refusal telescope.**  The full stopped occupation of the
positive forced-owner refusal is bounded by the initial semantic debt of the
same literal profile and the same fixed owner. -/
theorem sum_stageCoalitionMass_mul_forcedRefusal_le_initialSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          max 0 (-quittingAtomicBlockerBalance reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner)) ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) owner := by
  let carried : ℕ → ℝ := fun time =>
    quittingLiveMass reward profile time *
      quittingForcedOwnerSpineDebt reward profile owner time
  have hrows := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) =>
    quittingStageCoalitionMass_mul_forcedRefusal_le_spineDebtDrop
      reward profile terminal owner howner time
  have htelescope := sum_range_forwardDrop_eq carried cutoff
  have hendpointDebt : 0 ≤
      quittingForcedOwnerSpineDebt reward profile owner cutoff := by
    unfold quittingForcedOwnerSpineDebt
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      (quittingTerminalSemanticPair_mem_carrier reward _) owner
  have hendpoint : 0 ≤ carried cutoff :=
    mul_nonneg (quittingLiveMass_nonneg reward profile cutoff) hendpointDebt
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal *
          max 0 (-quittingAtomicBlockerBalance reward
            (Function.update
              (quittingProfileLiveRoot reward profile time) owner
              (PMF.pure true)) owner)) ≤
      ∑ time ∈ Finset.range cutoff,
        (carried time - carried (time + 1)) := by
        simpa [carried] using hrows
    _ = carried 0 - carried cutoff := htelescope
    _ ≤ carried 0 := sub_le_self _ hendpoint
    _ = quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) owner := by
      simp [carried, quittingForcedOwnerSpineDebt,
        quittingAllContinueProfileSpine]

/-- **One legal owner deviation collects every finite refusal charge.**
For arbitrary positive approximation loss, one behavior deviation approaches
the initial best-response envelope closely enough to realize the entire
stopped forced-owner refusal occupation. -/
theorem exists_behaviorDeviation_gain_ge_sum_forcedRefusal_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty})
    (owner : ι) (howner : owner ∈ terminal.val) (cutoff : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal *
            max 0 (-quittingAtomicBlockerBalance reward
              (Function.update
                (quittingProfileLiveRoot reward profile time) owner
                (PMF.pure true)) owner)) - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward profile owner hδ
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  refine ⟨deviation, ?_⟩
  have hcharge :=
    sum_stageCoalitionMass_mul_forcedRefusal_le_initialSemanticDebt
      reward profile terminal owner howner cutoff
  unfold quittingTerminalSemanticDebt at hcharge
  dsimp only [quittingTerminalSemanticPair] at hcharge
  linarith

/-! ## Observer-absent finite-clock consumer -/

/-- **Finite observer-absent wall consumption.**  On a finite preemption
clock, half of the uniformly charged terminal mass is paid either by the
aggregate forced-outsider defect, or by one legal behavioral deviation of
the single fixed terminal owner.  Thus owner refusal is no longer a residual
of the observer-absent wall. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_finiteClock_strategicSplit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    quittingStoppingLawObserverAbsentMassLower packet *
          regime.terminalGap / 2 ≤
        ∑ time ∈ Finset.range stop,
          quittingStageCoalitionMass reward profile time packet.terminal *
            quittingForcedOwnerOutsiderDefect reward
              (Function.update
                (quittingProfileLiveRoot reward profile time) owner
                (PMF.pure true)) owner ∨
      ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
        quittingStoppingLawObserverAbsentMassLower packet *
              regime.terminalGap / 2 - δ ≤
          quittingTerminalPayoff reward
              (Function.update profile owner deviation) owner -
            quittingTerminalPayoff reward profile owner := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let outsiderCharge := ∑ time ∈ Finset.range stop,
    quittingStageCoalitionMass reward profile time packet.terminal *
      quittingForcedOwnerOutsiderDefect reward
        (Function.update (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure true)) owner
  let refusalCharge := ∑ time ∈ Finset.range stop,
    quittingStageCoalitionMass reward profile time packet.terminal *
      max 0 (-quittingAtomicBlockerBalance reward
        (Function.update (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure true)) owner)
  have hdispatch := packet.observerAbsent_forcedOwnerDispatch habsent
  unfold HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch at hdispatch
  rcases hdispatch with
    ⟨howner, _hownerNe, _hlowerPos, _hside, _hmassLower,
      hweightedLower, hclock, hrows⟩
  have hrowSum :
      (∑ time ∈ Finset.range stop,
          quittingStageCoalitionMass reward profile time packet.terminal) *
          regime.terminalGap ≤ outsiderCharge + refusalCharge := by
    rw [Finset.sum_mul]
    have hsum := Finset.sum_le_sum fun time htime => by
      have hrow := hrows n time (by
        rw [hstop]
        exact Finset.mem_range.mp htime)
      dsimp only at hrow
      rcases hrow with
        ⟨_hobserver, _hforcedProfile, _hmassCylinder, _hbarrier,
          hweightedBarrier, _halternative⟩
      let mass := quittingStageCoalitionMass reward profile time packet.terminal
      let forcedRoot := Function.update
        (quittingProfileLiveRoot reward profile time) owner (PMF.pure true)
      have hout0 : 0 ≤
          quittingForcedOwnerOutsiderDefect reward forcedRoot owner :=
        quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
      have hrefusal0 : 0 ≤
          max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) :=
        le_max_left _ _
      have hmax : max
          (quittingForcedOwnerOutsiderDefect reward forcedRoot owner)
          (max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner)) ≤
        quittingForcedOwnerOutsiderDefect reward forcedRoot owner +
          max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) :=
        max_le (le_add_of_nonneg_right hrefusal0)
          (le_add_of_nonneg_left hout0)
      have hmass0 : 0 ≤ mass :=
        quittingStageCoalitionMass_nonneg reward profile time packet.terminal
      exact hweightedBarrier.trans
        (mul_le_mul_of_nonneg_left hmax hmass0)
    simpa [outsiderCharge, refusalCharge, profile, owner,
      mul_add, Finset.sum_add_distrib] using hsum
  have hclockN := hclock n
  rw [hstop] at hclockN
  have htotal : quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap ≤ outsiderCharge + refusalCharge := by
    exact (hweightedLower n).trans (by
      rw [hclockN]
      exact hrowSum)
  by_cases hout : quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap / 2 ≤ outsiderCharge
  · exact Or.inl hout
  · right
    have hrefusal : quittingStoppingLawObserverAbsentMassLower packet *
        regime.terminalGap / 2 ≤ refusalCharge := by
      linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_behaviorDeviation_gain_ge_sum_forcedRefusal_sub reward profile
        packet.terminal owner howner stop δ hδ
    refine ⟨deviation, ?_⟩
    dsimp only [refusalCharge] at hrefusal hdeviation
    exact (sub_le_sub_right hrefusal δ).trans hdeviation

end GameTheory
