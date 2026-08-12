/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeNegativeCollisionAtomicDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification

/-!
# A forced-owner wall on the observer-absent rectangle

When the fixed terminal label of a stopping-law rectangle excludes its debt
observer, all of that terminal mass is realized strictly before the
observer's selected finite stop, or along the complete finite clock when the
observer selected `Never`.  The sign of the fixed terminal reward chooses one
literal endpoint, target for positive reward and source for negative reward,
which carries a uniform amount of this preemption mass.

Choose one fixed member of the terminal coalition.  At every row in the
preemption clock, forcing only this owner to Quit preserves the displayed
coalition cylinder and enters the counterexample regime's atomic-blocker
barrier against the literal shifted tail.  The output below retains the
exact finite/`tsum` accounting and the mass-weighted barrier at every row.

This is intentionally called a forced-owner wall, not a unilateral-gain
compiler.  The forced owner need not prefer the counterfactual row.  A later
consumer must turn the aggregate wall into a legal behavioral deviation or
an exact deletion/punishment certificate.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal target endpoint after installing the observer's selected
pure-time strategy. -/
def quittingStoppingLawRectangleTargetObserverProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (quittingStoppingLawRectangleTargetProfile packet n)
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- The reward sign selects a single literal endpoint for the entire fixed
label sequence. -/
def quittingStoppingLawObserverAbsentCarrierProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  if 0 < reward packet.terminal packet.observer then
    quittingStoppingLawRectangleTargetObserverProfile packet n
  else quittingStoppingLawRectangleSourceProfile packet n

/-- Uniform terminal-mass scale carried by the selected endpoint. -/
def quittingStoppingLawObserverAbsentMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : ℝ :=
  (packet.charge / 4) /
    ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      quittingRewardBound reward)

/-- One fixed member of the fixed nonempty terminal label. -/
def quittingStoppingLawObserverAbsentOwner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : ι :=
  packet.terminal.property.choose

theorem quittingStoppingLawObserverAbsentOwner_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    quittingStoppingLawObserverAbsentOwner packet ∈ packet.terminal.val :=
  packet.terminal.property.choose_spec

/-- Literal one-row profile obtained by forcing the fixed terminal owner to
Quit at one actual carrier row and resuming the carrier profile afterwards. -/
def quittingStoppingLawObserverAbsentForcedOwnerProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) : (quittingGame reward).BehaviorProfile :=
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  Function.update profile owner
    (quittingStagePureEndpointBehaviorDeviation reward profile owner time true)

/-- At one preemption row, the forced-owner wall is measured against the
carrier profile's literal continuation after that row. -/
def quittingStoppingLawObserverAbsentRowBarrier
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) : ℝ :=
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let root := Function.update (quittingProfileLiveRoot reward profile time)
    owner (PMF.pure true)
  max (quittingForcedOwnerOutsiderDefect reward root owner)
    (max 0 (-quittingAtomicBlockerBalance reward root owner))

/-- Game-facing output for the observer-absent rectangle.  The endpoint side
is fixed by the reward sign.  Its full terminal mass is exactly the finite
pre-stop sum or infinite clock, and every clock row admits a literal
forced-owner profile which retains the selected cylinder and carries the
mass-weighted counterexample barrier. -/
def HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : ℝ) : Prop :=
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet
  owner ∈ packet.terminal.val ∧ owner ≠ packet.observer ∧ 0 < lower ∧
    ((0 < reward packet.terminal packet.observer ∧
        ∀ n, profile n =
          quittingStoppingLawRectangleTargetObserverProfile packet n) ∨
      (reward packet.terminal packet.observer < 0 ∧
        ∀ n, profile n = quittingStoppingLawRectangleSourceProfile packet n)) ∧
    (∀ n, lower ≤ quittingTerminalOutcomeMass reward (profile n)
      (some packet.terminal)) ∧
    (∀ n, lower * regime.terminalGap ≤
      quittingTerminalOutcomeMass reward (profile n) (some packet.terminal) *
        regime.terminalGap) ∧
    (∀ n,
      quittingTerminalOutcomeMass reward (profile n) (some packet.terminal) =
        match packet.quitTime n with
        | some stop => ∑ time ∈ Finset.range stop,
            quittingStageCoalitionMass reward (profile n) time packet.terminal
        | none => ∑' time,
            quittingStageCoalitionMass reward (profile n) time packet.terminal) ∧
    ∀ n time,
      (match packet.quitTime n with
        | some stop => time < stop
        | none => True) →
      let actualRoot := quittingProfileLiveRoot reward (profile n) time
      let forcedRoot := Function.update actualRoot owner (PMF.pure true)
      let forcedProfile :=
        quittingStoppingLawObserverAbsentForcedOwnerProfile packet n time
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (time + 1))
      let mass := quittingStageCoalitionMass reward (profile n) time
        packet.terminal
      actualRoot packet.observer = PMF.pure false ∧
        quittingProfileLiveRoot reward forcedProfile time = forcedRoot ∧
        mass ≤ quittingLiveMass reward (profile n) time *
          quittingRootCoalitionMass forcedRoot packet.terminal.val ∧
        regime.terminalGap ≤
          quittingStoppingLawObserverAbsentRowBarrier packet n time ∧
        mass * regime.terminalGap ≤
          mass * quittingStoppingLawObserverAbsentRowBarrier packet n time ∧
        ((∃ who, who ≠ owner ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
            mass * regime.terminalGap ≤
              mass * quittingRootCoordinateNashDefect reward tail.1
                forcedRoot who) ∨
          (regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
            mass * regime.terminalGap ≤
              mass * max 0
                (-quittingAtomicBlockerBalance reward forcedRoot owner)))

theorem QuittingStoppingLawVanishingDebtRectangleSequence.reward_ne_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    reward packet.terminal packet.observer ≠ 0 := by
  intro hzero
  have hatom := packet.atom_pos 0
  unfold quittingTerminalPayoffDifferenceAtom at hatom
  simp only [quittingTerminalOutcomeReward] at hatom
  rw [hzero, mul_zero] at hatom
  exact (lt_irrefl 0) hatom

theorem QuittingStoppingLawVanishingDebtRectangleSequence.rewardBound_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    0 < quittingRewardBound reward := by
  have hbound := abs_reward_le_quittingRewardBound reward packet.terminal
    packet.observer
  exact (abs_pos.mpr packet.reward_ne_zero).trans_le hbound

theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsentMassLower_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    0 < quittingStoppingLawObserverAbsentMassLower packet := by
  unfold quittingStoppingLawObserverAbsentMassLower
  exact div_pos (div_pos packet.charge_pos (by norm_num))
    (mul_pos (by positivity) packet.rewardBound_pos)

/-- The reward-selected literal endpoint carries a uniform amount of the
fixed terminal mass. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_carrierMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) :
    quittingStoppingLawObserverAbsentMassLower packet ≤
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n)
        (some packet.terminal) := by
  classical
  by_cases hpositive : 0 < reward packet.terminal packet.observer
  · let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
    let M := quittingRewardBound reward
    let targetProfile :=
      quittingStoppingLawRectangleTargetObserverProfile packet n
    let sourceProfile := quittingStoppingLawRectangleSourceProfile packet n
    let targetMass := quittingTerminalOutcomeMass reward targetProfile
      (some packet.terminal)
    let sourceMass := quittingTerminalOutcomeMass reward sourceProfile
      (some packet.terminal)
    have hcard : 0 < card := by
      dsimp only [card]
      exact_mod_cast Fintype.card_pos
    have hMpos : 0 < M := packet.rewardBound_pos
    have htargetNonneg : 0 ≤ targetMass :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward targetProfile).1
        (some packet.terminal)
    have hsourceNonneg : 0 ≤ sourceMass :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward sourceProfile).1
        (some packet.terminal)
    have hrewardLe : reward packet.terminal packet.observer ≤ M :=
      (le_abs_self _).trans
        (abs_reward_le_quittingRewardBound reward packet.terminal
          packet.observer)
    have hbound := packet.atom_bound n
    have hsourceUpdate : Function.update
        (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
        (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1) =
          frontier.profiles (frontier.subseq (packet.rank n)) :=
      Function.update_eq_self _ _
    rw [hsourceUpdate] at hbound
    change packet.charge / 4 ≤ card *
      ((targetMass - sourceMass) *
        reward packet.terminal packet.observer) at hbound
    have hproductLe :
        (targetMass - sourceMass) * reward packet.terminal packet.observer ≤
          targetMass * M := by
      have hdiffLe : targetMass - sourceMass ≤ targetMass := by linarith
      exact (mul_le_mul_of_nonneg_right hdiffLe hpositive.le).trans
        (mul_le_mul_of_nonneg_left hrewardLe htargetNonneg)
    have htotal : packet.charge / 4 ≤ card * (targetMass * M) :=
      hbound.trans (mul_le_mul_of_nonneg_left hproductLe hcard.le)
    unfold quittingStoppingLawObserverAbsentMassLower
    rw [quittingStoppingLawObserverAbsentCarrierProfile, if_pos hpositive]
    apply (div_le_iff₀ (mul_pos hcard hMpos)).2
    change packet.charge / 4 ≤ targetMass * (card * M)
    calc
      packet.charge / 4 ≤ card * (targetMass * M) := htotal
      _ = targetMass * (card * M) := by ring
  · have hnegative : reward packet.terminal packet.observer < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hpositive)
        packet.reward_ne_zero
    rw [quittingStoppingLawObserverAbsentCarrierProfile, if_neg hpositive]
    exact packet.negativeCollision_sourceMassLower hnegative n

/-- Exact pre-observer-stop accounting for the selected endpoint. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_carrierMass_eq_clock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val) (n : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n)
        (some packet.terminal) =
      match packet.quitTime n with
      | some stop => ∑ time ∈ Finset.range stop,
          quittingStageCoalitionMass reward
            (quittingStoppingLawObserverAbsentCarrierProfile packet n)
            time packet.terminal
      | none => ∑' time,
          quittingStageCoalitionMass reward
            (quittingStoppingLawObserverAbsentCarrierProfile packet n)
            time packet.terminal := by
  cases htime : packet.quitTime n with
  | none =>
      simpa only using quittingTerminalOutcomeMass_eq_timeDisintegration reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n)
        (some packet.terminal)
  | some stop =>
      by_cases hpositive : 0 < reward packet.terminal packet.observer
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_pos hpositive,
          quittingStoppingLawRectangleTargetObserverProfile]
        simpa only [htime] using
          quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
            reward (quittingStoppingLawRectangleTargetProfile packet n)
              packet.observer stop packet.terminal habsent
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_neg hpositive,
          quittingStoppingLawRectangleSourceProfile]
        simpa only [htime] using
          quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
            reward (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.observer stop packet.terminal habsent

/-- Every row belonging to the preemption clock has the observer literally
playing Continue. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_carrierRoot_observer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ)
    (hbefore : match packet.quitTime n with
      | some stop => time < stop
      | none => True) :
    quittingProfileLiveRoot reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n) time
        packet.observer = PMF.pure false := by
  cases htime : packet.quitTime n with
  | none =>
      by_cases hpositive : 0 < reward packet.terminal packet.observer
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_pos hpositive,
          quittingStoppingLawRectangleTargetObserverProfile,
          quittingProfileLiveRoot_update_pureTime_self, htime,
          quittingPureTimeHazard_none]
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_neg hpositive,
          quittingStoppingLawRectangleSourceProfile,
          quittingProfileLiveRoot_update_pureTime_self, htime,
          quittingPureTimeHazard_none]
  | some stop =>
      have hlt : time < stop := by simpa only [htime] using hbefore
      by_cases hpositive : 0 < reward packet.terminal packet.observer
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_pos hpositive,
          quittingStoppingLawRectangleTargetObserverProfile]
        simpa only [htime] using
          quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
            reward (quittingStoppingLawRectangleTargetProfile packet n)
              packet.observer hlt
      · rw [quittingStoppingLawObserverAbsentCarrierProfile, if_neg hpositive,
          quittingStoppingLawRectangleSourceProfile]
        simpa only [htime] using
          quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
            reward (frontier.profiles (frontier.subseq (packet.rank n)))
              packet.observer hlt

/-- The literal one-row forced profile has exactly the advertised forced
product root at its selected row. -/
theorem quittingProfileLiveRoot_observerAbsentForcedOwnerProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingStoppingLawObserverAbsentForcedOwnerProfile packet n time)
        time =
      Function.update
        (quittingProfileLiveRoot reward
          (quittingStoppingLawObserverAbsentCarrierProfile packet n) time)
        (quittingStoppingLawObserverAbsentOwner packet) (PMF.pure true) := by
  funext player
  unfold quittingStoppingLawObserverAbsentForcedOwnerProfile
    quittingProfileLiveRoot
  by_cases hplayer : player = quittingStoppingLawObserverAbsentOwner packet
  · subst player
    simp [quittingStagePureEndpointBehaviorDeviation,
      quittingStageDeviationHazard_self]
  · simp [Function.update_of_ne hplayer]

/-- Forcing a fixed member of the selected terminal coalition to Quit cannot
decrease that coalition's actual stage cylinder. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.stageMass_le_forcedOwnerCylinder
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) :
    quittingStageCoalitionMass reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n) time
        packet.terminal ≤
      quittingLiveMass reward
          (quittingStoppingLawObserverAbsentCarrierProfile packet n) time *
        quittingRootCoalitionMass
          (Function.update
            (quittingProfileLiveRoot reward
              (quittingStoppingLawObserverAbsentCarrierProfile packet n) time)
            (quittingStoppingLawObserverAbsentOwner packet) (PMF.pure true))
          packet.terminal.val := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  apply mul_le_mul_of_nonneg_left
  · simpa [quittingPureEndpointRoutedCoalition,
      quittingStoppingLawObserverAbsentOwner_mem packet] using
      quittingRootCoalitionMass_le_pureEndpointRouted
        (quittingProfileLiveRoot reward
          (quittingStoppingLawObserverAbsentCarrierProfile packet n) time)
        packet.terminal.val
        (quittingStoppingLawObserverAbsentOwner packet) true
  · exact quittingLiveMass_nonneg reward
      (quittingStoppingLawObserverAbsentCarrierProfile packet n) time

/-- **Observer-absent forced-owner dispatch.**  The residual rectangle has a
fixed literal carrier side, exact aggregate preemption chronology, and a
fixed owner whose counterfactual one-row Quit walls retain the charged
cylinder and satisfy the mass-weighted atomic blocker barrier. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_forcedOwnerDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val) :
    HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch packet
      (quittingStoppingLawObserverAbsentMassLower packet) := by
  classical
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet
  have hownerMem : owner ∈ packet.terminal.val :=
    quittingStoppingLawObserverAbsentOwner_mem packet
  have hownerNe : owner ≠ packet.observer := by
    intro heq
    exact habsent (heq ▸ hownerMem)
  have hside :
      (0 < reward packet.terminal packet.observer ∧
          ∀ n, profile n =
            quittingStoppingLawRectangleTargetObserverProfile packet n) ∨
        (reward packet.terminal packet.observer < 0 ∧
          ∀ n, profile n =
            quittingStoppingLawRectangleSourceProfile packet n) := by
    by_cases hpositive : 0 < reward packet.terminal packet.observer
    · exact Or.inl ⟨hpositive, fun n => by
        simp [profile, quittingStoppingLawObserverAbsentCarrierProfile,
          hpositive]⟩
    · have hnegative : reward packet.terminal packet.observer < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpositive) packet.reward_ne_zero
      exact Or.inr ⟨hnegative, fun n => by
        simp [profile, quittingStoppingLawObserverAbsentCarrierProfile,
          hpositive]⟩
  have hmassLower : ∀ n,
      quittingStoppingLawObserverAbsentMassLower packet ≤
        quittingTerminalOutcomeMass reward (profile n)
          (some packet.terminal) := by
    intro n
    simpa only [profile] using packet.observerAbsent_carrierMassLower n
  have hmassWeighted : ∀ n,
      quittingStoppingLawObserverAbsentMassLower packet * regime.terminalGap ≤
        quittingTerminalOutcomeMass reward (profile n)
            (some packet.terminal) * regime.terminalGap := by
    intro n
    exact mul_le_mul_of_nonneg_right (hmassLower n)
      regime.terminalGap_pos.le
  refine ⟨hownerMem, hownerNe, packet.observerAbsentMassLower_pos, hside,
    hmassLower, hmassWeighted,
    packet.observerAbsent_carrierMass_eq_clock habsent, ?_⟩
  intro n time hbefore
  let actualRoot := quittingProfileLiveRoot reward (profile n) time
  let forcedRoot := Function.update actualRoot owner (PMF.pure true)
  let forcedProfile :=
    quittingStoppingLawObserverAbsentForcedOwnerProfile packet n time
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward (profile n) (time + 1))
  let mass := quittingStageCoalitionMass reward (profile n) time packet.terminal
  have hobserver : actualRoot packet.observer = PMF.pure false := by
    simpa only [actualRoot, profile] using
      packet.observerAbsent_carrierRoot_observer n time hbefore
  have hforcedProfile : quittingProfileLiveRoot reward forcedProfile time =
      forcedRoot := by
    simpa only [forcedProfile, forcedRoot, actualRoot, profile] using
      quittingProfileLiveRoot_observerAbsentForcedOwnerProfile packet n time
  have hmass : mass ≤ quittingLiveMass reward (profile n) time *
      quittingRootCoalitionMass forcedRoot packet.terminal.val := by
    simpa only [mass, forcedRoot, actualRoot, profile] using
      packet.stageMass_le_forcedOwnerCylinder n time
  have hownerForced : forcedRoot owner = PMF.pure true := by
    simp [forcedRoot]
  have hbarrier : regime.terminalGap ≤
      quittingStoppingLawObserverAbsentRowBarrier packet n time := by
    simpa only [quittingStoppingLawObserverAbsentRowBarrier, forcedRoot,
      actualRoot, owner, profile] using
      regime.terminalGap_le_atomicBlockerBarrier hownerForced
  have hmassNonneg : 0 ≤ mass := by
    exact quittingStageCoalitionMass_nonneg reward (profile n) time
      packet.terminal
  have hweightedBarrier : mass * regime.terminalGap ≤
      mass * quittingStoppingLawObserverAbsentRowBarrier packet n time :=
    mul_le_mul_of_nonneg_left hbarrier hmassNonneg
  have halternative :
      (∃ who, who ≠ owner ∧
          regime.terminalGap ≤
            quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
          mass * regime.terminalGap ≤
            mass * quittingRootCoordinateNashDefect reward tail.1
              forcedRoot who) ∨
        (regime.terminalGap ≤
            max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
          mass * regime.terminalGap ≤
            mass * max 0
              (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
    have hraw : regime.terminalGap ≤
        max (quittingForcedOwnerOutsiderDefect reward forcedRoot owner)
          (max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
      simpa only [quittingStoppingLawObserverAbsentRowBarrier, forcedRoot,
        actualRoot, owner, profile] using hbarrier
    rcases (le_max_iff.mp hraw) with hdefect | hrefusal
    · left
      obtain ⟨who, hwho, hcoordinate⟩ :=
        exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
          reward tail.1 forcedRoot owner hownerForced regime.terminalGap_pos
            hdefect
      exact ⟨who, hwho, hcoordinate,
        mul_le_mul_of_nonneg_left hcoordinate hmassNonneg⟩
    · exact Or.inr ⟨hrefusal,
        mul_le_mul_of_nonneg_left hrefusal hmassNonneg⟩
  exact ⟨hobserver, hforcedProfile, hmass, hbarrier, hweightedBarrier,
    halternative⟩

/-- **Static frontier after the observer-absent handoff.**  Every rectangle
orientation now reaches a named strategic consumer.  The observer-absent
consumer is the aggregate counterfactual forced-owner wall above; it is not
claimed to close the conjecture-facing branch.  The only remaining bare
atom orientation is the prescribed comparison sequence. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_prescribed_or_strategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch packet
            (quittingStoppingLawObserverAbsentMassLower packet) ∨
          HasQuittingStoppingLawSingletonStrategicOrientation packet ∨
          HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
            (quittingStoppingLawNegativeCollisionMassLower packet) ∨
          HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
            ((packet.charge / 4) /
              ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                quittingRewardBound reward)) := by
  classical
  rcases frontier.exists_prescribed_or_absent_or_staticStrategicDispatch with
    hprescribed | ⟨packet, habsent | hsingleton | hnegative | hpositive⟩
  · exact Or.inl hprescribed
  · exact Or.inr ⟨packet, Or.inl
      (packet.observerAbsent_forcedOwnerDispatch habsent)⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inl hsingleton)⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inr (Or.inl hnegative))⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inr (Or.inr hpositive))⟩

/-- The orientation-preserving strategic output carried by one fixed
rectangle packet.  Unlike the earlier consumer-only capstone, every branch
retains the terminal membership, cardinality, and reward-sign data which
selected its named consumer. -/
def HasQuittingStoppingLawOrientationPreservingStrategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    Prop :=
  (packet.observer ∉ packet.terminal.val ∧
      HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch packet
        (quittingStoppingLawObserverAbsentMassLower packet)) ∨
    HasQuittingStoppingLawSingletonStrategicOrientation packet ∨
    (packet.observer ∈ packet.terminal.val ∧
      1 < packet.terminal.val.card ∧
      reward packet.terminal packet.observer < 0 ∧
      HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
        (quittingStoppingLawNegativeCollisionMassLower packet)) ∨
    (packet.observer ∈ packet.terminal.val ∧
      1 < packet.terminal.val.card ∧
      0 < reward packet.terminal packet.observer ∧
      HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
        ((packet.charge / 4) /
          ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingRewardBound reward)))

/-- **Orientation-preserving exhaustive stopping-law capstone.**  A quitting
counterexample frontier supplies either a prescribed-payoff atom sequence or
one fixed rectangle packet in exactly one of the four terminal geometries.
Each geometry is returned together with the strategic dispatch constructed
from it, so downstream consumers do not have to recover discarded
provenance. -/
theorem
    QuittingCounterexampleStoppingLawFrontier.exists_prescribed_or_orientationPreservingStrategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        HasQuittingStoppingLawOrientationPreservingStrategicDispatch packet := by
  classical
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | hrectangle
  · exact Or.inl hprescribed
  · obtain ⟨packet⟩ := hrectangle
    refine Or.inr ⟨packet, ?_⟩
    rcases packet.openOrientation_or_positiveTargetCollision with hopen |
      ⟨hobserver, hcollision, hpositive⟩
    · rcases packet.refineOpenOrientation hopen with habsent | hsingleton |
        hnegative
      · exact Or.inl ⟨habsent,
          packet.observerAbsent_forcedOwnerDispatch habsent⟩
      · exact Or.inr (Or.inl hsingleton)
      · exact Or.inr (Or.inr (Or.inl ⟨hnegative.1, hnegative.2.1,
          hnegative.2.2,
          packet.negativeCollision_atomicDispatch hnegative.1
            hnegative.2.1 hnegative.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hobserver, hcollision, hpositive,
        packet.positiveTargetCollision_markedTailDispatch hobserver hcollision
          hpositive⟩))

end GameTheory
