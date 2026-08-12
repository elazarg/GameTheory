/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeObserverAbsentForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceLawTemporalSplit

/-!
# Positive observer rectangles retain their law on the reset face

When the fixed observer reward of an observer-absent rectangle is positive,
the mass-carrying endpoint is the same double endpoint whose observer debt
tends to zero.  Compactness therefore gives a joint semantic/law reset-face
point which retains a uniformly positive amount of the original terminal
coalition.  No independent reset-face minimization is needed.

For a nonsingleton terminal label, the landed reset-face law theorem then
concentrates this law into a recurrent same-profile stage atom.  The negative
observer-reward orientation is deliberately excluded: there the mass-carrying
endpoint is the comparison endpoint, while the known vanishing-debt estimate
belongs to the double endpoint.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Positive rectangle law-preserving reset-face limit.** -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_positiveObserver_carrierResetFaceLawPoint
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (hpositive : 0 < reward packet.terminal packet.observer) :
    ∃ point : QuittingTerminalSemanticLawPoint ι,
      ∃ subseq : ℕ → ℕ,
        point ∈ quittingTerminalSemanticLawCarrier reward ∧
        StrictMono subseq ∧
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward
              (quittingStoppingLawObserverAbsentCarrierProfile packet
                (subseq n)),
            quittingTerminalOutcomeMass reward
              (quittingStoppingLawObserverAbsentCarrierProfile packet
                (subseq n))))
          atTop (nhds point) ∧
        quittingTerminalSemanticDebt point.1 packet.observer = 0 ∧
        quittingStoppingLawObserverAbsentMassLower packet ≤
          point.2 (some packet.terminal) := by
  let endpoint : ℕ → QuittingTerminalSemanticLawPoint ι := fun n ↦
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawObserverAbsentCarrierProfile packet n))
  have hendpointMem : ∀ n,
      endpoint n ∈ quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨point, hpoint, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)).tendsto_subseq hendpointMem
  have hdebtLimit :=
    ((continuous_quittingTerminalSemanticDebt packet.observer).comp
      continuous_fst).tendsto point |>.comp hendpoint
  have hdebtZero : Tendsto (fun n ↦
      quittingTerminalSemanticDebt (endpoint n).1 packet.observer)
      atTop (nhds 0) := by
    simpa [endpoint, quittingStoppingLawObserverAbsentCarrierProfile,
      hpositive, quittingStoppingLawRectangleTargetObserverProfile,
      quittingStoppingLawRectangleTargetProfile] using
        packet.observer_debt_tendsto_zero
  have hdebtZeroSub := hdebtZero.comp hsubseq.tendsto_atTop
  have hpointReset :
      quittingTerminalSemanticDebt point.1 packet.observer = 0 := by
    change Tendsto (fun n ↦
      quittingTerminalSemanticDebt (endpoint (subseq n)).1 packet.observer)
      atTop (nhds (quittingTerminalSemanticDebt point.1 packet.observer))
      at hdebtLimit
    exact tendsto_nhds_unique hdebtLimit hdebtZeroSub
  have hmassLimit : Tendsto (fun n ↦
      (endpoint (subseq n)).2 (some packet.terminal)) atTop
      (nhds (point.2 (some packet.terminal))) :=
    ((continuous_apply (some packet.terminal)).comp continuous_snd).tendsto
      point |>.comp hendpoint
  have hdispatch := packet.observerAbsent_forcedOwnerDispatch habsent
  unfold HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch at hdispatch
  rcases hdispatch with
    ⟨_howner, _hownerNe, _hlowerPos, _hside, hmassLower,
      _hweightedLower, _hclock, _hrows⟩
  have hpointMass : quittingStoppingLawObserverAbsentMassLower packet ≤
      point.2 (some packet.terminal) := by
    apply ge_of_tendsto hmassLimit
    exact Eventually.of_forall fun n ↦ by
      simpa only [endpoint] using hmassLower (subseq n)
  refine ⟨point, subseq, hpoint, hsubseq, ?_, hpointReset, hpointMass⟩
  change Tendsto (endpoint ∘ subseq) atTop (nhds point)
  exact hendpoint

/-- **Positive collision rectangles have a concentrated reset-face law
packet.**  The original terminal coordinate itself stays positive at the
reset-face limit; the concentration theorem may return a different fixed
stage coalition, but that coalition contains a fixed player distinct from
the reset observer. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_positiveObserver_resetFaceConcentratedPacket_of_collision
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (hpositive : 0 < reward packet.terminal packet.observer)
    (hcollision : 1 < packet.terminal.val.card) :
    ∃ point : QuittingTerminalSemanticLawPoint ι,
      point ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt point.1 packet.observer = 0 ∧
      0 < point.2 (some packet.terminal) ∧
      ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ, ∃ scale : ℕ → ℝ,
      ∃ fixedOther : ι,
      ∃ exact : {S : Finset ι // S.Nonempty},
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (nhds 0) ∧
        fixedOther ≠ packet.observer ∧ fixedOther ∈ exact.val ∧
        Nonempty (QuittingReprojectionConcentratedPacket
          reward profiles packet.observer exact cutoff scale) := by
  obtain ⟨point, _subseq, hpoint, _hsubseq, _hlimit, hreset, hmass⟩ :=
    packet.exists_positiveObserver_carrierResetFaceLawPoint
      habsent hpositive
  have hmassPos : 0 < point.2 (some packet.terminal) :=
    packet.observerAbsentMassLower_pos.trans_le hmass
  obtain ⟨profiles, cutoff, scale, fixedOther, exact, hprofiles,
      hscalePos, hscaleZero, hfixedNe, hfixedMem, hconcentrated⟩ :=
    exists_resetFaceLaw_concentratedPacket_of_collision
      reward point packet.observer packet.terminal
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) hpoint hreset hmassPos
          hcollision
  exact ⟨point, hpoint, hreset, hmassPos, profiles, cutoff, scale,
    fixedOther, exact, hprofiles, hscalePos, hscaleZero, hfixedNe,
    hfixedMem, hconcentrated⟩

end GameTheory
