/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicCompression
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration

/-!
# The stopping-law singleton handoff is not a strategic closure interface

The strategic conjunct of `HasQuittingStoppingLawSingletonStrategicOrientation`
is supplied by `QuittingCounterexampleRegime.singletonStaticStrategicDispatch`
for every player, without using the rectangle packet.  Consequently the
purported handoff is equivalent to the bare label identity
`packet.terminal.val = {packet.observer}`.

The two-player calculation below records the remaining local obstruction.
The mover replacement is an exact best response at the unmodified base.
After the observer's time-zero pure stop, it creates a positive atom on the
observer singleton and leaves the observer with zero debt.  Nevertheless it
only transfers one unit of debt from the observer to the mover, so total debt
does not decrease.  The table already has the static atomic-toggle handoff.

This is a local architecture fence, not a counterexample to uniform
equilibrium existence: the table has zero-debt profiles elsewhere.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- In a counterexample regime, the named singleton strategic orientation
contains no information beyond the singleton label itself. -/
theorem hasQuittingStoppingLawSingletonStrategicOrientation_iff_terminal_eq
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    HasQuittingStoppingLawSingletonStrategicOrientation packet ↔
      packet.terminal.val = {packet.observer} := by
  classical
  constructor
  · rintro ⟨hmem, hcard, _hstrategic⟩
    obtain ⟨who, hterminal⟩ := Finset.card_eq_one.mp hcard
    have hobserver : packet.observer = who := by
      rw [hterminal] at hmem
      simpa using hmem
    simpa [hobserver] using hterminal
  · intro hterminal
    refine ⟨?_, ?_, regime.singletonStaticStrategicDispatch packet.observer⟩
    · rw [hterminal]
      simp
    · rw [hterminal]
      simp

namespace MinimalFinQuittingCounterexample

/-- **Common-object correction.**  The static atomic handoff is not specific
to the singleton stopping-law leaf.  The compression theorem supplies it or
exact player deletion for every owner of every counterexample regime, and
cardinal minimality rules out the deletion disjunct.  Hence all five formal
stopping-law leaves share this same game-wide object. -/
theorem hasStaticAtomicToggleHandoff
    (minimal : MinimalFinQuittingCounterexample) :
    HasQuittingStaticAtomicToggleHandoff minimal.reward := by
  have hcount : 0 < minimal.playerCount := by
    exact lt_of_lt_of_le (by norm_num) minimal.four_le_playerCount
  let owner : Fin minimal.playerCount :=
    ⟨0, hcount⟩
  rcases minimal.regime.singletonStaticStrategicDispatch_compress owner
      (minimal.regime.singletonStaticStrategicDispatch owner) with
    hatomic | hdelete
  · exact hatomic
  · obtain ⟨hnonempty, hgap, hcard⟩ := hdelete
    letI : Nonempty (QuittingDeletedPlayer owner) := hnonempty
    let reducedReward := quittingDeletePlayerReward minimal.reward owner
    have hno : ¬ ∃ payoff : Payoff (QuittingDeletedPlayer owner),
        (quittingGame reducedReward).IsUniformEquilibriumPayoff none payoff :=
      (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
        reducedReward).2
          ⟨minimal.regime.terminalGap,
            minimal.regime.terminalGap_pos, hgap⟩
    have hcard' : Fintype.card (QuittingDeletedPlayer owner) <
        minimal.playerCount := by
      simpa using hcard
    exact False.elim
      (hno (minimal.exists_uniformEquilibriumPayoff_of_card_lt
        hcard' reducedReward))

end MinimalFinQuittingCounterexample

namespace StoppingLawSingletonOrientationNoGo

abbrev Player := Bool
abbrev mover : Player := false
abbrev observer : Player := true

/-- The terminal rows are `{mover} ↦ (1,0)`,
`{observer} ↦ (0,-1)`, and `{mover,observer} ↦ (-1,1)`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal.val = {mover} then
      if who = mover then 1 else 0
    else if terminal.val = {observer} then
      if who = observer then -1 else 0
    else if who = mover then -1 else 1

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

def base : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

/-- Exact rectangle source: the observer stops at date zero and the mover
keeps the base strategy. -/
def source : (quittingGame reward).BehaviorProfile :=
  Function.update base observer
    (quittingPureTimeBehaviorStrategy reward observer (some 0))

/-- The mover's stationary sure-Quit replacement. -/
def replacement : (quittingGame reward).BehaviorStrategy mover :=
  (quittingStationaryProfile reward (quittingPureSetRoot {mover})) mover

/-- Exact rectangle target, using the same observer pure-time strategy. -/
def target : (quittingGame reward).BehaviorProfile :=
  Function.update source mover replacement

def observerTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{observer}, by simp⟩

theorem base_update_mover_eq_singleton :
    Function.update base mover replacement =
      quittingStationaryProfile reward (quittingPureSetRoot {mover}) := by
  funext who time history
  cases who <;>
    simp [base, replacement, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, mover]

theorem terminalPayoff_eq_rootAbsorbing_of_sure
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    (hsure : QuittingRootHasSureQuitter
      (quittingProfileRoot reward profile)) :
    quittingTerminalPayoff reward profile who =
      quittingRootAbsorbingContribution reward
        (quittingProfileRoot reward profile) who := by
  rw [quittingTerminalPayoff_eq_expect_rootContinuation]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [stageActionDist_quittingProfileRoot]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro action haction
  have hquit :=
    quittingQuitters_nonempty_of_mem_support_pmfPi_of_hasSureQuitter
      (quittingProfileRoot reward profile) hsure action haction
  simp [quittingRootContinuationPayoff, quittingRootPayoff, hquit]

theorem source_payoff_observer :
    quittingTerminalPayoff reward source observer = -1 := by
  unfold source base
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow]
  norm_num [quittingSetReward, reward, mover, observer]

theorem source_payoff_mover :
    quittingTerminalPayoff reward source mover = 0 := by
  have hsure : QuittingRootHasSureQuitter
      (quittingProfileRoot reward source) := by
    refine ⟨observer, ?_⟩
    simp [source, base, quittingProfileRoot,
      quittingStationaryProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      observer]
  rw [terminalPayoff_eq_rootAbsorbing_of_sure source mover hsure]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  norm_num [expect_eq_sum, source, base, quittingProfileRoot,
    quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingPureSetRoot, quittingSetAction, reward, quittingRootPayoff,
    quittingQuitters, mover, observer, Finset.ext_iff]

theorem target_payoff_observer :
    quittingTerminalPayoff reward target observer = 1 := by
  have htarget : target = Function.update
      (quittingStationaryProfile reward (quittingPureSetRoot {mover}))
      observer (quittingPureTimeBehaviorStrategy reward observer (some 0)) := by
    rw [target, source, Function.update_comm (by decide : observer ≠ mover),
      base_update_mover_eq_singleton]
  rw [htarget, quittingTerminalPayoff_update_pureSetRoot_quitNow]
  norm_num [quittingSetReward, reward, mover, observer,
    show ({true, false} : Finset Bool) ≠ {false} by decide,
    show ({true, false} : Finset Bool) ≠ {true} by decide]

theorem source_mover_deviation_payoff_le_zero
    (deviation : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalPayoff reward
      (Function.update source mover deviation) mover ≤ 0 := by
  let deviated := Function.update source mover deviation
  have hsure : QuittingRootHasSureQuitter
      (quittingProfileRoot reward deviated) := by
    refine ⟨observer, ?_⟩
    simp [deviated, source, base, quittingProfileRoot,
      quittingStationaryProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      mover, observer]
  rw [terminalPayoff_eq_rootAbsorbing_of_sure deviated mover hsure]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  norm_num [expect_eq_sum, deviated, source, base, quittingProfileRoot,
    quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingPureSetRoot, quittingSetAction, reward, quittingRootPayoff,
    quittingQuitters, mover, observer, Finset.ext_iff]

theorem base_bestResponse_observer :
    quittingContinuationBestResponseValue reward base observer = 0 := by
  unfold base
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward ∅ observer (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer]

theorem base_bestResponse_mover :
    quittingContinuationBestResponseValue reward base mover = 1 := by
  unfold base
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward ∅ mover (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer]

theorem source_bestResponse_observer :
    quittingContinuationBestResponseValue reward source observer = 0 := by
  rw [source, quittingContinuationBestResponseValue_update_self,
    base_bestResponse_observer]

theorem source_bestResponse_mover :
    quittingContinuationBestResponseValue reward source mover = 0 := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨deviation, rfl⟩
      exact source_mover_deviation_payoff_le_zero deviation
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward source mover (source mover) (M := 1) (by norm_num) reward_bound
    rw [Function.update_eq_self, source_payoff_mover] at hlower
    exact hlower

theorem target_bestResponse_mover :
    quittingContinuationBestResponseValue reward target mover = 0 := by
  rw [target, quittingContinuationBestResponseValue_update_self,
    source_bestResponse_mover]

theorem target_bestResponse_observer :
    quittingContinuationBestResponseValue reward target observer = 1 := by
  rw [target, source, Function.update_comm (by decide : observer ≠ mover),
    quittingContinuationBestResponseValue_update_self,
    base_update_mover_eq_singleton,
    quittingContinuationBestResponseValue_pureSetRoot_eq
      reward {mover} observer (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer,
    show ({true, false} : Finset Bool) ≠ {false} by decide,
    show ({true, false} : Finset Bool) ≠ {true} by decide]

theorem target_payoff_mover :
    quittingTerminalPayoff reward target mover = -1 := by
  have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward source mover replacement (M := 1) (by norm_num) reward_bound
  have htarget : Function.update source mover replacement = target := by rfl
  rw [htarget, source_bestResponse_mover] at hdeviation
  have hlower : -1 ≤ quittingTerminalPayoff reward target mover :=
    neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward target mover
      (M := 1) (by norm_num) reward_bound)
  -- The upper bound is already zero; direct first-stage evaluation fixes
  -- the endpoint at the joint reward `-1`.
  have hsure : QuittingRootHasSureQuitter
      (quittingProfileRoot reward target) := by
    refine ⟨observer, ?_⟩
    simp [target, source, replacement, base, quittingProfileRoot,
      quittingStationaryProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      mover, observer]
  rw [terminalPayoff_eq_rootAbsorbing_of_sure target mover hsure]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  norm_num [expect_eq_sum, target, source, replacement, base,
    quittingProfileRoot, quittingStationaryProfile,
    StochasticGame.stationaryBehaviorProfile,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
    quittingPureSetRoot, quittingSetAction, reward, quittingRootPayoff,
    quittingQuitters, mover, observer, Finset.ext_iff]

/-- The mover replacement is an exact best response at the unmodified base. -/
theorem replacement_is_exactBestResponse_at_base :
    quittingTerminalPayoff reward
        (Function.update base mover replacement) mover -
      quittingTerminalPayoff reward base mover =
        quittingTerminalDeviationDebt reward base mover := by
  rw [base_update_mover_eq_singleton,
    quittingTerminalPayoff_pureSetRoot]
  unfold base quittingTerminalDeviationDebt
  rw [quittingTerminalPayoff_pureSetRoot]
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward ∅ mover (by norm_num) reward_bound]
  norm_num [quittingSetReward, reward, mover, observer]

theorem source_liveRoot_zero :
    quittingProfileLiveRoot reward source 0 = fun who =>
      if who = observer then PMF.pure true else PMF.pure false := by
  funext who
  cases who <;>
    simp [source, base, quittingProfileLiveRoot,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      observer]

theorem target_liveRoot_zero :
    quittingProfileLiveRoot reward target 0 = fun _ => PMF.pure true := by
  funext who
  cases who <;>
    simp [target, source, replacement, base, quittingProfileLiveRoot,
      quittingStationaryProfile, StochasticGame.stationaryBehaviorProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingPureSetRoot, quittingSetAction, mover, observer]

theorem source_observer_mass_eq_one :
    quittingTerminalOutcomeMass reward source (some observerTerminal) = 1 := by
  rw [source,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward base observer 0 observerTerminal (by simp [observerTerminal])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward source 0 *
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward source 0) observerTerminal.val = 1
  rw [source_liveRoot_zero]
  simp [quittingRootCoalitionMass, quittingRootQuitRates,
    Math.PMFProduct.coalitionMass, observerTerminal, observer,
    show ({true} : Finset Bool)ᶜ = {false} by decide]

theorem target_observer_mass_eq_zero :
    quittingTerminalOutcomeMass reward target (some observerTerminal) = 0 := by
  have htarget : target = Function.update
      (quittingStationaryProfile reward (quittingPureSetRoot {mover}))
      observer (quittingPureTimeBehaviorStrategy reward observer (some 0)) := by
    rw [target, source, Function.update_comm (by decide : observer ≠ mover),
      base_update_mover_eq_singleton]
  rw [htarget,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward (quittingStationaryProfile reward (quittingPureSetRoot {mover}))
        observer 0 observerTerminal (by simp [observerTerminal])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward target 0 *
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward target 0) observerTerminal.val = 0
  rw [target_liveRoot_zero]
  simp [quittingRootCoalitionMass, quittingRootQuitRates,
    Math.PMFProduct.coalitionMass, observerTerminal, observer,
    show ({true} : Finset Bool) ≠ {true, false} by decide]

/-- The singleton rectangle atom is positive with charge one. -/
theorem singleton_observer_atom_eq_one :
    quittingTerminalPayoffDifferenceAtom reward target source observer
      (some observerTerminal) = 1 := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [target_observer_mass_eq_zero, source_observer_mass_eq_one]
  norm_num [quittingTerminalOutcomeReward, reward, observerTerminal,
    mover, observer]

theorem source_totalDebt : quittingTerminalDebtSum reward source = 1 := by
  unfold quittingTerminalDebtSum quittingTerminalDeviationDebt
  rw [Fintype.sum_bool, source_bestResponse_mover, source_payoff_mover,
    source_bestResponse_observer, source_payoff_observer]
  norm_num

theorem target_totalDebt : quittingTerminalDebtSum reward target = 1 := by
  unfold quittingTerminalDebtSum quittingTerminalDeviationDebt
  rw [Fintype.sum_bool, target_bestResponse_mover, target_payoff_mover,
    target_bestResponse_observer, target_payoff_observer]
  norm_num

theorem target_observer_debt_eq_zero :
    quittingTerminalDeviationDebt reward target observer = 0 := by
  rw [quittingTerminalDeviationDebt, target_bestResponse_observer,
    target_payoff_observer]
  norm_num

/-- The table already has the static atomic-toggle branch: at `{mover}` the
observer gains by joining, while at the joint row the mover can profitably
Continue. -/
theorem has_staticAtomicToggleHandoff :
    HasQuittingStaticAtomicToggleHandoff reward := by
  classical
  refine ⟨observer, {mover}, by simp, by simp [mover, observer], ?_, ?_⟩
  · have hnontrivial : ({true, false} : Finset Bool).Nontrivial := by decide
    norm_num [reward, quittingSetReward, mover, observer, hnontrivial,
      show ({true, false} : Finset Bool) ≠ {false} by decide,
      show ({true, false} : Finset Bool) ≠ {true} by decide,
      show ({true, false} : Finset Bool).erase false = {true} by decide]
  · refine ⟨mover, by decide, PMF.pure false, ?_⟩
    change quittingRootAbsorbingContribution reward
        (Function.update (quittingPureSetRoot {observer, mover}) mover
          (PMF.pure false)) mover >
      quittingRootAbsorbingContribution reward
        (quittingPureSetRoot {observer, mover}) mover
    rw [update_quittingPureSetRoot_false,
      quittingRootAbsorbingContribution_pureSetRoot,
      quittingRootAbsorbingContribution_pureSetRoot]
    have hnontrivial : ({true, false} : Finset Bool).Nontrivial := by decide
    norm_num [quittingSetReward, reward, mover, observer, hnontrivial,
      show ({true, false} : Finset Bool) ≠ {false} by decide,
      show ({true, false} : Finset Bool) ≠ {true} by decide,
      show ({true, false} : Finset Bool).erase false = {true} by decide]

/-- Exact local form of the obstruction: the current singleton data coexist,
but the reset only moves the unit debt to another coordinate. -/
theorem positive_singletonAtom_with_staticHandoff_is_pureDebtTransfer :
    quittingTerminalPayoff reward
          (Function.update base mover replacement) mover -
        quittingTerminalPayoff reward base mover =
          quittingTerminalDeviationDebt reward base mover ∧
      quittingTerminalPayoffDifferenceAtom reward target source observer
          (some observerTerminal) = 1 ∧
      quittingTerminalDeviationDebt reward target observer = 0 ∧
      HasQuittingStaticAtomicToggleHandoff reward ∧
      (∀ deviation : (quittingGame reward).BehaviorStrategy observer,
        quittingTerminalPayoff reward
            (Function.update target observer deviation) observer -
          quittingTerminalPayoff reward target observer ≤ 0) ∧
      quittingTerminalDebtSum reward target =
        quittingTerminalDebtSum reward source := by
  refine ⟨replacement_is_exactBestResponse_at_base,
    singleton_observer_atom_eq_one, target_observer_debt_eq_zero,
    has_staticAtomicToggleHandoff, ?_, ?_⟩
  · intro deviation
    have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward target observer deviation (M := 1) (by norm_num) reward_bound
    rw [target_bestResponse_observer] at hdeviation
    rw [target_payoff_observer]
    linarith
  · rw [target_totalDebt, source_totalDebt]

end StoppingLawSingletonOrientationNoGo

end GameTheory
