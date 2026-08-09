/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit

/-!
# Value convergence along infinite exact punishment-floor orbits

Inside a quitting counterexample regime, every arbitrary infinite exact
punishment-floor Nash--Bellman orbit has summable absorption mass.  This
module derives the resulting limit geometry of the orbit's Bellman
annotations.

Each one-stage Bellman edge moves a bounded value coordinate by at most
twice the reward bound times the stage's absorption mass.  Summability of
those masses therefore makes every value coordinate a Cauchy sequence, so
the annotations converge coordinatewise to a single payoff vector.

The limit inherits three constraints.  It stays in the canonical compact
reward box.  It dominates the behavioral punishment floor, because every
finite truncation of the orbit is an exact punishment-floor prefix.  And it
dominates every player's own solo quitting reward: at each stage the pure
Quit endpoint is within twice the reward bound times the opponent-absorption
hazard of the solo reward, exact root Nash keeps that endpoint below the
successor annotation, and the opponent hazard vanishes because it is
dominated by the summable joint absorption mass.  The one-shot quit
deviation thus survives to the limit, which is simultaneously individually
rational and solo-undercut-free.

The values here are prescribed Bellman annotations, not realized payoffs of
any strategy profile.  No claim is made that the limit payoff is achieved by
play; identifying annotations with realized continuation payoffs is
precisely the separate realization problem.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Forcing one player to pure Continue only removes absorption events: a
player's one-stage opponent-absorption hazard is at most the root's joint
absorption mass. -/
theorem quittingRootOpponentAbsorptionMass_le_absorptionMass
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who ≤
      quittingRootAbsorptionMass root := by
  have hcontinue : quittingStationaryContinueMass root ≤
      quittingStationaryContinueMass
        (Function.update root who (PMF.pure false)) :=
    quittingStationaryContinueMass_le_fixedOpponentsContinueMass root who
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  linarith

namespace QuittingPunishmentFloorInfiniteOrbit

variable (orbit : QuittingPunishmentFloorInfiniteOrbit reward)

/-- Every coordinate of every orbit annotation lies in the canonical reward
interval. -/
theorem abs_value_le_quittingRewardBound (time : ℕ) (who : ι) :
    |orbit.value time who| ≤ quittingRewardBound reward := by
  have hmem : orbit.value time ∈ Set.Icc
      (fun _ : ι => -quittingRewardBound reward)
      (fun _ : ι => quittingRewardBound reward) := orbit.value_mem time
  exact abs_le.mpr ⟨hmem.1 who, hmem.2 who⟩

/-- One-stage drift bound: consecutive orbit annotations differ
coordinatewise by at most twice the reward bound times the stage's
absorption mass. -/
theorem abs_value_succ_sub_le_two_mul_absorptionMass (time : ℕ) (who : ι) :
    |orbit.value (time + 1) who - orbit.value time who| ≤
      2 * quittingRewardBound reward *
        quittingRootAbsorptionMass (orbit.roots time) := by
  rw [orbit.policy time]
  exact abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    reward (orbit.value time) (orbit.roots time) who
    (quittingRewardBound reward)
    (abs_reward_le_quittingRewardBound reward)
    (orbit.abs_value_le_quittingRewardBound time who)

/-- Every orbit annotation dominates the behavioral punishment floor at
every date: truncating the orbit yields an exact finite prefix, whose anchor
floor propagates through the exact edges. -/
theorem punishmentValue_le_value (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ orbit.value time who :=
  quittingPunishmentValue_le_finitePrefixValue
    (orbit.toFinitePrefix time) time le_rfl who

/-- Pure-Quit endpoint estimate: each successor annotation is at least the
player's solo reward minus twice the reward bound times the current
opponent-absorption hazard.  Exact root Nash dominates the pure-Quit
endpoint, and that endpoint differs from the solo reward only on the event
that an opponent also quits. -/
theorem soloReward_sub_opponentHazard_le_value_succ (time : ℕ) (who : ι) :
    quittingSoloReward reward who who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (orbit.roots time) who ≤
      orbit.value (time + 1) who := by
  have hest :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (orbit.value time) (orbit.roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (orbit.value time) (orbit.roots time) who (orbit.exactNash time)
  have hsucc : orbit.value (time + 1) who =
      quittingRootSuccessorPayoff reward (orbit.value time)
        (orbit.roots time) who :=
    congrFun (orbit.policy time) who
  have hsolo : quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := rfl
  have hpair := abs_le.mp hest
  rw [hsolo]
  linarith [hpair.1, hquit, hsucc]

end QuittingPunishmentFloorInfiniteOrbit

namespace QuittingCounterexampleRegime

/-- Every player's opponent-absorption hazard vanishes along every arbitrary
infinite exact punishment-floor orbit, being squeezed by the joint
absorption mass. -/
theorem infiniteOrbit_opponentAbsorptionMass_tendsto_zero
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    Tendsto (fun time =>
        quittingRootOpponentAbsorptionMass (orbit.roots time) who)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time => quittingOpponentClockCharge_nonneg orbit.roots who time
  · exact fun time =>
      quittingRootOpponentAbsorptionMass_le_absorptionMass
        (orbit.roots time) who
  · exact regime.infiniteOrbit_absorptionMass_tendsto_zero orbit

/-- Coordinatewise absolute increments of the orbit annotations are
summable, by comparison with the summable absorption masses. -/
theorem infiniteOrbit_abs_value_succ_sub_summable
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) (who : ι) :
    Summable (fun time =>
      |orbit.value (time + 1) who - orbit.value time who|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun time => orbit.abs_value_succ_sub_le_two_mul_absorptionMass time who)
    ((regime.infiniteOrbit_absorptionMass_summable orbit).mul_left
      (2 * quittingRewardBound reward))

/-- **All-orbits value limit.**  Along every arbitrary infinite exact
punishment-floor orbit of a counterexample regime, the Bellman annotations
converge coordinatewise to a single payoff vector.  The limit lies in the
canonical compact reward box, dominates the behavioral punishment floor, and
dominates every player's own solo reward: the one-shot quit deviation
survives passage to the limit because opponent absorption vanishes.

The annotations are prescribed Bellman values, not realized payoffs of any
strategy profile; no realization claim is made about the limit. -/
theorem infiniteOrbit_exists_value_limit
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∃ limit : Payoff ι,
      (∀ who, Tendsto (fun time => orbit.value time who) atTop
        (nhds (limit who))) ∧
      limit ∈ quittingPunishmentFloorForwardCarrier reward ∧
      (∀ who, quittingPunishmentValue reward who ≤ limit who) ∧
      (∀ who, quittingSoloReward reward who who ≤ limit who) := by
  have hconverge : ∀ who : ι, ∃ coordinateLimit : ℝ,
      Tendsto (fun time => orbit.value time who) atTop
        (nhds coordinateLimit) := by
    intro who
    have hdist : Summable (fun time =>
        dist (orbit.value time who) (orbit.value (time + 1) who)) := by
      simpa [Real.dist_eq, abs_sub_comm] using
        regime.infiniteOrbit_abs_value_succ_sub_summable orbit who
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose limit hlimit using hconverge
  refine ⟨limit, hlimit, ?_, ?_, ?_⟩
  · have hbox : ∀ time, orbit.value time ∈ Set.Icc
        (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward) :=
      fun time => orbit.value_mem time
    have hlower : ∀ who, -quittingRewardBound reward ≤ limit who :=
      fun who => ge_of_tendsto' (hlimit who)
        (fun time => (hbox time).1 who)
    have hupper : ∀ who, limit who ≤ quittingRewardBound reward :=
      fun who => le_of_tendsto' (hlimit who)
        (fun time => (hbox time).2 who)
    exact Set.mem_Icc.mpr ⟨hlower, hupper⟩
  · exact fun who => ge_of_tendsto' (hlimit who)
      (fun time => orbit.punishmentValue_le_value time who)
  · intro who
    have hshift : Tendsto (fun time => orbit.value (time + 1) who) atTop
        (nhds (limit who)) := (hlimit who).comp (tendsto_add_atTop_nat 1)
    have hhazard : Tendsto (fun time =>
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds 0) := by
      simpa using
        (regime.infiniteOrbit_opponentAbsorptionMass_tendsto_zero orbit
          who).const_mul (2 * quittingRewardBound reward)
    have hlower : Tendsto (fun time =>
        quittingSoloReward reward who who -
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass (orbit.roots time) who)
        atTop (nhds (quittingSoloReward reward who who)) := by
      simpa using tendsto_const_nhds.sub hhazard
    exact le_of_tendsto_of_tendsto' hlower hshift
      (fun time =>
        orbit.soloReward_sub_opponentHazard_le_value_succ time who)

end QuittingCounterexampleRegime

end GameTheory
