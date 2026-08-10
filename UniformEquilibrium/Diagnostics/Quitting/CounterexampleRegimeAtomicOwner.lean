/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.Cycles.ConditionedSingletonStrategicPurification
import UniformEquilibrium.Quitting.Cycles.ThreeBranchDisjunction
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Punishment.SoloCycleCompletion

/-!
# The atomic owner-monopoly branch is the isolated-negative branch

Suppose a positive-rate solo row owned by `owner` is exact endpoint Nash
against the owner's singleton payoff vector.  The inactive coordinates then
have no stationary joining gain.  In a quitting counterexample the terminal
gap must therefore be witnessed by the owner's deviation to Never.  This
quantitatively forces

`r_owner({owner}) <= -terminalGap`.

The same row is a self-consistent absorbing period-one Nash--Bellman block.
Because every opponent is silent, its negative owner is precisely the
isolated-negative branch of the cyclic classification.  Thus an atomic
owner-monopoly limit is not a new fourth obstruction: it lands in the
existing isolated-negative branch, with its entire terminal gap carried by
the owner's Never deviation.

Punishment completion then supplies the decisive extra restriction.  If the
owner's behavioral punishment value is no larger than its singleton payoff,
the isolated cycle is itself uniformly enforceable.  Hence a counterexample
atomic owner must have punishment value *strictly above* its negative
singleton payoff.  In particular the coordinatewise punishment-tight
singleton stratum excludes the atomic owner-monopoly branch completely.

This does not justify deleting the owner: after deletion, the owner may still
join an absorbing coalition, and that terminal deviation cannot be punished
after the fact.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- **Quantitative atomic-monopoly restriction.**  If a positive-rate solo
row is exact endpoint Nash against its own singleton payoff vector, then a
counterexample's fixed terminal gap fits entirely inside the owner's gain
from refusing forever. -/
theorem terminalGap_le_neg_soloReward_of_soloEndpointNash
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard)) :
    regime.terminalGap ≤ -quittingSoloReward reward owner owner := by
  have hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other :=
    (isεQuittingRootEndpointNash_soloStationaryRoot_iff
      reward owner hazard).1 hnash
  have hownerNeg : quittingSoloReward reward owner owner < 0 := by
    by_contra hnotNeg
    have hownerNonneg : 0 ≤ quittingSoloReward reward owner owner :=
      le_of_not_gt hnotNeg
    have huniform := isUniformEquilibriumPayoff_soloReward_of_inactive
      reward owner hazard hpositive hownerNonneg hinactive
    exact regime.not_exists_uniformEquilibriumPayoff
      ⟨quittingSoloReward reward owner, huniform⟩
  obtain ⟨who, hgain⟩ := regime.exists_stationaryCap_gain
    (quittingSoloStationaryRoot owner hazard)
  by_cases hwho : who = owner
  · subst who
    rw [quittingTerminalPayoff_soloStationary reward owner owner hazard
        hpositive,
      quittingStationaryUnilateralCap_solo_owner,
      max_eq_right hownerNeg.le] at hgain
    linarith
  · have hfixed :
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingSoloStationaryRoot owner hazard) who ≤
          quittingSoloReward reward owner who := by
      rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho hazard]
      exact hinactive who hwho
    rw [quittingTerminalPayoff_soloStationary reward owner who hazard
        hpositive,
      quittingStationaryUnilateralCap_solo_other reward hwho hazard
        hpositive,
      max_eq_right hfixed] at hgain
    linarith [regime.terminalGap_pos]

/-- The quantitative restriction in its direct sign form. -/
theorem soloReward_le_neg_terminalGap_of_soloEndpointNash
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard)) :
    quittingSoloReward reward owner owner ≤ -regime.terminalGap := by
  linarith [regime.terminalGap_le_neg_soloReward_of_soloEndpointNash
    owner hazard hpositive hnash]

/-- **Atomic conditioned-limit restriction.**  When conditioned solo rows
converge to a positive owner rate and their continuation annotations converge
to the owner's singleton payoff vector, the limiting owner payoff is at most
the negated counterexample gap.  This is the quantitative strengthening of
the sign-only atomic restriction. -/
theorem soloReward_le_neg_terminalGap_of_atomicSoloLimit
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time)))) :
    quittingSoloReward reward owner owner ≤ -regime.terminalGap := by
  have hlimitNash := isEndpointNash_soloRate_of_tendsto
    reward owner rate tail limitRate hrateNonneg hrateOne
      hlimitPositive.le hlimitOne hrate htail hnash
  exact regime.soloReward_le_neg_terminalGap_of_soloEndpointNash
    owner (quittingHazardCoin limitRate hlimitPositive.le hlimitOne)
      (by simpa using hlimitPositive) hlimitNash

/-- **Punishment obstruction at an atomic owner.**  A counterexample
positive-rate solo endpoint equilibrium cannot have a punishment floor below
the owner's singleton payoff: punishment completion would enforce the
period-one solo cycle. -/
theorem soloReward_lt_punishmentValue_of_soloEndpointNash
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard)) :
    quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner := by
  by_contra hnot
  have hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner := le_of_not_gt hnot
  have huniform :=
    isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR
      reward owner hazard hpositive hnash hpunishment
  exact regime.not_exists_uniformEquilibriumPayoff
    ⟨quittingSoloReward reward owner, huniform⟩

/-- The punishment obstruction transferred through an atomic conditioned
limit. -/
theorem soloReward_lt_punishmentValue_of_atomicSoloLimit
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time)))) :
    quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner := by
  have hlimitNash := isEndpointNash_soloRate_of_tendsto
    reward owner rate tail limitRate hrateNonneg hrateOne
      hlimitPositive.le hlimitOne hrate htail hnash
  exact regime.soloReward_lt_punishmentValue_of_soloEndpointNash
    owner (quittingHazardCoin limitRate hlimitPositive.le hlimitOne)
      (by simpa using hlimitPositive) hlimitNash

/-- **Tight-punishment exclusion.**  The atomic conditioned owner-monopoly
limit is impossible whenever the owner's punishment value is bounded by its
singleton payoff. -/
theorem not_atomicSoloLimit_of_punishment_le_soloReward
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time))))
    (hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) : False := by
  have hstrict := regime.soloReward_lt_punishmentValue_of_atomicSoloLimit
    owner rate tail limitRate hrateNonneg hrateOne hlimitPositive hlimitOne
      hrate htail hnash
  linarith

/-- Boundary-shaped form used by conditioned phantom tails.  A punishment
lower bound on the phantom boundary and tightness of the owner's boundary
coordinate eliminate the atomic owner limit. -/
theorem not_atomicSoloLimit_of_punishment_le_tightBoundary
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (boundary : Payoff ι)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time))))
    (hpunishment : quittingPunishmentValue reward owner ≤ boundary owner)
    (htight : boundary owner = quittingSoloReward reward owner owner) : False := by
  apply regime.not_atomicSoloLimit_of_punishment_le_soloReward
    owner rate tail limitRate hrateNonneg hrateOne hlimitPositive hlimitOne
      hrate htail hnash
  exact hpunishment.trans_eq htight

end QuittingCounterexampleRegime

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-- **Direct conditioned-seam exclusion.**  On a counterexample seam, a
singleton-tight boundary coordinate cannot be the positive-rate atomic limit
of strategically purified solo rows.

The uniqueness/occupation argument that produces such a cluster is kept out
of the statement.  Its only required outputs are the convergence of the
conditioned continuation annotations to the owner's singleton vector and
exact endpoint Nash of the converging solo rows.  The seam supplies the
punishment inequality, while boundary tightness turns it into the precise
punishment-completion gate. -/
theorem not_atomicSoloLimit_of_limitValue_eq_singleton
    (seam : QuittingCounterexampleSeamWitness regime)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time))))
    (htight : seam.limit.value owner =
      quittingSoloReward reward owner owner) : False := by
  exact regime.not_atomicSoloLimit_of_punishment_le_tightBoundary
    owner rate tail limitRate seam.limit.value hrateNonneg hrateOne
      hlimitPositive hlimitOne hrate htail hnash
      (seam.punishmentValue_le_limitValue owner) htight

end QuittingCounterexampleSeamWitness

/-! ## Identification with the cyclic third branch -/

/-- A positive-rate solo endpoint equilibrium with a negative owner produces
an isolated-negative absorbing period-one Nash--Bellman block. -/
theorem hasIsolatedNegativeAbsorbingQuittingCycle_of_soloEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard))
    (hnegative : quittingSoloReward reward owner owner < 0) :
    HasIsolatedNegativeAbsorbingQuittingCycle reward := by
  let value : Payoff ι := quittingSoloReward reward owner
  let root : ι → PMF Bool := quittingSoloStationaryRoot owner hazard
  let block : QuittingFiniteNashBellmanPath ι 1 :=
    quittingRowBlock value root
  have hvalueBound : ∀ who, |value who| ≤ quittingRewardBound reward := by
    intro who
    exact abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) who
  have hsuccessor : value =
      quittingRootSuccessorPayoff reward value root := by
    exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward owner hazard).symm
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    dsimp only [root]
    rw [quittingRootAbsorptionMass_soloStationaryRoot]
    exact hpositive
  have hblock : IsQuittingCyclicContinuationBlock reward value 1 block :=
    quittingRowBlock_isQuittingCyclicContinuationBlock
      reward value root hvalueBound hsuccessor hnash habsorption
  have hisolated : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots 1 block) owner 1 := by
    intro time htime
    have htimeZero : time = 0 := by omega
    subst time
    rw [quittingFiniteNashBellmanPathRoots_of_lt 1 block 0 (by omega)]
    dsimp only [block]
    rw [quittingRootOfSimplex_quittingRowBlock]
    exact (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot
      root owner).2 ⟨hazard, rfl⟩
  exact ⟨value, 0, block, owner, hblock, hisolated, hnegative⟩

/-- In a counterexample, every positive-rate solo endpoint equilibrium lands
in the isolated-negative branch, and its owner payoff is separated from zero
by at least the counterexample's terminal gap. -/
theorem exists_isolatedNegativeCycle_and_soloReward_le_neg_terminalGap
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard)) :
    HasIsolatedNegativeAbsorbingQuittingCycle reward ∧
      quittingSoloReward reward owner owner ≤ -regime.terminalGap := by
  have hbound := regime.soloReward_le_neg_terminalGap_of_soloEndpointNash
    owner hazard hpositive hnash
  have hnegative : quittingSoloReward reward owner owner < 0 :=
    lt_of_le_of_lt hbound (neg_neg_of_pos regime.terminalGap_pos)
  exact ⟨hasIsolatedNegativeAbsorbingQuittingCycle_of_soloEndpointNash
    reward owner hazard hpositive hnash hnegative, hbound⟩

/-- The atomic conditioned limit lands quantitatively in the existing
isolated-negative cyclic branch. -/
theorem atomicSoloLimit_isolatedNegativeCycle_and_gap
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time)))) :
    HasIsolatedNegativeAbsorbingQuittingCycle reward ∧
      quittingSoloReward reward owner owner ≤ -regime.terminalGap := by
  have hlimitNash := isEndpointNash_soloRate_of_tendsto
    reward owner rate tail limitRate hrateNonneg hrateOne
      hlimitPositive.le hlimitOne hrate htail hnash
  exact exists_isolatedNegativeCycle_and_soloReward_le_neg_terminalGap
    regime owner (quittingHazardCoin limitRate hlimitPositive.le hlimitOne)
      (by simpa using hlimitPositive) hlimitNash

end GameTheory
