/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime

/-!
# Search consequences of the quitting counterexample regime

This module extracts local and finite rejection tests from the global
counterexample regime.  They are intended for exact search code: a proposed
Nash--Bellman predecessor graph can be rejected without constructing a
strategy once it exhibits a reachable positive-charge return.

The strongest graph restriction is local.  Every edge lying on a directed
cycle has zero absorption charge.  Hence every positive-charge edge is
strictly transient, and strictly decreases the canonical budget-to-go
potential.  Quantitatively, a path contains at most `C / threshold` edges
whose charge is at least a positive threshold, where `C` is the regime's
common prefix-charge bound.

The same prefix bound has an all-orbits consequence.  Every arbitrary
infinite exact punishment-floor Nash--Bellman orbit has total absorption at
most the common bound.  Its absorption masses, and every player's individual
quit probabilities, are summable; the roots therefore converge
coordinatewise to all-Continue.

The cycle-rejection statements concern the exact punishment-floor reachable
relation; the all-orbits statement uses the larger finite-prefix family whose
initial value may merely dominate the floor.  A numerical near-cycle is not
an exact rejection certificate unless its Bellman, Nash, endpoint, and return
equalities have been certified.
-/

noncomputable section

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation
namespace Path

universe u v

variable {State : Type u} {Edge : Type v}
variable {R : ChargedRelation State Edge}

/-- Number of edges in a path whose charge is at least `threshold`. -/
def highChargeCount (threshold : ℝ) :
    {source target : State} → R.Path source target → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons edge rest =>
      if threshold ≤ R.charge edge then highChargeCount threshold rest + 1
      else highChargeCount threshold rest

@[simp] theorem highChargeCount_nil (threshold : ℝ) (state : State) :
    highChargeCount threshold (Path.nil state : R.Path state state) = 0 := rfl

@[simp] theorem highChargeCount_cons (threshold : ℝ) (edge : Edge)
    {target : State} (rest : R.Path (R.tgt edge) target) :
    highChargeCount threshold (Path.cons edge rest) =
      if threshold ≤ R.charge edge then highChargeCount threshold rest + 1
      else highChargeCount threshold rest := rfl

/-- Counting high-charge edges gives a lower bound on total path charge. -/
theorem highChargeCount_mul_le_chargeSum
    (threshold : ℝ)
    {source target : State} (path : R.Path source target) :
    (highChargeCount threshold path : ℝ) * threshold ≤ path.chargeSum := by
  induction path with
  | nil state => simp
  | cons edge rest ih =>
      by_cases hedge : threshold ≤ R.charge edge
      · simp only [highChargeCount_cons, hedge, if_true,
          Nat.cast_add, Nat.cast_one, chargeSum_cons]
        nlinarith
      · simp only [highChargeCount_cons, hedge, if_false, chargeSum_cons]
        nlinarith [R.charge_nonneg edge]

end Path
end ChargedRelation
end ChargedPathBudget
end Math

namespace GameTheory

open Filter
open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPunishmentFloorFinitePrefix

/-- Number of certified prefix stages whose literal absorption mass is at
least `threshold`. -/
def highAbsorptionStageCount
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (threshold : ℝ) : ℕ :=
  (Finset.range cert.horizon |>.filter fun time =>
    threshold ≤ quittingRootAbsorptionMass (cert.roots time)).card

/-- The high-absorption stage count is controlled by the prefix's exact total
absorption charge. -/
theorem highAbsorptionStageCount_mul_le_charge
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (threshold : ℝ) :
    (cert.highAbsorptionStageCount threshold : ℝ) * threshold ≤ cert.charge := by
  let highStages := Finset.range cert.horizon |>.filter fun time =>
    threshold ≤ quittingRootAbsorptionMass (cert.roots time)
  calc
    (cert.highAbsorptionStageCount threshold : ℝ) * threshold =
        ∑ _time ∈ highStages, threshold := by
          simp [highAbsorptionStageCount, highStages]
    _ ≤ ∑ time ∈ highStages,
        quittingRootAbsorptionMass (cert.roots time) := by
          apply Finset.sum_le_sum
          intro time htime
          exact (Finset.mem_filter.mp htime).2
    _ ≤ ∑ time ∈ Finset.range cert.horizon,
        quittingRootAbsorptionMass (cert.roots time) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro time _ _
            unfold quittingRootAbsorptionMass
            linarith [quittingStationaryContinueMass_le_one (cert.roots time)]
    _ = cert.charge := rfl

end QuittingPunishmentFloorFinitePrefix

/-! ## Arbitrary infinite exact punishment-floor orbits -/

/-- An arbitrary infinite exact Nash--Bellman orbit in the canonical box,
anchored coordinatewise above the behavioral punishment floor.

Unlike the selected orbit, this structure carries no choice rule.  It is the
literal infinite-horizon analogue of `QuittingPunishmentFloorFinitePrefix`,
and every finite truncation belongs to that larger prefix family. -/
structure QuittingPunishmentFloorInfiniteOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  value_mem : ∀ time,
    value time ∈ quittingPunishmentFloorForwardCarrier reward
  anchor_floor : ∀ who,
    quittingPunishmentValue reward who ≤ value 0 who
  policy : ∀ time,
    value (time + 1) =
      quittingRootSuccessorPayoff reward (value time) (roots time)
  exactNash : ∀ time,
    IsεQuittingRootNash reward (value time) 0 (roots time)

namespace QuittingPunishmentFloorInfiniteOrbit

variable (orbit : QuittingPunishmentFloorInfiniteOrbit reward)

/-- Cumulative absorption mass before a finite horizon. -/
def partialAbsorption (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    quittingRootAbsorptionMass (orbit.roots time)

/-- Every finite truncation of an arbitrary infinite exact orbit is an exact
punishment-floor prefix certificate. -/
def toFinitePrefix (horizon : ℕ) :
    QuittingPunishmentFloorFinitePrefix reward where
  roots := orbit.roots
  value := orbit.value
  horizon := horizon
  value_mem := fun time _ => orbit.value_mem time
  anchor_floor := orbit.anchor_floor
  policy := fun time _ => orbit.policy time
  exactNash := fun time _ => orbit.exactNash time

@[simp] theorem toFinitePrefix_charge (horizon : ℕ) :
    (orbit.toFinitePrefix horizon).charge = orbit.partialAbsorption horizon :=
  rfl

theorem absorptionMass_nonneg (time : ℕ) :
    0 ≤ quittingRootAbsorptionMass (orbit.roots time) := by
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_le_one (orbit.roots time)]

/-- A player's quit probability is bounded by the probability that at least
one player quits. -/
theorem quitProbability_le_absorptionMass (time : ℕ) (who : ι) :
    (orbit.roots time who true).toReal ≤
      quittingRootAbsorptionMass (orbit.roots time) := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability
      (orbit.roots time) who
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (orbit.roots time) who
  unfold quittingRootAbsorptionMass
  linarith

theorem quitProbability_nonneg (time : ℕ) (who : ι) :
    0 ≤ (orbit.roots time who true).toReal :=
  ENNReal.toReal_nonneg

end QuittingPunishmentFloorInfiniteOrbit

namespace QuittingCounterexampleRegime

private abbrev ReachableRelation :=
  quittingPunishmentFloorReachableChargedRelation reward

/-- A counterexample path can cross a positive absorption threshold only
finitely often, with an explicit bound supplied by the common prefix budget.

This avoids division and rounding: search code can compare the integer count
after coercion directly with `prefixChargeBound / threshold`. -/
theorem highChargeCount_mul_threshold_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (threshold : ℝ)
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : ReachableRelation.Path source target) :
    (path.highChargeCount threshold : ℝ) * threshold ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  exact (path.highChargeCount_mul_le_chargeSum threshold).trans
    (regime.reachablePath_chargeSum_le_prefixChargeBound path)

/-- The same threshold-count restriction holds on the larger family of all
exact punishment-floor finite-prefix certificates, including those whose
initial value merely dominates the floor rather than equals its anchor. -/
theorem highAbsorptionStageCount_mul_threshold_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (threshold : ℝ) :
    (cert.highAbsorptionStageCount threshold : ℝ) * threshold ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  exact (cert.highAbsorptionStageCount_mul_le_charge threshold).trans
    (regime.prefixCharge_le cert)

/-- Every finite partial absorption sum along every exact punishment-floor
orbit is bounded by the one common regime constant. -/
theorem infiniteOrbit_partialAbsorption_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (horizon : ℕ) :
    orbit.partialAbsorption horizon ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  rw [← orbit.toFinitePrefix_charge horizon]
  exact regime.prefixCharge_le (orbit.toFinitePrefix horizon)

/-- Every arbitrary infinite exact punishment-floor orbit has summable total
absorption mass.  This is an all-orbits statement, not a property only of the
classically selected predecessor orbit. -/
theorem infiniteOrbit_absorptionMass_summable
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Summable (fun time =>
      quittingRootAbsorptionMass (orbit.roots time)) := by
  refine summable_of_sum_range_le
    (c := quittingPunishmentFloorPrefixChargeBound reward)
    (fun time => orbit.absorptionMass_nonneg time) ?_
  intro horizon
  simpa only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption] using
    regime.infiniteOrbit_partialAbsorption_le_prefixChargeBound orbit horizon

/-- The total absorption mass of every arbitrary exact orbit is bounded by
the same regime constant. -/
theorem infiniteOrbit_tsum_absorptionMass_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    ∑' time, quittingRootAbsorptionMass (orbit.roots time) ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  apply Real.tsum_le_of_sum_range_le orbit.absorptionMass_nonneg
  intro horizon
  simpa only [QuittingPunishmentFloorInfiniteOrbit.partialAbsorption] using
    regime.infiniteOrbit_partialAbsorption_le_prefixChargeBound orbit horizon

/-- Absorption mass tends to zero along every arbitrary exact
punishment-floor orbit. -/
theorem infiniteOrbit_absorptionMass_tendsto_zero
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Tendsto (fun time => quittingRootAbsorptionMass (orbit.roots time))
      atTop (nhds 0) :=
  (regime.infiniteOrbit_absorptionMass_summable orbit).tendsto_atTop_zero

/-- Every player's quit probability tends to zero along every arbitrary exact
punishment-floor orbit. -/
theorem infiniteOrbit_quitProbability_tendsto_zero
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Tendsto (fun time => (orbit.roots time who true).toReal)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time => orbit.quitProbability_nonneg time who
  · exact fun time => orbit.quitProbability_le_absorptionMass time who
  · exact regime.infiniteOrbit_absorptionMass_tendsto_zero orbit

/-- Each individual player's quit probabilities are themselves summable
along every arbitrary exact punishment-floor orbit. -/
theorem infiniteOrbit_quitProbability_summable
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Summable (fun time => (orbit.roots time who true).toReal) :=
  Summable.of_nonneg_of_le
    (fun time => orbit.quitProbability_nonneg time who)
    (fun time => orbit.quitProbability_le_absorptionMass time who)
    (regime.infiniteOrbit_absorptionMass_summable orbit)

/-- Equivalently, every player's continuation probability tends to one: all
arbitrary exact punishment-floor roots converge coordinatewise to the
all-Continue root. -/
theorem infiniteOrbit_continueProbability_tendsto_one
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : ι) :
    Tendsto (fun time => (orbit.roots time who false).toReal)
      atTop (nhds 1) := by
  have hquit := regime.infiniteOrbit_quitProbability_tendsto_zero orbit who
  have hidentity : (fun time => (orbit.roots time who false).toReal) =
      fun time => 1 - (orbit.roots time who true).toReal := by
    funext time
    linarith [quittingRoot_continueProbability_add_quitProbability
      (orbit.roots time) who]
  rw [hidentity]
  simpa using tendsto_const_nhds.sub hquit

/-- **Combined all-orbits counterexample capstone.**  Along every arbitrary
exact punishment-floor orbit, every sufficiently late current root has
arbitrarily small absorption, yet the actual root-sequence behavior profile
starting at that date still admits a unilateral terminal improvement of at
least the regime's common terminal gap.

The terminal payoffs here are the genuine stochastic-game terminal payoffs of
`quittingRootSequenceProfile`.  No equality with `orbit.value time` is used or
claimed: the stored orbit values certify exact one-stage Nash--Bellman edges,
whereas identifying them with realized continuation payoffs is precisely the
separate realization problem.  The exploiting player and deviation may vary
with time. -/
theorem eventually_smallAbsorption_and_terminalExploitability
    (regime : QuittingCounterexampleRegime reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ time in atTop,
      quittingRootAbsorptionMass (orbit.roots time) < ε ∧
        ∃ (who : ι) (dev : (quittingGame reward).BehaviorStrategy who),
          quittingTerminalPayoff reward
              (quittingRootSequenceProfile reward orbit.roots time) who +
              regime.terminalGap ≤
            quittingTerminalPayoff reward
              (Function.update
                (quittingRootSequenceProfile reward orbit.roots time)
                who dev) who := by
  have hsmall : ∀ᶠ time in atTop,
      quittingRootAbsorptionMass (orbit.roots time) < ε :=
    (regime.infiniteOrbit_absorptionMass_tendsto_zero orbit).eventually
      (Iio_mem_nhds hε)
  filter_upwards [hsmall] with time htime
  exact ⟨htime, regime.terminalExploitability
    (quittingRootSequenceProfile reward orbit.roots time)⟩

/-- A positive-charge edge strictly decreases the canonical budget-to-go
potential. -/
theorem canonicalPotential_strict_decrease_of_positiveCharge
    (regime : QuittingCounterexampleRegime reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    quittingPunishmentFloorReachablePotential reward edge.current <
      quittingPunishmentFloorReachablePotential reward edge.tail := by
  have hdecrement := regime.canonicalPotential_predecessor_decrement edge
  linarith

/-- Every edge admitting a return path has zero absorption charge.  Thus all
edges internal to a directed strongly connected component are zero-charge. -/
theorem absorptionCharge_eq_zero_of_returnPath
    (regime : QuittingCounterexampleRegime reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (returnPath : ReachableRelation.Path edge.current edge.tail) :
    edge.toBoxEdge.absorptionCharge = 0 := by
  let cycle : ReachableRelation.Path edge.tail edge.tail :=
    ChargedRelation.Path.cons edge returnPath
  have hcycle : cycle.chargeSum = 0 :=
    regime.reachable_cycle_chargeSum_eq_zero cycle
  have hreturn := returnPath.chargeSum_nonneg
  change edge.toBoxEdge.absorptionCharge + returnPath.chargeSum = 0 at hcycle
  exact le_antisymm (by linarith)
    (QuittingPunishmentFloorBoxEdge.absorptionCharge_nonneg edge.toBoxEdge)

end QuittingCounterexampleRegime

/-! ## Exact positive certificates -/

variable [Nonempty ι]

/-- If exact prefixes can realize arbitrarily many stages above one fixed
positive absorption threshold, then their total charges are unbounded and the
finite-prefix compiler produces a uniform-equilibrium payoff.  This is the
counting form of the positive producer, convenient for enumerative search. -/
theorem quittingGame_exists_uniformPayoff_of_unbounded_highAbsorptionCount
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hprefix : ∀ countTarget : ℕ,
      Nonempty {cert : QuittingPunishmentFloorFinitePrefix reward //
        countTarget ≤ cert.highAbsorptionStageCount threshold}) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformPayoff_of_arbitrarilyCharged_floorPrefixes
    reward
  intro chargeTarget _
  obtain ⟨countTarget, hcountTarget⟩ :=
    exists_nat_ge (chargeTarget / threshold)
  obtain ⟨⟨cert, hcount⟩⟩ := hprefix countTarget
  refine ⟨⟨cert, ?_⟩⟩
  have hchargeTarget : chargeTarget ≤ (countTarget : ℝ) * threshold :=
    (div_le_iff₀ hthreshold).mp hcountTarget
  have hcountReal : (countTarget : ℝ) ≤
      cert.highAbsorptionStageCount threshold := by
    exact_mod_cast hcount
  exact hchargeTarget.trans <|
    (mul_le_mul_of_nonneg_right hcountReal hthreshold.le).trans
      (cert.highAbsorptionStageCount_mul_le_charge threshold)

/-- Any positive-charge cycle in the reachable exact predecessor relation is
a finite certificate that the game has a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_positive_reachable_cycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {state : QuittingPunishmentFloorReachableState reward}
    (cycle : (quittingPunishmentFloorReachableChargedRelation reward).Path
      state state)
    (hpositive : 0 < cycle.chargeSum) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
  have hzero := regime.reachable_cycle_chargeSum_eq_zero cycle
  linarith

/-- A reachable exact predecessor edge with positive absorption and an exact
return path is a finite certificate that the game has a uniform-equilibrium
payoff. -/
theorem quittingGame_exists_uniformPayoff_of_positive_reachable_return
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (returnPath :
      (quittingPunishmentFloorReachableChargedRelation reward).Path
        edge.current edge.tail)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformPayoff_of_positive_reachable_cycle reward
    (ChargedRelation.Path.cons edge returnPath)
  change 0 < edge.toBoxEdge.absorptionCharge + returnPath.chargeSum
  nlinarith [returnPath.chargeSum_nonneg]

/-- In particular, a positive-absorption self-loop in the exact reachable
predecessor relation certifies existence of a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_positive_reachable_selfLoop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (hloop : edge.current = edge.tail)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformPayoff_of_positive_reachable_return
    reward edge
  · exact (ChargedRelation.Path.nil edge.current).castTgt hloop
  · exact hpositive

end GameTheory
