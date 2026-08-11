/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalIncomingPathAlternative
import UniformEquilibrium.Quitting.Debt.Dynamic.CyclePinnedDebt

/-!
# Near-maximal admissible capacity and the rebasing seam

Every exact punishment-floor prefix is literally a path in the full
floor-admissible charged relation.  This identifies the canonical prefix
capacity with near-maximal values of the global budget-to-go potential: for
every positive error there is an admissible source state with remaining
capacity below that error.

This does not choose a zero-boundary calibrated exact-D anchor at the same
state.  The final statements isolate that co-realization seam.  An arbitrary
endpoint uses the terminal mismatch against that endpoint, not the fixed
positive-singleton debt cap; if the endpoint dominates every singleton own
reward, its terminal mismatch vanishes identically.  Thus arbitrary-state
rebasing can erase the terminal debt which carries the counterexample gap.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-! ## Exact prefixes are admissible charged paths -/

/-- The root stored at one prefix value.  At time zero it is irrelevant;
later it records the root which produced that value. -/
def quittingFinitePrefixStoredRoot
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ℕ → QuittingRootSimplex ι
  | 0 => quittingAllContinueSimplexRoot
  | time + 1 => quittingFrozenRootLiftSimplex (cert.roots time)

/-- One displayed prefix value as a boxed floor-admissible state. -/
def quittingFinitePrefixAdmissibleState
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time ≤ cert.horizon) :
    QuittingPunishmentFloorAdmissibleState reward :=
  ⟨⟨(cert.value time, quittingFinitePrefixStoredRoot cert time),
      cert.value_mem time htime⟩,
    fun who ↦ quittingPunishmentValue_le_finitePrefixValue
      cert time htime who⟩

/-- One exact prefix transition as an edge of the full admissible relation. -/
def quittingFinitePrefixAdmissibleEdge
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time < cert.horizon) :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := quittingFinitePrefixAdmissibleState cert time htime.le
  current := quittingFinitePrefixAdmissibleState cert (time + 1) htime
  exactEdge := by
    constructor
    · change cert.value (time + 1) = quittingRootSuccessorPayoff reward
        (cert.value time)
          (quittingRootOfSimplex
            (quittingFrozenRootLiftSimplex (cert.roots time)))
      rw [quittingRootOfSimplex_frozenRootLiftSimplex]
      exact cert.policy time htime
    · change IsεQuittingRootEndpointNash reward (cert.value time) 0
        (quittingRootOfSimplex
          (quittingFrozenRootLiftSimplex (cert.roots time)))
      rw [quittingRootOfSimplex_frozenRootLiftSimplex]
      exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (cert.value time) (cert.roots time)).2
          (cert.exactNash time htime)

/-- The initial segment of an exact prefix, as a literal admissible path. -/
def quittingFinitePrefixAdmissiblePath
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ∀ (time : ℕ) (htime : time ≤ cert.horizon),
      (AdmissibleRelation reward).Path
        (quittingFinitePrefixAdmissibleState cert 0 (by omega))
        (quittingFinitePrefixAdmissibleState cert time htime)
  | 0, htime => ChargedRelation.Path.nil _
  | time + 1, htime => by
      let path := quittingFinitePrefixAdmissiblePath cert time (by omega)
      let edge := quittingFinitePrefixAdmissibleEdge cert time (by omega)
      exact path.append (ChargedRelation.Path.edge edge rfl rfl)

/-- Decoding preserves the exact cumulative absorption charge. -/
theorem chargeSum_quittingFinitePrefixAdmissiblePath
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ∀ (time : ℕ) (htime : time ≤ cert.horizon),
      (quittingFinitePrefixAdmissiblePath cert time htime).chargeSum =
        ∑ offset ∈ Finset.range time,
          quittingRootAbsorptionMass (cert.roots offset)
  | 0, htime => by
      simp [quittingFinitePrefixAdmissiblePath]
  | time + 1, htime => by
      rw [Finset.sum_range_succ]
      simp only [quittingFinitePrefixAdmissiblePath,
        ChargedRelation.Path.chargeSum_append,
        ChargedRelation.Path.chargeSum_edge]
      rw [chargeSum_quittingFinitePrefixAdmissiblePath cert time]
      change _ + quittingRootAbsorptionMass
          (quittingRootOfSimplex
            (quittingFrozenRootLiftSimplex (cert.roots time))) = _
      rw [quittingRootOfSimplex_frozenRootLiftSimplex]

/-- The full decoded prefix has exactly the certificate's charge. -/
theorem chargeSum_quittingFinitePrefixAdmissiblePath_horizon
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    (quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega)).chargeSum =
      cert.charge := by
  rw [chargeSum_quittingFinitePrefixAdmissiblePath]
  rfl

/-! ## Near-maximal global admissible capacity -/

/-- Remaining capacity of the full floor-admissible budget-to-go at an
arbitrary boxed state. -/
def quittingPunishmentFloorAdmissibleRemainingCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingPunishmentFloorAdmissibleState reward) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    quittingPunishmentFloorAdmissiblePotential reward state

/-- The charge of a finite exact prefix is already available from the
budget-to-go at its literal source state. -/
theorem finitePrefix_charge_le_admissiblePotential_source
    (regime : QuittingCounterexampleRegime reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    cert.charge ≤ quittingPunishmentFloorAdmissiblePotential reward
      (quittingFinitePrefixAdmissibleState cert 0 (by omega)) := by
  rw [← chargeSum_quittingFinitePrefixAdmissiblePath_horizon cert]
  exact (AdmissibleRelation reward).chargeSum_le_value
    (quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
      regime.prefixCharge_le)
    (quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega))

/-- Every positive tolerance is beaten by an exact prefix whose charge is
within that tolerance of the least prefix-charge bound. -/
theorem exists_finitePrefix_charge_gt_prefixChargeBound_sub
    (regime : QuittingCounterexampleRegime reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      quittingPunishmentFloorPrefixChargeBound reward - ε < cert.charge := by
  classical
  by_cases htarget : 0 ≤ quittingPunishmentFloorPrefixChargeBound reward - ε
  · by_contra hno
    have hall : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ quittingPunishmentFloorPrefixChargeBound reward - ε := by
      intro cert
      exact le_of_not_gt fun hgt ↦ hno ⟨cert, hgt⟩
    have hleast :=
      (punishmentFloorPrefixChargeCapacity_toReal_le_iff
        regime.prefixChargeCapacity_ne_top htarget).2 hall
    linarith
  · refine ⟨quittingPunishmentFloorForwardFinitePrefix reward 0, ?_⟩
    have hnegative : quittingPunishmentFloorPrefixChargeBound reward - ε < 0 :=
      lt_of_not_ge htarget
    change quittingPunishmentFloorPrefixChargeBound reward - ε < 0
    exact hnegative

/-- Literal prefix sources approach the global least capacity from below.
This is an existence statement about admissible states, not about calibrated
zero-boundary minimizers at those same states. -/
theorem exists_finitePrefix_source_remainingCapacity_lt
    (regime : QuittingCounterexampleRegime reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      0 ≤ quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) ∧
      quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) < ε := by
  obtain ⟨cert, hcharge⟩ :=
    exists_finitePrefix_charge_gt_prefixChargeBound_sub regime hε
  refine ⟨cert, ?_, ?_⟩
  · unfold quittingPunishmentFloorAdmissibleRemainingCapacity
    exact sub_nonneg.mpr
      (QuittingFiniteDynamicDebtAdmissibleChronology.admissiblePotential_le_prefixChargeBound
        regime _)
  · unfold quittingPunishmentFloorAdmissibleRemainingCapacity
    have hlower := finitePrefix_charge_le_admissiblePotential_source regime cert
    linarith

/-- Any literal incoming path must fit in the remaining capacity of its
target.  This is the quantitative least-capacity obstruction to attaching a
fixed positive-charge terminal funding path at a near-maximal state. -/
theorem admissiblePath_chargeSum_le_target_remainingCapacity
    (regime : QuittingCounterexampleRegime reward)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : (AdmissibleRelation reward).Path source target) :
    path.chargeSum ≤
      quittingPunishmentFloorAdmissibleRemainingCapacity reward target := by
  have hdrop :=
    (quittingPunishmentFloorAdmissiblePotential_isBoundedPotential
      regime.prefixCharge_le).isPotential.chargeSum_le path
  have hsource :=
    QuittingFiniteDynamicDebtAdmissibleChronology.admissiblePotential_le_prefixChargeBound
      regime source
  unfold quittingPunishmentFloorAdmissibleRemainingCapacity
  linarith

/-- At every scale there is a literal exact-prefix source which cannot be the
target of any admissible incoming path carrying that scale of charge. -/
theorem exists_finitePrefix_source_forbids_incoming_charge
    (regime : QuittingCounterexampleRegime reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      0 ≤ quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) ∧
      ∀ (source : QuittingPunishmentFloorAdmissibleState reward)
        (path : (AdmissibleRelation reward).Path source
          (quittingFinitePrefixAdmissibleState cert 0 (by omega))),
        path.chargeSum < ε := by
  obtain ⟨cert, hnonneg, hsmall⟩ :=
    exists_finitePrefix_source_remainingCapacity_lt regime hε
  refine ⟨cert, hnonneg, ?_⟩
  intro source path
  exact lt_of_le_of_lt
    (admissiblePath_chargeSum_le_target_remainingCapacity regime path) hsmall

/-! ## Exact endpoint-rebasing obstruction -/

/-- The constant reward-bound endpoint dominates every singleton own reward,
so endpoint-rebased terminal mismatch is identically zero there. -/
theorem quittingTerminalContinuationMismatch_rewardBound_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalContinuationMismatch reward
        (fun _ ↦ quittingRewardBound reward) who = 0 := by
  apply quittingTerminalContinuationMismatch_eq_zero_of_singleton_le
  intro owner
  exact le_trans (le_abs_self _)
    (abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) owner)

/-- Consequently the aggregate endpoint-rebased terminal debt at the upper
box face is zero, regardless of the positive zero-boundary debt cap. -/
theorem sum_quittingTerminalContinuationMismatch_rewardBound_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∑ who, quittingTerminalContinuationMismatch reward
      (fun _ ↦ quittingRewardBound reward) who) = 0 := by
  apply Finset.sum_eq_zero
  intro who _
  exact quittingTerminalContinuationMismatch_rewardBound_eq_zero reward who

namespace QuittingCapacityNearMaximizerRebaseRegression

open QuittingBoundedSurgeryDescentCounterexample

/-- A concrete exact rebasing regression.  In the bounded-surgery table the
zero endpoint carries strictly positive terminal mismatch for player `false`,
while the realized absorbing stationary continuation carries zero mismatch.
Thus even rebasing to an actual cyclic continuation need not preserve the
positive zero-boundary debt. -/
theorem realizedEndpoint_can_erase_positive_zeroBoundaryMismatch
    (a : ℝ) (ha0 : 0 < a) :
    ∃ terminal : Payoff Bool,
      IsQuittingCyclicContinuation
          (QuittingBoundedSurgeryDescentCounterexample.reward a) terminal ∧
        0 < quittingTerminalContinuationMismatch
          (QuittingBoundedSurgeryDescentCounterexample.reward a) 0 false ∧
        quittingTerminalContinuationMismatch
          (QuittingBoundedSurgeryDescentCounterexample.reward a) terminal false = 0 := by
  refine ⟨stationaryValue a, stationaryValue_isQuittingCyclicContinuation a ha0,
    ?_, quittingTerminalContinuationMismatch_stationaryValue a false⟩
  rw [quittingTerminalContinuationMismatch_zero,
    positiveSingletonDebtCap_false a ha0]
  exact ha0

end QuittingCapacityNearMaximizerRebaseRegression

end GameTheory
