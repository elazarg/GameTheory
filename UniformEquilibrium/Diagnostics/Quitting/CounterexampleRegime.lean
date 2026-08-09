/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtPositiveLimit

/-!
# A combined counterexample regime for finite quitting games

This module packages three unconditional restrictions on any finite quitting
game without a uniform-equilibrium payoff.

* Every behavioral profile has a unilateral terminal improvement bounded below
  by one common positive gap.
* The attained minimum playerwise maximum exact dynamic debt stays above one
  common positive floor at every zero-boundary cutoff.
* Every exact punishment-rational Nash--Bellman prefix in the canonical box has
  total absorption charge below one common finite bound.

The package is equivalent to nonexistence because the terminal gap already
implies nonexistence, while the other two fields are additional necessary
structure.  They have useful derived forms: the debt floor produces a
projective positive-debt tail with a summable opponent clock, and the prefix
bound produces the canonical bounded potential on the punishment-floor
reachable predecessor relation.

The two path witnesses are not identified here.  The positive-debt tail comes
from zero-boundary optimized exact-D chains, whereas the bounded potential is
defined on the punishment-floor reachable relation.  Relating those carriers
requires an additional anchoring or realization theorem.
-/

noncomputable section

namespace GameTheory

open Filter
open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A direct quantitative normal form for a finite quitting-game
counterexample.

The fields deliberately retain the three scalar margins used by computation:
a terminal exploitability gap, an optimized dynamic-debt floor, and an exact
prefix absorption budget. -/
structure QuittingCounterexampleRegime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  /-- Uniform positive terminal exploitability margin. -/
  terminalGap : ℝ
  terminalGap_pos : 0 < terminalGap
  terminalExploitability : HasTerminalExploitabilityGap reward terminalGap
  /-- Uniform positive lower bound on every attained finite-cutoff min-max
  dynamic debt. -/
  debtFloor : ℝ
  debtFloor_pos : 0 < debtFloor
  debtFloor_le : ∀ cutoff : ℕ,
    debtFloor ≤
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff
  /-- Common upper bound on total absorption charge of every exact
  punishment-floor prefix. -/
  prefixChargeBound : ℝ
  prefixChargeBound_nonneg : 0 ≤ prefixChargeBound
  prefixCharge_le : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
    cert.charge ≤ prefixChargeBound

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal-gap field alone refutes every uniform-equilibrium payoff. -/
theorem not_exists_uniformEquilibriumPayoff
    (regime : QuittingCounterexampleRegime reward) :
    ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).2
      ⟨regime.terminalGap, regime.terminalGap_pos,
        regime.terminalExploitability⟩

/-- The recorded finite-prefix bound controls every charged path starting at
the exact punishment-floor anchor. -/
theorem hasAnchoredChargeBound
    (regime : QuittingCounterexampleRegime reward) :
    HasQuittingPunishmentFloorAnchoredChargeBound reward
      regime.prefixChargeBound :=
  hasAnchoredChargeBound_of_finitePrefixChargeBound regime.prefixCharge_le

/-- The full punishment-floor reachable predecessor relation has finite path
budget. -/
theorem reachable_hasFiniteBudget
    (regime : QuittingCounterexampleRegime reward) :
    (quittingPunishmentFloorReachableChargedRelation reward).HasFiniteBudget :=
  quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
    regime.hasAnchoredChargeBound

/-- The recorded scalar bounds every finite path inside the full reachable
predecessor relation, regardless of its reachable source. -/
theorem reachablePath_chargeSum_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : (quittingPunishmentFloorReachableChargedRelation reward).Path
      source target) :
    path.chargeSum ≤ regime.prefixChargeBound :=
  reachablePath_chargeSum_le_of_anchoredChargeBound
    regime.hasAnchoredChargeBound path

/-- The named budget-to-go is a bounded potential on every reachable exact
predecessor state. -/
theorem canonicalPotential_isBoundedPotential
    (regime : QuittingCounterexampleRegime reward) :
    (quittingPunishmentFloorReachableChargedRelation reward).IsBoundedPotential
      (quittingPunishmentFloorReachablePotential reward) :=
  quittingPunishmentFloorReachablePotential_isBoundedPotential
    regime.hasAnchoredChargeBound

/-- The canonical reachable potential is nonnegative. -/
theorem canonicalPotential_nonneg
    (regime : QuittingCounterexampleRegime reward)
    (state : QuittingPunishmentFloorReachableState reward) :
    0 ≤ quittingPunishmentFloorReachablePotential reward state :=
  quittingPunishmentFloorReachablePotential_nonneg
    regime.hasAnchoredChargeBound state

/-- The recorded prefix budget bounds the canonical reachable potential
pointwise. -/
theorem canonicalPotential_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (state : QuittingPunishmentFloorReachableState reward) :
    quittingPunishmentFloorReachablePotential reward state ≤
      regime.prefixChargeBound :=
  quittingPunishmentFloorReachablePotential_le_chargeBound
    regime.hasAnchoredChargeBound state

/-- Every reachable exact predecessor edge spends its literal absorption mass
as a decrease of the canonical potential. -/
theorem canonicalPotential_predecessor_decrement
    (regime : QuittingCounterexampleRegime reward)
    (edge : QuittingPunishmentFloorReachableEdge reward) :
    quittingPunishmentFloorReachablePotential reward edge.current +
        edge.toBoxEdge.absorptionCharge ≤
      quittingPunishmentFloorReachablePotential reward edge.tail :=
  quittingPunishmentFloorReachablePotential_predecessor_decrement
    regime.hasAnchoredChargeBound edge

/-- Every closed path in the reachable predecessor relation has zero charge.
This is the cycle-level falsification test most directly usable in finite
searches. -/
theorem reachable_cycle_chargeSum_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    {state : QuittingPunishmentFloorReachableState reward}
    (path : (quittingPunishmentFloorReachableChargedRelation reward).Path
      state state) :
    path.chargeSum = 0 := by
  have hnotPositive : ¬ 0 < path.chargeSum := by
    intro hpositive
    exact
      (quittingPunishmentFloorReachableChargedRelation reward).not_hasFiniteBudget_of_positive_cycle
        path hpositive regime.reachable_hasFiniteBudget
  exact le_antisymm (le_of_not_gt hnotPositive) path.chargeSum_nonneg

/-- The stored debt floor lies below the infimum of the attained min-max debts. -/
theorem debtFloor_le_iInf_minMaxDynamicDebt
    (regime : QuittingCounterexampleRegime reward) :
    regime.debtFloor ≤
      ⨅ cutoff : ℕ,
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  le_ciInf regime.debtFloor_le

/-- The optimized min-max exact dynamic-debt obstruction has positive
infimum. -/
theorem iInf_minMaxDynamicDebt_pos
    (regime : QuittingCounterexampleRegime reward) :
    0 < ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff :=
  regime.debtFloor_pos.trans_le regime.debtFloor_le_iInf_minMaxDynamicDebt

/-- The positive debt floor yields the projective exact-D obstruction: a
subsequential limiting tail with a positive debt owner and a summable opponent
clock. -/
theorem exists_positiveDynamicDebtTail
    (regime : QuittingCounterexampleRegime reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      0 < (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) :=
  exists_projective_positiveDynamicDebtTail_of_iInf_minMax_pos reward
    regime.iInf_minMaxDynamicDebt_pos

end QuittingCounterexampleRegime

/-! ## Exact characterization -/

/-- Canonical choice of the three quantitative margins forced by
nonexistence.  Choice is used only to expose numerical witnesses already
provided by the three proposition-level theorems. -/
noncomputable def quittingCounterexampleRegimeOfNoUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    QuittingCounterexampleRegime reward := by
  classical
  have terminalExists : ∃ gap : ℝ,
      0 < gap ∧ HasTerminalExploitabilityGap reward gap :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).1 hno
  let terminalGap := Classical.choose terminalExists
  have terminalSpec := Classical.choose_spec terminalExists
  let debtFloor := ⨅ cutoff : ℕ,
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff
  have debtFloor_nonneg : 0 ≤ debtFloor :=
    iInf_quittingFiniteMinMaxDynamicDebt_nonneg reward
  have debtFloor_ne_zero : debtFloor ≠ 0 := by
    intro hzero
    exact hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinMaxDynamicDebt_eq_zero
        reward hzero)
  have debtFloor_pos : 0 < debtFloor :=
    lt_of_le_of_ne debtFloor_nonneg (Ne.symm debtFloor_ne_zero)
  have debtFloor_le : ∀ cutoff : ℕ,
      debtFloor ≤
        quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff := by
    intro cutoff
    apply ciInf_le
    refine ⟨0, ?_⟩
    rintro debt ⟨index, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward index
  have prefixBoundExists : ∃ chargeBound : ℝ, 0 ≤ chargeBound ∧
      ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ chargeBound := by
    rcases quittingGame_uniformPayoff_or_bounded_floorPrefixCharge reward with
      hpayoff | hbound
    · exact (hno hpayoff).elim
    · exact hbound
  let prefixChargeBound := Classical.choose prefixBoundExists
  have prefixBoundSpec := Classical.choose_spec prefixBoundExists
  exact {
    terminalGap := terminalGap
    terminalGap_pos := terminalSpec.1
    terminalExploitability := terminalSpec.2
    debtFloor := debtFloor
    debtFloor_pos := debtFloor_pos
    debtFloor_le := debtFloor_le
    prefixChargeBound := prefixChargeBound
    prefixChargeBound_nonneg := prefixBoundSpec.1
    prefixCharge_le := prefixBoundSpec.2 }

/-- Every counterexample supplies a combined regime. -/
theorem nonempty_counterexampleRegime_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty (QuittingCounterexampleRegime reward) :=
  ⟨quittingCounterexampleRegimeOfNoUniformPayoff reward hno⟩

/-- **Combined counterexample normal form.**  Nonexistence of a
uniform-equilibrium payoff is equivalent to simultaneous terminal instability,
a positive optimized exact-D floor, and a finite common absorption budget for
all exact punishment-floor prefixes. -/
theorem not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      Nonempty (QuittingCounterexampleRegime reward) := by
  constructor
  · exact nonempty_counterexampleRegime_of_not_exists_uniformEquilibriumPayoff
      reward
  · rintro ⟨regime⟩
    exact regime.not_exists_uniformEquilibriumPayoff

end GameTheory
