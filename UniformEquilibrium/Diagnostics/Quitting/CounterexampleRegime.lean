/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargeCapacity

/-!
# A combined counterexample regime for finite quitting games

This module packages two unconditional restrictions on any finite quitting
game without a uniform-equilibrium payoff.

* Every behavioral profile has a unilateral terminal improvement bounded below
  by one common positive gap.
* The canonical extended-real capacity of all exact punishment-rational
  Nash--Bellman prefixes is finite; this is derived from the terminal gap and
  the finite-prefix closing theorem rather than stored independently.

The package is equivalent to nonexistence because the terminal gap already
implies nonexistence.  The real value of the derived capacity produces the
canonical bounded potential on the punishment-floor reachable predecessor
relation.

Optimized exact dynamic debt is deliberately absent from the structure.  It is
not a third independent assumption: terminal exploitability quantitatively
bounds every optimized exact-D value from below.  The resulting positive-debt
tail is derived in `CounterexampleRegimeQuantitative`.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A direct quantitative normal form for a finite quitting-game
counterexample.

The terminal margin is the only stored scalar.  Prefix-capacity finiteness and
its least real upper bound are theorems below, not additional fields. -/
structure QuittingCounterexampleRegime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  /-- Uniform positive terminal exploitability margin. -/
  terminalGap : ℝ
  terminalGap_pos : 0 < terminalGap
  terminalExploitability : HasTerminalExploitabilityGap reward terminalGap

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal-gap witness itself forces the player type to be inhabited. -/
private theorem nonemptyPlayers_of_terminalGap
    (regime : QuittingCounterexampleRegime reward) : Nonempty ι := by
  classical
  obtain ⟨who, _, _⟩ :=
    regime.terminalExploitability (quittingAlwaysContinueProfile reward)
  exact ⟨who⟩

/-- Finiteness of canonical prefix capacity is derivable from the stored
terminal gap.  An infinite capacity would supply arbitrarily charged exact
prefixes, hence a uniform-equilibrium payoff, contradicting the gap. -/
theorem prefixChargeCapacity_ne_top
    (regime : QuittingCounterexampleRegime reward) :
    quittingPunishmentFloorPrefixChargeCapacity reward ≠ ⊤ := by
  letI : Nonempty ι := regime.nonemptyPlayers_of_terminalGap
  have hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward regime.terminalGap_pos regime.terminalExploitability
  rcases quittingGame_uniformPayoff_or_bounded_floorPrefixCharge reward with
    hpayoff | ⟨bound, hbound0, hbound⟩
  · exact (hno hpayoff).elim
  · exact punishmentFloorPrefixChargeCapacity_ne_top_iff.mpr
      ⟨bound, hbound0, hbound⟩

/-- Every exact punishment-floor prefix is controlled by the canonical least
real charge bound. -/
theorem prefixCharge_le
    (regime : QuittingCounterexampleRegime reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    cert.charge ≤ quittingPunishmentFloorPrefixChargeBound reward :=
  punishmentFloorPrefixCharge_le_capacity_toReal
    regime.prefixChargeCapacity_ne_top cert

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

/-- The canonical finite-prefix bound controls every charged path starting at
the exact punishment-floor anchor. -/
theorem hasAnchoredChargeBound
    (regime : QuittingCounterexampleRegime reward) :
    HasQuittingPunishmentFloorAnchoredChargeBound reward
      (quittingPunishmentFloorPrefixChargeBound reward) :=
  hasAnchoredChargeBound_of_finitePrefixChargeBound regime.prefixCharge_le

/-- The full punishment-floor reachable predecessor relation has finite path
budget. -/
theorem reachable_hasFiniteBudget
    (regime : QuittingCounterexampleRegime reward) :
    (quittingPunishmentFloorReachableChargedRelation reward).HasFiniteBudget :=
  quittingPunishmentFloorReachable_hasFiniteBudget_of_anchoredChargeBound
    regime.hasAnchoredChargeBound

/-- The canonical charge capacity bounds every finite path inside the reachable
predecessor relation, regardless of its reachable source. -/
theorem reachablePath_chargeSum_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    {source target : QuittingPunishmentFloorReachableState reward}
    (path : (quittingPunishmentFloorReachableChargedRelation reward).Path
      source target) :
    path.chargeSum ≤ quittingPunishmentFloorPrefixChargeBound reward :=
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

/-- The canonical least prefix budget bounds the reachable potential
pointwise. -/
theorem canonicalPotential_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (state : QuittingPunishmentFloorReachableState reward) :
    quittingPunishmentFloorReachablePotential reward state ≤
      quittingPunishmentFloorPrefixChargeBound reward :=
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

end QuittingCounterexampleRegime

/-! ## Exact characterization -/

/-- Canonical construction of the regime forced by nonexistence.  Choice is
used only for the terminal margin; intrinsic prefix-capacity finiteness is
derived from that margin. -/
noncomputable def quittingCounterexampleRegimeOfNoUniformPayoff
    [Nonempty ι]
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
  exact {
    terminalGap := terminalGap
    terminalGap_pos := terminalSpec.1
    terminalExploitability := terminalSpec.2 }

/-- Every counterexample supplies a combined regime. -/
theorem nonempty_counterexampleRegime_of_not_exists_uniformEquilibriumPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty (QuittingCounterexampleRegime reward) :=
  ⟨quittingCounterexampleRegimeOfNoUniformPayoff reward hno⟩

/-- **Combined counterexample normal form.**  Nonexistence of a
uniform-equilibrium payoff is equivalent to simultaneous terminal instability
and finite canonical absorption capacity for all exact punishment-floor prefixes.
Positive optimized exact-D persistence is a theorem from the former, not an
additional field. -/
theorem not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      Nonempty (QuittingCounterexampleRegime reward) := by
  constructor
  · exact nonempty_counterexampleRegime_of_not_exists_uniformEquilibriumPayoff
      reward
  · rintro ⟨regime⟩
    exact regime.not_exists_uniformEquilibriumPayoff

/-- Quantifier-expanded form of the combined regime.  A counterexample is
exactly a positive terminal gap together with one finite bound valid for every
exact punishment-floor prefix.  This is the direct interface for search code
that does not need the bundled structure. -/
theorem not_exists_uniformEquilibriumPayoff_iff_exists_gap_and_chargeBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∃ (gap chargeBound : ℝ),
        0 < gap ∧
        HasTerminalExploitabilityGap reward gap ∧
        0 ≤ chargeBound ∧
        ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
          cert.charge ≤ chargeBound := by
  constructor
  · intro hno
    let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
    exact ⟨regime.terminalGap,
      quittingPunishmentFloorPrefixChargeBound reward,
      regime.terminalGap_pos, regime.terminalExploitability,
      quittingPunishmentFloorPrefixChargeBound_nonneg reward,
      regime.prefixCharge_le⟩
  · rintro ⟨gap, _chargeBound, hgap, hexploit, _hbound_nonneg, _hbound⟩
    exact ({
      terminalGap := gap
      terminalGap_pos := hgap
      terminalExploitability := hexploit } :
        QuittingCounterexampleRegime reward).not_exists_uniformEquilibriumPayoff

/-- Canonical quantifier-expanded form.  The charge condition is finiteness of
the intrinsic prefix capacity, rather than existence of a chosen upper-bound
witness. -/
theorem not_exists_uniformEquilibriumPayoff_iff_exists_gap_and_finiteChargeCapacity
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∃ gap : ℝ,
        0 < gap ∧
        HasTerminalExploitabilityGap reward gap ∧
        quittingPunishmentFloorPrefixChargeCapacity reward ≠ ⊤ := by
  constructor
  · intro hno
    let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
    exact ⟨regime.terminalGap, regime.terminalGap_pos,
      regime.terminalExploitability, regime.prefixChargeCapacity_ne_top⟩
  · rintro ⟨gap, hgap, hexploit, _hcapacity⟩
    exact ({
      terminalGap := gap
      terminalGap_pos := hgap
      terminalExploitability := hexploit } :
        QuittingCounterexampleRegime reward).not_exists_uniformEquilibriumPayoff

end GameTheory
