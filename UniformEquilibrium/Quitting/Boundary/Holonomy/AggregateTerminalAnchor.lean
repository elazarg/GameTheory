/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Quitting.Root.SeparatedTerminalAnchor
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtOptimizer

/-!
# Aggregate-calibrated terminal anchors

The aggregate exact dynamic-debt objective is the quantity controlled by the
calibrated prepend-loss theorem.  This module records the corresponding
terminal packet without silently replacing its aggregate minimizer by the
different min--max minimizer used by `QuittingCalibratedTerminalAnchor`.

The stored path is an aggregate zero-boundary Nash--Bellman minimizer.  A
positive aggregate value supplies a positive owner coordinate; the separated
terminal-anchor theorem then supplies a terminal action with positive
preterminal opponent survival, positive terminal atom mass, a nonempty
quitter set, and positive terminal advantage.  The packet is the product of
the two probability factors, kept separate in the API.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An aggregate-calibrated finite terminal anchor.

The path and its aggregate provenance are retained explicitly.  The owner,
marked terminal action, and separated probability bounds are exactly the
fields needed by the subsequent packet and replacement arguments. -/
structure QuittingAggregateCalibratedTerminalAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  last : ℕ
  path : QuittingFiniteNashBellmanPath ι (last + 1)
  path_eq_minimizer :
    path = quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward (last + 1)
  path_mem : path ∈
    quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1)
  aggregateDebt_pos :
    0 < quittingFiniteNashBellmanPathAggregateDynamicDebt
      reward (last + 1) path
  owner : ι
  action : ι → Bool
  ownerDebt_pos :
    0 < quittingFiniteNashBellmanPathDynamicDebt
      reward (last + 1) path owner 0
  preterminalSurvival_pos :
    0 < quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots (last + 1) path)
      owner 0 last
  preterminalSurvival_le_one :
    quittingOpponentSurvivalWeight
      (quittingFiniteNashBellmanPathRoots (last + 1) path)
      owner 0 last ≤ 1
  terminalMass_pos :
    0 < ((pmfPi (Function.update
      (quittingFiniteNashBellmanPathRoots (last + 1) path last)
      owner (PMF.pure false))) action).toReal
  terminalMass_le_one :
    ((pmfPi (Function.update
      (quittingFiniteNashBellmanPathRoots (last + 1) path last)
      owner (PMF.pure false))) action).toReal ≤ 1
  owner_continues : action owner = false
  terminalQuitters_nonempty : (quittingQuitters action).Nonempty
  terminalAdvantage_pos :
    0 < quittingTerminalOpponentAdvantage reward owner action
  debt_le_weighted_packet :
    quittingFiniteNashBellmanPathDynamicDebt
        reward (last + 1) path owner 0 ≤
      (Fintype.card (ι → Bool) : ℝ) *
        (quittingOpponentSurvivalWeight
          (quittingFiniteNashBellmanPathRoots (last + 1) path)
          owner 0 last *
          ((pmfPi (Function.update
            (quittingFiniteNashBellmanPathRoots (last + 1) path last)
            owner (PMF.pure false))) action).toReal) *
        quittingTerminalOpponentAdvantage reward owner action

namespace QuittingAggregateCalibratedTerminalAnchor

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The product roots of the retained aggregate-selected path. -/
def roots (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    ℕ → ι → PMF Bool :=
  quittingFiniteNashBellmanPathRoots (anchor.last + 1) anchor.path

@[simp] theorem path_is_aggregate_minimizer
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.path = quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward (anchor.last + 1) :=
  anchor.path_eq_minimizer

theorem minAggregate_pos
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
      reward (anchor.last + 1) := by
  change 0 < quittingFiniteNashBellmanPathAggregateDynamicDebt
    reward (anchor.last + 1)
      (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
        reward (anchor.last + 1))
  rw [← anchor.path_eq_minimizer]
  exact anchor.aggregateDebt_pos

/-- Opponent survival strictly before the marked terminal root. -/
def preterminalSurvival
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) : ℝ :=
  quittingOpponentSurvivalWeight anchor.roots anchor.owner 0 anchor.last

/-- Mass of the marked complete action at the terminal root. -/
def terminalMass
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) : ℝ :=
  ((pmfPi (Function.update (anchor.roots anchor.last) anchor.owner
    (PMF.pure false))) anchor.action).toReal

/-- The separated terminal packet carried by the aggregate anchor. -/
def packetMass
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) : ℝ :=
  anchor.preterminalSurvival * anchor.terminalMass

@[simp] theorem preterminalSurvival_eq
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.preterminalSurvival =
      quittingOpponentSurvivalWeight
        (quittingFiniteNashBellmanPathRoots (anchor.last + 1) anchor.path)
        anchor.owner 0 anchor.last :=
  rfl

@[simp] theorem terminalMass_eq
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.terminalMass =
      ((pmfPi (Function.update
        (quittingFiniteNashBellmanPathRoots (anchor.last + 1) anchor.path
          anchor.last)
        anchor.owner (PMF.pure false))) anchor.action).toReal :=
  rfl

theorem preterminalSurvival_positive
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < anchor.preterminalSurvival :=
  anchor.preterminalSurvival_pos

theorem preterminalSurvival_upper_bound
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.preterminalSurvival ≤ 1 :=
  anchor.preterminalSurvival_le_one

theorem terminalMass_positive
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < anchor.terminalMass :=
  anchor.terminalMass_pos

theorem terminalMass_upper_bound
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.terminalMass ≤ 1 :=
  anchor.terminalMass_le_one

theorem packetMass_pos
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < anchor.packetMass := by
  exact mul_pos anchor.preterminalSurvival_pos anchor.terminalMass_pos

theorem packetMass_le_one
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    anchor.packetMass ≤ 1 := by
  calc
    anchor.preterminalSurvival * anchor.terminalMass ≤
        anchor.preterminalSurvival * 1 :=
      mul_le_mul_of_nonneg_left anchor.terminalMass_le_one
        (le_of_lt anchor.preterminalSurvival_pos)
    _ = anchor.preterminalSurvival := by ring
    _ ≤ 1 := anchor.preterminalSurvival_le_one

/-- Positive aggregate optimum yields an aggregate-calibrated anchor.

The owner is extracted from a positive coordinate of the aggregate sum, and
the separated terminal-anchor theorem is applied to the aggregate minimizer
itself. -/
theorem exists_of_minAggregate_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ)
    (hpositive :
      0 < quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (last + 1)) :
    Nonempty (QuittingAggregateCalibratedTerminalAnchor reward) := by
  let selected :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward (last + 1)
  have hselected : selected ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1) :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward (last + 1)
  have haggregate :
      0 < quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (last + 1) selected := by
    simpa [selected, quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt] using
      hpositive
  have hsum :
      0 < ∑ who,
        quittingFiniteNashBellmanPathDynamicDebt
          reward (last + 1) selected who 0 := by
    simpa [quittingFiniteNashBellmanPathAggregateDynamicDebt] using haggregate
  obtain ⟨owner, _howner, howner_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun who _ ↦ quittingFiniteNashBellmanPathDynamicDebt_nonneg
        reward (last + 1) selected hselected who 0)).mp hsum
  obtain ⟨action, hsurvival0, hsurvival1, hmass0, hmass1,
      hownerFalse, hquitters, hadvantage, hweighted, _, _⟩ :=
    exists_finiteDynamicDebt_separatedTerminalAnchor_quantitative
      reward last selected hselected owner howner_pos
  exact ⟨{
    last := last
    path := selected
    path_eq_minimizer := by rfl
    path_mem := hselected
    aggregateDebt_pos := haggregate
    owner := owner
    action := action
    ownerDebt_pos := howner_pos
    preterminalSurvival_pos := hsurvival0
    preterminalSurvival_le_one := hsurvival1
    terminalMass_pos := hmass0
    terminalMass_le_one := hmass1
    owner_continues := hownerFalse
    terminalQuitters_nonempty := hquitters
    terminalAdvantage_pos := hadvantage
    debt_le_weighted_packet := hweighted }⟩

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory
