/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralFiniteDeflationIteration
import Math.Probability.AnalyticFiniteOccupationDeflation

/-!
# A second strict deflation from a residual analytic potential

The first zero-drift restriction changes the analytic index type to a
dependent subtype.  This file transports the leading drift of the next
residual potential back to the fixed original occupation-index type through
the ambient active-set representation.

The resulting construction accepts a `ZeroDriftAnalyticPotentialJet`
directly.  Either every residual leading drift is zero, or all strictly
positive residual drifts are deleted in one second ambient step.  In the
second branch:

* the active-set cardinal rank decreases strictly;
* the new exceptional set is the union of the first and second strict sets;
* every missing full-family constraint lies in the accumulated exceptional
  set, where an independent transition-account theorem can charge it.

Thus there is no remaining dependent-type obstruction to the second finite
deletion.  Iterating the analytic construction beyond this step still
requires restricting the moving analytic column and charge germs to an
arbitrary ambient active finset, rather than only to the first
`ZeroDriftIndex`.

No public strategy or recurrent-child assertion is made here.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

local instance residualStrictDeflationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}

/-- Leading state potential of the next residual analytic jet. -/
def ZeroDriftAnalyticPotentialJet.ambientLeadingPotential
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    G.State → ℝ :=
  next.gaugeFixedJet.factor 0

/-- Drift of the residual leading potential on an arbitrary index of the
original full ambient family. -/
def ZeroDriftAnalyticPotentialJet.ambientDrift
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : germ.PlayerNeutralOccupationIndex who) : ℝ :=
  expect
      (germ.playerNeutralOccupationKernel who index)
      next.ambientLeadingPotential -
    next.ambientLeadingPotential
      (germ.playerNeutralOccupationSource who index)

/-- Drift of the next residual leading potential, transported to the active
subtype of the fixed original ambient occupation-index type. -/
def ZeroDriftAnalyticPotentialJet.residualActiveDrift
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : C.zeroDriftDeflationState.ActiveIndex) : ℝ :=
  next.ambientDrift index.1

/-- The transported next drift is nonnegative on every currently active
ambient index. -/
theorem ZeroDriftAnalyticPotentialJet.residualActiveDrift_nonneg
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (index : C.zeroDriftDeflationState.ActiveIndex) :
    0 ≤ next.residualActiveDrift index := by
  let residualIndex : C.ZeroDriftIndex :=
    C.zeroDriftIndexEquivActive.symm index
  have drift_nonneg :=
    next.gaugeFixedJet.leading_pair_nonneg
      C.analytic_zeroDriftRawOccupationColumn
      C.analytic_zeroDriftRawOccupationCharge
      C.eventually_sum_zeroDriftRawOccupationColumn_eq_zero
      (C.zeroDrift_endpointNormalizedPositiveChargedCirculation
        circulation)
      residualIndex
  rw [C.zeroDriftRawOccupationColumn_zero] at drift_nonneg
  rw [potential_pair_actualOccupationColumn] at drift_nonneg
  simpa [ZeroDriftAnalyticPotentialJet.residualActiveDrift,
    ZeroDriftAnalyticPotentialJet.ambientDrift,
    ZeroDriftAnalyticPotentialJet.ambientLeadingPotential,
    zeroDriftKernel, zeroDriftSource,
    residualIndex, zeroDriftIndexEquivActive] using drift_nonneg

/-- Negative part of the residual potential's drift on the original full
ambient family. -/
def ZeroDriftAnalyticPotentialJet.negativeAmbientDriftCost
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : germ.PlayerNeutralOccupationIndex who) : ℝ :=
  min (next.ambientDrift index) 0

/-- Every missing drift constraint of the residual potential is supported
on the already accumulated exceptional set.  This is the ambient extension
statement needed by transition-account arguments. -/
theorem
    ZeroDriftAnalyticPotentialJet.negativeAmbientDriftCost_exceptional
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    C.zeroDriftDeflationState.SupportsExceptional
      next.negativeAmbientDriftCost := by
  intro index index_active
  let activeIndex : C.zeroDriftDeflationState.ActiveIndex :=
    ⟨index, index_active⟩
  have drift_nonneg :=
    next.residualActiveDrift_nonneg circulation activeIndex
  change min (next.ambientDrift index) 0 = 0
  rw [min_eq_right]
  simpa [ZeroDriftAnalyticPotentialJet.residualActiveDrift,
    activeIndex] using drift_nonneg

/-- Delete every currently active ambient index on which the next residual
leading potential has strictly positive drift. -/
def ZeroDriftAnalyticPotentialJet.secondDeflationState
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who) :=
  C.zeroDriftDeflationState.deleteStrict
    next.residualActiveDrift

/-- The ambient indices deleted by the second strict step. -/
def ZeroDriftAnalyticPotentialJet.secondStrictAmbientSet
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    Finset (germ.PlayerNeutralOccupationIndex who) :=
  C.zeroDriftDeflationState.strictAmbientSet
    next.residualActiveDrift

/-- The next residual jet gives the exact second-step alternative: either
all retained drifts vanish, or its positive-drift set is a genuine ambient
deflation. -/
theorem
    ZeroDriftAnalyticPotentialJet.residualDrifts_zero_or_secondDeflates
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    (∀ index : C.zeroDriftDeflationState.ActiveIndex,
        next.residualActiveDrift index = 0) ∨
      next.secondDeflationState.Deflates
        C.zeroDriftDeflationState := by
  exact
    C.zeroDriftDeflationState.all_score_zero_or_deleteStrict_deflates
      next.residualActiveDrift
      (next.residualActiveDrift_nonneg circulation)

/-- A strict residual drift witness produces a second strict ambient
active-set rank decrease. -/
theorem ZeroDriftAnalyticPotentialJet.secondDeflationState_rank_lt
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (strict :
      ∃ index : C.zeroDriftDeflationState.ActiveIndex,
        0 < next.residualActiveDrift index) :
    next.secondDeflationState.rank <
      C.zeroDriftDeflationState.rank := by
  exact C.zeroDriftDeflationState.rank_deleteStrict_lt
    next.residualActiveDrift strict

/-- The exceptional set after the second strict deletion is the first strict
set together with the second strict ambient set. -/
theorem
    ZeroDriftAnalyticPotentialJet.secondDeflationState_exceptional
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    next.secondDeflationState.exceptional =
      C.strictIndexSet ∪ next.secondStrictAmbientSet := by
  rw [show next.secondDeflationState.exceptional =
      C.zeroDriftDeflationState.exceptional ∪
        C.zeroDriftDeflationState.strictAmbientSet
          next.residualActiveDrift by
    exact C.zeroDriftDeflationState.exceptional_deleteStrict_eq
      next.residualActiveDrift]
  rw [C.zeroDriftDeflationState_exceptional]
  rfl

/-- The second strict ambient set is disjoint from the first strict set. -/
theorem ZeroDriftAnalyticPotentialJet.secondStrictAmbientSet_disjoint
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    Disjoint C.strictIndexSet next.secondStrictAmbientSet := by
  rw [Finset.disjoint_left]
  intro index index_first index_second
  have second_active :
      index ∈ C.zeroDriftDeflationState.active :=
    C.zeroDriftDeflationState.strictAmbientSet_subset_active
      next.residualActiveDrift index_second
  exact
    ((C.mem_zeroDriftDeflationState_active_iff index).mp
      second_active) index_first

/-- The second strict step is therefore another honest deletion from the
original ambient finite family, not merely a decrease in a nested subtype. -/
theorem ZeroDriftAnalyticPotentialJet.secondDeflates_of_strict
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (strict :
      ∃ index : C.zeroDriftDeflationState.ActiveIndex,
        0 < next.residualActiveDrift index) :
    next.secondDeflationState.Deflates
      C.zeroDriftDeflationState :=
  C.zeroDriftDeflationState.deleteStrict_deflates
    next.residualActiveDrift strict

/-- The first residual endpoint circulation, reindexed on the fixed ambient
active subtype. -/
theorem zeroDriftDeflationState_hasEndpointCirculation
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn C.zeroDriftDeflationState
        (germ.rawPlayerNeutralOccupationColumn who) 0)
      (activeOccupationCharge C.zeroDriftDeflationState
        (germ.rawPlayerNeutralOccupationCharge B who) 0) := by
  have zeroDriftCirculation :=
    C.zeroDrift_endpointNormalizedPositiveChargedCirculation
      circulation
  let equiv :
      C.zeroDriftDeflationState.ActiveIndex ≃
        C.ZeroDriftIndex :=
    C.zeroDriftIndexEquivActive.symm
  have reindexed :=
    HasNormalizedPositiveChargedCirculation.reindex
      (C.zeroDriftRawOccupationColumn 0)
      (C.zeroDriftRawOccupationCharge 0)
      zeroDriftCirculation equiv
  have equiv_value
      (index : C.zeroDriftDeflationState.ActiveIndex) :
      (equiv index).1 = index.1 := by
    rfl
  have column_eq :
      (fun index =>
        C.zeroDriftRawOccupationColumn 0 (equiv index)) =
        activeOccupationColumn C.zeroDriftDeflationState
          (germ.rawPlayerNeutralOccupationColumn who) 0 := by
    funext index destination
    change
      germ.rawPlayerNeutralOccupationColumn who 0
          (equiv index).1 destination =
        germ.rawPlayerNeutralOccupationColumn who 0
          index.1 destination
    rw [equiv_value]
  have charge_eq :
      (fun index =>
        C.zeroDriftRawOccupationCharge 0 (equiv index)) =
        activeOccupationCharge C.zeroDriftDeflationState
          (germ.rawPlayerNeutralOccupationCharge B who) 0 := by
    funext index
    change
      germ.rawPlayerNeutralOccupationCharge B who 0
          (equiv index).1 =
        germ.rawPlayerNeutralOccupationCharge B who 0 index.1
    rw [equiv_value]
  rw [column_eq, charge_eq] at reindexed
  exact reindexed

/-- The transported residual drift is exactly the generic leading endpoint
pairing of the ambient moving occupation column. -/
theorem
    ZeroDriftAnalyticPotentialJet.residualActiveDrift_eq_leadingPairing
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : C.zeroDriftDeflationState.ActiveIndex) :
    next.residualActiveDrift index =
      ∑ destination,
        next.gaugeFixedJet.factor 0 destination *
          germ.rawPlayerNeutralOccupationColumn
            who 0 index.1 destination := by
  change
    expect
        (germ.playerNeutralOccupationKernel who index.1)
        (next.gaugeFixedJet.factor 0) -
      next.gaugeFixedJet.factor 0
        (germ.playerNeutralOccupationSource who index.1) =
      ∑ destination,
        next.gaugeFixedJet.factor 0 destination *
          germ.rawPlayerNeutralOccupationColumn
            who 0 index.1 destination
  rw [germ.rawPlayerNeutralOccupationColumn_zero who]
  rw [potential_pair_actualOccupationColumn]

/-- Complementarity transports the normalized endpoint circulation through
the second strict ambient deletion. -/
theorem
    ZeroDriftAnalyticPotentialJet.secondDeflationState_hasEndpointCirculation
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn next.secondDeflationState
        (germ.rawPlayerNeutralOccupationColumn who) 0)
      (activeOccupationCharge next.secondDeflationState
        (germ.rawPlayerNeutralOccupationCharge B who) 0) := by
  have zeroDriftCirculation :=
    C.zeroDrift_endpointNormalizedPositiveChargedCirculation
      circulation
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one, complementary⟩ :=
    next.gaugeFixedJet.exists_leading_complementary_mass
      C.analytic_zeroDriftRawOccupationColumn
      C.analytic_zeroDriftRawOccupationCharge
      C.eventually_sum_zeroDriftRawOccupationColumn_eq_zero
      zeroDriftCirculation
  let equiv : C.ZeroDriftIndex ≃
      C.zeroDriftDeflationState.ActiveIndex :=
    C.zeroDriftIndexEquivActive
  have equiv_symm_value
      (index : C.zeroDriftDeflationState.ActiveIndex) :
      (equiv.symm index).1 = index.1 := by
    rfl
  let ambientMass :
      C.zeroDriftDeflationState.ActiveIndex → ℝ :=
    fun index => mass (equiv.symm index)
  have ambientMass_nonneg :
      ∀ index, 0 ≤ ambientMass index := by
    intro index
    exact mass_nonneg (equiv.symm index)
  have ambientBalance :
      ∀ destination,
        ∑ index,
          ambientMass index *
            germ.rawPlayerNeutralOccupationColumn
              who 0 index.1 destination = 0 := by
    intro destination
    have reindexed :=
      equiv.symm.sum_comp
        (fun index : C.ZeroDriftIndex =>
          mass index *
            C.zeroDriftRawOccupationColumn
              0 index destination)
    rw [balance destination] at reindexed
    simpa only [ambientMass, zeroDriftRawOccupationColumn,
      equiv_symm_value] using reindexed
  have ambientCharge :
      (∑ index,
        ambientMass index *
          germ.rawPlayerNeutralOccupationCharge
            B who 0 index.1) = 1 := by
    have reindexed :=
      equiv.symm.sum_comp
        (fun index : C.ZeroDriftIndex =>
          mass index *
            C.zeroDriftRawOccupationCharge 0 index)
    rw [charge_eq_one] at reindexed
    simpa only [ambientMass, zeroDriftRawOccupationCharge,
      equiv_symm_value] using reindexed
  have ambientComplementary :
      ∀ index, 0 < ambientMass index →
        next.residualActiveDrift index = 0 := by
    intro index mass_pos
    have pairing_zero :=
      complementary (equiv.symm index) mass_pos
    rw [next.residualActiveDrift_eq_leadingPairing]
    simpa only [zeroDriftRawOccupationColumn,
      equiv_symm_value] using pairing_zero
  change
    HasNormalizedPositiveChargedCirculation
      (fun index : next.secondDeflationState.ActiveIndex =>
        germ.rawPlayerNeutralOccupationColumn
          who 0 index.1)
      (fun index : next.secondDeflationState.ActiveIndex =>
        germ.rawPlayerNeutralOccupationCharge
          B who 0 index.1)
  exact deleteStrict_hasNormalizedPositiveChargedCirculation
    C.zeroDriftDeflationState
    (germ.rawPlayerNeutralOccupationColumn who 0)
    (germ.rawPlayerNeutralOccupationCharge B who 0)
    next.residualActiveDrift ambientMass
    ambientMass_nonneg ambientBalance ambientCharge
    ambientComplementary

/-- The analytic charged-flow alternative can now be rerun at the second
ambient active-set node, with the endpoint circulation invariant preserved. -/
theorem
    ZeroDriftAnalyticPotentialJet.secondDeflationState_analyticAlternative
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (thirdAnchor : G.State) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (activeOccupationColumn next.secondDeflationState
            (germ.rawPlayerNeutralOccupationColumn who))
          (activeOccupationCharge next.secondDeflationState
            (germ.rawPlayerNeutralOccupationCharge B who))))
      (Nonempty
        (ActiveAnalyticPotentialJet next.secondDeflationState
          (germ.rawPlayerNeutralOccupationColumn who)
          (germ.rawPlayerNeutralOccupationCharge B who)
          thirdAnchor)) := by
  exact activePositiveChargedCirculation_xor_nextPotentialJet
    next.secondDeflationState
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
    (germ.analytic_rawPlayerNeutralOccupationColumn who)
    (germ.analytic_rawPlayerNeutralOccupationCharge B who)
    (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
    (next.secondDeflationState_hasEndpointCirculation circulation)
    thirdAnchor

/-- Starting from the second residual node, the generic proper-subset
recursion terminates after finitely many further analytic deflations in
either an analytic circulation or an all-zero leading-pairing jet. -/
theorem
    ZeroDriftAnalyticPotentialJet.exists_secondDeflationTerminalOutcome
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (terminalAnchor : G.State) :
    Nonempty
      (AnalyticOccupationDeflationOutcome
        next.secondDeflationState
        (germ.rawPlayerNeutralOccupationColumn who)
        (germ.rawPlayerNeutralOccupationCharge B who)
        terminalAnchor) := by
  exact exists_analyticOccupationDeflationOutcome
    next.secondDeflationState
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
    (germ.analytic_rawPlayerNeutralOccupationColumn who)
    (germ.analytic_rawPlayerNeutralOccupationCharge B who)
    (germ.eventually_sum_rawPlayerNeutralOccupationColumn_eq_zero who)
    (next.secondDeflationState_hasEndpointCirculation circulation)
    terminalAnchor

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
