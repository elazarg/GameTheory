/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralResidualOccupation
import GameTheory.Concepts.Stochastic.PlayerNeutralStrictSetDeflation
import Math.Probability.AdaptiveTransitionAccount

/-!
# Accounts for residual player-neutral potential jets

After strict player-neutral deflation, a next analytic potential is certified
only on the residual transition family.  It need not have nonnegative drift
on the deleted columns, so it is generally false that it is harmonic or
subharmonic for the original full kernel family.

The deleted columns already have sublinear expected use.  This file uses that
fact instead of restoring a false full-family statement:

* the next leading potential has nonnegative drift on every residual column;
* its negative drift on the original family is supported entirely on the
  previously deleted strict set;
* this negative-drift cost is asymptotically sublinear under every
  source-compatible adaptive pure selector or predictable mixture; and
* pathwise, the selected centered transition scores are bounded by endpoint
  motion of the potential plus that exceptional cost.

This is the accounting invariant needed to iterate analytic deflation even
when a prescribed baseline column was deleted.
-/

set_option autoImplicit false

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

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- The state potential supplied by the first nonzero coefficient of a
residual analytic potential. -/
def ZeroDriftAnalyticPotentialJet.leadingPotential
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) :
    G.State → ℝ :=
  next.gaugeFixedJet.factor 0

/-- The next leading coefficient has nonnegative drift under every retained
residual transition. -/
theorem ZeroDriftAnalyticPotentialJet.residualDrift_nonneg
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (index : C.ZeroDriftIndex) :
    0 ≤
      expect (C.zeroDriftKernel index) next.leadingPotential -
        next.leadingPotential (C.zeroDriftSource index) := by
  have pairing_nonneg :=
    next.gaugeFixedJet.leading_pair_nonneg
      C.analytic_zeroDriftRawOccupationColumn
      C.analytic_zeroDriftRawOccupationCharge
      C.eventually_sum_zeroDriftRawOccupationColumn_eq_zero
      (C.zeroDrift_endpointNormalizedPositiveChargedCirculation
        circulation)
      index
  rw [C.zeroDriftRawOccupationColumn_zero] at pairing_nonneg
  rw [potential_pair_actualOccupationColumn] at pairing_nonneg
  exact pairing_nonneg

/-- Drift of the residual leading potential, evaluated on an index of the
original full player-neutral family. -/
def ZeroDriftAnalyticPotentialJet.fullDrift
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : germ.PlayerNeutralOccupationIndex who) : ℝ :=
  transitionPotentialDrift
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    next.leadingPotential index

/-- Negative part of the next potential's full-family drift. -/
def ZeroDriftAnalyticPotentialJet.negativeDriftCost
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : germ.PlayerNeutralOccupationIndex who) : ℝ :=
  min (next.fullDrift index) 0

/-- The negative drift cost vanishes outside the previously deflated strict
set. -/
theorem ZeroDriftAnalyticPotentialJet.negativeDriftCost_eq_zero_of_not_mem
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (index : germ.PlayerNeutralOccupationIndex who)
    (index_not_mem : index ∉ C.strictIndexSet) :
    next.negativeDriftCost index = 0 := by
  have drift_nonneg :=
    next.residualDrift_nonneg circulation
      (⟨index, index_not_mem⟩ : C.ZeroDriftIndex)
  change min (next.fullDrift index) 0 = 0
  rw [min_eq_right]
  simpa [ZeroDriftAnalyticPotentialJet.fullDrift,
    transitionPotentialDrift, zeroDriftKernel,
    zeroDriftSource] using drift_nonneg

/-- A finite bound for the negative drift cost on the original family. -/
def ZeroDriftAnalyticPotentialJet.negativeDriftBound
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor) : ℝ :=
  ∑ index, |next.negativeDriftCost index|

/-- Every coordinate is bounded by the finite total absolute negative
drift. -/
theorem ZeroDriftAnalyticPotentialJet.abs_negativeDriftCost_le_bound
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (index : germ.PlayerNeutralOccupationIndex who) :
    |next.negativeDriftCost index| ≤ next.negativeDriftBound := by
  exact Finset.single_le_sum
    (fun other _ => abs_nonneg (next.negativeDriftCost other))
    (Finset.mem_univ index)

/-- Under every source-compatible adaptive pure selector, the accumulated
negative drift of the next residual potential is sublinear in expected
absolute value. -/
theorem ZeroDriftAnalyticPotentialJet.negativeDriftCost_isSublinear
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison
                (germ.playerNeutralOccupationKernel who) choice))
            (T + 1))
          (fun history =>
            |selectedTransitionCostSum choice
              next.negativeDriftCost T history|)) := by
  letI := strictSetOccupationIndexDecidableEq germ who
  apply exceptionalTransitionCost_isAsymptoticallySublinear
    initial (germ.playerNeutralOccupationKernel who)
    choice next.negativeDriftCost C.strictIndexSet
    next.negativeDriftBound
  · intro index index_not_mem
    exact next.negativeDriftCost_eq_zero_of_not_mem
      circulation index index_not_mem
  · intro index _
    exact next.abs_negativeDriftCost_le_bound index
  · change IsAsymptoticallySublinear
      (C.strictSetExpectedUse initial choice)
    exact C.strictSetExpectedUse_isAsymptoticallySublinear
      initial choice source_compatible

/-- Pathwise account inequality for the next residual potential.  Its
selected centered scores are paid by endpoint account motion plus the
negative drift accumulated on previously deleted transitions. -/
theorem ZeroDriftAnalyticPotentialJet.centeredScore_le_account_add_negativeCost
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → G.State) :
    predictableScoreSum
        (adaptiveSelectedTransitionCenteredScore
          (germ.playerNeutralOccupationKernel who)
          next.leadingPotential choice)
        (T + 1) history ≤
      next.leadingPotential (history (Fin.last T)) -
          next.leadingPotential (history 0) +
        |selectedTransitionCostSum choice
          next.negativeDriftCost T history| := by
  apply selectedTransitionCenteredScore_le_accountIncrement_add_cost
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    next.leadingPotential choice source_compatible
    next.negativeDriftCost
  intro index
  exact min_le_left _ _

/-- Behavioral version of `negativeDriftCost_isSublinear`: predictable mixed
mass on the previously deleted strict set pays every negative drift of the
next residual potential. -/
theorem ZeroDriftAnalyticPotentialJet.negativeDriftCost_isSublinear_mixed
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n)) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (germ.playerNeutralOccupationKernel who) selection))
            (T + 1))
          (fun history =>
            |mixedTransitionCostSum
              selection next.negativeDriftCost T history|)) := by
  apply exceptionalMixedTransitionCost_isAsymptoticallySublinear
    initial (germ.playerNeutralOccupationKernel who)
    selection next.negativeDriftCost C.strictIndexSet
    next.negativeDriftBound
  · intro index index_not_mem
    exact next.negativeDriftCost_eq_zero_of_not_mem
      circulation index index_not_mem
  · intro index _
    exact next.abs_negativeDriftCost_le_bound index
  · change IsAsymptoticallySublinear
      (C.strictSetExpectedMass initial selection)
    exact C.strictSetExpectedMass_isAsymptoticallySublinear
      initial selection source_compatible

/-- Pathwise behavioral account inequality.  Scores are centered under the
complete mixed transition, while all negative residual drift is charged to
predictable mass on the previously deleted strict set. -/
theorem
    ZeroDriftAnalyticPotentialJet.mixedCenteredScore_le_account_add_negativeCost
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {nextAnchor : G.State}
    (next : C.ZeroDriftAnalyticPotentialJet nextAnchor)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n))
    (T : ℕ) (history : Fin (T + 1) → G.State) :
    predictableScoreSum
        (adaptiveMixedTransitionCenteredScore
          (germ.playerNeutralOccupationKernel who)
          next.leadingPotential selection)
        (T + 1) history ≤
      next.leadingPotential (history (Fin.last T)) -
          next.leadingPotential (history 0) +
        |mixedTransitionCostSum selection
          next.negativeDriftCost T history| := by
  apply mixedTransitionCenteredScore_le_accountIncrement_add_cost
    (germ.playerNeutralOccupationKernel who)
    (germ.playerNeutralOccupationSource who)
    next.leadingPotential selection source_compatible
    next.negativeDriftCost
  intro index
  exact min_le_left _ _

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
