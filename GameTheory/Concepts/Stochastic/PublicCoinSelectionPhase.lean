/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.DeviationSafePublicCoinSelection

/-!
# Potential and charge accounting for a finite public-coin phase

A deviation-safe public coin fixes the terminal-child law independently of
play.  This file turns that law into the three potential inequalities needed
during the finite selection prefix.

The potential at a public state is the expected target of the eventual child.
It is exactly harmonic under prescribed play and every unilateral deviation.
The stage charge is the absolute gap between this continuation target and the
current expected payoff, cut off when the selection fuel is exhausted.  Its
total expected mass is at most
`fuel * (payoffBound + targetBound)`.

This is only the finite selection prefix.  No child certificate is extended
after the stopping history here; suffix rebasing and the child charge remain
separate splice fields.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace DeviationSafePublicCoinSelector

open Math Math.Probability Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- Expected terminal-child target, viewed as a potential on public states. -/
def terminalTargetPotential
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ) (who : ι) :
    G.State → ℝ :=
  fun state =>
    expect (selector.process.value state)
      (fun child => terminalTarget child who)

/-- The terminal-target potential read from the current state of a history. -/
def terminalTargetHistoryPotential
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ) (who : ι) :
    G.HistoryPotential :=
  fun _ history =>
    selector.terminalTargetPotential terminalTarget who history.2

/-- During the finite selection prefix, charge the absolute difference
between the current expected payoff and the terminal-target potential. -/
def selectionStageCharge
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι) (fuel : ℕ) :
    G.HistoryPotential :=
  fun stage history =>
    if stage < fuel then
      |G.stageEUAt profile history who -
        selector.terminalTargetPotential terminalTarget who history.2|
    else
      0

/-- One stopped public step preserves the expected terminal target. -/
theorem expect_stoppedStep_terminalTargetPotential
    [Finite Child]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ) (who : ι) (state : G.State) :
    expect (selector.process.stoppedStep state)
        (selector.terminalTargetPotential terminalTarget who) =
      selector.terminalTargetPotential terminalTarget who state := by
  unfold terminalTargetPotential
  rw [← expect_bind, selector.process.stoppedStep_bind_value]

/-- The terminal-target history potential has its semantic initial value. -/
@[simp] theorem terminalTargetHistoryPotential_zero
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ) (who : ι)
    (initial : G.State) :
    selector.terminalTargetHistoryPotential terminalTarget who
        0 (G.emptyHist initial) =
      expect (selector.process.value initial)
        (fun child => terminalTarget child who) :=
  rfl

/-- At a terminal selector state, the potential is the observed child's
target. -/
theorem terminalTargetPotential_eq_of_terminal
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ) (who : ι)
    (state : G.State) (hterminal : selector.process.terminal state) :
    selector.terminalTargetPotential terminalTarget who state =
      terminalTarget (selector.process.observe state) who := by
  unfold terminalTargetPotential
  rw [selector.process.terminal_value state hterminal, expect_pure]

/-- The expected terminal target is an exact one-step continuation under
every behavior profile. -/
theorem historyContinuationEU_terminalTargetHistoryPotential_eq
    [Finite Child] [Fintype ι] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage) :
    G.historyContinuationEU profile
        (selector.terminalTargetHistoryPotential terminalTarget who)
        history =
      selector.terminalTargetPotential terminalTarget who history.2 := by
  unfold historyContinuationEU terminalTargetHistoryPotential
  calc
    expect (G.stageActionDist profile history)
        (fun action =>
          expect (G.transition history.2 action)
            (selector.terminalTargetPotential terminalTarget who)) =
      expect (G.stageActionDist profile history)
        (fun _ =>
          expect (selector.process.stoppedStep history.2)
            (selector.terminalTargetPotential terminalTarget who)) := by
          apply congrArg (expect (G.stageActionDist profile history))
          funext action
          rw [selector.transition_eq_stoppedStep history.2 action]
    _ =
      expect (selector.process.stoppedStep history.2)
        (selector.terminalTargetPotential terminalTarget who) :=
      expect_const _ _
    _ = selector.terminalTargetPotential terminalTarget who history.2 :=
      selector.expect_stoppedStep_terminalTargetPotential
        terminalTarget who history.2

/-- On a supported terminal history, the history potential is exactly the
selected child's target. -/
theorem terminalTargetHistoryPotential_eq_of_mem_support
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel)
    (who : ι) (history : G.Hist fuel)
    (hhistory : history ∈ (G.histDist profile initial fuel).support) :
    selector.terminalTargetHistoryPotential terminalTarget who
        fuel history =
      terminalTarget (selector.process.observe history.2) who := by
  apply selector.terminalTargetPotential_eq_of_terminal
  exact selector.terminal_of_mem_support_histDist
    profile initial fuel hfuel history hhistory

/-- Before the cutoff, the common absolute charge proves the lower stage
inequality. -/
theorem terminalTargetPotential_le_stageEUAt_add_selectionStageCharge
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι) (fuel : ℕ)
    {stage : ℕ} (history : G.Hist stage) (hstage : stage < fuel) :
    selector.terminalTargetPotential terminalTarget who history.2 ≤
      G.stageEUAt profile history who +
        selector.selectionStageCharge terminalTarget
          profile who fuel stage history := by
  rw [selectionStageCharge]
  simp only [if_pos hstage]
  linarith [neg_le_abs
    (G.stageEUAt profile history who -
      selector.terminalTargetPotential terminalTarget who history.2)]

/-- Before the cutoff, the same charge proves the upper stage inequality. -/
theorem stageEUAt_le_terminalTargetPotential_add_selectionStageCharge
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι) (fuel : ℕ)
    {stage : ℕ} (history : G.Hist stage) (hstage : stage < fuel) :
    G.stageEUAt profile history who ≤
      selector.terminalTargetPotential terminalTarget who history.2 +
        selector.selectionStageCharge terminalTarget
          profile who fuel stage history := by
  rw [selectionStageCharge]
  simp only [if_pos hstage]
  linarith [le_abs_self
    (G.stageEUAt profile history who -
      selector.terminalTargetPotential terminalTarget who history.2)]

/-- The selection charge vanishes after the fixed public-coin prefix. -/
theorem selectionStageCharge_eq_zero_of_fuel_le
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι) (fuel : ℕ)
    {stage : ℕ} (hstage : fuel ≤ stage) :
    selector.selectionStageCharge terminalTarget
        profile who fuel stage = 0 := by
  funext history
  simp [selectionStageCharge, Nat.not_lt.mpr hstage]

/-- A uniform target bound controls the terminal-target potential. -/
theorem abs_terminalTargetPotential_le
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    {targetBound : ℝ}
    (htarget : ∀ child who, |terminalTarget child who| ≤ targetBound)
    (who : ι) (state : G.State) :
    |selector.terminalTargetPotential terminalTarget who state| ≤
      targetBound := by
  unfold terminalTargetPotential
  exact abs_expect_le_of_abs_le _ _
    (fun child => htarget child who)

/-- A uniform payoff bound controls every mixed stage expectation. -/
theorem abs_stageEUAt_le
    [Fintype ι]
    (profile : G.BehaviorProfile) {payoffBound : ℝ}
    (hpayoff :
      ∀ state action who,
        |G.stagePayoff state action who| ≤ payoffBound)
    {stage : ℕ} (history : G.Hist stage) (who : ι) :
    |G.stageEUAt profile history who| ≤ payoffBound := by
  unfold stageEUAt
  exact abs_expect_le_of_abs_le _ _
    (fun action => hpayoff history.2 action who)

/-- Every active selection-stage charge is bounded by the payoff bound plus
the terminal-target bound. -/
theorem selectionStageCharge_le
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (who : ι) (fuel : ℕ)
    {payoffBound targetBound : ℝ}
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound)
    {stage : ℕ} (history : G.Hist stage) :
    selector.selectionStageCharge terminalTarget
        profile who fuel stage history ≤
      payoffBound + targetBound := by
  unfold selectionStageCharge
  split_ifs
  · calc
      |G.stageEUAt profile history who -
          selector.terminalTargetPotential
            terminalTarget who history.2| ≤
        |G.stageEUAt profile history who| +
          |selector.terminalTargetPotential
            terminalTarget who history.2| :=
        abs_sub _ _
      _ ≤ payoffBound + targetBound :=
        add_le_add
          (abs_stageEUAt_le profile hpayoff history who)
          (selector.abs_terminalTargetPotential_le
            terminalTarget htarget who history.2)
  · exact add_nonneg hpayoffNonneg htargetNonneg

/-- The expected charge at any prefix stage is bounded by the same constant. -/
theorem expectedHistoryValue_selectionStageCharge_le
    [Fintype ι] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) (fuel : ℕ) {payoffBound targetBound : ℝ}
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound)
    (stage : ℕ) :
    G.expectedHistoryValue profile initial
        (selector.selectionStageCharge terminalTarget
          profile who fuel) stage ≤
      payoffBound + targetBound := by
  unfold expectedHistoryValue
  simpa only [expect_const] using
    expect_mono (G.histDist profile initial stage) _ _
      (selector.selectionStageCharge_le
        terminalTarget profile who fuel hpayoff htarget
        hpayoffNonneg htargetNonneg)

/-- The total expected charge of the selection prefix is bounded independently
of the later horizon. -/
theorem sum_expectedHistoryValue_selectionStageCharge_le
    [Fintype ι] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) (fuel : ℕ) {payoffBound targetBound : ℝ}
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound)
    (horizon : ℕ) (hfuel : fuel ≤ horizon) :
    ∑ stage ∈ Finset.range horizon,
        G.expectedHistoryValue profile initial
          (selector.selectionStageCharge terminalTarget
            profile who fuel) stage ≤
      (fuel : ℝ) * (payoffBound + targetBound) := by
  rw [← Finset.sum_range_add_sum_Ico _ hfuel]
  have hprefix :
      ∑ stage ∈ Finset.range fuel,
          G.expectedHistoryValue profile initial
            (selector.selectionStageCharge terminalTarget
              profile who fuel) stage ≤
        (fuel : ℝ) * (payoffBound + targetBound) := by
    calc
      ∑ stage ∈ Finset.range fuel,
          G.expectedHistoryValue profile initial
            (selector.selectionStageCharge terminalTarget
              profile who fuel) stage ≤
        ∑ _stage ∈ Finset.range fuel,
          (payoffBound + targetBound) := by
            apply Finset.sum_le_sum
            intro stage _
            exact
              selector.expectedHistoryValue_selectionStageCharge_le
                terminalTarget profile initial who fuel
                hpayoff htarget hpayoffNonneg htargetNonneg stage
      _ = (fuel : ℝ) * (payoffBound + targetBound) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail :
      ∑ stage ∈ Finset.Ico fuel horizon,
          G.expectedHistoryValue profile initial
            (selector.selectionStageCharge terminalTarget
              profile who fuel) stage = 0 := by
    apply Finset.sum_eq_zero
    intro stage hstage
    have hzero :=
      selector.selectionStageCharge_eq_zero_of_fuel_le
        terminalTarget profile who fuel (Finset.mem_Ico.mp hstage).1
    unfold expectedHistoryValue
    rw [hzero]
    exact expect_const _ 0
  rw [htail, add_zero]
  exact hprefix

/-- The complete lower, upper, and unilateral-deviation accounting supplied
by a finite deviation-safe public-coin prefix.

All potentials and charges are full-history objects so that a later theorem
can splice them to child suffix certificates.  Their obligations stop at
`fuel`; this structure intentionally contains no statement about play after
the selected child has been observed. -/
structure SelectionPhaseSystemAt
    [Fintype ι] [DecidableEq ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (parentTarget : ι → ℝ) (error : ℝ) (fuel : ℕ)
    (payoffBound targetBound : ℝ) where
  lowerPotential : ι → G.HistoryPotential
  upperPotential : ι → G.HistoryPotential
  deviationPotential : ι → G.HistoryPotential
  lowerCharge : ι → G.HistoryPotential
  upperCharge : ι → G.HistoryPotential
  deviationCharge :
    ∀ who, G.BehaviorStrategy who → G.HistoryPotential
  fuel_covers_rank : selector.process.rank initial ≤ fuel
  lower_initial : ∀ who,
    |lowerPotential who 0 (G.emptyHist initial) - parentTarget who| ≤
      error
  upper_initial : ∀ who,
    |upperPotential who 0 (G.emptyHist initial) - parentTarget who| ≤
      error
  deviation_initial : ∀ who,
    |deviationPotential who 0 (G.emptyHist initial) -
        parentTarget who| ≤
      error
  lower_subharmonic : ∀ who (stage : ℕ) (history : G.Hist stage),
    lowerPotential who stage history ≤
      G.historyContinuationEU profile (lowerPotential who) history
  upper_superharmonic : ∀ who (stage : ℕ) (history : G.Hist stage),
    G.historyContinuationEU profile (upperPotential who) history ≤
      upperPotential who stage history
  deviation_superharmonic :
    ∀ who (deviation : G.BehaviorStrategy who)
      (stage : ℕ) (history : G.Hist stage),
      G.historyContinuationEU
          (Function.update profile who deviation)
          (deviationPotential who) history ≤
        deviationPotential who stage history
  lower_stage : ∀ who (stage : ℕ) (history : G.Hist stage),
    stage < fuel →
      lowerPotential who stage history ≤
        G.stageEUAt profile history who +
          lowerCharge who stage history
  upper_stage : ∀ who (stage : ℕ) (history : G.Hist stage),
    stage < fuel →
      G.stageEUAt profile history who ≤
        upperPotential who stage history +
          upperCharge who stage history
  deviation_stage :
    ∀ who (deviation : G.BehaviorStrategy who)
      (stage : ℕ) (history : G.Hist stage),
      stage < fuel →
        G.stageEUAt (Function.update profile who deviation) history who ≤
          deviationPotential who stage history +
            deviationCharge who deviation stage history
  lower_terminal_value :
    ∀ (phaseProfile : G.BehaviorProfile) who
      (history : G.Hist fuel),
      history ∈ (G.histDist phaseProfile initial fuel).support →
        lowerPotential who fuel history =
          terminalTarget (selector.process.observe history.2) who
  upper_terminal_value :
    ∀ (phaseProfile : G.BehaviorProfile) who
      (history : G.Hist fuel),
      history ∈ (G.histDist phaseProfile initial fuel).support →
        upperPotential who fuel history =
          terminalTarget (selector.process.observe history.2) who
  deviation_terminal_value :
    ∀ (phaseProfile : G.BehaviorProfile) who
      (history : G.Hist fuel),
      history ∈ (G.histDist phaseProfile initial fuel).support →
        deviationPotential who fuel history =
          terminalTarget (selector.process.observe history.2) who
  lower_charge_sum : ∀ who horizon, fuel ≤ horizon →
    ∑ stage ∈ Finset.range horizon,
        G.expectedHistoryValue profile initial
          (lowerCharge who) stage ≤
      (fuel : ℝ) * (payoffBound + targetBound)
  upper_charge_sum : ∀ who horizon, fuel ≤ horizon →
    ∑ stage ∈ Finset.range horizon,
        G.expectedHistoryValue profile initial
          (upperCharge who) stage ≤
      (fuel : ℝ) * (payoffBound + targetBound)
  deviation_charge_sum :
    ∀ who (deviation : G.BehaviorStrategy who) horizon,
      fuel ≤ horizon →
        ∑ stage ∈ Finset.range horizon,
            G.expectedHistoryValue
              (Function.update profile who deviation) initial
              (deviationCharge who deviation) stage ≤
          (fuel : ℝ) * (payoffBound + targetBound)

/-- A deviation-safe selector canonically supplies the complete finite-prefix
selection system.  The only numerical input is a bound on stage payoffs and
terminal child targets. -/
def toSelectionPhaseSystemAt
    [Fintype ι] [DecidableEq ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (parentTarget : ι → ℝ) (error : ℝ) (fuel : ℕ)
    (payoffBound targetBound : ℝ)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hparent :
      ∀ who,
        |expect (selector.process.value initial)
            (fun child => terminalTarget child who) -
          parentTarget who| ≤ error)
    (hpayoff :
      ∀ state action who,
        |G.stagePayoff state action who| ≤ payoffBound)
    (htarget :
      ∀ child who, |terminalTarget child who| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound) :
    SelectionPhaseSystemAt selector terminalTarget profile initial
      parentTarget error fuel payoffBound targetBound where
  lowerPotential :=
    selector.terminalTargetHistoryPotential terminalTarget
  upperPotential :=
    selector.terminalTargetHistoryPotential terminalTarget
  deviationPotential :=
    selector.terminalTargetHistoryPotential terminalTarget
  lowerCharge := fun who =>
    selector.selectionStageCharge terminalTarget profile who fuel
  upperCharge := fun who =>
    selector.selectionStageCharge terminalTarget profile who fuel
  deviationCharge := fun who deviation =>
    selector.selectionStageCharge terminalTarget
      (Function.update profile who deviation) who fuel
  fuel_covers_rank := hfuel
  lower_initial := by
    intro who
    exact hparent who
  upper_initial := by
    intro who
    exact hparent who
  deviation_initial := by
    intro who
    exact hparent who
  lower_subharmonic := by
    intro who stage history
    rw [
      selector.historyContinuationEU_terminalTargetHistoryPotential_eq
        terminalTarget profile who history
    ]
    rfl
  upper_superharmonic := by
    intro who stage history
    rw [
      selector.historyContinuationEU_terminalTargetHistoryPotential_eq
        terminalTarget profile who history
    ]
    rfl
  deviation_superharmonic := by
    intro who deviation stage history
    rw [
      selector.historyContinuationEU_terminalTargetHistoryPotential_eq
        terminalTarget (Function.update profile who deviation)
        who history
    ]
    rfl
  lower_stage := by
    intro who stage history hstage
    exact
      selector.terminalTargetPotential_le_stageEUAt_add_selectionStageCharge
        terminalTarget profile who fuel history hstage
  upper_stage := by
    intro who stage history hstage
    exact
      selector.stageEUAt_le_terminalTargetPotential_add_selectionStageCharge
        terminalTarget profile who fuel history hstage
  deviation_stage := by
    intro who deviation stage history hstage
    exact
      selector.stageEUAt_le_terminalTargetPotential_add_selectionStageCharge
        terminalTarget (Function.update profile who deviation)
        who fuel history hstage
  lower_terminal_value := by
    intro phaseProfile who history hhistory
    exact selector.terminalTargetHistoryPotential_eq_of_mem_support
      terminalTarget phaseProfile initial fuel hfuel
      who history hhistory
  upper_terminal_value := by
    intro phaseProfile who history hhistory
    exact selector.terminalTargetHistoryPotential_eq_of_mem_support
      terminalTarget phaseProfile initial fuel hfuel
      who history hhistory
  deviation_terminal_value := by
    intro phaseProfile who history hhistory
    exact selector.terminalTargetHistoryPotential_eq_of_mem_support
      terminalTarget phaseProfile initial fuel hfuel
      who history hhistory
  lower_charge_sum := by
    intro who horizon hfuelHorizon
    exact selector.sum_expectedHistoryValue_selectionStageCharge_le
      terminalTarget profile initial who fuel hpayoff htarget
      hpayoffNonneg htargetNonneg horizon hfuelHorizon
  upper_charge_sum := by
    intro who horizon hfuelHorizon
    exact selector.sum_expectedHistoryValue_selectionStageCharge_le
      terminalTarget profile initial who fuel hpayoff htarget
      hpayoffNonneg htargetNonneg horizon hfuelHorizon
  deviation_charge_sum := by
    intro who deviation horizon hfuelHorizon
    exact selector.sum_expectedHistoryValue_selectionStageCharge_le
      terminalTarget (Function.update profile who deviation)
      initial who fuel hpayoff htarget hpayoffNonneg
      htargetNonneg horizon hfuelHorizon

namespace SelectionPhaseSystemAt

variable [Fintype ι] [DecidableEq ι] [Finite Child] [Finite G.State]
  [∀ player, Finite (G.Act player)]
  {selector : DeviationSafePublicCoinSelector G Child}
  {terminalTarget : Child → ι → ℝ}
  {profile : G.BehaviorProfile} {initial : G.State}
  {parentTarget : ι → ℝ} {error : ℝ} {fuel : ℕ}
  {payoffBound targetBound : ℝ}

omit [DecidableEq ι] [Finite G.State]
  [∀ player, Finite (G.Act player)] in
/-- A fixed prefix-cost bound becomes a Cesàro bound at every later horizon.
This is the arithmetic bridge from selection accounting to the charge fields
of `PublicPhasePunishmentSystemAt`. -/
theorem average_le_of_sum_le_prefixCost
    (accountingHorizon : ℕ) (horizon : ℕ)
    (haccountingPositive : 0 < accountingHorizon)
    (haccountingHorizon : accountingHorizon ≤ horizon)
    (herrorNonneg : 0 ≤ error)
    (hprefixCost :
      (fuel : ℝ) * (payoffBound + targetBound) ≤
        (accountingHorizon : ℝ) * error)
    (charge : G.HistoryPotential)
    (chargeSum :
      ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge stage ≤
        (fuel : ℝ) * (payoffBound + targetBound)) :
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge stage ≤
      error := by
  have hhorizonPositive : 0 < horizon :=
    lt_of_lt_of_le haccountingPositive haccountingHorizon
  have hhorizonRealPositive : (0 : ℝ) < horizon := by
    exact_mod_cast hhorizonPositive
  have haccountingReal :
      (accountingHorizon : ℝ) ≤ horizon := by
    exact_mod_cast haccountingHorizon
  have hsum :
      ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge stage ≤
        (horizon : ℝ) * error := by
    calc
      ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge stage ≤
        (fuel : ℝ) * (payoffBound + targetBound) :=
          chargeSum
      _ ≤ (accountingHorizon : ℝ) * error := hprefixCost
      _ ≤ (horizon : ℝ) * error :=
        mul_le_mul_of_nonneg_right haccountingReal herrorNonneg
  calc
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial charge stage ≤
      (horizon : ℝ)⁻¹ * ((horizon : ℝ) * error) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hhorizonRealPositive.le)
    _ = error := by
      field_simp

/-- The prescribed lower prefix charge satisfies the required Cesàro bound
once the accounting horizon absorbs its fixed total cost. -/
theorem lower_charge_cesaro
    (system :
      SelectionPhaseSystemAt selector terminalTarget profile initial
        parentTarget error fuel payoffBound targetBound)
    (accountingHorizon : ℕ) (haccountingPositive : 0 < accountingHorizon)
    (hfuelAccounting : fuel ≤ accountingHorizon)
    (herrorNonneg : 0 ≤ error)
    (hprefixCost :
      (fuel : ℝ) * (payoffBound + targetBound) ≤
        (accountingHorizon : ℝ) * error)
    (who : ι) (horizon : ℕ)
    (haccountingHorizon : accountingHorizon ≤ horizon) :
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial
            (system.lowerCharge who) stage ≤
      error := by
  apply average_le_of_sum_le_prefixCost
    accountingHorizon horizon haccountingPositive
    haccountingHorizon herrorNonneg hprefixCost
  exact system.lower_charge_sum who horizon
    (le_trans hfuelAccounting haccountingHorizon)

/-- The prescribed upper prefix charge satisfies the required Cesàro bound
at the same accounting horizon. -/
theorem upper_charge_cesaro
    (system :
      SelectionPhaseSystemAt selector terminalTarget profile initial
        parentTarget error fuel payoffBound targetBound)
    (accountingHorizon : ℕ) (haccountingPositive : 0 < accountingHorizon)
    (hfuelAccounting : fuel ≤ accountingHorizon)
    (herrorNonneg : 0 ≤ error)
    (hprefixCost :
      (fuel : ℝ) * (payoffBound + targetBound) ≤
        (accountingHorizon : ℝ) * error)
    (who : ι) (horizon : ℕ)
    (haccountingHorizon : accountingHorizon ≤ horizon) :
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue profile initial
            (system.upperCharge who) stage ≤
      error := by
  apply average_le_of_sum_le_prefixCost
    accountingHorizon horizon haccountingPositive
    haccountingHorizon herrorNonneg hprefixCost
  exact system.upper_charge_sum who horizon
    (le_trans hfuelAccounting haccountingHorizon)

/-- Every unilateral-deviation prefix charge satisfies the same Cesàro bound,
because the public stopped law and the payoff bound are profile-independent. -/
theorem deviation_charge_cesaro
    (system :
      SelectionPhaseSystemAt selector terminalTarget profile initial
        parentTarget error fuel payoffBound targetBound)
    (accountingHorizon : ℕ) (haccountingPositive : 0 < accountingHorizon)
    (hfuelAccounting : fuel ≤ accountingHorizon)
    (herrorNonneg : 0 ≤ error)
    (hprefixCost :
      (fuel : ℝ) * (payoffBound + targetBound) ≤
        (accountingHorizon : ℝ) * error)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (horizon : ℕ)
    (haccountingHorizon : accountingHorizon ≤ horizon) :
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (system.deviationCharge who deviation) stage ≤
      error := by
  have hhorizonPositive : 0 < horizon :=
    lt_of_lt_of_le haccountingPositive haccountingHorizon
  have hhorizonRealPositive : (0 : ℝ) < horizon := by
    exact_mod_cast hhorizonPositive
  have haccountingReal :
      (accountingHorizon : ℝ) ≤ horizon := by
    exact_mod_cast haccountingHorizon
  have hsum :
      ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (system.deviationCharge who deviation) stage ≤
        (horizon : ℝ) * error := by
    calc
      ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (system.deviationCharge who deviation) stage ≤
        (fuel : ℝ) * (payoffBound + targetBound) :=
          system.deviation_charge_sum who deviation horizon
            (le_trans hfuelAccounting haccountingHorizon)
      _ ≤ (accountingHorizon : ℝ) * error := hprefixCost
      _ ≤ (horizon : ℝ) * error :=
        mul_le_mul_of_nonneg_right haccountingReal herrorNonneg
  calc
    (horizon : ℝ)⁻¹ *
        ∑ stage ∈ Finset.range horizon,
          G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (system.deviationCharge who deviation) stage ≤
      (horizon : ℝ)⁻¹ * ((horizon : ℝ) * error) :=
        mul_le_mul_of_nonneg_left hsum
          (inv_nonneg.mpr hhorizonRealPositive.le)
    _ = error := by
      field_simp

end SelectionPhaseSystemAt

end DeviationSafePublicCoinSelector
end StochasticGame
end GameTheory
