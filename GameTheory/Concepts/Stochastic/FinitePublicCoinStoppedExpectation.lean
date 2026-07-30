/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.DeviationSafePublicCoinSelection

/-!
# Expectation accounting for a locally stopped public coin

`FinitePublicCoinStoppingRegion` constrains game transitions only before the
public stopping time.  Consequently it cannot satisfy the global, pointwise
off-path obligations of a public-phase certificate by itself.

This file uses a separate stopped-history law.  Before stopping it samples the
actual public action distribution and the region's action-independent kernel.
After stopping it pads the mathematical history with self-loops and charges
nothing.  No condition is imposed on the game's transitions after stopping.

A terminal target boundary supplies only:

* an observable child at terminal states;
* a scalar target potential for every player;
* the terminal boundary value; and
* harmonicity under the local nonterminal kernel.

The resulting potential is expectation-preserving under prescribed play and
every unilateral deviation.  Its active lower, upper, and deviation charges
have total expectation bounded by the initial rank times the uniform
payoff-plus-target bound.  A strategic suffix theorem must still identify its
actual stopped-history law with this mathematical law.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FinitePublicCoinStoppingRegion

open Math Math.OutcomeClosure Math.Probability
  Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- The trivial value process associated with a finite stopping region.
Its outcome is irrelevant; it is used to reuse the finite-rank stopping
theorem. -/
def toUnitValueProcess
    (region : FinitePublicCoinStoppingRegion G) :
    ValueProcess G.State Unit where
  terminal := region.terminal
  step := region.kernel
  rank := region.rank
  observe := fun _ => ()
  value := fun _ => PMF.pure ()
  terminal_of_rank_zero := region.terminal_of_rank_zero
  terminal_value := by
    intro state hterminal
    rfl
  step_value := by
    intro state hnonterminal
    exact PMF.bind_const _ _
  step_rank := region.step_rank

/-- The stopped public kernel: use the region kernel before stopping and
self-loop afterwards. -/
def stoppedStep
    (region : FinitePublicCoinStoppingRegion G) (state : G.State) :
    PMF G.State :=
  region.toUnitValueProcess.stoppedStep state

@[simp] theorem stoppedStep_terminal
    (region : FinitePublicCoinStoppingRegion G) {state : G.State}
    (hterminal : region.terminal state) :
    region.stoppedStep state = PMF.pure state :=
  region.toUnitValueProcess.stoppedStep_terminal hterminal

@[simp] theorem stoppedStep_nonterminal
    (region : FinitePublicCoinStoppingRegion G) {state : G.State}
    (hnonterminal : ¬region.terminal state) :
    region.stoppedStep state = region.kernel state :=
  region.toUnitValueProcess.stoppedStep_nonterminal hnonterminal

/-- A full public-history law for the mathematically stopped selection phase.
Actions are still recorded after stopping, but the state self-loops there. -/
def stoppedHistDist
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State) :
    (fuel : ℕ) → PMF (G.Hist fuel)
  | 0 => PMF.pure (G.emptyHist initial)
  | fuel + 1 =>
      (region.stoppedHistDist profile initial fuel).bind fun history =>
        (G.stageActionDist profile history).bind fun action =>
          (region.stoppedStep history.2).bind fun successor =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), successor) :
                G.Hist (fuel + 1))

@[simp] theorem stoppedHistDist_zero
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State) :
    region.stoppedHistDist profile initial 0 =
      PMF.pure (G.emptyHist initial) :=
  rfl

theorem stoppedHistDist_succ
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) :
    region.stoppedHistDist profile initial (fuel + 1) =
      (region.stoppedHistDist profile initial fuel).bind fun history =>
        (G.stageActionDist profile history).bind fun action =>
          (region.stoppedStep history.2).bind fun successor =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), successor) :
                G.Hist (fuel + 1)) :=
  rfl

/-- The state marginal of the stopped-history law is the finite stopped
state process. -/
theorem stateMarginal_stoppedHistDist_eq_run
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State) :
    ∀ fuel,
      (region.stoppedHistDist profile initial fuel).map Prod.snd =
        region.toUnitValueProcess.run fuel initial := by
  intro fuel
  change
    (region.stoppedHistDist profile initial fuel).map Prod.snd =
      Math.PMFIter.iter region.stoppedStep fuel initial
  induction fuel with
  | zero =>
      rw [stoppedHistDist_zero]
      change
        PMF.map Prod.snd (PMF.pure (Fin.elim0, initial)) =
          PMF.pure initial
      rw [PMF.pure_map]
  | succ fuel ih =>
      rw [
        Math.PMFIter.iter_succ',
        ← ih,
        stoppedHistDist_succ,
        PMF.bind_map
      ]
      simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure]
      congr 1
      funext history
      exact PMF.bind_const _ _

/-- Enough fuel makes every history in the stopped law terminal. -/
theorem terminal_of_mem_support_stoppedHistDist
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : region.rank initial ≤ fuel)
    (history : G.Hist fuel)
    (hhistory :
      history ∈
        (region.stoppedHistDist profile initial fuel).support) :
    region.terminal history.2 := by
  have hstate :
      history.2 ∈
        ((region.stoppedHistDist profile initial fuel).map
          Prod.snd).support := by
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨history, hhistory, rfl⟩
  rw [region.stateMarginal_stoppedHistDist_eq_run
    profile initial fuel] at hstate
  exact region.toUnitValueProcess.support_terminal_of_rank_le
    fuel initial history.2 hfuel hstate

/-- Minimal scalar boundary data for terminal child targets. -/
structure TerminalTargetBoundary
    (region : FinitePublicCoinStoppingRegion G)
    (terminalTarget : Child → ι → ℝ) where
  observe : G.State → Child
  potential : ι → G.State → ℝ
  terminal_value :
    ∀ state, region.terminal state →
      ∀ who, potential who state = terminalTarget (observe state) who
  step_harmonic :
    ∀ state, ¬region.terminal state →
      ∀ who,
        expect (region.kernel state) (potential who) =
          potential who state

namespace TerminalTargetBoundary

variable {region : FinitePublicCoinStoppingRegion G}
  {terminalTarget : Child → ι → ℝ}

/-- The boundary potential is harmonic for the artificially stopped kernel,
including at terminal self-loops. -/
theorem expect_stoppedStep_potential
    (boundary : TerminalTargetBoundary region terminalTarget)
    (state : G.State) (who : ι) :
    expect (region.stoppedStep state) (boundary.potential who) =
      boundary.potential who state := by
  by_cases hterminal : region.terminal state
  · rw [region.stoppedStep_terminal hterminal, expect_pure]
  · rw [region.stoppedStep_nonterminal hterminal]
    exact boundary.step_harmonic state hterminal who

/-- One-step continuation under the artificial stopped-history law. -/
def stoppedHistoryContinuationEU
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage) : ℝ :=
  expect (G.stageActionDist profile history) fun _ =>
    expect (region.stoppedStep history.2) (boundary.potential who)

/-- The stopped continuation potential is exactly constant, independently
of the action distribution. -/
theorem stoppedHistoryContinuationEU_eq
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage) :
    boundary.stoppedHistoryContinuationEU profile who history =
      boundary.potential who history.2 := by
  unfold stoppedHistoryContinuationEU
  rw [boundary.expect_stoppedStep_potential]
  exact expect_const _ _

/-- While selection is active, artificial stopped continuation is the actual
game continuation.  No assertion is made at a terminal history. -/
theorem historyContinuationEU_eq_stopped_of_nonterminal
    [Fintype ι] [Finite G.State] [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬region.terminal history.2) :
    G.historyContinuationEU profile
        (fun _ next => boundary.potential who next.2) history =
      boundary.stoppedHistoryContinuationEU profile who history := by
  unfold historyContinuationEU stoppedHistoryContinuationEU
  apply congrArg (expect (G.stageActionDist profile history))
  funext action
  rw [
    region.transition_eq_kernel history.2 hnonterminal action,
    region.stoppedStep_nonterminal hnonterminal
  ]

/-- Expected value under the artificial stopped public-history law. -/
def stoppedExpectedPotential
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) (fuel : ℕ) : ℝ :=
  expect (region.stoppedHistDist profile initial fuel)
    (fun history => boundary.potential who history.2)

/-- One-step recursion for the expected stopped target potential. -/
theorem stoppedExpectedPotential_succ
    [Fintype ι] [Finite G.State] [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) (fuel : ℕ) :
    boundary.stoppedExpectedPotential profile initial who (fuel + 1) =
      expect (region.stoppedHistDist profile initial fuel)
        (boundary.stoppedHistoryContinuationEU profile who) := by
  unfold stoppedExpectedPotential stoppedHistoryContinuationEU
  rw [region.stoppedHistDist_succ, expect_bind]
  apply congrArg
  funext history
  rw [expect_bind]
  apply congrArg
  funext action
  rw [expect_bind]
  apply congrArg
  funext successor
  rw [expect_pure]

/-- The stopped terminal-target potential has the same expectation at every
fuel, under every behavior profile. -/
theorem stoppedExpectedPotential_eq_initial
    [Fintype ι] [Finite G.State] [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) :
    ∀ fuel,
      boundary.stoppedExpectedPotential profile initial who fuel =
        boundary.potential who initial := by
  intro fuel
  induction fuel with
  | zero =>
      simp [stoppedExpectedPotential]
      rfl
  | succ fuel ih =>
      rw [boundary.stoppedExpectedPotential_succ]
      calc
        expect (region.stoppedHistDist profile initial fuel)
            (boundary.stoppedHistoryContinuationEU profile who) =
          expect (region.stoppedHistDist profile initial fuel)
            (fun history => boundary.potential who history.2) := by
              apply congrArg
              funext history
              exact boundary.stoppedHistoryContinuationEU_eq
                profile who history
        _ = boundary.potential who initial := ih

/-- The stopped terminal-child law after a fixed amount of fuel. -/
def terminalChildLaw
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) : PMF Child :=
  (region.stoppedHistDist profile initial fuel).map
    (fun history => boundary.observe history.2)

/-- Once the rank is exhausted, expected terminal child target equals the
initial boundary potential. -/
theorem expect_terminalChildLaw_eq_initial
    [Fintype ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : region.rank initial ≤ fuel)
    (who : ι) :
    expect (boundary.terminalChildLaw profile initial fuel)
        (fun child => terminalTarget child who) =
      boundary.potential who initial := by
  unfold terminalChildLaw
  rw [expect_map]
  calc
    expect (region.stoppedHistDist profile initial fuel)
        (fun history =>
          terminalTarget (boundary.observe history.2) who) =
      expect (region.stoppedHistDist profile initial fuel)
        (fun history => boundary.potential who history.2) := by
          apply expect_congr_on_support
          intro history hhistory
          symm
          exact boundary.terminal_value history.2
            (region.terminal_of_mem_support_stoppedHistDist
              profile initial fuel hfuel history hhistory) who
    _ = boundary.potential who initial :=
      boundary.stoppedExpectedPotential_eq_initial
        profile initial who fuel

/-- The current-stage payoff gap, charged only while the stopped process is
still selecting. -/
def activeStageCharge
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι) :
    G.HistoryPotential := by
  classical
  exact fun _ history =>
    if region.terminal history.2 then
      0
    else
      |G.stageEUAt profile history who -
        boundary.potential who history.2|

/-- On a selecting history, the boundary potential is exactly the actual
one-step game continuation. -/
theorem historyContinuationEU_potential_eq_of_nonterminal
    [Fintype ι] [Finite G.State] [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬region.terminal history.2) :
    G.historyContinuationEU profile
        (fun _ next => boundary.potential who next.2) history =
      boundary.potential who history.2 := by
  rw [
    boundary.historyContinuationEU_eq_stopped_of_nonterminal
      profile who history hnonterminal,
    boundary.stoppedHistoryContinuationEU_eq profile who history
  ]

/-- The active absolute charge proves the lower stage inequality. -/
theorem potential_le_stageEUAt_add_activeStageCharge
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬region.terminal history.2) :
    boundary.potential who history.2 ≤
      G.stageEUAt profile history who +
        boundary.activeStageCharge profile who stage history := by
  simp only [activeStageCharge, if_neg hnonterminal]
  linarith [neg_le_abs
    (G.stageEUAt profile history who -
      boundary.potential who history.2)]

/-- The same active charge proves the upper stage inequality. -/
theorem stageEUAt_le_potential_add_activeStageCharge
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬region.terminal history.2) :
    G.stageEUAt profile history who ≤
      boundary.potential who history.2 +
        boundary.activeStageCharge profile who stage history := by
  simp only [activeStageCharge, if_neg hnonterminal]
  linarith [le_abs_self
    (G.stageEUAt profile history who -
      boundary.potential who history.2)]

/-- The active charge is zero at a terminal history. -/
theorem activeStageCharge_eq_zero_of_terminal
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {stage : ℕ} (history : G.Hist stage)
    (hterminal : region.terminal history.2) :
    boundary.activeStageCharge profile who stage history = 0 := by
  simp [activeStageCharge, hterminal]

/-- A terminal-target bound controls every harmonic boundary potential. -/
theorem abs_potential_le
    [Finite ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile)
    {targetBound : ℝ}
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (who : ι) (state : G.State) :
    |boundary.potential who state| ≤ targetBound := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [← boundary.expect_terminalChildLaw_eq_initial
    profile state (region.rank state) (le_refl _) who]
  exact abs_expect_le_of_abs_le _ _
    (fun child => htarget child who)

/-- A uniform payoff bound controls any mixed stage payoff. -/
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

/-- Every active stage charge is at most the payoff bound plus the terminal
target bound. -/
theorem activeStageCharge_le
    [Fintype ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (who : ι)
    {payoffBound targetBound : ℝ}
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound)
    {stage : ℕ} (history : G.Hist stage) :
    boundary.activeStageCharge profile who stage history ≤
      payoffBound + targetBound := by
  unfold activeStageCharge
  split_ifs
  · exact add_nonneg hpayoffNonneg htargetNonneg
  · calc
      |G.stageEUAt profile history who -
          boundary.potential who history.2| ≤
        |G.stageEUAt profile history who| +
          |boundary.potential who history.2| :=
        abs_sub _ _
      _ ≤ payoffBound + targetBound :=
        add_le_add
          (abs_stageEUAt_le profile hpayoff history who)
          (boundary.abs_potential_le profile htarget who history.2)

/-- Total expected active charge under the mathematical stopped-history law
is bounded by the initial rank times the one-stage bound. -/
theorem sum_expect_activeStageCharge_le
    [Fintype ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (who : ι) {payoffBound targetBound : ℝ}
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound)
    (horizon : ℕ) (hrank : region.rank initial ≤ horizon) :
    ∑ stage ∈ Finset.range horizon,
        expect (region.stoppedHistDist profile initial stage)
          (boundary.activeStageCharge profile who stage) ≤
      (region.rank initial : ℝ) * (payoffBound + targetBound) := by
  rw [← Finset.sum_range_add_sum_Ico _ hrank]
  have hprefix :
      ∑ stage ∈ Finset.range (region.rank initial),
          expect (region.stoppedHistDist profile initial stage)
            (boundary.activeStageCharge profile who stage) ≤
        (region.rank initial : ℝ) *
          (payoffBound + targetBound) := by
    calc
      ∑ stage ∈ Finset.range (region.rank initial),
          expect (region.stoppedHistDist profile initial stage)
            (boundary.activeStageCharge profile who stage) ≤
        ∑ _stage ∈ Finset.range (region.rank initial),
          (payoffBound + targetBound) := by
            apply Finset.sum_le_sum
            intro stage _
            simpa only [expect_const] using
              expect_mono
                (region.stoppedHistDist profile initial stage) _ _
                (boundary.activeStageCharge_le profile who
                  hpayoff htarget hpayoffNonneg htargetNonneg)
      _ = (region.rank initial : ℝ) *
          (payoffBound + targetBound) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail :
      ∑ stage ∈ Finset.Ico (region.rank initial) horizon,
          expect (region.stoppedHistDist profile initial stage)
            (boundary.activeStageCharge profile who stage) = 0 := by
    apply Finset.sum_eq_zero
    intro stage hstage
    have hterminal :
        ∀ history ∈
          (region.stoppedHistDist profile initial stage).support,
            region.terminal history.2 := by
      intro history hhistory
      exact region.terminal_of_mem_support_stoppedHistDist
        profile initial stage (Finset.mem_Ico.mp hstage).1
        history hhistory
    calc
      expect (region.stoppedHistDist profile initial stage)
          (boundary.activeStageCharge profile who stage) =
        expect (region.stoppedHistDist profile initial stage)
          (fun _ => 0) := by
            apply expect_congr_on_support
            intro history hhistory
            exact boundary.activeStageCharge_eq_zero_of_terminal
              profile who history (hterminal history hhistory)
      _ = 0 := expect_const _ 0
  rw [htail, add_zero]
  exact hprefix

/-- The terminal-child law of the mathematical stopped process is independent
of the behavior profile, including unilateral deviations. -/
theorem terminalChildLaw_profileIndependent
    [Fintype ι]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (first second : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) :
    boundary.terminalChildLaw first initial fuel =
      boundary.terminalChildLaw second initial fuel := by
  unfold terminalChildLaw
  change
    PMF.map (boundary.observe ∘ Prod.snd)
        (region.stoppedHistDist first initial fuel) =
      PMF.map (boundary.observe ∘ Prod.snd)
        (region.stoppedHistDist second initial fuel)
  rw [
    ← PMF.map_comp,
    region.stateMarginal_stoppedHistDist_eq_run first initial fuel,
    ← PMF.map_comp,
    region.stateMarginal_stoppedHistDist_eq_run second initial fuel
  ]

/-- Capstone expectation-level selection theorem.

Every behavior profile, chosen adaptively or obtained by a unilateral update,
has the same expected boundary potential and terminal target.  Its total
active selection charge is uniformly bounded by the initial public rank. -/
theorem adaptiveSelection_expectationBounds
    [Fintype ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (initial : G.State) (parentTarget : ι → ℝ) (error : ℝ)
    {payoffBound targetBound : ℝ}
    (hparent :
      ∀ who,
        |boundary.potential who initial - parentTarget who| ≤ error)
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound) :
    (∀ (phaseProfile : G.BehaviorProfile) who fuel,
        |boundary.stoppedExpectedPotential
            phaseProfile initial who fuel -
          parentTarget who| ≤ error) ∧
      (∀ (phaseProfile : G.BehaviorProfile) who fuel,
        region.rank initial ≤ fuel →
          |expect
              (boundary.terminalChildLaw phaseProfile initial fuel)
              (fun child => terminalTarget child who) -
            parentTarget who| ≤ error) ∧
      (∀ (phaseProfile : G.BehaviorProfile) who horizon,
        region.rank initial ≤ horizon →
          ∑ stage ∈ Finset.range horizon,
              expect
                (region.stoppedHistDist phaseProfile initial stage)
                (boundary.activeStageCharge
                  phaseProfile who stage) ≤
            (region.rank initial : ℝ) *
              (payoffBound + targetBound)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phaseProfile who fuel
    rw [boundary.stoppedExpectedPotential_eq_initial]
    exact hparent who
  · intro phaseProfile who fuel hfuel
    rw [boundary.expect_terminalChildLaw_eq_initial
      phaseProfile initial fuel hfuel who]
    exact hparent who
  · intro phaseProfile who horizon hrank
    exact boundary.sum_expect_activeStageCharge_le
      phaseProfile initial who hpayoff htarget
      hpayoffNonneg htargetNonneg horizon hrank

end TerminalTargetBoundary

/-- Exact realization boundary for a dynamically stopped strategic history
law.

`realizedStoppedLaw` is intended to be the pushforward of an actual public
history by a first-stopping-and-padding map.  A dispatcher construction must
prove this equality; it is not implied by local transition identities after
the stopping time. -/
def IsStoppedHistoryLaw
    [Fintype ι]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (initial : G.State)
    (realizedStoppedLaw : ∀ fuel, PMF (G.Hist fuel)) : Prop :=
  ∀ fuel,
    realizedStoppedLaw fuel =
      region.stoppedHistDist profile initial fuel

namespace TerminalTargetBoundary

variable {region : FinitePublicCoinStoppingRegion G}
  {terminalTarget : Child → ι → ℝ}

/-- Once a strategic construction realizes the exact stopped-history law,
all adaptive expectation and charge bounds transfer to that construction. -/
theorem adaptiveSelection_expectationBounds_of_stoppedHistoryLaw
    [Fintype ι] [Finite Child] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (boundary : TerminalTargetBoundary region terminalTarget)
    (profile : G.BehaviorProfile) (initial : G.State)
    (realizedStoppedLaw : ∀ fuel, PMF (G.Hist fuel))
    (hrealized :
      region.IsStoppedHistoryLaw profile initial realizedStoppedLaw)
    (parentTarget : ι → ℝ) (error : ℝ)
    {payoffBound targetBound : ℝ}
    (hparent :
      ∀ who,
        |boundary.potential who initial - parentTarget who| ≤ error)
    (hpayoff :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (htarget :
      ∀ child player, |terminalTarget child player| ≤ targetBound)
    (hpayoffNonneg : 0 ≤ payoffBound)
    (htargetNonneg : 0 ≤ targetBound) :
    (∀ who fuel,
        |expect (realizedStoppedLaw fuel)
            (fun history => boundary.potential who history.2) -
          parentTarget who| ≤ error) ∧
      (∀ who fuel, region.rank initial ≤ fuel →
        |expect
            ((realizedStoppedLaw fuel).map
              (fun history => boundary.observe history.2))
            (fun child => terminalTarget child who) -
          parentTarget who| ≤ error) ∧
      (∀ who horizon, region.rank initial ≤ horizon →
        ∑ stage ∈ Finset.range horizon,
            expect (realizedStoppedLaw stage)
              (boundary.activeStageCharge profile who stage) ≤
          (region.rank initial : ℝ) *
            (payoffBound + targetBound)) := by
  obtain ⟨hpotential, hterminal, hcharge⟩ :=
    boundary.adaptiveSelection_expectationBounds
      initial parentTarget error hparent hpayoff htarget
      hpayoffNonneg htargetNonneg
  refine ⟨?_, ?_, ?_⟩
  · intro who fuel
    rw [hrealized fuel]
    exact hpotential profile who fuel
  · intro who fuel hfuel
    rw [hrealized fuel]
    exact hterminal profile who fuel hfuel
  · intro who horizon hrank
    have heq :
        ∑ stage ∈ Finset.range horizon,
            expect (realizedStoppedLaw stage)
              (boundary.activeStageCharge profile who stage) =
          ∑ stage ∈ Finset.range horizon,
            expect (region.stoppedHistDist profile initial stage)
              (boundary.activeStageCharge profile who stage) := by
      apply Finset.sum_congr rfl
      intro stage _
      rw [hrealized stage]
    rw [heq]
    exact hcharge profile who horizon hrank

end TerminalTargetBoundary
end FinitePublicCoinStoppingRegion
end StochasticGame
end GameTheory
