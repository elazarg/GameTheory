/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Strategy.Potential.Adaptive
import Math.OutcomeClosure

/-!
# Deviation-safe finite public-coin selection

Random selection among recurrent children is strategically harmless when the
selection phase is driven by public transitions that no action can affect.
This file packages a finite, rank-decreasing version of that condition.

The selector carries an `OutcomeClosure.ValueProcess`.  Its stopped public
kernel must be the actual game transition after every joint action.  Therefore
the public-state marginal of every behavior profile, including every
unilateral deviation, is exactly the stopped process.  Once the available
fuel dominates the rank, the entire terminal-child law is independent of
play.

This is deliberately only the selection theorem.  Applying a child's
public-phase certificate after the stopping history still requires a suffix
rebase and finite-prefix accounting.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- A finite public selection region.  Before a terminal state is reached,
the public kernel is independent of every joint action and strictly lowers
the natural-valued rank on its support.

Unlike `DeviationSafePublicCoinSelector` below, this structure imposes no
condition on game transitions after stopping.  It is therefore the right
local interface for a phase which immediately rebases to a child strategy. -/
structure FinitePublicCoinStoppingRegion (G : StochasticGame ι) where
  terminal : G.State → Prop
  kernel : G.State → PMF G.State
  rank : G.State → ℕ
  terminal_of_rank_zero :
    ∀ state, rank state = 0 → terminal state
  transition_eq_kernel :
    ∀ state, ¬ terminal state →
      ∀ action, G.transition state action = kernel state
  step_rank :
    ∀ state successor,
      ¬ terminal state →
        kernel state successor ≠ 0 →
          rank successor + 1 = rank state

namespace FinitePublicCoinStoppingRegion

/-- Before stopping, every behavior profile has exactly the same one-step
continuation law for a state potential. -/
theorem historyContinuationEU_statePotential_eq
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (potential : G.State → ℝ)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬ region.terminal history.2) :
    G.historyContinuationEU profile
        (fun _ next => potential next.2) history =
      expect (region.kernel history.2) potential := by
  unfold historyContinuationEU
  calc
    expect (G.stageActionDist profile history)
        (fun action =>
          expect (G.transition history.2 action) potential) =
      expect (G.stageActionDist profile history)
        (fun _ => expect (region.kernel history.2) potential) := by
          apply congrArg (expect (G.stageActionDist profile history))
          funext action
          rw [region.transition_eq_kernel history.2 hnonterminal action]
    _ = expect (region.kernel history.2) potential :=
      expect_const _ _

/-- A superharmonic child-continuation ceiling remains a one-step ceiling
under every behavior profile, hence under every unilateral deviation. -/
theorem historyContinuationEU_statePotential_le
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (region : FinitePublicCoinStoppingRegion G)
    (profile : G.BehaviorProfile) (potential : G.State → ℝ)
    (superharmonic :
      ∀ state,
        ¬ region.terminal state →
          expect (region.kernel state) potential ≤ potential state)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬ region.terminal history.2) :
    G.historyContinuationEU profile
        (fun _ next => potential next.2) history ≤
      potential history.2 := by
  rw [
    region.historyContinuationEU_statePotential_eq
      profile potential history hnonterminal
  ]
  exact superharmonic history.2 hnonterminal

/-- Before stopping, two arbitrary profiles induce the same one-step
continuation value. -/
theorem historyContinuationEU_statePotential_profileIndependent
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (region : FinitePublicCoinStoppingRegion G)
    (first second : G.BehaviorProfile)
    (potential : G.State → ℝ)
    {stage : ℕ} (history : G.Hist stage)
    (hnonterminal : ¬ region.terminal history.2) :
    G.historyContinuationEU first
        (fun _ next => potential next.2) history =
      G.historyContinuationEU second
        (fun _ next => potential next.2) history := by
  rw [
    region.historyContinuationEU_statePotential_eq
      first potential history hnonterminal,
    region.historyContinuationEU_statePotential_eq
      second potential history hnonterminal
  ]

/-- At every nonterminal supported step, the public stopping rank decreases
by exactly one. -/
theorem successor_rank_add_one
    (region : FinitePublicCoinStoppingRegion G)
    {state successor : G.State}
    (hnonterminal : ¬ region.terminal state)
    (hsuccessor : successor ∈ (region.kernel state).support) :
    region.rank successor + 1 = region.rank state := by
  exact region.step_rank state successor hnonterminal
    (by simpa [PMF.mem_support_iff] using hsuccessor)

end FinitePublicCoinStoppingRegion

/-- A bounded public selector whose stopped state kernel is unaffected by
any joint action.

The `process.value state` distribution is the semantic law of the terminal
child selected from `state`.  `transition_eq_stoppedStep` is the strategic
condition: players cannot alter even one step of the public selection law. -/
structure DeviationSafePublicCoinSelector
    (G : StochasticGame ι) (Child : Type) where
  process : Math.OutcomeClosure.ValueProcess G.State Child
  transition_eq_stoppedStep :
    ∀ state action,
      G.transition state action = process.stoppedStep state

namespace DeviationSafePublicCoinSelector

/-- Forget the absorbing stopped implementation and retain only the local
pre-stopping public-coin region. -/
def toFinitePublicCoinStoppingRegion
    (selector : DeviationSafePublicCoinSelector G Child) :
    FinitePublicCoinStoppingRegion G where
  terminal := selector.process.terminal
  kernel := selector.process.step
  rank := selector.process.rank
  terminal_of_rank_zero := selector.process.terminal_of_rank_zero
  transition_eq_kernel state hnonterminal action := by
    rw [
      selector.transition_eq_stoppedStep state action,
      selector.process.stoppedStep_nonterminal hnonterminal
    ]
  step_rank := selector.process.step_rank

/-- The current-state marginal under an arbitrary behavior profile is the
finite stopped public process. -/
theorem stateMarginal_eq_run
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (profile : G.BehaviorProfile) (initial : G.State) :
    ∀ fuel,
      (G.histDist profile initial fuel).map Prod.snd =
        selector.process.run fuel initial := by
  intro fuel
  change
    (G.histDist profile initial fuel).map Prod.snd =
      Math.PMFIter.iter selector.process.stoppedStep fuel initial
  induction fuel with
  | zero =>
      rw [G.histDist_zero]
      change
        PMF.map Prod.snd (PMF.pure (Fin.elim0, initial)) =
          PMF.pure initial
      rw [PMF.pure_map]
  | succ fuel ih =>
      rw [
        Math.PMFIter.iter_succ',
        ← ih,
        G.histDist_succ,
        PMF.bind_map
      ]
      simp only [PMF.map_bind, PMF.pure_map, PMF.bind_pure]
      congr 1
      funext history
      simp only [
        Function.comp_apply,
        selector.transition_eq_stoppedStep
      ]
      exact PMF.bind_const _ _

/-- The terminal-child law obtained after a fixed amount of selection fuel. -/
def terminalChildLaw
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) : PMF Child :=
  PMF.map selector.process.observe
    ((G.histDist profile initial fuel).map Prod.snd)

/-- Once the fuel dominates the initial rank, every behavior profile induces
exactly the semantic child law stored in the selector. -/
theorem terminalChildLaw_eq_value
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel) :
    selector.terminalChildLaw profile initial fuel =
      selector.process.value initial := by
  unfold terminalChildLaw
  rw [selector.stateMarginal_eq_run profile initial fuel]
  exact selector.process.map_observe_run_eq_value fuel initial hfuel

/-- The complete terminal-child distribution is invariant under an arbitrary
change of behavior profile. -/
theorem terminalChildLaw_profileIndependent
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (first second : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel) :
    selector.terminalChildLaw first initial fuel =
      selector.terminalChildLaw second initial fuel := by
  rw [
    selector.terminalChildLaw_eq_value
      first initial fuel hfuel,
    selector.terminalChildLaw_eq_value
      second initial fuel hfuel
  ]

/-- Every history in the support has reached a terminal selector state once
the public rank has been exhausted. -/
theorem terminal_of_mem_support_histDist
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel)
    (history : G.Hist fuel)
    (hhistory : history ∈ (G.histDist profile initial fuel).support) :
    selector.process.terminal history.2 := by
  have hstate :
      history.2 ∈
        ((G.histDist profile initial fuel).map Prod.snd).support := by
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨history, hhistory, rfl⟩
  rw [selector.stateMarginal_eq_run profile initial fuel] at hstate
  exact selector.process.support_terminal_of_rank_le
    fuel initial history.2 hfuel hstate

/-- Every coordinate of the expected terminal target is fixed before play,
regardless of the behavior profile used during selection. -/
theorem expect_terminalTarget_eq_value
    [Fintype ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel)
    (who : ι) :
    expect (selector.terminalChildLaw profile initial fuel)
        (fun child => terminalTarget child who) =
      expect (selector.process.value initial)
        (fun child => terminalTarget child who) := by
  rw [selector.terminalChildLaw_eq_value profile initial fuel hfuel]

/-- In particular, prescribed play and an arbitrary unilateral deviation
produce the same expected terminal continuation target. -/
theorem expect_terminalTarget_update_eq
    [Fintype ι] [DecidableEq ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (selector.terminalChildLaw
          (Function.update profile who deviation) initial fuel)
        (fun child => terminalTarget child who) =
      expect (selector.terminalChildLaw profile initial fuel)
        (fun child => terminalTarget child who) := by
  rw [
    selector.expect_terminalTarget_eq_value terminalTarget
      (Function.update profile who deviation) initial fuel hfuel who,
    selector.expect_terminalTarget_eq_value terminalTarget
      profile initial fuel hfuel who
  ]

/-- A semantic continuation ceiling on the stored child law is therefore a
deviation ceiling for every finite public-coin selection phase. -/
theorem expect_terminalTarget_update_le
    [Fintype ι] [DecidableEq ι]
    (selector : DeviationSafePublicCoinSelector G Child)
    (terminalTarget : Child → ι → ℝ)
    (profile : G.BehaviorProfile) (initial : G.State)
    (fuel : ℕ) (hfuel : selector.process.rank initial ≤ fuel)
    (parentTarget : ι → ℝ) (error : ℝ)
    (ceiling :
      ∀ who,
        expect (selector.process.value initial)
            (fun child => terminalTarget child who) ≤
          parentTarget who + error)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (selector.terminalChildLaw
          (Function.update profile who deviation) initial fuel)
        (fun child => terminalTarget child who) ≤
      parentTarget who + error := by
  rw [
    selector.expect_terminalTarget_eq_value terminalTarget
      (Function.update profile who deviation) initial fuel hfuel who
  ]
  exact ceiling who

end DeviationSafePublicCoinSelector
end StochasticGame
end GameTheory
