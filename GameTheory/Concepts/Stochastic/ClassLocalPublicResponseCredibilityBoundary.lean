/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.DeviationSafePublicCoinSelection
import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticCirculationTerminalSemantics

/-!
# Credibility boundary for class-local analytic responses

The analytic-circulation terminal branch supplies a class-local response
whose source lies in the selected positive communicating class and whose
occupation and charge are strictly positive.

If that response is transition-visible, its source cannot initiate a
nontrivial exact action-independent public selector.  At a nonterminal state
of a `DeviationSafePublicCoinSelector`, every joint action induces one common
public-state kernel.  A transition charge instead certifies that the Fink
baseline and pure-deviation kernels differ.

This is only an initiation boundary.  The forced terminal source is fully
compatible with being the child selected by an earlier public draw.  The
results below neither construct nor forbid parent and child enforcement
ledgers.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

/-- At a nonterminal selector state, all stationary Fink mixtures, including
every pure unilateral replacement, induce the same public-state kernel. -/
theorem DeviationSafePublicCoinSelector.finkPureDeviationStateKernel_eq
    [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (selector : DeviationSafePublicCoinSelector G Child)
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (owner : ι) (action : G.Act owner)
    (hnonterminal : ¬selector.process.terminal source) :
    G.finkPureDeviationStateKernel z source owner action =
      G.finkStateKernel z source := by
  have htransition :
      ∀ jointAction : G.JointAct,
        G.transition source jointAction =
          selector.process.step source := by
    intro jointAction
    rw [selector.transition_eq_stoppedStep,
      selector.process.stoppedStep_nonterminal hnonterminal]
  have htransitionFunction :
      G.transition source =
        fun _ => selector.process.step source :=
    funext htransition
  unfold finkPureDeviationStateKernel finkStateKernel
  rw [htransitionFunction, PMF.bind_const, PMF.bind_const]

/-- A transition-visible public response forces its source to be terminal in
every deviation-safe selector.  It therefore cannot itself initiate a
nontrivial exact action-independent selection phase. -/
theorem FinkPublicTransitionCharge.terminal_of_deviationSafeSelector
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} {z : G.finkDomain U} {source : G.State}
    {owner : ι} {action : G.Act owner}
    (charge : G.FinkPublicTransitionCharge z source owner action)
    (selector : DeviationSafePublicCoinSelector G Child) :
    selector.process.terminal source := by
  by_contra hnonterminal
  have hkernel :=
    selector.finkPureDeviationStateKernel_eq
      z source owner action hnonterminal
  have hpositive := charge.forward_positive
  rw [hkernel, charge.baseline_centered] at hpositive
  exact (lt_irrefl 0) hpositive

namespace AnalyticBellmanGerm

variable
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who)}
    {terminalAnchor : G.State}

namespace PlayerNeutralAnalyticCirculationTerminalData

/-- In the transition-detector branch, the source of the actual
class-local response is terminal in every deviation-safe selector. -/
theorem classLocalTransitionResponse_terminal_of_deviationSafeSelector
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor)
    (charge :
      G.FinkPublicTransitionCharge
        germ.endpointFinkPoint
        data.classLocalPublicResponse.response.source who
        data.classLocalPublicResponse.response.1.2)
    (selector : DeviationSafePublicCoinSelector G Child) :
    selector.process.terminal
      data.classLocalPublicResponse.response.source :=
  charge.terminal_of_deviationSafeSelector selector

/-- The actual class-local response either has positive endpoint stage gain
or has a transition charge, in which case its source is terminal for the
proposed selector.

The terminal alternative is compatible with using this source as a selected
child; it only rules out starting a nontrivial exact selector there. -/
theorem classLocalResponse_stageGainPos_or_selectorTerminal
    (data :
      PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor)
    (selector : DeviationSafePublicCoinSelector G Child) :
    0 <
        G.finkStageGain germ.endpointFinkPoint
          data.classLocalPublicResponse.response.source who
          data.classLocalPublicResponse.response.1.2 ∨
      selector.process.terminal
        data.classLocalPublicResponse.response.source := by
  cases data.classLocalPublicResponse.publicResponse with
  | stage positive =>
      exact Or.inl positive
  | transition charge =>
      exact Or.inr
        (charge.terminal_of_deviationSafeSelector selector)

end PlayerNeutralAnalyticCirculationTerminalData
end AnalyticBellmanGerm

end StochasticGame
end GameTheory
