/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticHarmonicAdjustmentClosure
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.DeclaredTargetLeafGates

/-!
# Canonical analytic endpoint Bellman rows

`DeclaredTargetLeafGates` accepts an owner-labelled stochastic row system, but
its neutral interface intentionally permits the source, owner, transition and
gross gain to be supplied by hand.  This file gives the narrow canonical
compiler for the actual pure-deviation data already present in
`AnalyticFinkObstruction`.

A row is literally a player, a source state, and one of that player's pure
actions.  Its transition is the raw pure-deviation transition curve evaluated
at the analytic endpoint.  Its gross gain is the endpoint baseline stage
payoff plus the raw pure-deviation stage gain.  Thus all four row fields are
definitions, not hypotheses.  The endpoint identities prove that these raw
coordinates are respectively the genuine endpoint deviation PMF and the
genuine expected stage payoff of that deviation.  Stochasticity and
`NodeFlowRows.IsEndpointKernelTagged` then follow.

`NodeFlowRows.entry_isSource` requires the row type to contain a row at the
node's entry.  Finite action types are allowed to be empty, so the compiler
takes one explicit player/action anchor.  The anchor is used only for that
nonemptiness proof; it does not alter any compiled row field.

## Deliberate boundary

This is a one-step analytic-to-finite-row adapter.  It does **not** select a
legal public response, prove that a deviation can be monitored or enforced,
construct a recursive child, supply a circulation, or claim a uniform
equilibrium.  In particular, the compiler produces a `NodeGluingGate`, not a
`NodeAccountBridgeGate`.  Public-response and recursive-child realization
remain separate obligations.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Math.LinearAlgebra.OwnerLabeledFlowHolonomy

variable {ι : Type} {G : StochasticGame ι}

/-! ## The canonical owned pure-deviation row -/

/-- One actual endpoint pure-deviation row: its owner, source state and pure
action.  No response or monitoring interpretation is added. -/
abbrev EndpointOwnedPureDeviationRow (G : StochasticGame ι) :=
  Σ who : ι, G.State × G.Act who

/-- A player/action pair witnessing that canonical rows exist at every source
state.  It is needed only for `NodeFlowRows.entry_isSource`. -/
abbrev EndpointOwnedPureDeviationAnchor (G : StochasticGame ι) :=
  Σ who : ι, G.Act who

namespace EndpointOwnedPureDeviationRow

/-- The owner encoded by a canonical row. -/
def owner (row : EndpointOwnedPureDeviationRow G) : ι := row.1

/-- The source encoded by a canonical row. -/
def source (row : EndpointOwnedPureDeviationRow G) : G.State := row.2.1

/-- The actual pure action encoded by a canonical row. -/
def action (row : EndpointOwnedPureDeviationRow G) : G.Act row.owner := row.2.2

@[simp] theorem owner_mk (who : ι) (source : G.State) (action : G.Act who) :
    owner (G := G) ⟨who, source, action⟩ = who := rfl

@[simp] theorem source_mk (who : ι) (source : G.State) (action : G.Act who) :
    EndpointOwnedPureDeviationRow.source ⟨who, source, action⟩ = source := rfl

@[simp] theorem action_mk (who : ι) (source : G.State) (action : G.Act who) :
    EndpointOwnedPureDeviationRow.action ⟨who, source, action⟩ = action := rfl

end EndpointOwnedPureDeviationRow

variable [Fintype G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

open EndpointOwnedPureDeviationRow

/-- The endpoint transition coordinate of an actual owned pure deviation,
defined directly by evaluating the raw analytic obstruction row at zero. -/
def endpointPureDeviationTransition
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) : G.State → ℝ :=
  fun destination =>
    germ.rawPureDeviationStateKernelCurve
      0 row.source row.owner row.action destination

/-- The gross endpoint Bellman row payoff.  It is the raw endpoint baseline
stage payoff plus the raw endpoint pure-deviation stage gain, hence it is
target-independent and definitionally extracted from the analytic
obstruction data. -/
def endpointPureDeviationGrossGain
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) : ℝ :=
  germ.rawStageCurve 0 row.source row.owner +
    germ.rawPureDeviationStageGainCurve
      0 row.source row.owner row.action

/-- The raw baseline stage coordinate at zero is the genuine endpoint Fink
stage payoff. -/
theorem rawStageCurve_zero_apply_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm) (source : G.State) (who : ι) :
    germ.rawStageCurve 0 source who =
      G.finkStageEU germ.endpointFinkPoint source who := by
  unfold rawStageCurve finkStageEU
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro action _
  rw [germ.rawProfileWeight_zero_eq_pmfPi_endpointProfile,
    germ.finkProfile_endpointFinkPoint]

/-- The compiled raw transition is exactly the genuine endpoint deviation
PMF, coordinate by coordinate. -/
@[simp] theorem endpointPureDeviationTransition_eq_endpointFinkPoint
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) (destination : G.State) :
    germ.endpointPureDeviationTransition row destination =
      (G.finkPureDeviationStateKernel germ.endpointFinkPoint
        row.source row.owner row.action destination).toReal := by
  exact germ.rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint
    row.source row.owner row.action destination

/-- The compiled gross coordinate is the actual expected stage payoff when
the row owner plays the encoded pure action against the other endpoint mixed
actions. -/
theorem endpointPureDeviationGrossGain_eq_mixedStageEU
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) :
    germ.endpointPureDeviationGrossGain row =
      G.mixedStageEU row.source
        (Function.update
          (G.finkProfile germ.endpointFinkPoint row.source)
          row.owner (PMF.pure row.action)) row.owner := by
  rw [endpointPureDeviationGrossGain,
    germ.rawStageCurve_zero_apply_eq_endpointFinkPoint,
    germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint]
  unfold finkStageGain finkStageEU mixedStageEU
  ring

/-- Equivalent semantic decomposition of the compiled gross coordinate into
the endpoint baseline payoff and endpoint pure-deviation gain. -/
theorem endpointPureDeviationGrossGain_eq_stageEU_add_stageGain
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) :
    germ.endpointPureDeviationGrossGain row =
      G.finkStageEU germ.endpointFinkPoint row.source row.owner +
        G.finkStageGain germ.endpointFinkPoint
          row.source row.owner row.action := by
  rw [endpointPureDeviationGrossGain,
    germ.rawStageCurve_zero_apply_eq_endpointFinkPoint,
    germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint]

end AnalyticBellmanGerm

/-! ## Compilation into the declared-target gate interface -/

namespace DeclaredTargetNode

open EndpointOwnedPureDeviationRow

/-- Compile every actual owned pure deviation at every source state into the
declared-target row interface.  `anchor` only supplies the row at `node.entry`
required by `entry_isSource`; every computational field is independent of it.
-/
def endpointBellmanRows
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    NodeFlowRows node (EndpointOwnedPureDeviationRow G) where
  src := source
  transition := node.germ.endpointPureDeviationTransition
  ownerOf := owner
  grossGain := node.germ.endpointPureDeviationGrossGain
  stochastic :=
    { nonneg := fun row destination => by
        simp only [AnalyticBellmanGerm.endpointPureDeviationTransition_eq_endpointFinkPoint]
        exact ENNReal.toReal_nonneg
      row_sum := fun row => by
        simpa only [AnalyticBellmanGerm.endpointPureDeviationTransition_eq_endpointFinkPoint]
          using Math.Probability.pmf_toReal_sum_one
            (G.finkPureDeviationStateKernel node.germ.endpointFinkPoint
              row.source row.owner row.action) }
  entry_isSource :=
    ⟨⟨anchor.1, node.entry, anchor.2⟩, rfl⟩

@[simp] theorem endpointBellmanRows_src
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) :
    (node.endpointBellmanRows anchor).src row = row.source := rfl

@[simp] theorem endpointBellmanRows_ownerOf
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) :
    (node.endpointBellmanRows anchor).ownerOf row = row.owner := rfl

@[simp] theorem endpointBellmanRows_transition
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) (destination : G.State) :
    (node.endpointBellmanRows anchor).transition row destination =
      node.germ.endpointPureDeviationTransition row destination := rfl

@[simp] theorem endpointBellmanRows_grossGain
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) :
    (node.endpointBellmanRows anchor).grossGain row =
      node.germ.endpointPureDeviationGrossGain row := rfl

@[simp] theorem endpointBellmanRows_entryRow_src
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    (node.endpointBellmanRows anchor).src
      ⟨anchor.1, node.entry, anchor.2⟩ = node.entry := rfl

/-- The anchor changes only the proof of entry-row nonemptiness, hence by
proof irrelevance it does not change the compiled row system. -/
theorem endpointBellmanRows_anchor_irrel
    (node : DeclaredTargetNode G)
    (left right : EndpointOwnedPureDeviationAnchor G) :
    node.endpointBellmanRows left = node.endpointBellmanRows right := by
  rfl

/-- The target-relative charge of a compiled row contains no hand-entered
quantity: it is the raw endpoint deviation payoff minus the declared target
coordinate of that row's owner. -/
@[simp] theorem endpointBellmanRows_charge
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) :
    (node.endpointBellmanRows anchor).charge row =
      node.germ.endpointPureDeviationGrossGain row -
        node.target row.owner := rfl

/-- Semantic form of the compiled charge: actual endpoint pure-deviation
stage payoff minus the node's declared owner target. -/
theorem endpointBellmanRows_charge_eq_mixedStageEU_sub_target
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) :
    (node.endpointBellmanRows anchor).charge row =
      G.mixedStageEU row.source
          (Function.update
            (G.finkProfile node.germ.endpointFinkPoint row.source)
            row.owner (PMF.pure row.action)) row.owner -
        node.target row.owner := by
  rw [node.endpointBellmanRows_charge,
    node.germ.endpointPureDeviationGrossGain_eq_mixedStageEU]

/-- The canonical compiled rows satisfy the refutable endpoint-kernel tagging
predicate without any supplied coherence assumption. -/
theorem endpointBellmanRows_isEndpointKernelTagged
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    (node.endpointBellmanRows anchor).IsEndpointKernelTagged
      (fun row => row.action) := by
  intro row w
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro destination _
  simp only [endpointBellmanRows_src, endpointBellmanRows_ownerOf,
    endpointBellmanRows_transition,
    AnalyticBellmanGerm.endpointPureDeviationTransition_eq_endpointFinkPoint]

section Gate

variable [DecidableEq G.State]

/-- Feed the canonical analytic endpoint rows directly to the declared-target
gluing gate.  No `grossGain` argument or row-coherence hypothesis remains. -/
def endpointBellmanGluingGate
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    NodeGluingGate G (EndpointOwnedPureDeviationRow G) :=
  NodeGluingGate.of (node.endpointBellmanRows anchor)

@[simp] theorem endpointBellmanGluingGate_node
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    (node.endpointBellmanGluingGate anchor).node = node := rfl

/-- The resulting gluing gate is likewise independent of which anchor proves
that an entry row exists. -/
theorem endpointBellmanGluingGate_anchor_irrel
    (node : DeclaredTargetNode G)
    (left right : EndpointOwnedPureDeviationAnchor G) :
    node.endpointBellmanGluingGate left =
      node.endpointBellmanGluingGate right := by
  change NodeGluingGate.of (node.endpointBellmanRows left) =
    NodeGluingGate.of (node.endpointBellmanRows right)
  rw [endpointBellmanRows_anchor_irrel node left right]

/-- Endpoint tagging is retained by the compiled gluing gate. -/
theorem endpointBellmanGluingGate_isEndpointKernelTagged
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G) :
    (node.endpointBellmanGluingGate anchor).rows.IsEndpointKernelTagged
      (fun row => row.action) :=
  node.endpointBellmanRows_isEndpointKernelTagged anchor

end Gate

end DeclaredTargetNode

/-! ## Concrete inhabitation probe -/

namespace PureExternalityCycleGates

open PureExternalityCycle (game)

/-- A concrete player/action anchor for the pure-externality cycle. -/
def endpointBellmanAnchor : EndpointOwnedPureDeviationAnchor game :=
  ⟨false, false⟩

/-- The canonical all-state, all-owner, all-action endpoint rows at the
prescribed pure-externality node.  Unlike `cycleRows`, no payoff or transition
coordinate is entered by hand. -/
def canonicalPrescribedEndpointBellmanRows :
    NodeFlowRows prescribedNode (EndpointOwnedPureDeviationRow game) :=
  prescribedNode.endpointBellmanRows endpointBellmanAnchor

/-- The corresponding concrete gluing gate is inhabited. -/
def canonicalPrescribedEndpointBellmanGluingGate :
    NodeGluingGate game (EndpointOwnedPureDeviationRow game) :=
  prescribedNode.endpointBellmanGluingGate endpointBellmanAnchor

/-- The concrete canonical rows carry the endpoint tag by construction. -/
theorem canonicalPrescribedEndpointBellmanRows_isEndpointKernelTagged :
    canonicalPrescribedEndpointBellmanRows.IsEndpointKernelTagged
      (fun row => row.action) :=
  prescribedNode.endpointBellmanRows_isEndpointKernelTagged
    endpointBellmanAnchor

end PureExternalityCycleGates

end StochasticGame
end GameTheory
