/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringInstances
import GameTheory.Concepts.Repeated.MonitoringRank
import GameTheory.Concepts.Stochastic.AnalyticEndpointBellmanRowCompiler

/-!
# Transition Monitoring for Fink/Bellman Rows

At a fixed source state of a stochastic game, transition monitoring exposes
only the publicly observed successor state.  A pure stage profile therefore
induces the original transition kernel.  After behavioral lifting, a mixed
stage profile induces the action-mixture of transition kernels.

For a decoded Fink profile, those two signal laws are definitionally the
baseline Fink state kernel and each pure unilateral-deviation state kernel.
Consequently the monitoring deviation vector is exactly the genuine Fink
transition difference.  At an analytic endpoint, its deviating signal law is
exactly the raw transition row compiled by
`AnalyticEndpointBellmanRowCompiler`.

## Deliberate boundary

This is a one-step observability adapter.  The signal records the successor
state, not the joint action, and the source state is fixed externally.  The
module does not construct a history-dependent monitor, a continuation payoff,
a legal public response, a punishment, or a recursive closer.  It supplies
concrete signal vectors for the existing finite-dimensional tools once the
relevant row family and rank hypotheses are provided; strategic realization
remains separate.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.PMFProduct

variable {ι : Type} {G : StochasticGame ι}

/-- Public monitoring of one transition from a fixed source state.  The
public signal is precisely the successor state. -/
@[reducible] def transitionMonitoring (G : StochasticGame ι)
    (source : G.State) : (G.stageGame source).PublicMonitoring where
  Signal := G.State
  signalKernel := G.transition source

@[simp] theorem transitionMonitoring_signalKernel
    (G : StochasticGame ι) (source : G.State) (action : G.JointAct) :
    (G.transitionMonitoring source).signalKernel action =
      G.transition source action :=
  rfl

/-- The behavioral lift first samples the independently mixed joint action
and then samples its successor state. -/
@[simp] theorem transitionMonitoring_mixedExtension_signalKernel
    (G : StochasticGame ι) [Fintype ι]
    (source : G.State) (mixed : ∀ who, PMF (G.Act who)) :
    (G.transitionMonitoring source).mixedExtension.signalKernel mixed =
      (pmfPi mixed).bind (G.transition source) :=
  rfl

section FinkRows

variable [Fintype G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]

omit [DecidableEq ι] in
/-- Under transition monitoring, the decoded mixed Fink profile generates
exactly its genuine baseline state kernel. -/
@[simp] theorem transitionMonitoring_signalKernel_finkProfile
    {U : ℝ} (z : G.finkDomain U) (source : G.State) :
    (G.transitionMonitoring source).mixedExtension.signalKernel
        (G.finkProfile z source) =
      G.finkStateKernel z source :=
  rfl

/-- Replacing one component by a pure action generates exactly the genuine
Fink pure-deviation state kernel. -/
@[simp] theorem transitionMonitoring_signalKernel_finkPureDeviation
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (owner : ι) (action : G.Act owner) :
    (G.transitionMonitoring source).mixedExtension.signalKernel
        (Function.update (G.finkProfile z source)
          owner (PMF.pure action)) =
      G.finkPureDeviationStateKernel z source owner action :=
  rfl

/-- One monitoring deviation row is exactly the coordinatewise difference
between the genuine pure-deviation and baseline Fink transition kernels. -/
theorem transitionMonitoring_deviationSignalVector_finkPureDeviation
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (owner : ι) (action : G.Act owner) :
    (G.transitionMonitoring source).mixedExtension.deviationSignalVector
        (G.finkProfile z source) owner (PMF.pure action) =
      fun destination =>
        (G.finkPureDeviationStateKernel z source owner action
          destination).toReal -
        (G.finkStateKernel z source destination).toReal := by
  funext destination
  rfl

/-- The same row evaluated against a scalar continuation score is the
difference of its Fink deviation and baseline continuation expectations. -/
theorem sum_transitionMonitoring_deviationSignalVector_mul
    {U : ℝ} (z : G.finkDomain U) (source : G.State)
    (owner : ι) (action : G.Act owner) (score : G.State → ℝ) :
    ∑ destination,
        (G.transitionMonitoring source).mixedExtension.deviationSignalVector
            (G.finkProfile z source) owner (PMF.pure action) destination *
          score destination =
      Math.Probability.expect
          (G.finkPureDeviationStateKernel z source owner action) score -
        Math.Probability.expect (G.finkStateKernel z source) score := by
  rw [transitionMonitoring_deviationSignalVector_finkPureDeviation]
  simp only [Finset.sum_sub_distrib, sub_mul]
  rw [Math.Probability.expect_eq_sum, Math.Probability.expect_eq_sum]

end FinkRows

section EndpointRows

variable [Fintype G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)] [∀ who, DecidableEq (G.Act who)]

open EndpointOwnedPureDeviationRow

/-- At the analytic endpoint, the raw compiled Bellman transition row is
exactly the real coordinate of the transition-monitoring signal law generated
by its encoded unilateral pure action. -/
theorem endpointPureDeviationTransition_eq_transitionMonitoring
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) (destination : G.State) :
    germ.endpointPureDeviationTransition row destination =
      ((G.transitionMonitoring row.source).mixedExtension.signalKernel
        (Function.update
          (G.finkProfile germ.endpointFinkPoint row.source)
          row.owner (PMF.pure row.action)) destination).toReal := by
  rw [transitionMonitoring_signalKernel_finkPureDeviation,
    germ.endpointPureDeviationTransition_eq_endpointFinkPoint]

/-- Thus the endpoint monitoring deviation vector is the compiled raw
Bellman row minus the genuine endpoint baseline transition row. -/
theorem transitionMonitoring_deviationSignalVector_endpoint
    (germ : G.AnalyticBellmanGerm)
    (row : EndpointOwnedPureDeviationRow G) (destination : G.State) :
    (G.transitionMonitoring row.source).mixedExtension.deviationSignalVector
        (G.finkProfile germ.endpointFinkPoint row.source)
        row.owner (PMF.pure row.action) destination =
      germ.endpointPureDeviationTransition row destination -
        (G.finkStateKernel germ.endpointFinkPoint row.source
          destination).toReal := by
  rw [transitionMonitoring_deviationSignalVector_finkPureDeviation,
    germ.endpointPureDeviationTransition_eq_endpointFinkPoint]

/-- The canonical declared-target row compiler retains the same exact
transition-monitoring interpretation.  The anchor is only the pre-existing
entry-row nonemptiness witness. -/
theorem DeclaredTargetNode.endpointBellmanRows_transition_eq_transitionMonitoring
    (node : DeclaredTargetNode G)
    (anchor : EndpointOwnedPureDeviationAnchor G)
    (row : EndpointOwnedPureDeviationRow G) (destination : G.State) :
    (node.endpointBellmanRows anchor).transition row destination =
      ((G.transitionMonitoring row.source).mixedExtension.signalKernel
        (Function.update
          (G.finkProfile node.germ.endpointFinkPoint row.source)
          row.owner (PMF.pure row.action)) destination).toReal := by
  rw [node.endpointBellmanRows_transition,
    endpointPureDeviationTransition_eq_transitionMonitoring]

end EndpointRows

end StochasticGame
end GameTheory
