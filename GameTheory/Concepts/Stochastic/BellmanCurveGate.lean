/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BellmanGerm
import GameTheory.Concepts.Stochastic.FinkLimit
import Math.Probability

/-!
# The curve-selection gate for polynomial Bellman equilibria

This file proves that every finite stochastic game has a vanishing-discount
endpoint in the closure of its polynomial Bellman solution set.  It then
reduces that endpoint to one complete polynomial sign cell and states the
single-cell analytic selection hypothesis needed to construct an analytic
Bellman germ.

No selection principle is assumed in the closure and sign-cell theorems.
The final conditional theorem makes the remaining real-algebraic input
literal: an analytic arc must be selected in the one coupled Bellman cell.
-/

noncomputable section

open Filter Math Math.Probability Math.PolynomialSignCell Set Topology

namespace GameTheory
namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G.Act i)] in
/-- Convergent Fink points and discount factors give a convergent sequence
of their complete polynomial Bellman assignments. -/
theorem tendsto_bellmanAssignment_fink
    {U : ℝ} {β : ℕ → ℝ} {βlim : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hβ : Tendsto β atTop (𝓝 βlim))
    (hz : Tendsto z atTop (𝓝 zlim)) :
    Tendsto
      (fun n =>
        G.bellmanAssignment (G.finkProfile (z n))
          (G.finkValue (z n)) (β n))
      atTop
      (𝓝
        (G.bellmanAssignment (G.finkProfile zlim)
          (G.finkValue zlim) βlim)) := by
  apply tendsto_pi_nhds.2
  intro v
  cases v with
  | mix s i a =>
      simpa [bellmanAssignment] using
        G.tendsto_finkStrategyWeight_apply hz s i a
  | val s i =>
      simpa [bellmanAssignment] using
        G.tendsto_finkValue_apply hz s i
  | disc =>
      simpa [bellmanAssignment] using tendsto_const_nhds.sub hβ

/-- At a fixed payoff bound, compact Fink selection supplies a Bellman
assignment with zero discount-complement coordinate in the closure of the
positive-discount polynomial solution set. -/
theorem exists_vanishingDiscount_bellmanEndpoint_of_bound
    [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure G.polynomialBellmanSolutionSet := by
  obtain ⟨z, zlim, φ, hfix, _hφ, hzlim, hβlim⟩ :=
    G.exists_convergent_approachOne_finkFixedPoint_subsequence
      U hU hpay
  let assign : ℕ → BellmanVar G → ℝ := fun n =>
    G.bellmanAssignment
      (G.finkProfile (z (φ n)))
      (G.finkValue (z (φ n)))
      (approachOneDiscount (φ n))
  let assign₀ : BellmanVar G → ℝ :=
    G.bellmanAssignment (G.finkProfile zlim)
      (G.finkValue zlim) 1
  have htend : Tendsto assign atTop (𝓝 assign₀) := by
    exact G.tendsto_bellmanAssignment_fink hβlim hzlim
  have hsolution :
      ∀ n, assign n ∈ G.polynomialBellmanSolutionSet := by
    intro n
    change G.IsPolynomialBellmanSolution (assign n)
    apply G.isPolynomialBellmanSolution_bellmanAssignment
    apply G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
      (approachOneDiscount (φ n)) U
      (approachOneDiscount_nonneg (φ n))
      (approachOneDiscount_le_one (φ n)) hpay
      (z (φ n))
    exact hfix (φ n)
  refine ⟨assign₀, ?_, mem_closure_of_tendsto htend
    (Eventually.of_forall hsolution)⟩
  simp [assign₀, bellmanAssignment]

/-- Finiteness of the game data supplies the payoff bound in
`exists_vanishingDiscount_bellmanEndpoint_of_bound`. -/
theorem exists_vanishingDiscount_bellmanEndpoint
    [∀ i, Nonempty (G.Act i)] :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure G.polynomialBellmanSolutionSet := by
  let payoffCoordinate : G.State × G.JointAct × ι → ℝ := fun p =>
    G.stagePayoff p.1 p.2.1 p.2.2
  obtain ⟨C, hC⟩ :=
    exists_abs_bound_of_finite payoffCoordinate
  let U : ℝ := max C 0
  have hU : 0 ≤ U := le_max_right C 0
  have hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U := by
    intro s a who
    exact (hC (s, a, who)).trans (le_max_left C 0)
  exact G.exists_vanishingDiscount_bellmanEndpoint_of_bound
    U hU hpay

/-- Every game has a vanishing-discount endpoint and one complete Bellman
sign cell approaching it from within the polynomial solution set. -/
theorem exists_vanishingDiscount_bellmanSignCell
    [∀ i, Nonempty (G.Act i)] :
    ∃ (assign₀ : BellmanVar G → ℝ)
        (τ : SignPattern G.BellmanConstraint),
      assign₀ BellmanVar.disc = 0 ∧
        signCell G.bellmanConstraintPoly τ ⊆
          G.polynomialBellmanSolutionSet ∧
        assign₀ ∈ closure
          (signCell G.bellmanConstraintPoly τ) := by
  obtain ⟨assign₀, hdisc, hclosure⟩ :=
    G.exists_vanishingDiscount_bellmanEndpoint
  obtain ⟨τ, hsubset, hcell⟩ :=
    G.exists_bellmanSignCell_subset_of_mem_closure hclosure
  exact ⟨assign₀, τ, hdisc, hsubset, hcell⟩

/-- The exact remaining Gate G property: every selected Bellman sign cell
approaching a zero-discount endpoint admits one coupled analytic right arc
whose discount coordinate becomes positive. -/
def HasBellmanSignCellCurveSelection : Prop :=
  ∀ (assign₀ : BellmanVar G → ℝ)
      (τ : SignPattern G.BellmanConstraint),
    assign₀ BellmanVar.disc = 0 →
    assign₀ ∈ closure
      (signCell G.bellmanConstraintPoly τ) →
    HasPositiveCoordinateAnalyticArcAt
      (signCell G.bellmanConstraintPoly τ)
      G.bellmanDiscountCoordinate assign₀

/-- Sign-compatible analytic curve selection constructs an analytic Bellman
germ for every finite game. -/
theorem exists_analyticBellmanGerm
    [∀ i, Nonempty (G.Act i)]
    (hselection : G.HasBellmanSignCellCurveSelection) :
    Nonempty G.AnalyticBellmanGerm := by
  obtain ⟨assign₀, τ, hdisc, hsubset, hclosure⟩ :=
    G.exists_vanishingDiscount_bellmanSignCell
  have harcCell :=
    hselection assign₀ τ hdisc hclosure
  have harcSolution :=
    harcCell.mono hsubset
  exact
    ⟨G.analyticBellmanGermOfPowerCurve
      harcSolution.toHasAnalyticPowerCurveAt⟩

end StochasticGame
end GameTheory
