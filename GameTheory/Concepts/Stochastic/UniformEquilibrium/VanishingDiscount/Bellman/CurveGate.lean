/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Bellman.Germ
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Limit
import Math.CoordinatewisePuiseuxCurve
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
strictly positive-discount polynomial solution set. -/
theorem exists_vanishingDiscount_bellmanEndpoint_pos_of_bound
    [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure
          (G.polynomialBellmanSolutionSet ∩
            {assign | 0 < assign BellmanVar.disc}) := by
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
  have hdisc_pos :
      ∀ n, 0 < assign n BellmanVar.disc := by
    intro n
    simp only [assign, bellmanAssignment]
    exact sub_pos.mpr (approachOneDiscount_lt_one (φ n))
  refine ⟨assign₀, ?_, mem_closure_of_tendsto htend
    (Eventually.of_forall fun n => ⟨hsolution n, hdisc_pos n⟩)⟩
  simp [assign₀, bellmanAssignment]

/-- Forgetting strict positivity recovers the ordinary endpoint theorem. -/
theorem exists_vanishingDiscount_bellmanEndpoint_of_bound
    [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure G.polynomialBellmanSolutionSet := by
  obtain ⟨assign₀, hdisc, hclosure⟩ :=
    G.exists_vanishingDiscount_bellmanEndpoint_pos_of_bound U hU hpay
  exact ⟨assign₀, hdisc,
    closure_mono inter_subset_left hclosure⟩

/-- Finiteness of the game data supplies the payoff bound in
`exists_vanishingDiscount_bellmanEndpoint_of_bound`. -/
theorem exists_vanishingDiscount_bellmanEndpoint_pos
    [∀ i, Nonempty (G.Act i)] :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure
          (G.polynomialBellmanSolutionSet ∩
            {assign | 0 < assign BellmanVar.disc}) := by
  let payoffCoordinate : G.State × G.JointAct × ι → ℝ := fun p =>
    G.stagePayoff p.1 p.2.1 p.2.2
  obtain ⟨C, hC⟩ :=
    exists_abs_bound_of_finite payoffCoordinate
  let U : ℝ := max C 0
  have hU : 0 ≤ U := le_max_right C 0
  have hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U := by
    intro s a who
    exact (hC (s, a, who)).trans (le_max_left C 0)
  exact G.exists_vanishingDiscount_bellmanEndpoint_pos_of_bound
    U hU hpay

/-- The positive endpoint theorem implies the ordinary closure statement. -/
theorem exists_vanishingDiscount_bellmanEndpoint
    [∀ i, Nonempty (G.Act i)] :
    ∃ assign₀ : BellmanVar G → ℝ,
      assign₀ BellmanVar.disc = 0 ∧
        assign₀ ∈ closure G.polynomialBellmanSolutionSet := by
  obtain ⟨assign₀, hdisc, hclosure⟩ :=
    G.exists_vanishingDiscount_bellmanEndpoint_pos
  exact ⟨assign₀, hdisc,
    closure_mono inter_subset_left hclosure⟩

/-- Every game has a vanishing-discount endpoint and one complete Bellman
sign cell approaching it through strictly positive discount complement. -/
theorem exists_vanishingDiscount_bellmanSignCell
    [∀ i, Nonempty (G.Act i)] :
    ∃ (assign₀ : BellmanVar G → ℝ)
        (τ : SignPattern G.BellmanConstraint),
      assign₀ BellmanVar.disc = 0 ∧
        signCell G.bellmanConstraintPoly τ ⊆
          G.polynomialBellmanSolutionSet ∧
        assign₀ ∈ closure
          (signCell G.bellmanConstraintPoly τ ∩
            {assign | 0 < assign BellmanVar.disc}) := by
  obtain ⟨assign₀, hdisc, hclosure⟩ :=
    G.exists_vanishingDiscount_bellmanEndpoint_pos
  let T :=
    selectedPatterns G.bellmanConstraintPoly
      G.polynomialBellmanSolutionSet
  have hrepresentation :
      G.polynomialBellmanSolutionSet =
        ⋃ τ ∈ T, signCell G.bellmanConstraintPoly τ := by
    exact signInvariant_eq_iUnion_signCell
      G.signInvariant_polynomialBellmanSolutionSet
  have hpositiveRepresentation :
      G.polynomialBellmanSolutionSet ∩
          {assign | 0 < assign BellmanVar.disc} =
        ⋃ τ ∈ T,
          signCell G.bellmanConstraintPoly τ ∩
            {assign | 0 < assign BellmanVar.disc} := by
    rw [hrepresentation]
    simp only [iUnion_inter]
  rw [hpositiveRepresentation,
    T.closure_biUnion
      (fun τ =>
        signCell G.bellmanConstraintPoly τ ∩
          {assign | 0 < assign BellmanVar.disc})] at hclosure
  rw [Set.mem_iUnion] at hclosure
  obtain ⟨τ, hclosure⟩ := hclosure
  rw [Set.mem_iUnion] at hclosure
  obtain ⟨hτ, hcell⟩ := hclosure
  have hsubset :
      signCell G.bellmanConstraintPoly τ ⊆
        G.polynomialBellmanSolutionSet := by
    apply signCell_subset_of_mem_selectedPatterns
      G.signInvariant_polynomialBellmanSolutionSet
    simpa [T] using hτ
  exact ⟨assign₀, τ, hdisc, hsubset, hcell⟩

/-- Coordinatewise Newton--Puiseux data for one selected curve in every
Bellman sign cell.

The same unramified curve occurs in every coordinate. The coordinatewise
denominators may differ; finiteness synchronizes them automatically. -/
def HasBellmanCoordinatewisePuiseuxSelection : Prop :=
  ∀ (assign₀ : BellmanVar G → ℝ)
      (τ : SignPattern G.BellmanConstraint),
    assign₀ BellmanVar.disc = 0 →
    assign₀ ∈ closure
      (signCell G.bellmanConstraintPoly τ ∩
        {assign | 0 < assign BellmanVar.disc}) →
    HasCoordinatewiseRamifiedSelectionAt
      (signCell G.bellmanConstraintPoly τ)
      G.bellmanDiscountCoordinate assign₀

/-- The exact remaining germ-existence property: every selected Bellman sign cell
approaching a zero-discount endpoint admits one coupled analytic right arc
whose discount coordinate becomes positive. -/
def HasBellmanSignCellCurveSelection : Prop :=
  ∀ (assign₀ : BellmanVar G → ℝ)
      (τ : SignPattern G.BellmanConstraint),
    assign₀ BellmanVar.disc = 0 →
    assign₀ ∈ closure
      (signCell G.bellmanConstraintPoly τ ∩
        {assign | 0 < assign BellmanVar.disc}) →
    HasPositiveCoordinateAnalyticArcAt
      (signCell G.bellmanConstraintPoly τ)
      G.bellmanDiscountCoordinate assign₀

/-- Coordinatewise convergent Puiseux expansions of one selected Bellman
curve synchronize to the coupled analytic arc required by analytic
Bellman-germ existence. -/
theorem HasBellmanCoordinatewisePuiseuxSelection.toSignCellCurveSelection
    (h : G.HasBellmanCoordinatewisePuiseuxSelection) :
    G.HasBellmanSignCellCurveSelection := by
  intro assign₀ τ hdisc hclosure
  exact
    (h assign₀ τ hdisc hclosure).toPositiveCoordinateAnalyticArc
      hdisc

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

/-- Coordinatewise convergent Newton--Puiseux for one common selected curve
is sufficient for an analytic Bellman germ. -/
theorem exists_analyticBellmanGerm_of_coordinatewisePuiseuxSelection
    [∀ i, Nonempty (G.Act i)]
    (hselection : G.HasBellmanCoordinatewisePuiseuxSelection) :
    Nonempty G.AnalyticBellmanGerm :=
  G.exists_analyticBellmanGerm hselection.toSignCellCurveSelection

end StochasticGame
end GameTheory
