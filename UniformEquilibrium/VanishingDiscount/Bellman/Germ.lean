/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Bellman.SignCell
import Math.AnalyticCoordinateCurve

/-!
# Analytic Bellman germs

This file defines the exact output of the analytic Bellman-germ existence
theorem.  An analytic Bellman germ is
one coupled analytic assignment of all strategy, value, and discount
variables.  On a positive punctured interval it solves every polynomial
Bellman equality and inequality, while its discount-complement coordinate
is exactly a positive integral power of the curve parameter.

The construction theorem consumes an analytic curve in the polynomial
Bellman solution set.  Thus the remaining foundational theorem is precisely
analytic curve selection for the selected polynomial sign cell.
-/

noncomputable section

open Math Set

namespace GameTheory
namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- A manifestly finite code for the dependent indices in `BellmanVar`. -/
abbrev BellmanVarCode :=
  (G.State × (Σ i : ι, G.Act i)) ⊕ ((G.State × ι) ⊕ Unit)

/-- `BellmanVar` is equivalent to a finite sum of finite dependent products. -/
def bellmanVarEquiv : BellmanVar G ≃ G.BellmanVarCode where
  toFun
    | .mix s i a => .inl (s, ⟨i, a⟩)
    | .val s i => .inr (.inl (s, i))
    | .disc => .inr (.inr ())
  invFun
    | .inl (s, ⟨i, a⟩) => .mix s i a
    | .inr (.inl (s, i)) => .val s i
    | .inr (.inr ()) => .disc
  left_inv v := by cases v <;> rfl
  right_inv code := by
    rcases code with code | code
    · rcases code with ⟨s, i, a⟩
      rfl
    · rcases code with code | code
      · rcases code with ⟨s, i⟩
        rfl
      · rcases code with ⟨⟩
        rfl

noncomputable instance instFintypeBellmanVar : Fintype (BellmanVar G) :=
  Fintype.ofEquiv G.BellmanVarCode G.bellmanVarEquiv.symm

/-- The continuous-linear projection to the discount-complement variable. -/
def bellmanDiscountCoordinate :
    (BellmanVar G → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj BellmanVar.disc

omit [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
@[simp]
theorem bellmanDiscountCoordinate_apply (assign : BellmanVar G → ℝ) :
    G.bellmanDiscountCoordinate assign = assign BellmanVar.disc :=
  rfl

/-- A coupled analytic germ of polynomial Bellman solutions with exact
positive-power discount coordinate. -/
structure AnalyticBellmanGerm where
  ramification : ℕ
  radius : ℝ
  assignment : ℝ → (BellmanVar G → ℝ)
  ramification_pos : 0 < ramification
  radius_pos : 0 < radius
  analytic_assignment : AnalyticAt ℝ assignment 0
  solution :
    ∀ t ∈ Ioo (0 : ℝ) radius,
      G.IsPolynomialBellmanSolution (assignment t)
  discountCoordinate :
    ∀ t ∈ Ioo (0 : ℝ) radius,
      assignment t BellmanVar.disc = t ^ ramification

namespace AnalyticBellmanGerm

variable {G}

/-- The endpoint assignment of an analytic Bellman germ. -/
def endpoint (germ : G.AnalyticBellmanGerm) : BellmanVar G → ℝ :=
  germ.assignment 0

/-- Every coordinate of the coupled assignment is analytic. -/
theorem analytic_coordinate (germ : G.AnalyticBellmanGerm)
    (v : BellmanVar G) :
    AnalyticAt ℝ (fun t => germ.assignment t v) 0 := by
  exact ((ContinuousLinearMap.proj v).analyticAt
    (germ.assignment 0)).comp germ.analytic_assignment

/-- The decoded discount factor on the germ is `1 - t ^ q`. -/
theorem bellmanDecodeDiscount_eq (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.bellmanDecodeDiscount (germ.assignment t) =
      1 - t ^ germ.ramification := by
  rw [bellmanDecodeDiscount, germ.discountCoordinate t ht]

/-- Every positive point of the germ decodes to a discounted stationary
Bellman equilibrium at discount factor `1 - t ^ q`. -/
theorem isDiscountedStationaryBellmanEq (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    G.IsDiscountedStationaryBellmanEq
      (1 - t ^ germ.ramification)
      (G.bellmanDecodeProfile (germ.solution t ht))
      (G.bellmanDecodeValue (germ.assignment t)) := by
  have h :=
    G.isDiscountedStationaryBellmanEq_bellmanDecode
      (germ.solution t ht)
  rwa [germ.bellmanDecodeDiscount_eq ht] at h

end AnalyticBellmanGerm

/-- An exact-power analytic curve in the polynomial Bellman solution set
produces an analytic Bellman germ with the prescribed endpoint. -/
theorem exists_analyticBellmanGerm_of_powerCurve
    {assign₀ : BellmanVar G → ℝ}
    (hcurve :
      HasAnalyticPowerCurveAt G.polynomialBellmanSolutionSet
        G.bellmanDiscountCoordinate assign₀) :
    ∃ germ : G.AnalyticBellmanGerm,
      germ.endpoint = assign₀ := by
  obtain ⟨q, gamma, eta, hq, heta, hgamma, _hgamma0, hmem⟩ := hcurve
  refine ⟨
    { ramification := q
      radius := eta
      assignment := gamma
      ramification_pos := hq
      radius_pos := heta
      analytic_assignment := hgamma
      solution := fun t ht => (hmem t ht).1
      discountCoordinate := fun t ht => by
        simpa using (hmem t ht).2 },
    _hgamma0⟩

/-- A chosen analytic Bellman germ supplied by an exact-power curve. -/
noncomputable def analyticBellmanGermOfPowerCurve
    {assign₀ : BellmanVar G → ℝ}
    (hcurve :
      HasAnalyticPowerCurveAt G.polynomialBellmanSolutionSet
        G.bellmanDiscountCoordinate assign₀) :
    G.AnalyticBellmanGerm :=
  (G.exists_analyticBellmanGerm_of_powerCurve hcurve).choose

@[simp]
theorem analyticBellmanGermOfPowerCurve_endpoint
    {assign₀ : BellmanVar G → ℝ}
    (hcurve :
      HasAnalyticPowerCurveAt G.polynomialBellmanSolutionSet
        G.bellmanDiscountCoordinate assign₀) :
    (G.analyticBellmanGermOfPowerCurve hcurve).endpoint = assign₀ :=
  (G.exists_analyticBellmanGerm_of_powerCurve hcurve).choose_spec

/-- A positive-coordinate analytic arc in the polynomial Bellman solution
set produces an analytic Bellman germ after exact-power normalization. -/
theorem exists_analyticBellmanGerm_of_positiveCoordinateArc
    {assign₀ : BellmanVar G → ℝ}
    (harc :
      HasPositiveCoordinateAnalyticArcAt
        G.polynomialBellmanSolutionSet
        G.bellmanDiscountCoordinate assign₀) :
    ∃ germ : G.AnalyticBellmanGerm,
      germ.endpoint = assign₀ := by
  obtain ⟨q, gamma, eta, hq, heta, hgamma, hgamma0, hmem⟩ :=
    harc.toHasAnalyticPowerCurveAt
  let germ : G.AnalyticBellmanGerm :=
    { ramification := q
      radius := eta
      assignment := gamma
      ramification_pos := hq
      radius_pos := heta
      analytic_assignment := hgamma
      solution := fun t ht => (hmem t ht).1
      discountCoordinate := fun t ht => by
        simpa using (hmem t ht).2 }
  exact ⟨germ, hgamma0⟩

end StochasticGame
end GameTheory
