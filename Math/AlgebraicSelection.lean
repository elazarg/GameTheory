/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Piecewise monotonicity of algebraically-selected functions

A continuous function `w` that is implicitly defined near `0` by a nonzero bivariate polynomial
`P (v, λ) = 0` cannot oscillate infinitely often as `λ → 0⁺`: the "bad" locus where the implicit
function theorem could fail (double roots of `P` in `v`, or where a chosen auxiliary polynomial
vanishes along the curve `λ ↦ (λ, w λ)`) is contained in the zero set of a single nonzero
univariate polynomial, hence is finite. This is the analytic input that turns "the discounted
value is algebraic in the discount" into the bounded-variation hypothesis of Mertens–Neyman-style
vanishing-discount arguments.

## Convention

We represent a bivariate polynomial as `P : Polynomial (Polynomial ℝ)`: the *outer* variable is
`v` (the value being selected, i.e. `w λ`), and the coefficients live in `ℝ[λ]`. Concretely,
`P = ∑ i, C (a i) * v ^ i` with `a i : Polynomial ℝ`. The point `(v, λ) = (y, lam)` is evaluated
via `bivEval P lam y`, defined below by first specialising each coefficient `a i` at `λ = lam`
(via `Polynomial.evalRingHom`) and then evaluating the resulting real polynomial in `v` at `y`.
This convention was chosen because `Polynomial.resultant`, viewed with `R := Polynomial ℝ` as the
base (commutative) ring, directly computes an elimination polynomial *in `λ`* from two polynomials
*in `v`* over `ℝ[λ]` — exactly the object needed to bound "bad" loci in `λ` by a univariate
polynomial's root set.

## Mathlib inventory (as of this file's construction)

* `Polynomial.resultant` (`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`) is defined for
  polynomials over any `CommRing`, as the determinant of the Sylvester matrix, with `natDegree`
  bounds `m n : ℕ` as `optParam`s. Depth is substantial: `resultant_map_map` (resultants commute
  with ring homomorphisms — the key elimination-theory fact used below), `resultant_eq_zero_iff`
  (over a *field*: `resultant f g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g`, at the *default*
  `natDegree` bounds), `resultant_add_left_deg` / `resultant_add_right_deg` (relating the resultant
  at inflated degree bounds to the resultant at the actual `natDegree`s, needed because a
  specialised coefficient can cancel the leading term). There is no "resultant = 0 iff common
  root" restated directly (over a general field the correct statement is in terms of `IsCoprime`,
  since roots may not exist in the base field); the common-root direction we need is supplied by
  `Polynomial.aeval_ne_zero_of_isCoprime`.
* `Polynomial.finite_setOf_isRoot : p ≠ 0 → {x | p.IsRoot x}.Finite` (`Mathlib/Algebra/Polynomial/
  Roots.lean`) gives finiteness of a nonzero real polynomial's zero set directly as a `Set`
  statement (no need to go through `Polynomial.roots : Multiset`).
* No `Squarefree`-specific API was needed: working with `resultant P Q ≠ 0` as a hypothesis
  (rather than "`P` squarefree in `v`") is both what the resultant machinery naturally produces
  and matches the file's design rule of preferring "∃ nonzero univariate polynomial containing the
  bad set" hypotheses.
* The implicit function theorem is available in exactly the shape needed for a curried bivariate
  function at `Mathlib/Analysis/Calculus/ImplicitFunction/Bivariate.lean`
  (`implicitFunctionOfBivariate`, with derivative formula
  `hasStrictFDerivAt_implicitFunctionOfBivariate :
  HasStrictFDerivAt ψ (-(f₂ u).inverse ∘L f₁ u) u.1`
  and the local-uniqueness fact `eventually_apply_eq_iff_implicitFunctionOfBivariate`, which is
  exactly the "continuous selection through simple roots is locally the IFT branch" ingredient).
  It *is* instantiated below (`hasDerivAt_of_polynomial_root`), only *locally* at a single point:
  the derivative formula it produces is combined with the *global* sign-constancy fact
  (`eventually_sign_constant_of_polynomial`) instead of any branch-matching/gluing argument, which
  is what lets the headline theorem land without the "glue monotone pieces across the excluded
  set" step originally anticipated. Turning `bivEval P lam y` into `HasFDerivAt` data in each
  argument separately needed `bivDerivLam` (the coefficient-wise `λ`-derivative of `P`, a new
  bivariate polynomial) plus term-by-term differentiation via `bivEval_eq_sum`; matching the
  resulting `ℝ →L[ℝ] ℝ` derivatives against `ContinuousLinearMap.toSpanSingleton`/
  `ContinuousLinearEquiv.unitsEquivAut` supplied the joint continuity and invertibility
  side-conditions the bivariate IFT API asks for.
* `BoundedVariationOn` / `MonotoneOn.boundedVariationOn` (`Mathlib/Topology/EMetricSpace/
  BoundedVariation.lean`) give bounded variation directly from monotonicity plus a bound; there is
  no ready-made `AntitoneOn.boundedVariationOn`, but it is one line from
  `MonotoneOn.boundedVariationOn` applied to `-f` composed with the fact that negation is
  `1`-Lipschitz (`LipschitzWith.comp_boundedVariationOn`). `eVariationOn.edist_le` /
  `BoundedVariationOn.dist_le` bound a value difference by the variation on *any* subset containing
  both points — in particular on `Set.uIcc a b`, which is the "interval control regardless of
  order" fact a non-monotone index needs; `Set.OrdConnected.uIcc_subset` (with
  `Set.ordConnected_Ioo`) transports this from the whole eventually-monotone interval down to
  `uIcc a b`.
* `IsPreconnected.intermediate_value` (`Mathlib/Topology/Order/IntermediateValue.lean`) gives "a
  continuous, nowhere-zero, real-valued function on a preconnected set has one fixed strict sign"
  in a couple of lines (`constant_sign_of_continuousOn_of_ne_zero` below), by contradiction against
  the two possible sign changes; this is the engine behind
  `eventually_sign_constant_of_polynomial`. (`IsPreconnected.constant` /
  `Mathlib/Topology/Instances/Sign.lean`'s `SignType.sign` machinery was investigated as an
  alternative route but the direct IVT argument was more economical here.)
* The "vanishing oscillation near an excluded endpoint" fact ultimately did not need
  `MonotoneOn.tendsto_nhdsWithin_Ioo_left` (stated for the *right* endpoint of an `Ioo`) or any
  endpoint reflection at all: `BoundedVariationOn.tendsto_eVariationOn_Ioc_zero` (`Mathlib/Topology/
  EMetricSpace/BoundedVariation.lean`) directly gives "variation on small open-closed intervals to
  the right of a point → 0" for *any* bounded-variation function (monotone is a special case, via
  `MonotoneOn.boundedVariationOn`), which is exactly the shape needed at the left endpoint `0` of
  `Set.Ioo 0 ρ'` — see `eventually_tendsto_eVariationOn_nhds_zero_of_polynomial_root`.

## Main declarations

* `bivEval`: evaluate `P : Polynomial (Polynomial ℝ)` at `(λ, v) = (lam, y)`.
* `resultant_eval_eq_zero_or_leadingCoeff_eval_eq_zero`: if `P (lam, y) = Q (lam, y) = 0` then
  either `lam` is a root of `resultant P Q` (an element of `Polynomial ℝ`), or of `P`'s `v`-leading
  coefficient — the core elimination-theory fact.
* `finite_bivEval_common_zero`: consequently, if `P ≠ 0` and `resultant P Q ≠ 0`, the set of `lam`
  at which `P` and `Q` have a common `v`-root is finite.
* `eventually_sign_constant_of_polynomial`: for `P ≠ 0` with `resultant P Q ≠ 0` and `w`
  implicitly selected by `P`, the sign of `Q (lam, w lam)` is eventually constant as `lam → 0⁺`.
* `bivDerivLam`: the coefficient-wise `λ`-derivative of a bivariate polynomial (the "other half"
  of the total derivative, alongside `Polynomial.derivative` for the `v`-direction).
* `hasDerivAt_of_polynomial_root`: the *only* place the implicit function theorem is invoked, and
  only locally — gives `w`'s derivative in closed form, `-∂_λP / ∂ᵥP`, wherever `∂ᵥP ≠ 0`.
* `eventually_monotone_of_polynomial_root` (**the headline theorem**): under the setup, plus
  `resultant P (Polynomial.derivative P) ≠ 0` and `resultant P (bivDerivLam P) ≠ 0`, `w` is
  eventually `MonotoneOn`/`AntitoneOn` as `λ → 0⁺`.
* `boundedVariationOn_of_polynomial_root`: the same, plus boundedness of `w`, gives
  `BoundedVariationOn`.
* `dist_le_eVariationOn_uIcc_of_polynomial_root`: the interval-control export — `|w a - w b|` is
  bounded by the total variation on `Set.uIcc a b`, for `a, b` in either order.
* `eventually_tendsto_eVariationOn_nhds_zero_of_polynomial_root`:
  `eVariationOn w (Set.Ioo 0 δ) → 0` as `δ → 0⁺`. Proved via `BoundedVariationOn.
  tendsto_eVariationOn_Ioc_zero` at `0` (variation on small open-closed intervals to the right of a
  point vanishes for a bounded-variation function), transported from `nhdsWithin 0 (Set.Ioo 0 ρ')`
  to `nhdsWithin 0 (Set.Ioi 0)` via `nhdsWithin_inter_of_mem'`, then squeezed against
  `eVariationOn.mono`.
* `tailEVariation_vanishes_of_polynomial_root`: the Mertens–Neyman-facing scalar packaging of the
  above in explicit `ε`–`δ` form — the per-coordinate feeder for `MertensNeymanCriterion.
  StochasticGame.IsTailVariationBounded`.
* `puiseuxDerivativeEnvelope_of_rpow_reparam`: a local representation
  `w(λ) = g(λ^q)` with `q > 0` and bounded `g'` gives the exact normalized
  derivative envelope consumed by the account construction.
* `puiseuxDerivativeEnvelope_of_analytic_rpow_reparam`: analyticity of the
  reparameterized factor supplies that local derivative and bound
  automatically.
* `puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root`: if the
  ramified factor `g` is a simple polynomial root at zero, its derivative
  and bound are derived automatically.
* `tendsto_zero_of_rpow_reparam`: if the same regular factor `g` is continuous
  at zero, the selected branch tends to `g(0)` from positive rates.
* `puiseuxDerivativeEnvelope_of_regular_polynomial_root`: a polynomial branch
  that stays a simple root at its limiting point needs no fractional
  reparameterization; it has the required envelope with exponent `q = 1`.

No `TODO`s remain in this file.
-/

open Polynomial Set Topology

namespace Math

/-- Two real-analytic germs have an eventually fixed comparison on the right: they either agree,
or one is strictly below the other. This is the analytic core of finite Puiseux-hierarchy
stabilization after a common ramification has turned all branches into ordinary analytic
functions. -/
theorem analyticAt_eventually_eq_or_lt_or_gt
    {f g : ℝ → ℝ} {x₀ : ℝ}
    (hf : AnalyticAt ℝ f x₀) (hg : AnalyticAt ℝ g x₀) :
    (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), f x = g x) ∨
      (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), f x < g x) ∨
      (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), g x < f x) := by
  let d : ℝ → ℝ := f - g
  have hd : AnalyticAt ℝ d x₀ := hf.sub hg
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · left
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds] with x hx
    simpa [d, sub_eq_zero] using hx
  · have hnotzero : ¬∀ᶠ x in 𝓝 x₀, d x = 0 := by
      intro h
      have hz : ∀ᶠ x in 𝓝[≠] x₀, d x = 0 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨x, hne, heq⟩ := (hnonzero.and hz).exists
      exact hne heq
    obtain ⟨n, u, hu, hu0, hfactor⟩ :=
      hd.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
    rcases lt_or_gt_of_ne hu0.symm with hu0pos | hu0neg
    · right
      right
      have hupos : ∀ᶠ x in 𝓝 x₀, 0 < u x :=
        hu.continuousAt.tendsto.eventually_const_lt hu0pos
      filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
        hupos.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with x hfac hux hx
      have hxpos : 0 < x - x₀ := sub_pos.mpr hx
      have hpow : 0 < (x - x₀) ^ n := pow_pos hxpos n
      change f x - g x = (x - x₀) ^ n * u x at hfac
      change g x < f x
      nlinarith
    · right
      left
      have huneg : ∀ᶠ x in 𝓝 x₀, u x < 0 :=
        hu.continuousAt.tendsto.eventually_lt_const hu0neg
      filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
        huneg.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with x hfac hux hx
      have hxpos : 0 < x - x₀ := sub_pos.mpr hx
      have hpow : 0 < (x - x₀) ^ n := pow_pos hxpos n
      change f x - g x = (x - x₀) ^ n * u x at hfac
      change f x < g x
      nlinarith

/-- A finite family of real-analytic germs has one common right neighborhood on which every
    pairwise weak comparison has a fixed truth value. The resulting relation records the stable
    total preorder of the family. -/
theorem finite_analytic_family_eventually_stable
    {I : Type*} [Finite I] (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) :
    ∃ R : I → I → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ i j,
        (f i x ≤ f j x ↔ R i j) := by
  let L := nhdsWithin x₀ (Set.Ioi x₀)
  let R : I → I → Prop := fun i j => ∀ᶠ x in L, f i x ≤ f j x
  refine ⟨R, Filter.eventually_all.mpr fun i =>
    Filter.eventually_all.mpr fun j => ?_⟩
  rcases analyticAt_eventually_eq_or_lt_or_gt (hf i) (hf j) with
    heq | hlt | hgt
  · have hR : R i j := heq.mono fun x hx => hx.le
    filter_upwards [heq] with x hx
    simp [R, hR, hx]
  · have hR : R i j := hlt.mono fun x hx => hx.le
    filter_upwards [hlt] with x hx
    simp [R, hR, hx.le]
  · have hR : ¬R i j := by
      intro hle
      obtain ⟨x, hgtx, hlex⟩ := (hgt.and hle).exists
      exact (not_lt_of_ge hlex) hgtx
    filter_upwards [hgt] with x hx
    simp [R, hR, not_le.mpr hx]

/-- A finite family of real-analytic germs has one fixed member which
eventually dominates every member without taking absolute values. -/
theorem finite_analytic_family_eventually_fixed_maximizer
    {I : Type*} [Finite I] [Nonempty I]
    (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) :
    ∃ i, ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ j,
      f j x ≤ f i x := by
  letI := Fintype.ofFinite I
  obtain ⟨R, hstable⟩ :=
    finite_analytic_family_eventually_stable f hf
  obtain ⟨x, hxstable⟩ := hstable.exists
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => f j x)
  refine ⟨i, ?_⟩
  filter_upwards [hstable] with y hystable
  intro j
  have hxle : f j x ≤ f i x := by
    have hsup :=
      Finset.le_sup' (fun k => f k x) (Finset.mem_univ j)
    rwa [hi] at hsup
  exact (hystable j i).mpr ((hxstable j i).mp hxle)

/-- A finite family of real-analytic germs has one fixed index whose absolute
value eventually dominates every member of the family. -/
theorem finite_analytic_family_eventually_fixed_abs_maximizer
    {I : Type*} [Finite I] [Nonempty I]
    (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) :
    ∃ i, ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ j,
      |f j x| ≤ |f i x| := by
  letI := Fintype.ofFinite I
  let square : I → ℝ → ℝ := fun i x => (f i x) ^ 2
  have hsquare : ∀ i, AnalyticAt ℝ (square i) x₀ := by
    intro i
    exact (hf i).pow 2
  obtain ⟨R, hstable⟩ :=
    finite_analytic_family_eventually_stable square hsquare
  obtain ⟨x, hxstable⟩ := hstable.exists
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => square j x)
  refine ⟨i, ?_⟩
  filter_upwards [hstable] with y hystable
  intro j
  have hxle : square j x ≤ square i x := by
    have hsup :=
      Finset.le_sup' (fun k => square k x) (Finset.mem_univ j)
    rwa [hi] at hsup
  have hR : R j i := (hxstable j i).mp hxle
  have hyle : square j y ≤ square i y := (hystable j i).mpr hR
  exact sq_le_sq.mp hyle

/-- If some member of a finite analytic family is a nonzero right germ, one
fixed member and one fixed sign eventually attain the absolute envelope
exactly. The orientation is represented by the real scalar `-1` or `1`. -/
theorem finite_analytic_family_eventually_fixed_oriented_abs_maximizer
    {I : Type*} [Finite I] [Nonempty I]
    (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    (hnonzero : ∃ j,
      ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), f j x = 0) :
    ∃ i, ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        0 < σ * f i x ∧ ∀ j, |f j x| ≤ σ * f i x := by
  obtain ⟨i, himax⟩ :=
    finite_analytic_family_eventually_fixed_abs_maximizer f hf
  have hine : ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), f i x = 0 := by
    rintro hizero
    obtain ⟨j, hj⟩ := hnonzero
    apply hj
    filter_upwards [himax, hizero] with x hxmax hxzero
    have hle := hxmax j
    rw [hxzero, abs_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  rcases analyticAt_eventually_eq_or_lt_or_gt
      (hf i) analyticAt_const with heq | hneg | hpos
  · exact False.elim (hine heq)
  · refine ⟨i, -1, Or.inl rfl, ?_⟩
    filter_upwards [himax, hneg] with x hxmax hxneg
    have hsign : (-1 : ℝ) * f i x = |f i x| := by
      rw [neg_one_mul, abs_of_neg hxneg]
    rw [hsign]
    exact ⟨abs_pos.mpr (ne_of_lt hxneg), hxmax⟩
  · refine ⟨i, 1, Or.inr rfl, ?_⟩
    filter_upwards [himax, hpos] with x hxmax hxpos
    have hsign : (1 : ℝ) * f i x = |f i x| := by
      rw [one_mul, abs_of_pos hxpos]
    rw [hsign]
    exact ⟨abs_pos.mpr (ne_of_gt hxpos), hxmax⟩

/-- A right-nonnegative analytic germ is either identically zero as a right
germ or eventually strictly positive. -/
theorem analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
    {g : ℝ → ℝ} {x₀ : ℝ}
    (hg : AnalyticAt ℝ g x₀)
    (hnonneg : ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ g x) :
    (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), g x = 0) ∨
      (∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 < g x) := by
  rcases analyticAt_eventually_eq_or_lt_or_gt
      hg analyticAt_const with heq | hneg | hpos
  · exact Or.inl heq
  · exfalso
    obtain ⟨x, hxneg, hxnonneg⟩ := (hneg.and hnonneg).exists
    exact (not_lt_of_ge hxnonneg) hxneg
  · exact Or.inr hpos

/-- A finite family of nonnegative analytic germs with nonzero total has one
fixed member carrying at least the average total charge. -/
theorem finite_analytic_nonnegative_family_eventually_fixed_charge
    {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    (hnonneg : ∀ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ f i x)
    (htotal :
      ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∑ i, f i x = 0) :
    ∃ i, ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
      0 < f i x ∧
        (Fintype.card I : ℝ)⁻¹ * (∑ j, f j x) ≤ f i x := by
  obtain ⟨i, himax⟩ :=
    finite_analytic_family_eventually_fixed_maximizer f hf
  let total : ℝ → ℝ := fun x => ∑ i, f i x
  have htotal_analytic : AnalyticAt ℝ total x₀ := by
    simpa [total] using
      (Finset.univ.analyticAt_fun_sum fun i _ => hf i)
  have htotal_nonneg :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ total x := by
    filter_upwards [Filter.eventually_all.mpr hnonneg] with x hx
    exact Finset.sum_nonneg fun i _ => hx i
  have htotal_pos :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 < total x := by
    rcases analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
        htotal_analytic htotal_nonneg with hzero | hpos
    · exact False.elim (htotal hzero)
    · exact hpos
  refine ⟨i, ?_⟩
  filter_upwards [himax, htotal_pos] with x hxmax hsumpos
  have hsum_le :
      (∑ j, f j x) ≤ (Fintype.card I : ℝ) * f i x := by
    calc
      (∑ j, f j x) ≤ ∑ _j : I, f i x :=
        Finset.sum_le_sum fun j _ => hxmax j
      _ = (Fintype.card I : ℝ) * f i x := by simp
  have hcard_pos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  constructor
  · nlinarith
  · rw [inv_mul_le_iff₀ hcard_pos]
    exact hsum_le

/-- A positive real-analytic right germ has a positive power-law lower
bound. The exponent is the order of its first nonzero Taylor coefficient. -/
theorem analyticAt_eventually_const_mul_pow_le_of_eventually_pos
    {g : ℝ → ℝ} {x₀ : ℝ}
    (hg : AnalyticAt ℝ g x₀)
    (hpos : ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 < g x) :
    ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        c * (x - x₀) ^ n ≤ g x := by
  have hnotzero : ¬∀ᶠ x in 𝓝 x₀, g x = 0 := by
    intro hzero
    obtain ⟨x, hxzero, hxpos⟩ :=
      ((hzero.filter_mono nhdsWithin_le_nhds).and hpos).exists
    exact (ne_of_gt hxpos) hxzero
  obtain ⟨n, u, hu, hu0, hfactor⟩ :=
    hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have hu0pos : 0 < u x₀ := by
    by_contra hnotpos
    have hu0neg : u x₀ < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnotpos) hu0
    have huneg : ∀ᶠ x in 𝓝 x₀, u x < 0 :=
      hu.continuousAt.tendsto.eventually_lt_const hu0neg
    have hgneg :
        ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), g x < 0 := by
      filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
        huneg.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with x hfac hux hxright
      have hxpow : 0 < (x - x₀) ^ n :=
        pow_pos (sub_pos.mpr hxright) n
      change g x = (x - x₀) ^ n * u x at hfac
      nlinarith
    obtain ⟨x, hxneg, hxpos⟩ := (hgneg.and hpos).exists
    exact (not_lt_of_ge hxpos.le) hxneg
  refine ⟨n, u x₀ / 2, by linarith, ?_⟩
  have hulower : ∀ᶠ x in 𝓝 x₀, u x₀ / 2 < u x :=
    hu.continuousAt.tendsto.eventually_const_lt (by linarith)
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hulower.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hfac hux hxright
  change g x = (x - x₀) ^ n * u x at hfac
  rw [hfac]
  have hxpow : 0 ≤ (x - x₀) ^ n :=
    (pow_nonneg (sub_pos.mpr hxright).le n)
  nlinarith

/-- A nonzero finite sum of nonnegative analytic germs has one fixed member
which carries both its average share and a positive power-law charge. -/
theorem finite_analytic_nonnegative_family_eventually_fixed_power_charge
    {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {x₀ : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    (hnonneg : ∀ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ f i x)
    (htotal :
      ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∑ i, f i x = 0) :
    ∃ i n c, 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        c * (x - x₀) ^ n ≤
            (Fintype.card I : ℝ)⁻¹ * (∑ j, f j x) ∧
          (Fintype.card I : ℝ)⁻¹ * (∑ j, f j x) ≤ f i x := by
  obtain ⟨i, hcharge⟩ :=
    finite_analytic_nonnegative_family_eventually_fixed_charge
      f hf hnonneg htotal
  let total : ℝ → ℝ := fun x => ∑ i, f i x
  have htotal_analytic : AnalyticAt ℝ total x₀ := by
    simpa [total] using
      (Finset.univ.analyticAt_fun_sum fun i _ => hf i)
  have htotal_nonneg :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ total x := by
    filter_upwards [Filter.eventually_all.mpr hnonneg] with x hx
    exact Finset.sum_nonneg fun j _ => hx j
  have htotal_pos :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 < total x := by
    rcases analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
        htotal_analytic htotal_nonneg with hzero | hpos
    · exact False.elim (htotal hzero)
    · exact hpos
  obtain ⟨n, c, hc, hpower⟩ :=
    analyticAt_eventually_const_mul_pow_le_of_eventually_pos
      htotal_analytic htotal_pos
  have hcard_pos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  refine ⟨i, n, c / Fintype.card I, div_pos hc hcard_pos, ?_⟩
  filter_upwards [hpower, hcharge] with x hxpower hxcharge
  constructor
  · calc
      (c / Fintype.card I) * (x - x₀) ^ n =
          (c * (x - x₀) ^ n) / Fintype.card I := by ring
      _ ≤ total x / Fintype.card I :=
        div_le_div_of_nonneg_right hxpower hcard_pos.le
      _ = (Fintype.card I : ℝ)⁻¹ * (∑ j, f j x) := by
        simp [total, div_eq_inv_mul]
  · exact hxcharge.2

/-- A finite family of right-nonnegative analytic constraint germs has one
eventual active set. Active constraints vanish identically as right germs;
every other constraint is eventually strictly positive. -/
theorem finite_analytic_nonnegative_family_eventually_active_set
    {I : Type*} [Finite I]
    (g : I → ℝ → ℝ) {x₀ : ℝ}
    (hg : ∀ i, AnalyticAt ℝ (g i) x₀)
    (hnonneg : ∀ i,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ g i x) :
    ∃ active : I → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ i,
        (g i x = 0 ↔ active i) ∧ (0 < g i x ↔ ¬active i) := by
  let L := nhdsWithin x₀ (Set.Ioi x₀)
  let active : I → Prop := fun i => ∀ᶠ x in L, g i x = 0
  refine ⟨active, Filter.eventually_all.mpr fun i => ?_⟩
  rcases analyticAt_eventually_eq_zero_or_pos_of_eventually_nonneg
      (hg i) (hnonneg i) with hzero | hpos
  · have hactive : active i := hzero
    filter_upwards [hzero] with x hx
    simp [hactive, hx]
  · have hinactive : ¬active i := by
      intro hactive
      obtain ⟨x, hxzero, hxpos⟩ := (hactive.and hpos).exists
      exact (ne_of_gt hxpos) hxzero
    filter_upwards [hpos] with x hx
    simp [hinactive, ne_of_gt hx, hx]

/-- Evaluate a bivariate polynomial `P : Polynomial (Polynomial ℝ)` — outer variable `v`,
coefficients in `ℝ[λ]` — at the point `(λ, v) = (lam, y)`: specialise every coefficient at `λ =
lam`, then evaluate the resulting real polynomial in `v` at `y`. -/
noncomputable def bivEval (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) : ℝ :=
  Polynomial.eval₂ (Polynomial.evalRingHom lam) y P

/-- `bivEval` unfolds to the expected finite sum `∑ i, aᵢ(λ) * yⁱ`. -/
theorem bivEval_eq_sum (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) :
    bivEval P lam y = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval lam * y ^ i := by
  simp [bivEval, Polynomial.eval₂_eq_sum_range, Polynomial.coe_evalRingHom]

/-- `bivEval P lam` agrees with evaluating the `λ`-specialised univariate polynomial `P.map
(Polynomial.evalRingHom lam)` at `y`. -/
theorem bivEval_eq_eval_map (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) :
    bivEval P lam y = (P.map (Polynomial.evalRingHom lam)).eval y :=
  Polynomial.eval₂_eq_eval_map _

/-- If `f` continuously selects `y = f lam`, the composite `lam ↦ bivEval P lam (f lam)` is
continuous. -/
theorem continuous_bivEval_comp {P : Polynomial (Polynomial ℝ)} {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous fun lam => bivEval P lam (f lam) := by
  simp_rw [bivEval_eq_sum]
  exact continuous_finsetSum _ fun i _ => (P.coeff i).continuous.mul (hf.pow i)

/-- `ContinuousOn` version of `continuous_bivEval_comp`. -/
theorem continuousOn_bivEval_comp {P : Polynomial (Polynomial ℝ)} {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ContinuousOn f s) : ContinuousOn (fun lam => bivEval P lam (f lam)) s := by
  simp_rw [bivEval_eq_sum]
  exact continuousOn_finsetSum _ fun i _ => ((P.coeff i).continuous.continuousOn).mul (hf.pow i)

/-- Joint continuity of `bivEval P` in both arguments at once. -/
theorem continuous_bivEval (P : Polynomial (Polynomial ℝ)) :
    Continuous fun p : ℝ × ℝ => bivEval P p.1 p.2 := by
  simp_rw [bivEval_eq_sum]
  exact continuous_finsetSum _ fun i _ =>
    ((P.coeff i).continuous.comp continuous_fst).mul (continuous_snd.pow i)

/-- The `λ`-partial-derivative of a bivariate polynomial `P`: differentiate every coefficient
`aᵢ : ℝ[λ]` while leaving the outer (`v`) exponents untouched. Together with
`Polynomial.derivative P` (the `v`-partial-derivative, differentiating the outer variable), this
is the other half of the total derivative of `bivEval P` needed for the implicit function
theorem. -/
noncomputable def bivDerivLam (P : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℝ) :=
  ∑ i ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (Polynomial.derivative (P.coeff i)) * Polynomial.X ^ i

theorem coeff_bivDerivLam (P : Polynomial (Polynomial ℝ)) (j : ℕ) :
    (bivDerivLam P).coeff j = Polynomial.derivative (P.coeff j) := by
  rw [bivDerivLam, Polynomial.finsetSum_coeff]
  by_cases hj : j < P.natDegree + 1
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hij
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hij)]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'
  · have hcoeff0 : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff0, Polynomial.derivative_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hij : i ≠ j := by simp only [Finset.mem_range] at hi; omega
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hij)]

theorem bivDerivLam_natDegree_le (P : Polynomial (Polynomial ℝ)) :
    (bivDerivLam P).natDegree ≤ P.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [coeff_bivDerivLam, Polynomial.coeff_eq_zero_of_natDegree_lt hN, Polynomial.derivative_zero]

/-- `bivEval (bivDerivLam P) lam y` computes the `λ`-partial-derivative sum
`∑ i, aᵢ'(λ) * yⁱ`. -/
theorem bivEval_bivDerivLam (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) :
    bivEval (bivDerivLam P) lam y =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        (Polynomial.derivative (P.coeff i)).eval lam * y ^ i := by
  have hn : (bivDerivLam P).natDegree < P.natDegree + 1 :=
    Nat.lt_succ_of_le (bivDerivLam_natDegree_le P)
  rw [bivEval, Polynomial.eval₂_eq_sum_range' (Polynomial.evalRingHom lam) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_bivDerivLam, Polynomial.coe_evalRingHom]

/-- Differentiating `bivEval P · y` in `λ` recovers `bivEval (bivDerivLam P) lam y`. -/
theorem hasDerivAt_bivEval_left (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) :
    HasDerivAt (fun l => bivEval P l y) (bivEval (bivDerivLam P) lam y) lam := by
  rw [bivEval_bivDerivLam]
  have heq : (fun l => bivEval P l y) =
      fun l => ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval l * y ^ i :=
    funext fun l => bivEval_eq_sum P l y
  rw [heq, ← Finset.sum_fn]
  exact HasDerivAt.sum fun i (_ : i ∈ Finset.range (P.natDegree + 1)) =>
    ((P.coeff i).hasDerivAt lam).mul_const (y ^ i)

/-- Differentiating `bivEval P lam ·` in `v` recovers `bivEval (Polynomial.derivative P) lam y`. -/
theorem hasDerivAt_bivEval_right (P : Polynomial (Polynomial ℝ)) (lam y : ℝ) :
    HasDerivAt (fun v => bivEval P lam v) (bivEval (Polynomial.derivative P) lam y) y := by
  have heq : (fun v => bivEval P lam v) = fun v => (P.map (Polynomial.evalRingHom lam)).eval v :=
    funext fun v => bivEval_eq_eval_map P lam v
  rw [heq, bivEval_eq_eval_map, ← Polynomial.derivative_map]
  exact (P.map (Polynomial.evalRingHom lam)).hasDerivAt y

/-- `ContinuousLinearMap.toSpanSingleton ℝ : ℝ → (ℝ →L[ℝ] ℝ)` is `1`-Lipschitz, hence
continuous: it is additive in its argument, and norm-preserving
(`ContinuousLinearMap.norm_toSpanSingleton`). -/
theorem continuous_toSpanSingleton_real :
    Continuous fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℝ x := by
  have hsub : ∀ x y : ℝ, ContinuousLinearMap.toSpanSingleton ℝ x -
      ContinuousLinearMap.toSpanSingleton ℝ y = ContinuousLinearMap.toSpanSingleton ℝ (x - y) := by
    intro x y
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  have hdist : ∀ x y : ℝ, dist (ContinuousLinearMap.toSpanSingleton ℝ x)
      (ContinuousLinearMap.toSpanSingleton ℝ y) = dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, hsub, ContinuousLinearMap.norm_toSpanSingleton]
  have hlip : LipschitzWith 1 fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℝ x := by
    intro x y
    rw [edist_dist, edist_dist, hdist]
    simp
  exact hlip.continuous

/-- `Polynomial.resultant` vanishing at the actual `natDegree`s of `f`, `g` forces it to vanish at
any larger degree bounds `m, n` as well: bumping the bounds only multiplies by extra coefficient
powers (`Polynomial.resultant_add_left_deg`, `Polynomial.resultant_add_right_deg`). -/
theorem resultant_eq_zero_of_le_of_not_isCoprime {f g : Polynomial ℝ} {m n : ℕ}
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n) (hfg : f ≠ 0 ∨ g ≠ 0)
    (h : ¬ IsCoprime f g) : Polynomial.resultant f g m n = 0 := by
  have hbase : Polynomial.resultant f g = 0 := Polynomial.resultant_eq_zero_iff.mpr ⟨hfg, h⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl, hk',
    Polynomial.resultant_add_right_deg _ _ _ _ k' le_rfl, hbase, mul_zero, mul_zero]

/-- The elimination-theory core fact: if `P` and `Q` have a common `v`-root over `λ = lam`, then
either `lam` is a root of `resultant P Q` (an element of `ℝ[λ]`), or `lam` is a root of `P`'s
`v`-leading coefficient (in which case `P`'s specialisation at `λ = lam` degenerates, and the
resultant elimination carries no information — this locus is separately finite whenever `P ≠ 0`,
via `P.leadingCoeff ≠ 0`). -/
theorem resultant_eval_eq_zero_or_leadingCoeff_eval_eq_zero
    {P Q : Polynomial (Polynomial ℝ)} {lam y : ℝ}
    (hP0 : bivEval P lam y = 0) (hQ0 : bivEval Q lam y = 0) :
    (Polynomial.resultant P Q).eval lam = 0 ∨ (P.leadingCoeff).eval lam = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, hL⟩ := hcon
  apply hR
  set f := P.map (Polynomial.evalRingHom lam) with hf_def
  set g := Q.map (Polynomial.evalRingHom lam) with hg_def
  have hfne : f ≠ 0 := by
    intro h0
    apply hL
    have hcoeff : f.coeff P.natDegree = 0 := by rw [h0]; simp
    rwa [hf_def, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      ← Polynomial.leadingCoeff] at hcoeff
  have hfy : f.eval y = 0 := by rw [hf_def, ← Polynomial.eval₂_eq_eval_map]; exact hP0
  have hgy : g.eval y = 0 := by rw [hg_def, ← Polynomial.eval₂_eq_eval_map]; exact hQ0
  have hnotcop : ¬ IsCoprime f g := by
    intro hcop
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcop y with h' | h' <;>
      simp_all [Polynomial.aeval_def, Polynomial.eval₂_id]
  have hm : f.natDegree ≤ P.natDegree := hf_def ▸ Polynomial.natDegree_map_le
  have hn : g.natDegree ≤ Q.natDegree := hg_def ▸ Polynomial.natDegree_map_le
  have hzero := resultant_eq_zero_of_le_of_not_isCoprime hm hn (Or.inl hfne) hnotcop
  have hmap : Polynomial.resultant f g P.natDegree Q.natDegree
      = (Polynomial.resultant P Q).eval lam := by
    rw [hf_def, hg_def, Polynomial.resultant_map_map, Polynomial.coe_evalRingHom]
  rw [← hmap]
  exact hzero

/-- If `P ≠ 0` and `resultant P Q ≠ 0`, the set of `λ` at which `P` and `Q` (viewed as bivariate
polynomials with outer variable `v`) have a common `v`-root is finite. This bounds any "bad locus"
(critical points, sign-change loci of an auxiliary polynomial along the implicit curve) that is
expressible as such a common-root set. -/
theorem finite_bivEval_common_zero {P Q : Polynomial (Polynomial ℝ)}
    (hP : P ≠ 0) (hR : Polynomial.resultant P Q ≠ 0) :
    {lam : ℝ | ∃ y, bivEval P lam y = 0 ∧ bivEval Q lam y = 0}.Finite := by
  have hS : Polynomial.resultant P Q * P.leadingCoeff ≠ 0 :=
    mul_ne_zero hR (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hsub : {lam : ℝ | ∃ y, bivEval P lam y = 0 ∧ bivEval Q lam y = 0} ⊆
      {lam | (Polynomial.resultant P Q * P.leadingCoeff).IsRoot lam} := by
    rintro lam ⟨y, hP0, hQ0⟩
    rcases resultant_eval_eq_zero_or_leadingCoeff_eval_eq_zero hP0 hQ0 with h | h <;>
      simp [Polynomial.IsRoot, h]
  exact (Polynomial.finite_setOf_isRoot hS).subset hsub

/-- A continuous, nowhere-zero real function on a preconnected set has a single, fixed strict
sign throughout the set. -/
theorem constant_sign_of_continuousOn_of_ne_zero {s : Set ℝ} (hs : IsPreconnected s)
    {g : ℝ → ℝ} (hg : ContinuousOn g s) (hne : ∀ x ∈ s, g x ≠ 0) {a : ℝ} (ha : a ∈ s) :
    (∀ x ∈ s, 0 < g x) ∨ (∀ x ∈ s, g x < 0) := by
  rcases lt_or_gt_of_ne (hne a ha) with hneg | hpos
  · refine Or.inr fun x hx => ?_
    by_contra hcon
    have hxpos : 0 < g x := (lt_or_gt_of_ne (hne x hx)).resolve_left hcon
    obtain ⟨y, hys, hgy⟩ := hs.intermediate_value ha hx hg ⟨hneg.le, hxpos.le⟩
    exact hne y hys hgy
  · refine Or.inl fun x hx => ?_
    by_contra hcon
    have hxneg : g x < 0 := (lt_or_gt_of_ne (hne x hx)).resolve_right hcon
    obtain ⟨y, hys, hgy⟩ := hs.intermediate_value hx ha hg ⟨hxneg.le, hpos.le⟩
    exact hne y hys hgy

/-- A finite set does not accumulate at `0` from the right: given `ρ > 0`, there is a smaller
`ε ∈ (0, ρ]` such that `Ioo 0 ε` avoids the finite set entirely. -/
theorem exists_Ioo_forall_notMem_of_finite {B : Set ℝ} (hB : B.Finite) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε, 0 < ε ∧ ε ≤ ρ ∧ ∀ lam ∈ Set.Ioo (0 : ℝ) ε, lam ∉ B := by
  classical
  have hB2 : (B ∩ Set.Ioo (0 : ℝ) ρ).Finite := hB.inter_of_left _
  rcases (B ∩ Set.Ioo (0 : ℝ) ρ).eq_empty_or_nonempty with hempty | hne
  · refine ⟨ρ, hρ, le_rfl, fun lam hlam hmem => ?_⟩
    have : lam ∈ B ∩ Set.Ioo (0 : ℝ) ρ := ⟨hmem, hlam⟩
    rw [hempty] at this
    exact this
  · have hne' : hB2.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
    set m := hB2.toFinset.min' hne' with hm_def
    have hm_mem : m ∈ B ∩ Set.Ioo (0 : ℝ) ρ := by
      have := hB2.toFinset.min'_mem hne'
      rwa [Set.Finite.mem_toFinset] at this
    refine ⟨m, hm_mem.2.1, hm_mem.2.2.le, fun lam hlam hmem => ?_⟩
    have hlamB2 : lam ∈ B ∩ Set.Ioo (0 : ℝ) ρ := ⟨hmem, hlam.1, hlam.2.trans hm_mem.2.2⟩
    have hle : m ≤ lam := hB2.toFinset.min'_le lam (by rwa [Set.Finite.mem_toFinset])
    exact absurd hle (not_le.mpr hlam.2)

/-- **Bonus (item 3).** For `w` continuously selected by the nonzero polynomial `P` on
`Ioo 0 ρ`, and any auxiliary polynomial `Q` with `resultant P Q ≠ 0`, the sign of
`bivEval Q lam (w lam)` is eventually constant as `lam → 0⁺`. This is the "finitely many sign
changes" germ fact used by vanishing-discount arguments. -/
theorem eventually_sign_constant_of_polynomial
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P Q : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hR : Polynomial.resultant P Q ≠ 0) :
    (∀ᶠ lam in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < bivEval Q lam (w lam)) ∨
    (∀ᶠ lam in nhdsWithin (0 : ℝ) (Set.Ioi 0), bivEval Q lam (w lam) < 0) := by
  have hZ : {lam ∈ Set.Ioo (0 : ℝ) ρ | bivEval Q lam (w lam) = 0}.Finite := by
    refine Set.Finite.subset (finite_bivEval_common_zero hP hR) ?_
    rintro lam ⟨hlam, hQ0⟩
    exact ⟨w lam, hroot lam hlam, hQ0⟩
  obtain ⟨ε, hεpos, hερ, hεnot⟩ := exists_Ioo_forall_notMem_of_finite hZ hρ
  have hεsub : Set.Ioo (0 : ℝ) ε ⊆ Set.Ioo (0 : ℝ) ρ := Set.Ioo_subset_Ioo_right hερ
  have hcont : ContinuousOn (fun lam => bivEval Q lam (w lam)) (Set.Ioo (0 : ℝ) ε) :=
    continuousOn_bivEval_comp (hw.mono hεsub)
  have hne : ∀ lam ∈ Set.Ioo (0 : ℝ) ε, bivEval Q lam (w lam) ≠ 0 := by
    intro lam hlam hcontra
    exact hεnot lam hlam ⟨hεsub hlam, hcontra⟩
  have ha : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨by linarith, by linarith⟩
  have hmemIco : (0 : ℝ) ∈ Set.Ico (0 : ℝ) ε := ⟨le_refl 0, hεpos⟩
  have hnbhd : Set.Ioo (0 : ℝ) ε ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT_of_mem hmemIco
  rcases constant_sign_of_continuousOn_of_ne_zero isPreconnected_Ioo hcont hne ha with hpos | hneg
  · exact Or.inl (Filter.eventually_of_mem hnbhd hpos)
  · exact Or.inr (Filter.eventually_of_mem hnbhd hneg)

/-- **The only place the implicit function theorem is used, and only locally, for the
derivative formula.** If `w` is continuous at `lam0`, satisfies `bivEval P lam (w lam) = 0` for
`λ` near `lam0`, and `∂ᵥP (lam0, w lam0) ≠ 0`, then `w` is differentiable at `lam0` with
`w'(lam0) = -∂_λP(lam0, w lam0) / ∂ᵥP(lam0, w lam0)`. No global matching of `w` against an
implicit branch is needed: `implicitFunctionOfBivariate` is only invoked at the single point
`lam0`, and `w` is shown to agree with it on a neighbourhood of `lam0` via continuity. -/
theorem hasDerivAt_of_polynomial_root {P : Polynomial (Polynomial ℝ)} {w : ℝ → ℝ} {lam0 : ℝ}
    (hwc : ContinuousAt w lam0) (hroot : ∀ᶠ lam in nhds lam0, bivEval P lam (w lam) = 0)
    (hD : bivEval (Polynomial.derivative P) lam0 (w lam0) ≠ 0) :
    HasDerivAt w
      (-(bivEval (bivDerivLam P) lam0 (w lam0)) / bivEval (Polynomial.derivative P) lam0 (w lam0))
      lam0 := by
  set y0 := w lam0 with hy0
  set u : ℝ × ℝ := (lam0, y0) with hu
  set f : ℝ → ℝ → ℝ := fun lam y => bivEval P lam y with hfdef
  set f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun lam y => ContinuousLinearMap.toSpanSingleton ℝ (bivEval (bivDerivLam P) lam y) with hf1def
  set f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun lam y => ContinuousLinearMap.toSpanSingleton ℝ (bivEval (Polynomial.derivative P) lam y)
      with hf2def
  have df₁ : ∀ᶠ v : ℝ × ℝ in nhds u, HasFDerivAt (fun l => f l v.2) (f₁ v.1 v.2) v.1 :=
    Filter.Eventually.of_forall fun v => (hasDerivAt_bivEval_left P v.1 v.2).hasFDerivAt
  have df₂ : ∀ᶠ v : ℝ × ℝ in nhds u, HasFDerivAt (fun y => f v.1 y) (f₂ v.1 v.2) v.2 :=
    Filter.Eventually.of_forall fun v => (hasDerivAt_bivEval_right P v.1 v.2).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) u :=
    (continuous_toSpanSingleton_real.comp (continuous_bivEval (bivDerivLam P))).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry f₂) u :=
    (continuous_toSpanSingleton_real.comp
      (continuous_bivEval (Polynomial.derivative P))).continuousAt
  have he : (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hD) : ℝ →L[ℝ] ℝ) = f₂ u.1 u.2 := by
    ext
    simp [hf2def, hu, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply]
  have hinv : (f₂ u.1 u.2).IsInvertible := ⟨_, he⟩
  set ψ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv with hψdef
  have hψeq : ∀ᶠ v : ℝ × ℝ in nhds u, f v.1 v.2 = f u.1 u.2 ↔ ψ v.1 = v.2 :=
    eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  have hfu0 : f u.1 u.2 = 0 := hroot.self_of_nhds
  have hcontu : Filter.Tendsto (fun l => (l, w l)) (nhds lam0) (nhds u) := by
    rw [hu]
    exact Filter.Tendsto.prodMk_nhds Filter.tendsto_id hwc
  have hwψ : w =ᶠ[nhds lam0] ψ := by
    have hev := hcontu.eventually hψeq
    have hroot' : ∀ᶠ l in nhds lam0, f l (w l) = f u.1 u.2 := by
      filter_upwards [hroot] with l hl using hl.trans hfu0.symm
    filter_upwards [hev, hroot'] with l hiff hl
    exact (hiff.mp hl).symm
  have hderiv := hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  have hderivψ : HasDerivAt ψ ((-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2) 1) lam0 :=
    hderiv.hasFDerivAt.hasDerivAt
  have hderivw : HasDerivAt w ((-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2) 1) lam0 :=
    hderivψ.congr_of_eventuallyEq hwψ
  convert hderivw using 1
  rw [← he, ContinuousLinearMap.inverse_equiv]
  simp [hf1def, hu, ContinuousLinearEquiv.unitsEquivAut_apply_symm, div_eq_mul_inv]

/-- A continuous function on an open interval whose derivative (given pointwise via
`HasDerivAt`) has a single, fixed strict sign throughout is monotone or antitone there. -/
theorem monotoneOn_or_antitoneOn_of_hasDerivAt_sign
    {ρ' : ℝ} {w w' : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ'))
    (hderiv : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ', HasDerivAt w (w' lam) lam)
    (hsign : (∀ lam ∈ Set.Ioo (0 : ℝ) ρ', 0 < w' lam) ∨
      (∀ lam ∈ Set.Ioo (0 : ℝ) ρ', w' lam < 0)) :
    MonotoneOn w (Set.Ioo 0 ρ') ∨ AntitoneOn w (Set.Ioo 0 ρ') := by
  have hconv : Convex ℝ (Set.Ioo (0 : ℝ) ρ') := convex_Ioo _ _
  have hint : interior (Set.Ioo (0 : ℝ) ρ') = Set.Ioo (0 : ℝ) ρ' := isOpen_Ioo.interior_eq
  rcases hsign with hpos | hneg
  · refine Or.inl (StrictMonoOn.monotoneOn ?_)
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := w') hconv hw (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [hint] at hx; rw [hint]; exact (hderiv x hx).hasDerivWithinAt
    · rw [hint] at hx; exact hpos x hx
  · refine Or.inr (StrictAntiOn.antitoneOn ?_)
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := w') hconv hw (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [hint] at hx; rw [hint]; exact (hderiv x hx).hasDerivWithinAt
    · rw [hint] at hx; exact hneg x hx

/-- **The headline theorem, via the derivative-sign route.** Under the setup (`P ≠ 0`, `w`
continuous on `Ioo 0 ρ` with `bivEval P lam (w lam) = 0` there), if additionally
`resultant P (Polynomial.derivative P) ≠ 0` (excludes vertical tangents / branch points along the
curve — the "squarefree in `v`" reduction) and `resultant P (bivDerivLam P) ≠ 0` (excludes
degenerate `λ`-critical points), then `w` is eventually monotone or antitone as `λ → 0⁺`.

The implicit function theorem (`hasDerivAt_of_polynomial_root`) is used only *locally*, to derive
the closed-form derivative `w' = -∂_λP / ∂ᵥP` at each point below the smallest excluded point; the
sign of `w'` is then controlled *globally* by `eventually_sign_constant_of_polynomial`, applied
once to each of the numerator and denominator, entirely avoiding any branch-gluing argument. -/
theorem eventually_monotone_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0) :
    ∃ ρ' ∈ Set.Ioc (0 : ℝ) ρ, MonotoneOn w (Set.Ioo 0 ρ') ∨ AntitoneOn w (Set.Ioo 0 ρ') := by
  rcases eventually_sign_constant_of_polynomial hρ hw hP hroot hRlam with hNc | hNc <;>
    rcases eventually_sign_constant_of_polynomial hρ hw hP hroot hRv with hDc | hDc
  all_goals
    obtain ⟨ε, hεpos, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hNc.and hDc)
  -- In every branch, `ε` bounds an interval on which both the numerator `N` and the
  -- denominator `D` of `w' = -N / D` have a known, fixed strict sign.
  all_goals
    set ρ' := min ε ρ with hρ'def
  all_goals
    have hρ'pos : 0 < ρ' := lt_min hεpos hρ
  all_goals
    have hρ'ε : Set.Ioo (0 : ℝ) ρ' ⊆ Set.Ioo (0 : ℝ) ε := Set.Ioo_subset_Ioo_right (min_le_left _ _)
  all_goals
    have hρ'ρ : Set.Ioo (0 : ℝ) ρ' ⊆ Set.Ioo (0 : ℝ) ρ :=
      Set.Ioo_subset_Ioo_right (min_le_right _ _)
  all_goals
    have hwρ' : ContinuousOn w (Set.Ioo 0 ρ') := hw.mono hρ'ρ
  all_goals
    have hderiv : ∀ lam0 ∈ Set.Ioo (0 : ℝ) ρ', HasDerivAt w
        (-(bivEval (bivDerivLam P) lam0 (w lam0)) /
          bivEval (Polynomial.derivative P) lam0 (w lam0)) lam0 := by
      intro lam0 hlam0
      have hlam0ρ : lam0 ∈ Set.Ioo (0 : ℝ) ρ := hρ'ρ hlam0
      refine hasDerivAt_of_polynomial_root
        (hw.continuousAt (Ioo_mem_nhds hlam0ρ.1 hlam0ρ.2)) ?_
        (by have h := (hsub (hρ'ε hlam0)).2; first | exact h.ne' | exact h.ne)
      filter_upwards [Ioo_mem_nhds hlam0ρ.1 hlam0ρ.2] with lam hlam using hroot lam hlam
  all_goals
    refine ⟨ρ', ⟨hρ'pos, min_le_right _ _⟩,
      monotoneOn_or_antitoneOn_of_hasDerivAt_sign hwρ' hderiv ?_⟩
  · exact Or.inr fun lam hlam => by
      have h := hsub (hρ'ε hlam)
      exact div_neg_iff.mpr (Or.inr ⟨by linarith [h.1], h.2⟩)
  · exact Or.inl fun lam hlam => by
      have h := hsub (hρ'ε hlam)
      exact div_pos_iff.mpr (Or.inr ⟨by linarith [h.1], h.2⟩)
  · exact Or.inl fun lam hlam => by
      have h := hsub (hρ'ε hlam)
      exact div_pos_iff.mpr (Or.inl ⟨by linarith [h.1], h.2⟩)
  · exact Or.inr fun lam hlam => by
      have h := hsub (hρ'ε hlam)
      exact div_neg_iff.mpr (Or.inl ⟨by linarith [h.1], h.2⟩)

/-- The `Antitone` counterpart of `MonotoneOn.boundedVariationOn`: not in Mathlib directly, but
one line from it via negation, since negation is `1`-Lipschitz. -/
theorem _root_.AntitoneOn.boundedVariationOn {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    {C : ℝ} (hC : ∀ x ∈ s, |f x| ≤ C) : BoundedVariationOn f s := by
  have hmono : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  have hbv : BoundedVariationOn (fun x => -f x) s :=
    hmono.boundedVariationOn fun x hx => by simpa using hC x hx
  have hlip : LipschitzWith 1 (Neg.neg : ℝ → ℝ) := LipschitzWith.id.neg
  have h2 := hlip.comp_boundedVariationOn hbv
  have heq : (Neg.neg ∘ fun x => -f x) = f := by funext x; simp
  rwa [heq] at h2

/-- **Target 2(a).** Once `w` is eventually monotone or antitone
(`eventually_monotone_of_polynomial_root`) and bounded, it has bounded variation on the
corresponding interval — the hypothesis form Mertens–Neyman-style vanishing-discount arguments
consume directly. -/
theorem boundedVariationOn_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0)
    {C : ℝ} (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, |w lam| ≤ C) :
    ∃ ρ' ∈ Set.Ioc (0 : ℝ) ρ, BoundedVariationOn w (Set.Ioo 0 ρ') := by
  obtain ⟨ρ', hρ'mem, hmono | hanti⟩ :=
    eventually_monotone_of_polynomial_root hρ hw hP hroot hRv hRlam
  · exact ⟨ρ', hρ'mem,
      hmono.boundedVariationOn fun x hx => hC x (Set.Ioo_subset_Ioo_right hρ'mem.2 hx)⟩
  · exact ⟨ρ', hρ'mem,
      hanti.boundedVariationOn fun x hx => hC x (Set.Ioo_subset_Ioo_right hρ'mem.2 hx)⟩

/-- A bounded continuous algebraic selection has a finite right-limit at
zero. The resultant hypotheses make the selection eventually monotone or
antitone; boundedness then gives the corresponding endpoint limit. -/
theorem exists_tendsto_nhdsWithin_zero_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0)
    {C : ℝ} (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      |w lam| ≤ C) :
    ∃ L : ℝ, Filter.Tendsto w
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  obtain ⟨ρ', hρ'mem, hmono | hanti⟩ :=
    eventually_monotone_of_polynomial_root
      hρ hw hP hroot hRv hRlam
  · have hnonempty : (Set.Ioo (0 : ℝ) ρ').Nonempty := by
      exact ⟨ρ' / 2, by constructor <;> linarith [hρ'mem.1]⟩
    have hbdd : BddBelow (w '' Set.Ioo (0 : ℝ) ρ') := by
      refine ⟨-C, ?_⟩
      rintro y ⟨lam, hlam, rfl⟩
      exact neg_le_of_abs_le
        (hC lam (Set.Ioo_subset_Ioo_right hρ'mem.2 hlam))
    exact ⟨sInf (w '' Set.Ioo (0 : ℝ) ρ'),
      hmono.tendsto_nhdsWithin_Ioo_right hnonempty hbdd⟩
  · have hnonempty : (Set.Ioo (0 : ℝ) ρ').Nonempty := by
      exact ⟨ρ' / 2, by constructor <;> linarith [hρ'mem.1]⟩
    have hbdd : BddAbove (w '' Set.Ioo (0 : ℝ) ρ') := by
      refine ⟨C, ?_⟩
      rintro y ⟨lam, hlam, rfl⟩
      exact le_of_abs_le
        (hC lam (Set.Ioo_subset_Ioo_right hρ'mem.2 hlam))
    exact ⟨sSup (w '' Set.Ioo (0 : ℝ) ρ'),
      hanti.tendsto_nhdsWithin_Ioo_right hnonempty hbdd⟩

/-- **Target 2(b), interval control.** The value difference `w a - w b` is controlled by the
total variation on the (order-independent) interval spanned by `a` and `b` — not by a
decreasing-chain sum — which is what a criterion whose index moves in both directions needs:
`min a b` and `max a b` may occur in either order as the index varies. Also records that the
total variation on the whole eventually-monotone interval is finite.

The corresponding vanishing-tail result is
`eventually_tendsto_eVariationOn_nhds_zero_of_polynomial_root` below. -/
theorem dist_le_eVariationOn_uIcc_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0)
    {C : ℝ} (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, |w lam| ≤ C) :
    ∃ ρ' ∈ Set.Ioc (0 : ℝ) ρ, eVariationOn w (Set.Ioo 0 ρ') ≠ ⊤ ∧
      ∀ a ∈ Set.Ioo (0 : ℝ) ρ', ∀ b ∈ Set.Ioo (0 : ℝ) ρ',
        dist (w a) (w b) ≤ (eVariationOn w (Set.uIcc a b)).toReal := by
  obtain ⟨ρ', hρ'mem, hbv⟩ := boundedVariationOn_of_polynomial_root hρ hw hP hroot hRv hRlam hC
  refine ⟨ρ', hρ'mem, hbv, fun a ha b hb => ?_⟩
  have huIcc : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) ρ' :=
    Set.ordConnected_Ioo.uIcc_subset ha hb
  exact (hbv.mono huIcc).dist_le Set.left_mem_uIcc Set.right_mem_uIcc

/-- **Target 1, closing the file's `TODO`.** Once `w` is eventually monotone or antitone
(`eventually_monotone_of_polynomial_root`) and bounded, the tail variation
`eVariationOn w (Set.Ioo 0 δ)` tends to `0` as `δ → 0⁺`. Route: `BoundedVariationOn.
tendsto_eVariationOn_Ioc_zero` (a bounded-variation function's variation on small open-closed
intervals to the right of a point tends to `0`) applied at `0` to `w` on `Set.Ioo 0 ρ'`, after
identifying `nhdsWithin 0 (Set.Ioo 0 ρ')` with `nhdsWithin 0 (Set.Ioi 0)` (since `Set.Ioo 0 ρ'` is
a punctured neighbourhood of `0` within `Set.Ioi 0`), then squeezing `eVariationOn w (Set.Ioo 0 δ)`
between `0` and `eVariationOn w (Set.Ioo 0 ρ' ∩ Set.Ioc 0 δ)` for `δ` near `0`. -/
theorem eventually_tendsto_eVariationOn_nhds_zero_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0)
    {C : ℝ} (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, |w lam| ≤ C) :
    ∃ ρ' ∈ Set.Ioc (0 : ℝ) ρ, Filter.Tendsto (fun δ => eVariationOn w (Set.Ioo 0 δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ρ', hρ'mem, hbv⟩ := boundedVariationOn_of_polynomial_root hρ hw hP hroot hRv hRlam hC
  refine ⟨ρ', hρ'mem, ?_⟩
  have hρ'pos : 0 < ρ' := hρ'mem.1
  have htendsto := hbv.tendsto_eVariationOn_Ioc_zero (0 : ℝ)
  have hIioMem : Set.Iio ρ' ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ'pos)
  have hfeq : nhdsWithin (0 : ℝ) (Set.Ioo 0 ρ') = nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have hIoo : Set.Ioi (0 : ℝ) ∩ Set.Iio ρ' = Set.Ioo 0 ρ' := rfl
    rw [← hIoo]
    exact nhdsWithin_inter_of_mem' hIioMem
  rw [hfeq] at htendsto
  have hbound : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      eVariationOn w (Set.Ioo 0 y) ≤ eVariationOn w (Set.Ioo 0 ρ' ∩ Set.Ioc 0 y) :=
    Filter.eventually_of_mem hIioMem fun y hy =>
      eVariationOn.mono w fun x hx => ⟨⟨hx.1, hx.2.trans hy⟩, hx.1, hx.2.le⟩
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  have hle := ENNReal.tendsto_nhds_zero.mp htendsto ε hε
  filter_upwards [hbound, hle] with y hy1 hy2 using hy1.trans hy2

/-- **Target 2, the Mertens–Neyman-facing scalar bridge lemma.** For `w` continuously selected
by the nonzero bivariate polynomial `P` on `Set.Ioo 0 ρ`, eventually squarefree-in-`v` and
non-degenerate-in-`λ` (`hRv`, `hRlam`), and bounded, the tail variation modulus vanishes: for
every `ε > 0` there is `δ > 0` with `eVariationOn w (Set.Ioo 0 δ) ≤ ENNReal.ofReal ε`. This is
exactly the per-coordinate content of `MertensNeymanCriterion.StochasticGame.
IsTailVariationBounded` in the UE zero-sum `MertensNeymanCriterion.lean` module,
which
demands this ε–δ bound for a `ℝ → G.State → Payoff ι`-valued family `v`; the game-level assembly
(finitely many `(state, player)` coordinates, each of the form `fun lam => v lam s who`, feeding
this lemma and reassembled via `Pi`/`sup`-norm control) is left to the Stochastic layer. -/
theorem tailEVariation_vanishes_of_polynomial_root
    {ρ : ℝ} (hρ : 0 < ρ) {w : ℝ → ℝ} (hw : ContinuousOn w (Set.Ioo 0 ρ))
    {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, bivEval P lam (w lam) = 0)
    (hRv : Polynomial.resultant P (Polynomial.derivative P) ≠ 0)
    (hRlam : Polynomial.resultant P (bivDerivLam P) ≠ 0)
    {C : ℝ} (hC : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, |w lam| ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ eVariationOn w (Set.Ioo 0 δ) ≤ ENNReal.ofReal ε := by
  obtain ⟨ρ', hρ'mem, htendsto⟩ :=
    eventually_tendsto_eVariationOn_nhds_zero_of_polynomial_root hρ hw hP hroot hRv hRlam hC
  intro ε hε
  have hev := ENNReal.tendsto_nhds_zero.mp htendsto (ENNReal.ofReal ε) (by positivity)
  obtain ⟨u, hu_pos, hu_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu_pos' : 0 < u := hu_pos
  exact ⟨u / 2, by linarith, hu_sub ⟨by linarith, by linarith⟩⟩

/-- A polynomial branch that is regular at its limiting point has a uniformly
bounded derivative on a smaller positive interval.

The numerator and denominator in the implicit derivative formula are
continuous along the branch. Nonvanishing of the value-direction derivative
at `(0, w 0)` therefore keeps the denominator uniformly away from zero, while
the parameter-direction derivative stays bounded. The pointwise implicit
function theorem then supplies the derivative formula throughout the smaller
interval.

Branches singular at the limiting point fall outside this regular-root
criterion and require a fractional reparameterization. -/
theorem exists_regularPolynomialDerivativeBound
    {P : Polynomial (Polynomial ℝ)} {w : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hw0 : ContinuousAt w 0)
    (hw : ContinuousOn w (Set.Ioo 0 ρ))
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      bivEval P lam (w lam) = 0)
    (hD0 : bivEval (Polynomial.derivative P) 0 (w 0) ≠ 0) :
    ∃ ρ' K : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ 0 ≤ K ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ',
        HasDerivAt w
          (-(bivEval (bivDerivLam P) lam (w lam)) /
            bivEval (Polynomial.derivative P) lam (w lam)) lam ∧
        |-(bivEval (bivDerivLam P) lam (w lam)) /
            bivEval (Polynomial.derivative P) lam (w lam)| ≤ K := by
  let N : ℝ → ℝ := fun lam =>
    bivEval (bivDerivLam P) lam (w lam)
  let D : ℝ → ℝ := fun lam =>
    bivEval (Polynomial.derivative P) lam (w lam)
  have hpair : ContinuousAt (fun lam : ℝ => (lam, w lam)) 0 :=
    continuousAt_id.prodMk hw0
  have hNcont : ContinuousAt N 0 := by
    exact (continuous_bivEval (bivDerivLam P)).continuousAt.comp' hpair
  have hDcont : ContinuousAt D 0 := by
    exact (continuous_bivEval (Polynomial.derivative P)).continuousAt.comp' hpair
  have hD0' : D 0 ≠ 0 := hD0
  have hDabs : 0 < |D 0| := abs_pos.mpr hD0'
  have hNclose : ∀ᶠ lam in 𝓝 (0 : ℝ),
      dist (N lam) (N 0) < 1 := by
    exact (Metric.tendsto_nhds.mp hNcont.tendsto) 1 zero_lt_one
  have hDclose : ∀ᶠ lam in 𝓝 (0 : ℝ),
      dist (D lam) (D 0) < |D 0| / 2 := by
    exact (Metric.tendsto_nhds.mp hDcont.tendsto)
      (|D 0| / 2) (half_pos hDabs)
  obtain ⟨δN, hδN, hNδ⟩ := Metric.mem_nhds_iff.mp hNclose
  obtain ⟨δD, hδD, hDδ⟩ := Metric.mem_nhds_iff.mp hDclose
  let ρ' := min ρ (min δN δD)
  let K := 2 * (|N 0| + 1) / |D 0|
  have hρ' : 0 < ρ' := lt_min hρ (lt_min hδN hδD)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hK : 0 ≤ K := by positivity
  refine ⟨ρ', K, hρ', hρ'ρ, hK, ?_⟩
  intro lam hlam
  have hlamρ : lam ∈ Set.Ioo (0 : ℝ) ρ :=
    ⟨hlam.1, hlam.2.trans_le hρ'ρ⟩
  have hlamN : dist lam 0 < δN := by
    simp only [Real.dist_eq, sub_zero]
    have hδ : ρ' ≤ δN :=
      (min_le_right ρ (min δN δD)).trans (min_le_left _ _)
    rw [abs_of_pos hlam.1]
    exact hlam.2.trans_le hδ
  have hlamD : dist lam 0 < δD := by
    simp only [Real.dist_eq, sub_zero]
    have hδ : ρ' ≤ δD :=
      (min_le_right ρ (min δN δD)).trans (min_le_right _ _)
    rw [abs_of_pos hlam.1]
    exact hlam.2.trans_le hδ
  have hNdist := hNδ (Metric.mem_ball.mpr hlamN)
  have hDdist := hDδ (Metric.mem_ball.mpr hlamD)
  change dist (N lam) (N 0) < 1 at hNdist
  change dist (D lam) (D 0) < |D 0| / 2 at hDdist
  have hNbound : |N lam| ≤ |N 0| + 1 := by
    rw [Real.dist_eq] at hNdist
    have htri := abs_add_le (N lam - N 0) (N 0)
    rw [sub_add_cancel] at htri
    linarith
  have hDbound : |D 0| / 2 ≤ |D lam| := by
    rw [Real.dist_eq] at hDdist
    have htri := abs_sub_abs_le_abs_sub (D 0) (D lam)
    rw [abs_sub_comm] at htri
    linarith
  have hDne : D lam ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDbound
    linarith
  have hrootEventually :
      ∀ᶠ u in 𝓝 lam, bivEval P u (w u) = 0 := by
    filter_upwards [Ioo_mem_nhds hlamρ.1 hlamρ.2] with u hu
    exact hroot u hu
  have hderiv :
      HasDerivAt w (-(N lam) / D lam) lam := by
    exact hasDerivAt_of_polynomial_root
      (hw.continuousAt (Ioo_mem_nhds hlamρ.1 hlamρ.2))
      hrootEventually hDne
  refine ⟨hderiv, ?_⟩
  rw [abs_div, abs_neg]
  apply (div_le_iff₀ (abs_pos.mpr hDne)).2
  have hmul :
      |N lam| * |D 0| ≤ (|N 0| + 1) * (2 * |D lam|) := by
    calc
      |N lam| * |D 0| ≤ (|N 0| + 1) * |D 0| :=
        mul_le_mul_of_nonneg_right hNbound (abs_nonneg _)
      _ ≤ (|N 0| + 1) * (2 * |D lam|) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · positivity
  dsimp [K]
  field_simp
  nlinarith

/-- A genuine local Puiseux reparameterization supplies the exact derivative
envelope used by the stochastic account construction.

If `w(λ) = g(λ^q)` on a positive punctured interval, `q > 0`, and the
derivative of `g` is bounded there by `K`, then after shrinking the interval
there is one positive `λ₀` such that
`|w'(λ)| ≤ λ^(q-1) / λ₀`. The choice of `λ₀` absorbs both the original
parameterization radius and the constant factor `Kq`.

Thus a construction that supplies this reparameterization also supplies the
game-facing derivative estimate. -/
theorem puiseuxDerivativeEnvelope_of_rpow_reparam
    {w g g' : ℝ → ℝ} {q ρ K : ℝ}
    (hq : 0 < q) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hreparam : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      w lam = g (lam ^ q))
    (hgderiv : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      HasDerivAt g (g' (lam ^ q)) (lam ^ q))
    (hgbound : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      |g' (lam ^ q)| ≤ K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt w
            (g' (lam ^ q) * (q * lam ^ (q - 1))) lam ∧
          |g' (lam ^ q) * (q * lam ^ (q - 1))| ≤
            lam ^ (q - 1) / lam0 := by
  let A := K * q
  let r := 1 / (A + 1)
  let lam0 := min ρ r / 2
  have hA : 0 ≤ A := mul_nonneg hK hq.le
  have hA1 : 0 < A + 1 := by linarith
  have hr : 0 < r := one_div_pos.mpr hA1
  have hlam0 : 0 < lam0 := half_pos (lt_min hρ hr)
  refine ⟨lam0, hlam0, ?_⟩
  intro lam hlam hlam0'
  have hlamρ : lam < ρ := by
    have hlam0ρ : lam0 ≤ ρ := by
      dsimp [lam0]
      have hmin : min ρ r ≤ ρ := min_le_left _ _
      nlinarith [lt_min hρ hr]
    exact hlam0'.trans_le hlam0ρ
  have hlamMem : lam ∈ Set.Ioo (0 : ℝ) ρ := ⟨hlam, hlamρ⟩
  have heq : w =ᶠ[𝓝 lam] fun u => g (u ^ q) := by
    filter_upwards [Ioo_mem_nhds hlam hlamρ] with u hu
    exact hreparam u hu
  have hpow :
      HasDerivAt (fun u : ℝ => u ^ q)
        (q * lam ^ (q - 1)) lam :=
    Real.hasDerivAt_rpow_const (Or.inl hlam.ne')
  have hwderiv :
      HasDerivAt w
        (g' (lam ^ q) * (q * lam ^ (q - 1))) lam :=
    ((hgderiv lam hlamMem).comp lam hpow).congr_of_eventuallyEq heq
  refine ⟨hwderiv, ?_⟩
  have hpowNonneg : 0 ≤ lam ^ (q - 1) :=
    Real.rpow_nonneg hlam.le _
  have hraw :
      |g' (lam ^ q) * (q * lam ^ (q - 1))| ≤
        A * lam ^ (q - 1) := by
    rw [abs_mul, abs_mul, abs_of_pos hq, abs_of_nonneg hpowNonneg]
    calc
      |g' (lam ^ q)| * (q * lam ^ (q - 1)) ≤
          K * (q * lam ^ (q - 1)) :=
        mul_le_mul_of_nonneg_right (hgbound lam hlamMem)
          (mul_nonneg hq.le hpowNonneg)
      _ = A * lam ^ (q - 1) := by ring
  have hlam0r : lam0 ≤ r := by
    dsimp [lam0]
    have hmin : min ρ r ≤ r := min_le_right _ _
    nlinarith [lt_min hρ hr]
  have hAr : A * r ≤ 1 := by
    dsimp [r]
    rw [one_div]
    rw [← div_eq_mul_inv]
    exact (div_le_one hA1).2 (by linarith)
  have hAlam0 : A * lam0 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlam0r hA).trans hAr
  have hAinv : A ≤ lam0⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hlam0).2 hAlam0
  calc
    |g' (lam ^ q) * (q * lam ^ (q - 1))| ≤
        A * lam ^ (q - 1) := hraw
    _ ≤ lam0⁻¹ * lam ^ (q - 1) :=
      mul_le_mul_of_nonneg_right hAinv hpowNonneg
    _ = lam ^ (q - 1) / lam0 := by
      rw [div_eq_mul_inv]
      ring

/-- An analytic real factor has a derivative that exists and is uniformly
bounded on some neighborhood of the origin. -/
theorem exists_analytic_derivative_bound
    {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ t, |t| < ρ →
        HasDerivAt g (deriv g t) t ∧ |deriv g t| ≤ K := by
  have hdifferentiable :
      ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ g t := by
    filter_upwards [hg.eventually_analyticAt] with t ht
    exact ht.differentiableAt
  have hderivContinuous : ContinuousAt (deriv g) 0 :=
    hg.deriv.continuousAt
  have hclose :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        dist (deriv g t) (deriv g 0) < 1 :=
    (Metric.tendsto_nhds.mp hderivContinuous.tendsto)
      1 zero_lt_one
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.mp (hdifferentiable.and hclose)
  let K := |deriv g 0| + 1
  refine ⟨ρ, K, hρ, by positivity, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0 : ℝ) ρ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact ht
  obtain ⟨hdiff, hdist⟩ := hball htball
  refine ⟨hdiff.hasDerivAt, ?_⟩
  rw [Real.dist_eq] at hdist
  dsimp [K]
  calc
    |deriv g t| =
        |(deriv g t - deriv g 0) + deriv g 0| := by ring_nf
    _ ≤ |deriv g t - deriv g 0| + |deriv g 0| :=
      abs_add_le _ _
    _ ≤ |deriv g 0| + 1 := by linarith

/-- A local analytic Puiseux reparameterization supplies the normalized
derivative envelope used by the stochastic account construction.

This consumes the literal analytic output of a convergent Newton--Puiseux
expansion: no derivative function or derivative bound is assumed. -/
theorem puiseuxDerivativeEnvelope_of_analytic_rpow_reparam
    {w g : ℝ → ℝ} {q ρ : ℝ}
    (hq : 0 < q) (hρ : 0 < ρ)
    (hreparam : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      w lam = g (lam ^ q))
    (hganalytic : AnalyticAt ℝ g 0) :
    let g' := deriv g
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt w
            (g' (lam ^ q) * (q * lam ^ (q - 1))) lam ∧
          |g' (lam ^ q) * (q * lam ^ (q - 1))| ≤
            lam ^ (q - 1) / lam0 := by
  dsimp only
  obtain ⟨ρg, K, hρg, hK, hg⟩ :=
    exists_analytic_derivative_bound hganalytic
  let a := min ρg 1
  let δ := a ^ q⁻¹
  let ρ' := min ρ δ
  have ha : 0 < a := lt_min hρg zero_lt_one
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha _
  have hρ' : 0 < ρ' := lt_min hρ hδ
  have hpowδ : δ ^ q = a := by
    dsimp [δ]
    exact Real.rpow_inv_rpow ha.le hq.ne'
  have ht (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) ρ') :
      |lam ^ q| < ρg := by
    have hlamδ : lam < δ :=
      hlam.2.trans_le (min_le_right ρ δ)
    have hlt : lam ^ q < δ ^ q :=
      Real.rpow_lt_rpow hlam.1.le hlamδ hq
    rw [hpowδ] at hlt
    rw [abs_of_pos (Real.rpow_pos_of_pos hlam.1 q)]
    exact hlt.trans_le (min_le_left ρg 1)
  exact puiseuxDerivativeEnvelope_of_rpow_reparam
    (w := w) (g := g) (g' := deriv g)
    hq hρ' hK
    (fun lam hlam =>
      hreparam lam ⟨hlam.1,
        hlam.2.trans_le (min_le_left ρ δ)⟩)
    (fun lam hlam => (hg (lam ^ q) (ht lam hlam)).1)
    (fun lam hlam => (hg (lam ^ q) (ht lam hlam)).2)

/-- A ramified algebraic branch whose regular factor is a simple polynomial
root supplies the normalized Puiseux derivative envelope.

The factor derivative and its bound are not hypotheses: the implicit function
theorem derives both from the polynomial relation after ramification. The two
radii distinguish the original representation interval for
`w(λ) = g(λ^q)` from the interval on which `g` is a regular polynomial root. -/
theorem puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root
    {P : Polynomial (Polynomial ℝ)}
    {w g : ℝ → ℝ} {q ρw ρg : ℝ}
    (hq : 0 < q) (hρw : 0 < ρw) (hρg : 0 < ρg)
    (hreparam : ∀ lam ∈ Set.Ioo (0 : ℝ) ρw,
      w lam = g (lam ^ q))
    (hg0 : ContinuousAt g 0)
    (hg : ContinuousOn g (Set.Ioo 0 ρg))
    (hroot : ∀ t ∈ Set.Ioo (0 : ℝ) ρg,
      bivEval P t (g t) = 0)
    (hD0 : bivEval (Polynomial.derivative P) 0 (g 0) ≠ 0) :
    let g' := fun t =>
      -(bivEval (bivDerivLam P) t (g t)) /
        bivEval (Polynomial.derivative P) t (g t)
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt w
            (g' (lam ^ q) * (q * lam ^ (q - 1))) lam ∧
          |g' (lam ^ q) * (q * lam ^ (q - 1))| ≤
            lam ^ (q - 1) / lam0 := by
  dsimp only
  obtain ⟨ρ', K, hρ', hρ'ρg, hK, hregular⟩ :=
    exists_regularPolynomialDerivativeBound
      hρg hg0 hg hroot hD0
  let a := min ρ' 1
  let δ := a ^ q⁻¹
  let ρ := min ρw δ
  have ha : 0 < a := lt_min hρ' zero_lt_one
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha _
  have hρ : 0 < ρ := lt_min hρw hδ
  have hpowδ : δ ^ q = a := by
    dsimp [δ]
    exact Real.rpow_inv_rpow ha.le hq.ne'
  have ht (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) ρ) :
      lam ^ q ∈ Set.Ioo (0 : ℝ) ρ' := by
    have hlamδ : lam < δ :=
      hlam.2.trans_le (min_le_right ρw δ)
    have hlt :
        lam ^ q < δ ^ q :=
      Real.rpow_lt_rpow hlam.1.le hlamδ hq
    rw [hpowδ] at hlt
    exact ⟨Real.rpow_pos_of_pos hlam.1 q,
      hlt.trans_le (min_le_left ρ' 1)⟩
  exact puiseuxDerivativeEnvelope_of_rpow_reparam
    (w := w) (g := g)
    (g' := fun t =>
      -(bivEval (bivDerivLam P) t (g t)) /
        bivEval (Polynomial.derivative P) t (g t))
    hq hρ hK
    (fun lam hlam =>
      hreparam lam ⟨hlam.1,
        hlam.2.trans_le (min_le_left ρw δ)⟩)
    (fun lam hlam => (hregular (lam ^ q) (ht lam hlam)).1)
    (fun lam hlam => (hregular (lam ^ q) (ht lam hlam)).2)

/-- A regular polynomial branch satisfies the normalized account
envelope with Puiseux exponent `q = 1`.

This is the regular-branch specialization of
`puiseuxDerivativeEnvelope_of_rpow_reparam`, using `g = w`. Branches with
`∂ᵥP(0, w(0)) = 0` do not satisfy this theorem's regularity hypothesis. -/
theorem puiseuxDerivativeEnvelope_of_regular_polynomial_root
    {P : Polynomial (Polynomial ℝ)} {w : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hw0 : ContinuousAt w 0)
    (hw : ContinuousOn w (Set.Ioo 0 ρ))
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      bivEval P lam (w lam) = 0)
    (hD0 : bivEval (Polynomial.derivative P) 0 (w 0) ≠ 0) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt w
          (-(bivEval (bivDerivLam P) lam (w lam)) /
            bivEval (Polynomial.derivative P) lam (w lam)) lam ∧
        |-(bivEval (bivDerivLam P) lam (w lam)) /
            bivEval (Polynomial.derivative P) lam (w lam)| ≤
          lam ^ ((1 : ℝ) - 1) / lam0 := by
  obtain ⟨ρ', K, hρ', _hρ'ρ, hK, hregular⟩ :=
    exists_regularPolynomialDerivativeBound
      hρ hw0 hw hroot hD0
  simpa only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, one_mul] using
    (puiseuxDerivativeEnvelope_of_rpow_reparam
      (w := w) (g := w)
      (g' := fun lam =>
        -(bivEval (bivDerivLam P) lam (w lam)) /
          bivEval (Polynomial.derivative P) lam (w lam))
      (q := (1 : ℝ)) (ρ := ρ') (K := K)
      zero_lt_one hρ' hK
      (fun lam _ => by rw [Real.rpow_one])
      (fun lam hlam => by
        simpa only [Real.rpow_one] using (hregular lam hlam).1)
      (fun lam hlam => by
        simpa only [Real.rpow_one] using (hregular lam hlam).2))

/-- A local Puiseux reparameterization has the expected right limit.

The positive exponent sends `λ` to `λ^q → 0` as `λ → 0⁺`; continuity of the
regular factor `g` then gives `w(λ) → g(0)`. Together with
`puiseuxDerivativeEnvelope_of_rpow_reparam`, this discharges both analytic
inputs of the account theorem once a Newton--Puiseux reparameterization has
been constructed. -/
theorem tendsto_zero_of_rpow_reparam
    {w g : ℝ → ℝ} {q ρ : ℝ}
    (hq : 0 < q) (hρ : 0 < ρ)
    (hreparam : ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
      w lam = g (lam ^ q))
    (hg : ContinuousAt g 0) :
    Filter.Tendsto w
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g 0)) := by
  have hpowFull :
      Filter.Tendsto (fun lam : ℝ => lam ^ q) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hq.ne'] using
      (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
  have hpow :
      Filter.Tendsto (fun lam : ℝ => lam ^ q)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
    hpowFull.mono_left inf_le_left
  have hcomp :
      Filter.Tendsto (fun lam : ℝ => g (lam ^ q))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g 0)) :=
    hg.tendsto.comp hpow
  apply hcomp.congr'
  have hIio : Set.Iio ρ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ)
  filter_upwards [hIio, self_mem_nhdsWithin] with lam hlamρ hlam
  exact (hreparam lam ⟨hlam, hlamρ⟩).symm

end Math
