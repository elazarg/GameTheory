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
* No ready-made "bounded monotone function has vanishing oscillation near an excluded endpoint"
  lemma was found (`MonotoneOn.tendsto_nhdsWithin_Ioo_left` is stated for the *right* endpoint of
  an `Ioo`, not the left); see the `TODO` on `dist_le_eVariationOn_uIcc_of_polynomial_root` below.

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

## TODO (not landed in this file)

* `dist_le_eVariationOn_uIcc_of_polynomial_root` additionally claims (and does *not* prove) that
  `eVariationOn w (Set.Ioo 0 ρ') → 0` as `ρ' → 0⁺`. The missing statement is: for `w` eventually
  monotone (or antitone) and bounded on `Set.Ioo 0 ρ` (as furnished by
  `eventually_monotone_of_polynomial_root`), `Filter.Tendsto (fun ρ' => eVariationOn w (Set.Ioo 0
  ρ')) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)`. The expected route: a bounded `MonotoneOn` function on
  `Set.Ioo 0 ρ` has a limit `L` along `nhdsWithin 0 (Set.Ioi 0)` (reflect/adapt
  `MonotoneOn.tendsto_nhdsWithin_Ioo_left`, which is stated for the right endpoint), after which
  `eVariationOn w (Set.Ioo 0 ρ') = ENNReal.ofReal (sSup (w '' Set.Ioo 0 ρ') - L)` (for monotone `w`;
  `MonotoneOn.eVariationOn_le` gives one inequality) and the right-hand side `→ 0` as `ρ' → 0⁺` by
  continuity of `sSup (w '' Set.Ioo 0 ·)` at `0`, itself following from the limit `L`.
-/

open Polynomial Set

namespace Math

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

/-- **Target 2(b), interval control.** The value difference `w a - w b` is controlled by the
total variation on the (order-independent) interval spanned by `a` and `b` — not by a
decreasing-chain sum — which is what a criterion whose index moves in both directions needs:
`min a b` and `max a b` may occur in either order as the index varies. Also records that the
total variation on the whole eventually-monotone interval is finite.

**Remaining gap (not proved here):** that this tail variation `eVariationOn w (Ioo 0 ρ')` tends to
`0` as `ρ' → 0⁺`. This should follow because a bounded monotone (or antitone) function has a limit
at `0⁺` (`MonotoneOn.tendsto_nhdsWithin_Ioo_left`-style, applied at the reflected/rescaled interval
since that lemma is stated for the *right* endpoint of `Ioo`, not the left) so its oscillation on
shrinking sub-intervals `Ioo 0 ρ'` vanishes; formalising the endpoint reflection and the
"oscillation → 0" step from "has a limit" was not undertaken in this pass. -/
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

end Math
