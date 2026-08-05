/-
Scratch algebraic reduction for the analytic Bellman-germ construction.

This file contains only proved reductions.  In particular, the generic
finiteness hypothesis below is displayed explicitly rather than hidden as an
axiom.
-/

import Math.MultivariateElimination
import Math.UnivariatePolynomialCurveSelection
import Math.WeierstrassCurve
import Math.RamifiedWeierstrass
import Mathlib.Data.Complex.Basic
import GameTheory.Concepts.Stochastic.BellmanCurveGate

noncomputable section

open Filter Set SignType Topology

namespace Math
namespace CurveSelection.AlgebraicReductionScratch

open PolynomialSignCell
open MultivariateElimination

/-- Regard one distinguished variable as the coefficient parameter and all
other variables as affine variables. -/
noncomputable def parameterizeVariable
    {σ : Type*} (parameter : σ) :
    MvPolynomial σ ℝ ≃ₐ[ℝ]
      MvPolynomial {j : σ // j ≠ parameter} (Polynomial ℝ) := by
  classical
  exact
    (MvPolynomial.renameEquiv ℝ
      (Equiv.optionSubtypeNe parameter).symm).trans
      (MvPolynomial.optionEquivRight ℝ
        {j : σ // j ≠ parameter})

/-- Evaluation after `parameterizeVariable` is ordinary evaluation at the
parameter coordinate followed by evaluation of the remaining coordinates. -/
theorem eval_parameterizeVariable
    {σ : Type*} (parameter : σ)
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval₂
        (Polynomial.evalRingHom (x parameter))
        (fun j : {j : σ // j ≠ parameter} => x j.1)
        (parameterizeVariable parameter P) =
      MvPolynomial.eval x P := by
  classical
  let Φ : MvPolynomial σ ℝ →+* ℝ :=
    (MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom (x parameter))
      (fun j : {j : σ // j ≠ parameter} => x j.1)).comp
        (parameterizeVariable parameter).toRingHom
  have hΦ : Φ = MvPolynomial.eval x := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ, parameterizeVariable]
    · intro i
      by_cases hi : i = parameter
      · subst i
        simp [Φ, parameterizeVariable]
      · simp [Φ, parameterizeVariable, hi]
  exact DFunLike.congr_fun hΦ P

/-- The equations prescribed to have sign zero, viewed over the polynomial
parameter ring. -/
noncomputable def parameterizedZeroIdeal
    {I σ : Type*}
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ) :
    Ideal
      (MvPolynomial {j : σ // j ≠ parameter} (Polynomial ℝ)) :=
  Ideal.span
    (Set.range fun i : {i : I // τ i = 0} =>
      parameterizeVariable parameter (P i.1))

/-- Every point of the exact sign cell annihilates the parameterized zero
ideal after specializing the distinguished parameter. -/
theorem parameterizedZeroIdeal_le_evalKernel
    {I σ : Type*}
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    {x : σ → ℝ} (hx : x ∈ signCell P τ) :
    parameterizedZeroIdeal P τ parameter ≤
      RingHom.ker
        (MvPolynomial.eval₂Hom
          (Polynomial.evalRingHom (x parameter))
          (fun j : {j : σ // j ≠ parameter} => x j.1)) := by
  rw [parameterizedZeroIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change
    MvPolynomial.eval₂
        (Polynomial.evalRingHom (x parameter))
        (fun j : {j : σ // j ≠ parameter} => x j.1)
        (parameterizeVariable parameter (P i.1)) = 0
  rw [eval_parameterizeVariable]
  exact (eval_eq_zero_iff_of_mem_signCell hx i.1).2 i.2

/-- Product of all constraints carrying a strict sign, after treating the
distinguished coordinate as the polynomial parameter.  Its nonvanishing is
the single denominator used for Rabinowitsch saturation. -/
noncomputable def parameterizedStrictProduct
    {I σ : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ) :
    MvPolynomial {j : σ // j ≠ parameter} (Polynomial ℝ) := by
  classical
  exact ∏ i : {i : I // τ i ≠ 0},
    parameterizeVariable parameter (P i.1)

/-- The strict product does not vanish at a point of the exact sign cell. -/
theorem eval_parameterizedStrictProduct_ne_zero
    {I σ : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    {x : σ → ℝ} (hx : x ∈ signCell P τ) :
    MvPolynomial.eval₂
        (Polynomial.evalRingHom (x parameter))
        (fun j : {j : σ // j ≠ parameter} => x j.1)
        (parameterizedStrictProduct P τ parameter) ≠ 0 := by
  classical
  change
    (MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom (x parameter))
      (fun j : {j : σ // j ≠ parameter} => x j.1))
        (parameterizedStrictProduct P τ parameter) ≠ 0
  rw [parameterizedStrictProduct, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  change
    MvPolynomial.eval₂
      (Polynomial.evalRingHom (x parameter))
      (fun j : {j : σ // j ≠ parameter} => x j.1)
      (parameterizeVariable parameter (P i.1)) ≠ 0
  rw [eval_parameterizeVariable]
  intro hzero
  exact i.2
    ((eval_eq_zero_iff_of_mem_signCell hx i.1).mp hzero)

/-- Saturate the zero equations by the product of all strict constraints.
Every point of the exact sign cell lifts to this Rabinowitsch zero locus. -/
noncomputable def saturatedParameterizedIdeal
    {I σ : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ) :
    Ideal
      (MvPolynomial
        (Option {j : σ // j ≠ parameter}) (Polynomial ℝ)) :=
  rabinowitschIdeal
    (parameterizedZeroIdeal P τ parameter)
    (parameterizedStrictProduct P τ parameter)

/-- The canonical lift of a sign-cell point assigns the new Rabinowitsch
coordinate the inverse of the strict product. -/
noncomputable def saturatedPointLift
    {I σ : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x : σ → ℝ) :
    Option {j : σ // j ≠ parameter} → ℝ
  | none =>
      (MvPolynomial.eval₂
        (Polynomial.evalRingHom (x parameter))
        (fun j : {j : σ // j ≠ parameter} => x j.1)
        (parameterizedStrictProduct P τ parameter))⁻¹
  | some j => x j.1

/-- Every point of the exact sign cell annihilates the saturated ideal under
its canonical Rabinowitsch lift. -/
theorem saturatedParameterizedIdeal_le_evalKernel
    {I σ : Type*} [Fintype I]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    {x : σ → ℝ} (hx : x ∈ signCell P τ) :
    saturatedParameterizedIdeal P τ parameter ≤
      RingHom.ker
        (MvPolynomial.eval₂Hom
          (Polynomial.evalRingHom (x parameter))
          (saturatedPointLift P τ parameter x)) := by
  classical
  let e :
      MvPolynomial {j : σ // j ≠ parameter} (Polynomial ℝ) →+* ℝ :=
    MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom (x parameter))
      (fun j : {j : σ // j ≠ parameter} => x j.1)
  let E :
      MvPolynomial
        (Option {j : σ // j ≠ parameter}) (Polynomial ℝ) →+* ℝ :=
    MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom (x parameter))
      (saturatedPointLift P τ parameter x)
  have hzero :
      parameterizedZeroIdeal P τ parameter ≤ RingHom.ker e := by
    simpa [e] using
      parameterizedZeroIdeal_le_evalKernel P τ parameter hx
  have hstrict :
      e (parameterizedStrictProduct P τ parameter) ≠ 0 := by
    simpa [e] using
      eval_parameterizedStrictProduct_ne_zero
        P τ parameter hx
  change saturatedParameterizedIdeal P τ parameter ≤ RingHom.ker E
  rw [saturatedParameterizedIdeal, rabinowitschIdeal]
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change E (MvPolynomial.rename some f) = 0
    rw [MvPolynomial.eval₂Hom_rename]
    change e f = 0
    exact hzero hf
  · rw [Ideal.span_le]
    rintro z (rfl : z =
      MvPolynomial.X none *
        MvPolynomial.rename some
          (parameterizedStrictProduct P τ parameter) - 1)
    change E
      (MvPolynomial.X none *
        MvPolynomial.rename some
          (parameterizedStrictProduct P τ parameter) - 1) = 0
    simp only [E, map_sub, map_mul,
      MvPolynomial.coe_eval₂Hom, map_one]
    rw [MvPolynomial.eval₂_rename]
    simp only [MvPolynomial.eval₂_X, saturatedPointLift]
    have hlift_some :
        (fun j : {j : σ // j ≠ parameter} => x j.1) =
          saturatedPointLift P τ parameter x ∘ some := by
      rfl
    rw [← hlift_some]
    change
      (e (parameterizedStrictProduct P τ parameter))⁻¹ *
          e (parameterizedStrictProduct P τ parameter) - 1 = 0
    rw [inv_mul_cancel₀ hstrict]
    exact sub_self 1

/-- Evaluating a univariate coordinate relation inside a multivariate
polynomial ring is the same as the project's `bivEval` convention. -/
theorem eval₂_polynomial_aeval_X_eq_bivEval
    {κ : Type*}
    (q : Polynomial (Polynomial ℝ))
    (lam : ℝ) (y : κ → ℝ) (target : κ) :
    MvPolynomial.eval₂
        (Polynomial.evalRingHom lam) y
        (Polynomial.aeval (MvPolynomial.X target) q) =
      bivEval q lam (y target) := by
  rw [Polynomial.aeval_def]
  change
    (MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom lam) y)
        (Polynomial.eval₂
          (algebraMap (Polynomial ℝ)
            (MvPolynomial κ (Polynomial ℝ)))
          (MvPolynomial.X target) q) =
      bivEval q lam (y target)
  rw [Polynomial.hom_eval₂]
  simp [bivEval]

/-- If the strict-sign saturation is generically finite over the distinguished
parameter, then every remaining coordinate satisfies a genuine nonzero
bivariate polynomial relation on the entire exact sign cell.

This is the algebraic elimination output needed before Newton--Puiseux.  The
Rabinowitsch coordinate ensures that components on which a prescribed strict
constraint vanishes have been discarded. -/
theorem exists_coordinate_bivariateRelation_of_saturated_moduleFinite
    {I σ : Type*} [Fintype I] [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))]
    (target : {j : σ // j ≠ parameter}) :
    ∃ q : Polynomial (Polynomial ℝ),
      q ≠ 0 ∧
        ∀ x ∈ signCell P τ,
          bivEval q (x parameter) (x target.1) = 0 := by
  classical
  obtain ⟨q, hq, hqmem⟩ :=
    exists_nonzero_coordinateRelation_mem_of_moduleFinite_fractionRing
      (saturatedParameterizedIdeal P τ parameter) (some target)
  refine ⟨q, hq, ?_⟩
  intro x hx
  let E :
      MvPolynomial
        (Option {j : σ // j ≠ parameter}) (Polynomial ℝ) →+* ℝ :=
    MvPolynomial.eval₂Hom
      (Polynomial.evalRingHom (x parameter))
      (saturatedPointLift P τ parameter x)
  have hker :
      saturatedParameterizedIdeal P τ parameter ≤ RingHom.ker E := by
    simpa [E] using
      saturatedParameterizedIdeal_le_evalKernel
        P τ parameter hx
  have hz :
      E (Polynomial.aeval (MvPolynomial.X (some target)) q) = 0 := by
    exact hker hqmem
  rw [show
      E (Polynomial.aeval (MvPolynomial.X (some target)) q) =
        bivEval q (x parameter) (x target.1) by
      change
        MvPolynomial.eval₂
            (Polynomial.evalRingHom (x parameter))
            (saturatedPointLift P τ parameter x)
            (Polynomial.aeval (MvPolynomial.X (some target)) q) =
          bivEval q (x parameter) (x target.1)
      rw [eval₂_polynomial_aeval_X_eq_bivEval]
      rfl] at hz
  exact hz

/-- A closure approach through positive parameter values can be thinned to
one whose parameter is strictly decreasing to zero.  The selected assignments
still converge to the original endpoint and remain in the target set.

Strict decrease is useful when turning the sequence into the graph of a
single-valued partial algebraic branch. -/
theorem exists_strictAnti_parameter_approach
    {σ : Type*} [Finite σ]
    {A : Set (σ → ℝ)} {parameter : σ} {x₀ : σ → ℝ}
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure (A ∩ {x | 0 < x parameter})) :
    ∃ x : ℕ → (σ → ℝ),
      (∀ n, x n ∈ A) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      Tendsto (fun n => x n parameter) atTop (𝓝 0) := by
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨z, hzmem, hzlim⟩ :=
    (mem_closure_iff_seq_limit.mp hclosure)
  let a : ℕ → ℝ := fun n => z n parameter
  have hapos : ∀ n, 0 < a n := fun n => (hzmem n).2
  have halim : Tendsto a atTop (𝓝 0) := by
    have := (tendsto_pi_nhds.mp hzlim) parameter
    simpa [a, hparameter] using this
  have hglb : IsGLB (Set.range a) 0 :=
    IsGLB.range_of_tendsto (fun n => (hapos n).le) halim
  have hzero_notMem : (0 : ℝ) ∉ Set.range a := by
    rintro ⟨n, hn⟩
    have := hapos n
    rw [hn] at this
    exact (lt_irrefl 0 this).elim
  have hrange : (Set.range a).Nonempty :=
    ⟨a 0, Set.mem_range_self 0⟩
  obtain ⟨u, huanti, _hupos, hulim, humem⟩ :=
    hglb.exists_seq_strictAnti_tendsto_of_notMem
      hzero_notMem hrange
  choose φ hφ using humem
  have hφinj : Function.Injective φ := by
    intro n m hnm
    apply huanti.injective
    rw [← hφ n, ← hφ m, hnm]
  let x : ℕ → (σ → ℝ) := z ∘ φ
  have hxmem : ∀ n, x n ∈ A := fun n => (hzmem (φ n)).1
  have hxanti : StrictAnti (fun n => x n parameter) := by
    intro n m hnm
    change a (φ m) < a (φ n)
    rw [hφ n, hφ m]
    exact huanti hnm
  have hxpos : ∀ n, 0 < x n parameter :=
    fun n => (hzmem (φ n)).2
  have hxlim : Tendsto x atTop (𝓝 x₀) :=
    hzlim.comp hφinj.nat_tendsto_atTop
  have hxparameter :
      Tendsto (fun n => x n parameter) atTop (𝓝 0) := by
    have heq : (fun n => x n parameter) = u := by
      funext n
      exact hφ n
    rw [heq]
    exact hulim
  exact ⟨x, hxmem, hxanti, hxpos, hxlim, hxparameter⟩

/-- Replacing an approaching point in each parameter fiber by a nearest
point to the endpoint preserves convergence.  This is the compactness half
of the standard polar/nearest-point reduction: algebraic critical equations
may subsequently be imposed on the nearest points without losing the
selected germ. -/
theorem exists_nearest_compactFiber_approach
    {E : Type*} [PseudoMetricSpace E]
    (A : Set E) (parameter : E → ℝ) (x₀ : E)
    (x : ℕ → E)
    (hxA : ∀ n, x n ∈ A)
    (hxlim : Tendsto x atTop (𝓝 x₀))
    (hcompact :
      ∀ n,
        IsCompact
          (A ∩ {y | parameter y = parameter (x n)})) :
    ∃ y : ℕ → E,
      (∀ n, y n ∈ A) ∧
      (∀ n, parameter (y n) = parameter (x n)) ∧
      (∀ n,
        IsMinOn (fun z => dist z x₀)
          (A ∩ {z | parameter z = parameter (x n)}) (y n)) ∧
      Tendsto y atTop (𝓝 x₀) := by
  choose y hymem hymin using fun n =>
    (hcompact n).exists_isMinOn
      ⟨x n, hxA n, rfl⟩
      (continuous_id.dist continuous_const).continuousOn
  have hyA : ∀ n, y n ∈ A := fun n => (hymem n).1
  have hyparameter :
      ∀ n, parameter (y n) = parameter (x n) :=
    fun n => (hymem n).2
  have hydist :
      ∀ n, dist (y n) x₀ ≤ dist (x n) x₀ := by
    intro n
    exact hymin n ⟨hxA n, rfl⟩
  have hydistlim :
      Tendsto (fun n => dist (y n) x₀) atTop (𝓝 0) := by
    exact squeeze_zero
      (fun n => dist_nonneg)
      hydist
      (tendsto_iff_dist_tendsto_zero.mp hxlim)
  exact ⟨y, hyA, hyparameter, hymin,
    tendsto_iff_dist_tendsto_zero.mpr hydistlim⟩

/-- A positive closure germ with compact parameter fibers has a
strictly-parameter-decreasing sequence of fiberwise nearest points converging
to the same endpoint. -/
theorem exists_strictAnti_nearest_compactFiber_approach
    {σ : Type*} [Fintype σ]
    (A : Set (σ → ℝ)) (parameter : σ) (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure (A ∩ {x | 0 < x parameter}))
    (hcompact :
      ∀ lam,
        IsCompact
          (A ∩ {y | y parameter = lam})) :
    ∃ y : ℕ → (σ → ℝ),
      (∀ n, y n ∈ A) ∧
      StrictAnti (fun n => y n parameter) ∧
      (∀ n, 0 < y n parameter) ∧
      Tendsto y atTop (𝓝 x₀) ∧
      (∀ n,
        IsMinOn (fun z => dist z x₀)
          (A ∩ {z | z parameter = y n parameter}) (y n)) := by
  obtain ⟨x, hxA, hxanti, hxpos, hxlim, _hxparameter⟩ :=
    exists_strictAnti_parameter_approach hparameter hclosure
  obtain ⟨y, hyA, hyparameter, hymin, hylim⟩ :=
    exists_nearest_compactFiber_approach
      A (fun z => z parameter) x₀ x hxA hxlim
      (fun n => hcompact (x n parameter))
  have hyanti : StrictAnti (fun n => y n parameter) := by
    simpa only [hyparameter] using hxanti
  have hypos : ∀ n, 0 < y n parameter := by
    intro n
    rw [hyparameter n]
    exact hxpos n
  refine ⟨y, hyA, hyanti, hypos, hylim, ?_⟩
  intro n
  simpa only [hyparameter n] using hymin n

/-- Generically finite Rabinowitsch saturation plus closure yields a convergent
strict-parameter sequence on which every affine coordinate obeys one fixed
nonzero bivariate equation. -/
theorem exists_algebraic_strictAnti_signCell_approach
    {I σ : Type*} [Fintype I] [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure
        (signCell P τ ∩ {x | 0 < x parameter}))
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))] :
    ∃ (x : ℕ → (σ → ℝ))
        (q :
          {j : σ // j ≠ parameter} →
            Polynomial (Polynomial ℝ)),
      (∀ n, x n ∈ signCell P τ) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      Tendsto (fun n => x n parameter) atTop (𝓝 0) ∧
      (∀ j, q j ≠ 0) ∧
      ∀ n j,
        bivEval (q j) (x n parameter) (x n j.1) = 0 := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨x, hxmem, hxanti, hxpos, hxlim, hxparameter⟩ :=
    exists_strictAnti_parameter_approach
      hparameter hclosure
  choose q hqne hqroot using fun j =>
    exists_coordinate_bivariateRelation_of_saturated_moduleFinite
      P τ parameter j
  refine ⟨x, q, hxmem, hxanti, hxpos, hxlim,
    hxparameter, hqne, ?_⟩
  intro n j
  exact hqroot j (x n) (hxmem n)

/-- A fixed bivariate relation holding along a convergent assignment
sequence also holds at its endpoint. -/
theorem bivEval_endpoint_eq_zero_of_tendsto
    {σ : Type*} [Finite σ]
    {x : ℕ → (σ → ℝ)} {x₀ : σ → ℝ}
    (hxlim : Tendsto x atTop (𝓝 x₀))
    (parameter target : σ)
    (q : Polynomial (Polynomial ℝ))
    (hroot :
      ∀ n, bivEval q (x n parameter) (x n target) = 0) :
    bivEval q (x₀ parameter) (x₀ target) = 0 := by
  letI : Fintype σ := Fintype.ofFinite σ
  let F : (σ → ℝ) → ℝ :=
    (fun p : ℝ × ℝ => bivEval q p.1 p.2) ∘
      fun y => (y parameter, y target)
  have hF : Continuous F := by
    have hp :
        Continuous
          (fun y : σ → ℝ => (y parameter, y target)) :=
      (continuous_apply parameter).prodMk
        (continuous_apply target)
    exact (continuous_bivEval q).comp hp
  have htend : Tendsto (fun n => F (x n)) atTop (𝓝 (F x₀)) :=
    hF.continuousAt.tendsto.comp hxlim
  have hzero : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have heq : (fun n => F (x n)) = fun _n : ℕ => (0 : ℝ) := by
    funext n
    simpa only [F, Function.comp_apply] using hroot n
  rw [heq] at htend
  simpa only [F, Function.comp_apply] using
    tendsto_nhds_unique htend hzero

/-- Endpoint form of the generically finite algebraic approach: all selected
coordinate relations pass through the limiting assignment. -/
theorem exists_algebraic_strictAnti_signCell_approach_with_endpoint
    {I σ : Type*} [Fintype I] [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure
        (signCell P τ ∩ {x | 0 < x parameter}))
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))] :
    ∃ (x : ℕ → (σ → ℝ))
        (q :
          {j : σ // j ≠ parameter} →
            Polynomial (Polynomial ℝ)),
      (∀ n, x n ∈ signCell P τ) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      Tendsto (fun n => x n parameter) atTop (𝓝 0) ∧
      (∀ j, q j ≠ 0) ∧
      (∀ n j,
        bivEval (q j) (x n parameter) (x n j.1) = 0) ∧
      ∀ j, bivEval (q j) 0 (x₀ j.1) = 0 := by
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨x, q, hxmem, hxanti, hxpos, hxlim,
    hxparameter, hqne, hqroot⟩ :=
    exists_algebraic_strictAnti_signCell_approach
      P τ parameter x₀ hparameter hclosure
  refine ⟨x, q, hxmem, hxanti, hxpos, hxlim,
    hxparameter, hqne, hqroot, ?_⟩
  intro j
  simpa [hparameter] using
    bivEval_endpoint_eq_zero_of_tendsto
      hxlim parameter j.1 (q j) (fun n => hqroot n j)

/-- Removing parameter-only content and translating the limiting value
preserves an algebraic sequence branch up to its endpoint.  This is the exact
boundary datum consumed by Weierstrass preparation. -/
theorem bivEval_translate_primPart_endpoint_eq_zero_of_sequence
    {lam y : ℕ → ℝ} {L : ℝ}
    (hlam : Tendsto lam atTop (𝓝 0))
    (hlam_pos : ∀ n, 0 < lam n)
    (hy : Tendsto y atTop (𝓝 L))
    (q : Polynomial (Polynomial ℝ)) (hq : q ≠ 0)
    (hroot : ∀ n, bivEval q (lam n) (y n) = 0) :
    bivEval
      (translateBivPolynomialValue q L).primPart 0 0 = 0 := by
  let Q := translateBivPolynomialValue q L
  have hQ : Q ≠ 0 := by
    exact
      (Polynomial.comp_X_add_C_ne_zero_iff
        (p := q) (t := Polynomial.C L)).2 hq
  obtain ⟨ρ, hρ, hcontent⟩ :=
    exists_interval_content_eval_ne_zero Q hQ
  have hlam_lt : ∀ᶠ n in atTop, lam n < ρ :=
    hlam.eventually (Iio_mem_nhds hρ)
  have hprimitive :
      ∀ᶠ n in atTop,
        bivEval Q.primPart (lam n) (y n - L) = 0 := by
    filter_upwards [hlam_lt] with n hn
    apply bivEval_primPart_eq_zero Q
    · exact hcontent (lam n) ⟨hlam_pos n, hn⟩
    · dsimp only [Q]
      rw [bivEval_translateBivPolynomialValue]
      simpa using hroot n
  have hcentered :
      Tendsto (fun n => y n - L) atTop (𝓝 0) := by
    simpa using hy.sub_const L
  have hpair :
      Tendsto (fun n => (lam n, y n - L))
        atTop (𝓝 (0, 0)) :=
    hlam.prodMk_nhds hcentered
  have hvalue :
      Tendsto
        (fun n => bivEval Q.primPart (lam n) (y n - L))
        atTop
        (𝓝 (bivEval Q.primPart 0 0)) := by
    exact (continuous_bivEval Q.primPart).continuousAt.tendsto.comp hpair
  have hvalue_zero :
      Tendsto
        (fun n => bivEval Q.primPart (lam n) (y n - L))
        atTop (𝓝 0) :=
    tendsto_const_nhds.congr'
      (hprimitive.mono fun _n hn => hn.symm)
  exact tendsto_nhds_unique hvalue hvalue_zero

/-- If a bivariate polynomial vanishes at `(λ,y) = (0,0)`, reducing the
parameter-series coefficients makes the outer power series have zero constant
coefficient. -/
theorem constantCoeff_map_residue_bivPolynomialToIteratedPowerSeries_eq_zero
    (Q : Polynomial (Polynomial ℝ))
    (hQ : bivEval Q 0 0 = 0) :
    PowerSeries.constantCoeff
        (PowerSeries.map
          (IsLocalRing.residue (PowerSeries ℝ))
          (bivPolynomialToIteratedPowerSeries Q)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map, IsLocalRing.residue_eq_zero_iff,
    PowerSeries.maximalIdeal_eq_span_X,
    Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
  have hQ' : (Q.coeff 0).eval 0 = 0 := by
    simpa [bivEval] using hQ
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hQ'
  simpa [bivPolynomialToIteratedPowerSeries,
    bivPolynomialToPowerSeriesPolynomial] using hQ'

/-- A Weierstrass boundary passing through the centered endpoint has positive
degree.  Thus the resulting distinguished polynomial is a genuine
Newton--Puiseux input, not the constant polynomial `1`. -/
theorem natDegree_pos_of_weierstrassFactorization_of_bivEval_zero
    {Q : Polynomial (Polynomial ℝ)}
    {f : Polynomial (PowerSeries ℝ)}
    {unit : PowerSeries (PowerSeries ℝ)}
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f unit)
    (hQ : bivEval Q 0 0 = 0) :
    0 < f.natDegree := by
  let I := IsLocalRing.maximalIdeal (PowerSeries ℝ)
  have hI : I ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal (PowerSeries ℝ)).ne_top
  rw [H.natDegree_eq_toNat_order_map_of_ne_top hI]
  apply ENat.toNat_pos
  · exact PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr
      (constantCoeff_map_residue_bivPolynomialToIteratedPowerSeries_eq_zero
        Q hQ)
  · exact ne_of_lt
      (PowerSeries.order_finite_iff_ne_zero.mpr
        (H.map_ne_zero_of_ne_top hI))

/-- The only algebraic input still needed after Weierstrass preparation is
the ramified-root property.  Under that property, a positive-degree
Weierstrass boundary has a centered formal branch. -/
theorem exists_centeredFormalBranch_of_hasRamifiedRootProperty
    (Hroot : HasRamifiedRootProperty ℝ)
    {g : PowerSeries (PowerSeries ℝ)}
    {f : Polynomial (PowerSeries ℝ)}
    {unit : PowerSeries (PowerSeries ℝ)}
    (Hfactor : g.IsWeierstrassFactorization f unit)
    (hdegree : 0 < f.natDegree) :
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries ℝ),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s ∧
      s.constantCoeff = 0 := by
  obtain ⟨p, hp, s, hs⟩ :=
    Hroot f Hfactor.isDistinguishedAt.monic hdegree
  refine ⟨p, hp, s, hs, ?_⟩
  exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    (isDistinguishedAt_ramifyPowerSeriesPolynomial
      Hfactor.isDistinguishedAt p hp) hs

/-- The preceding construction can be chosen simultaneously for an arbitrary
family of Weierstrass boundaries.  No common ramification is asserted here;
that finite synchronization is a separate, elementary step when the index
type is finite. -/
theorem exists_centeredFormalBranches_of_hasRamifiedRootProperty
    {J : Type*}
    (Hroot : HasRamifiedRootProperty ℝ)
    (g : J → PowerSeries (PowerSeries ℝ))
    (f : J → Polynomial (PowerSeries ℝ))
    (unit : J → PowerSeries (PowerSeries ℝ))
    (Hfactor :
      ∀ j, (g j).IsWeierstrassFactorization (f j) (unit j))
    (hdegree : ∀ j, 0 < (f j).natDegree) :
    ∃ (p : J → ℕ) (s : J → PowerSeries ℝ)
        (hp : ∀ j, p j ≠ 0),
      (∀ j, (ramifyPowerSeriesPolynomial
        (p j) (hp j) (f j)).IsRoot (s j)) ∧
      ∀ j, (s j).constantCoeff = 0 := by
  classical
  choose p hp s hs hcenter using fun j =>
    exists_centeredFormalBranch_of_hasRamifiedRootProperty
      Hroot (Hfactor j) (hdegree j)
  exact ⟨p, s, hp, hs, hcenter⟩

/-- Finitely many distinguished boundaries admit one common ramification
after which every boundary splits, and every resulting formal root is
centered.  Taking the product of the individual ramification indices is
enough. -/
theorem exists_commonRamification_centeredSplittings
    {J : Type*} [Finite J]
    (Hroot : HasRamifiedRootProperty ℝ)
    (f : J → Polynomial (PowerSeries ℝ))
    (Hdist :
      ∀ j, (f j).IsDistinguishedAt
        (IsLocalRing.maximalIdeal (PowerSeries ℝ))) :
    ∃ (q : ℕ) (hq : q ≠ 0),
      ∀ j,
        (ramifyPowerSeriesPolynomial q hq (f j)).Splits ∧
        ∀ s,
          (ramifyPowerSeriesPolynomial q hq (f j)).IsRoot s →
            s.constantCoeff = 0 := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  choose p hp hsplit using fun j =>
    hasRamifiedPowerSeriesSplitting_of_hasRamifiedRootProperty
      Hroot (f j) (Hdist j).monic
  let q : ℕ := ∏ j, p j
  have hq : q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _hj => hp j
  refine ⟨q, hq, fun j => ?_⟩
  have hp_dvd : p j ∣ q := by
    exact Finset.dvd_prod_of_mem (fun k => p k) (Finset.mem_univ j)
  obtain ⟨r, hr⟩ := hp_dvd
  have hr_ne : r ≠ 0 := by
    intro hr0
    apply hq
    rw [hr, hr0, mul_zero]
  have hsplit' :
      (ramifyPowerSeriesPolynomial r hr_ne
        (ramifyPowerSeriesPolynomial (p j) (hp j) (f j))).Splits :=
    (hsplit j).map (PowerSeries.expand r hr_ne).toRingHom
  have hsplitq :
      (ramifyPowerSeriesPolynomial q hq (f j)).Splits := by
    rw [ramifyPowerSeriesPolynomial_comp] at hsplit'
    simpa [hr, mul_comm] using hsplit'
  refine ⟨hsplitq, ?_⟩
  intro s hs
  exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    (isDistinguishedAt_ramifyPowerSeriesPolynomial
      (Hdist j) q hq) hs

/-- Field-extension version of the common-ramification theorem.  This is the
mathematically relevant form over `ℝ`: extend coefficients to `ℂ`, apply
Newton--Puiseux there, and later recover the real branch selected by the real
approaching sequence. -/
theorem exists_commonRamification_centeredSplittingsOver
    {K L : Type*} [Field K] [Field L]
    {J : Type*} [Finite J]
    (σ : K →+* L)
    (Hroot : HasRamifiedRootProperty L)
    (f : J → Polynomial (PowerSeries K))
    (Hdist :
      ∀ j, (f j).IsDistinguishedAt
        (IsLocalRing.maximalIdeal (PowerSeries K))) :
    ∃ (q : ℕ) (hq : q ≠ 0),
      ∀ j,
        (ramifyPowerSeriesPolynomial q hq
          (mapPowerSeriesPolynomial σ (f j))).Splits ∧
        ∀ s,
          (ramifyPowerSeriesPolynomial q hq
            (mapPowerSeriesPolynomial σ (f j))).IsRoot s →
            s.constantCoeff = 0 := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  choose p hp hsplit using fun j =>
    hasRamifiedPowerSeriesSplittingOver_of_hasRamifiedRootProperty
      σ Hroot (Hdist j).monic
  let q : ℕ := ∏ j, p j
  have hq : q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _hj => hp j
  refine ⟨q, hq, fun j => ?_⟩
  have hp_dvd : p j ∣ q := by
    exact Finset.dvd_prod_of_mem (fun k => p k) (Finset.mem_univ j)
  obtain ⟨r, hr⟩ := hp_dvd
  have hr_ne : r ≠ 0 := by
    intro hr0
    apply hq
    rw [hr, hr0, mul_zero]
  have hsplit' :
      (ramifyPowerSeriesPolynomial r hr_ne
        (ramifyPowerSeriesPolynomial (p j) (hp j)
          (mapPowerSeriesPolynomial σ (f j)))).Splits :=
    (hsplit j).map (PowerSeries.expand r hr_ne).toRingHom
  have hsplitq :
      (ramifyPowerSeriesPolynomial q hq
        (mapPowerSeriesPolynomial σ (f j))).Splits := by
    rw [ramifyPowerSeriesPolynomial_comp] at hsplit'
    simpa [hr, mul_comm] using hsplit'
  refine ⟨hsplitq, ?_⟩
  intro s hs
  exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    (isDistinguishedAt_ramifyPowerSeriesPolynomial
      (isDistinguishedAt_mapPowerSeriesPolynomial σ (Hdist j))
      q hq) hs

/-- Every coordinate relation obtained from the saturated finite algebraic
reduction has a centered primitive Weierstrass boundary polynomial. -/
theorem exists_coordinate_weierstrassBoundaries_of_saturated_moduleFinite
    {I σ : Type*} [Fintype I] [Finite σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure
        (signCell P τ ∩ {x | 0 < x parameter}))
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))] :
    ∃ (x : ℕ → (σ → ℝ))
        (q :
          {j : σ // j ≠ parameter} →
            Polynomial (Polynomial ℝ))
        (f :
          {j : σ // j ≠ parameter} →
            Polynomial (PowerSeries ℝ))
        (unit :
          {j : σ // j ≠ parameter} →
            PowerSeries (PowerSeries ℝ)),
      (∀ n, x n ∈ signCell P τ) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      (∀ j, q j ≠ 0) ∧
      (∀ n j,
        bivEval (q j) (x n parameter) (x n j.1) = 0) ∧
      (∀ j,
        bivEval
          (translateBivPolynomialValue (q j) (x₀ j.1)).primPart
          0 0 = 0) ∧
      (∀ j, 0 < (f j).natDegree) ∧
      ∀ j,
        (bivPolynomialToIteratedPowerSeries
          (translateBivPolynomialValue
            (q j) (x₀ j.1)).primPart).IsWeierstrassFactorization
              (f j) (unit j) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨x, q, hxmem, hxanti, hxpos, hxlim,
    hxparameter, hqne, hqroot⟩ :=
    exists_algebraic_strictAnti_signCell_approach
      P τ parameter x₀ hparameter hclosure
  have hprimitive :
      ∀ j,
        bivEval
          (translateBivPolynomialValue (q j) (x₀ j.1)).primPart
          0 0 = 0 := by
    intro j
    exact
      bivEval_translate_primPart_endpoint_eq_zero_of_sequence
        hxparameter hxpos
        ((tendsto_pi_nhds.mp hxlim) j.1)
        (q j) (hqne j) (fun n => hqroot n j)
  choose f unit hfactor using fun j =>
    exists_weierstrassFactorization_translate_primPart
      (q j) (x₀ j.1)
  have hdegree : ∀ j, 0 < (f j).natDegree := by
    intro j
    exact
      natDegree_pos_of_weierstrassFactorization_of_bivEval_zero
        (hfactor j) (hprimitive j)
  exact ⟨x, q, f, unit, hxmem, hxanti, hxpos, hxlim,
    hqne, hqroot, hprimitive, hdegree, hfactor⟩

/-- Complete formal output of the elimination route: the selected sign-cell
sequence has one algebraic relation per coordinate, and after one common
ramification all corresponding Weierstrass boundaries split into centered
formal branches. -/
theorem exists_coordinate_commonRamifiedSplittings_of_saturated_moduleFinite
    {I σ : Type*} [Fintype I] [Finite σ]
    (Hroot : HasRamifiedRootProperty ℝ)
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure
        (signCell P τ ∩ {x | 0 < x parameter}))
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))] :
    ∃ (x : ℕ → (σ → ℝ))
        (relation :
          {j : σ // j ≠ parameter} →
            Polynomial (Polynomial ℝ))
        (f :
          {j : σ // j ≠ parameter} →
            Polynomial (PowerSeries ℝ))
        (unit :
          {j : σ // j ≠ parameter} →
            PowerSeries (PowerSeries ℝ))
        (ram : ℕ) (hram : ram ≠ 0),
      (∀ n, x n ∈ signCell P τ) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      (∀ j, relation j ≠ 0) ∧
      (∀ n j,
        bivEval (relation j) (x n parameter) (x n j.1) = 0) ∧
      (∀ j,
        bivEval
          (translateBivPolynomialValue
            (relation j) (x₀ j.1)).primPart 0 0 = 0) ∧
      (∀ j, 0 < (f j).natDegree) ∧
      (∀ j,
        (bivPolynomialToIteratedPowerSeries
          (translateBivPolynomialValue
            (relation j) (x₀ j.1)).primPart).IsWeierstrassFactorization
              (f j) (unit j)) ∧
      ∀ j,
        (ramifyPowerSeriesPolynomial ram hram (f j)).Splits ∧
        ∀ s,
          (ramifyPowerSeriesPolynomial ram hram (f j)).IsRoot s →
            s.constantCoeff = 0 := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨x, relation, f, unit, hxmem, hxanti, hxpos, hxlim,
    hrelation_ne, hrelation_root, hprimitive, hdegree, hfactor⟩ :=
    exists_coordinate_weierstrassBoundaries_of_saturated_moduleFinite
      P τ parameter x₀ hparameter hclosure
  obtain ⟨ram, hram, hsplit⟩ :=
    exists_commonRamification_centeredSplittings
      Hroot f (fun j => (hfactor j).isDistinguishedAt)
  exact
    ⟨x, relation, f, unit, ram, hram, hxmem, hxanti, hxpos,
      hxlim, hrelation_ne, hrelation_root, hprimitive, hdegree,
      hfactor, hsplit⟩

/-- Correct complex Newton--Puiseux version of the complete formal output.
Real distinguished polynomials need not split over real formal power series;
after coefficient extension to `ℂ`, one common ramification splits every
coordinate boundary. -/
theorem
    exists_coordinate_commonComplexRamifiedSplittings_of_saturated_moduleFinite
    {I σ : Type*} [Fintype I] [Finite σ]
    (Hroot : HasRamifiedRootProperty ℂ)
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I) (parameter : σ)
    (x₀ : σ → ℝ)
    (hparameter : x₀ parameter = 0)
    (hclosure :
      x₀ ∈ closure
        (signCell P τ ∩ {x | 0 < x parameter}))
    [Module.Finite
      (FractionRing (Polynomial ℝ))
      (MvPolynomial
          (Option {j : σ // j ≠ parameter})
          (FractionRing (Polynomial ℝ)) ⧸
        (saturatedParameterizedIdeal P τ parameter).map
          (MvPolynomial.map
            (algebraMap (Polynomial ℝ)
              (FractionRing (Polynomial ℝ)))))] :
    ∃ (x : ℕ → (σ → ℝ))
        (relation :
          {j : σ // j ≠ parameter} →
            Polynomial (Polynomial ℝ))
        (f :
          {j : σ // j ≠ parameter} →
            Polynomial (PowerSeries ℝ))
        (unit :
          {j : σ // j ≠ parameter} →
            PowerSeries (PowerSeries ℝ))
        (ram : ℕ) (hram : ram ≠ 0),
      (∀ n, x n ∈ signCell P τ) ∧
      StrictAnti (fun n => x n parameter) ∧
      (∀ n, 0 < x n parameter) ∧
      Tendsto x atTop (𝓝 x₀) ∧
      (∀ j, relation j ≠ 0) ∧
      (∀ n j,
        bivEval (relation j) (x n parameter) (x n j.1) = 0) ∧
      (∀ j,
        bivEval
          (translateBivPolynomialValue
            (relation j) (x₀ j.1)).primPart 0 0 = 0) ∧
      (∀ j, 0 < (f j).natDegree) ∧
      (∀ j,
        (bivPolynomialToIteratedPowerSeries
          (translateBivPolynomialValue
            (relation j) (x₀ j.1)).primPart).IsWeierstrassFactorization
              (f j) (unit j)) ∧
      ∀ j,
        (ramifyPowerSeriesPolynomial ram hram
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).Splits ∧
        ∀ s,
          (ramifyPowerSeriesPolynomial ram hram
            (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).IsRoot s →
            s.constantCoeff = 0 := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  obtain ⟨x, relation, f, unit, hxmem, hxanti, hxpos, hxlim,
    hrelation_ne, hrelation_root, hprimitive, hdegree, hfactor⟩ :=
    exists_coordinate_weierstrassBoundaries_of_saturated_moduleFinite
      P τ parameter x₀ hparameter hclosure
  obtain ⟨ram, hram, hsplit⟩ :=
    exists_commonRamification_centeredSplittingsOver
      Complex.ofRealHom Hroot f
      (fun j => (hfactor j).isDistinguishedAt)
  exact
    ⟨x, relation, f, unit, ram, hram, hxmem, hxanti, hxpos,
      hxlim, hrelation_ne, hrelation_root, hprimitive, hdegree,
      hfactor, hsplit⟩

end CurveSelection.AlgebraicReductionScratch
end Math
