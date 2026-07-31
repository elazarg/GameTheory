/- Production algebraic-to-analytic convergence implementation for the
analytic Bellman-germ construction. -/
import Math.CurveSelection.Termination
import Math.CurveSelection.FactorCoverage
import Math.AnalyticImplicitFunction
import Math.RamifiedWeierstrass
import Math.WeierstrassCurve
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Set Topology
open scoped PowerSeries.WithPiTopology

namespace Math
namespace CurveSelection.ConvergenceScratch

open CurveSelection.FactorCoverageScratch
open CurveSelection.TerminationScratch

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- The analytic implicit chart, specialized to complex normed spaces. -/
theorem analyticAt_implicitFunctionData_complex
    (φ : ImplicitFunctionData ℂ E F G)
    (hleft : AnalyticAt ℂ φ.leftFun φ.pt)
    (hright : AnalyticAt ℂ φ.rightFun φ.pt) :
    AnalyticAt ℂ
      (φ.implicitFunction (φ.leftFun φ.pt))
      (φ.rightFun φ.pt) := by
  let i : E ≃L[ℂ] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl
      φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
      φ.isCompl_ker
  have hprod : AnalyticAt ℂ φ.prodFun φ.pt := by
    change
      AnalyticAt ℂ
        (fun x => (φ.leftFun x, φ.rightFun x)) φ.pt
    exact hleft.prod hright
  obtain ⟨p, hp⟩ := hprod
  have hderiv :
      continuousMultilinearCurryFin1 ℂ E (F × G) (p 1) =
        (i : E →L[ℂ] F × G) := by
    exact hp.hasFDerivAt.unique φ.hasStrictFDerivAt.hasFDerivAt
  have hp_one :
      p 1 =
        (continuousMultilinearCurryFin1 ℂ E (F × G)).symm i := by
    apply (continuousMultilinearCurryFin1 ℂ E (F × G)).injective
    rw [hderiv]
    exact
      (continuousMultilinearCurryFin1 ℂ E (F × G)).apply_symm_apply i
  have hinverse :
      AnalyticAt ℂ
        φ.toOpenPartialHomeomorph.symm
        (φ.prodFun φ.pt) := by
    refine ⟨p.leftInv i φ.pt, ?_⟩
    simpa only [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
      φ.toOpenPartialHomeomorph.hasFPowerSeriesAt_symm
        φ.pt_mem_toOpenPartialHomeomorph_source hp hp_one
  have hslice :
      AnalyticAt ℂ
        (fun y : G => (φ.leftFun φ.pt, y))
        (φ.rightFun φ.pt) :=
    analyticAt_const.prod analyticAt_id
  have hcomposition :=
    hinverse.comp_of_eq hslice (by
      simp only [ImplicitFunctionData.prodFun_apply])
  have hfun :
      φ.toOpenPartialHomeomorph.symm ∘
          (fun y : G => (φ.leftFun φ.pt, y)) =
        φ.implicitFunction (φ.leftFun φ.pt) := by
    rfl
  rw [← hfun]
  exact hcomposition

/-- The product-domain implicit function is complex analytic. -/
theorem analyticAt_implicitFunctionOfProdDomain_complex
    {u : E × F} {f : E × F → G}
    {f' : E × F →L[ℂ] G}
    (hf' : HasStrictFDerivAt f f' u)
    (hf : AnalyticAt ℂ f u)
    (hinv :
      (f' ∘L ContinuousLinearMap.inr ℂ E F).IsInvertible) :
    AnalyticAt ℂ
      (hf'.implicitFunctionOfProdDomain hinv) u.1 := by
  let φ : ImplicitFunctionData ℂ (E × F) G E :=
    hf'.implicitFunctionDataOfProdDomain hinv
  have hleft : AnalyticAt ℂ φ.leftFun φ.pt := by
    simpa [φ] using hf
  have hright : AnalyticAt ℂ φ.rightFun φ.pt := by
    simpa [φ] using
      (ContinuousLinearMap.fst ℂ E F).analyticAt u
  have hfull :
      AnalyticAt ℂ
        (φ.implicitFunction (φ.leftFun φ.pt))
        (φ.rightFun φ.pt) :=
    analyticAt_implicitFunctionData_complex φ hleft hright
  have hsnd :
      AnalyticAt ℂ
        (fun x =>
          (ContinuousLinearMap.snd ℂ E F)
            (φ.implicitFunction (φ.leftFun φ.pt) x))
        (φ.rightFun φ.pt) :=
    ((ContinuousLinearMap.snd ℂ E F).analyticAt
      (φ.implicitFunction (φ.leftFun φ.pt)
        (φ.rightFun φ.pt))).comp hfull
  simpa [φ, HasStrictFDerivAt.implicitFunctionOfProdDomain_def] using
    hsnd

/-- Analyticity of the curried complex bivariate implicit function. -/
theorem analyticAt_implicitFunctionOfBivariate_complex
    {u : E × F}
    {f : E → F → G}
    {f₁ : E → F → E →L[ℂ] G}
    {f₂ : E → F → F →L[ℂ] G}
    (df₁ :
      ∀ᶠ v in 𝓝 u,
        HasFDerivAt (fun x => f x v.2) (f₁ v.1 v.2) v.1)
    (df₂ :
      ∀ᶠ v in 𝓝 u,
        HasFDerivAt (fun y => f v.1 y) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (Function.uncurry f₁) u)
    (cf₂ : ContinuousAt (Function.uncurry f₂) u)
    (hinv : (f₂ u.1 u.2).IsInvertible)
    (hf : AnalyticAt ℂ (Function.uncurry f) u) :
    AnalyticAt ℂ
      (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv) u.1 := by
  let hstrict :=
    hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂
  have hinv' :
      ((f₁ u.1 u.2).coprod (f₂ u.1 u.2) ∘L
          ContinuousLinearMap.inr ℂ E F).IsInvertible := by
    simpa using hinv
  have h :=
    analyticAt_implicitFunctionOfProdDomain_complex hstrict hf hinv'
  simpa [implicitFunctionOfBivariate_def, hstrict] using h

/-- Evaluation of a polynomial in `Y` whose coefficients are polynomials in
the complex parameter `X`. -/
noncomputable def complexBivEval
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) : ℂ :=
  Polynomial.eval₂ (Polynomial.evalRingHom x) y P

theorem complexBivEval_eq_sum
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    complexBivEval P x y =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        (P.coeff i).eval x * y ^ i := by
  simp [complexBivEval, Polynomial.eval₂_eq_sum_range,
    Polynomial.coe_evalRingHom]

theorem complexBivEval_eq_eval_map
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    complexBivEval P x y =
      (P.map (Polynomial.evalRingHom x)).eval y :=
  Polynomial.eval₂_eq_eval_map _

/-- Coefficientwise differentiation in the parameter. -/
noncomputable def complexBivDerivX
    (P : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial ℂ) :=
  ∑ i ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (Polynomial.derivative (P.coeff i)) *
      Polynomial.X ^ i

theorem coeff_complexBivDerivX
    (P : Polynomial (Polynomial ℂ)) (j : ℕ) :
    (complexBivDerivX P).coeff j =
      Polynomial.derivative (P.coeff j) := by
  rw [complexBivDerivX, Polynomial.finsetSum_coeff]
  by_cases hj : j < P.natDegree + 1
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i _ hij
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hij)]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'
  · have hcoeff0 : P.coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff0, Polynomial.derivative_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hij : i ≠ j := by
      simp only [Finset.mem_range] at hi
      omega
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hij)]

theorem complexBivDerivX_natDegree_le
    (P : Polynomial (Polynomial ℂ)) :
    (complexBivDerivX P).natDegree ≤ P.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [coeff_complexBivDerivX,
    Polynomial.coeff_eq_zero_of_natDegree_lt hN,
    Polynomial.derivative_zero]

theorem complexBivEval_complexBivDerivX
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    complexBivEval (complexBivDerivX P) x y =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        (Polynomial.derivative (P.coeff i)).eval x * y ^ i := by
  have hn :
      (complexBivDerivX P).natDegree < P.natDegree + 1 :=
    Nat.lt_succ_of_le (complexBivDerivX_natDegree_le P)
  rw [complexBivEval,
    Polynomial.eval₂_eq_sum_range' (Polynomial.evalRingHom x) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_complexBivDerivX, Polynomial.coe_evalRingHom]

theorem hasDerivAt_complexBivEval_left
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    HasDerivAt (fun u => complexBivEval P u y)
      (complexBivEval (complexBivDerivX P) x y) x := by
  rw [complexBivEval_complexBivDerivX]
  have heq :
      (fun u => complexBivEval P u y) =
        fun u =>
          ∑ i ∈ Finset.range (P.natDegree + 1),
            (P.coeff i).eval u * y ^ i :=
    funext fun u => complexBivEval_eq_sum P u y
  rw [heq, ← Finset.sum_fn]
  exact HasDerivAt.sum fun i
      (_ : i ∈ Finset.range (P.natDegree + 1)) =>
    ((P.coeff i).hasDerivAt x).mul_const (y ^ i)

theorem hasDerivAt_complexBivEval_right
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    HasDerivAt (fun v => complexBivEval P x v)
      (complexBivEval (Polynomial.derivative P) x y) y := by
  have heq :
      (fun v => complexBivEval P x v) =
        fun v => (P.map (Polynomial.evalRingHom x)).eval v :=
    funext fun v => complexBivEval_eq_eval_map P x v
  rw [heq, complexBivEval_eq_eval_map,
    ← Polynomial.derivative_map]
  exact (P.map (Polynomial.evalRingHom x)).hasDerivAt y

theorem continuous_complexBivEval
    (P : Polynomial (Polynomial ℂ)) :
    Continuous fun p : ℂ × ℂ =>
      complexBivEval P p.1 p.2 := by
  simp_rw [complexBivEval_eq_sum]
  exact continuous_finsetSum _ fun i _ =>
    ((P.coeff i).continuous.comp continuous_fst).mul
      (continuous_snd.pow i)

theorem analyticAt_complexBivEval
    (P : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    AnalyticAt ℂ
      (fun w : ℂ × ℂ => complexBivEval P w.1 w.2) p := by
  rw [show
      (fun w : ℂ × ℂ => complexBivEval P w.1 w.2) =
        fun w =>
          ∑ i ∈ Finset.range (P.natDegree + 1),
            (P.coeff i).eval w.1 * w.2 ^ i by
    funext w
    exact complexBivEval_eq_sum P w.1 w.2]
  apply (Finset.range (P.natDegree + 1)).analyticAt_fun_sum
  intro i _
  have hcoeff :
      AnalyticAt ℂ
        (fun w : ℂ × ℂ => (P.coeff i).eval w.1) p := by
    exact
      ((AnalyticOnNhd.eval_polynomial (P.coeff i))
        p.1 (Set.mem_univ _)).comp_of_eq analyticAt_fst rfl
  exact hcoeff.mul (analyticAt_snd.pow i)

theorem continuous_toSpanSingleton_complex :
    Continuous
      (fun x : ℂ =>
        ContinuousLinearMap.toSpanSingleton ℂ x) := by
  have hsub :
      ∀ x y : ℂ,
        ContinuousLinearMap.toSpanSingleton ℂ x -
            ContinuousLinearMap.toSpanSingleton ℂ y =
          ContinuousLinearMap.toSpanSingleton ℂ (x - y) := by
    intro x y
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  have hdist :
      ∀ x y : ℂ,
        dist (ContinuousLinearMap.toSpanSingleton ℂ x)
            (ContinuousLinearMap.toSpanSingleton ℂ y) =
          dist x y := by
    intro x y
    rw [dist_eq_norm, dist_eq_norm, hsub,
      ContinuousLinearMap.norm_toSpanSingleton]
  have hlip :
      LipschitzWith 1
        (fun x : ℂ =>
          ContinuousLinearMap.toSpanSingleton ℂ x) := by
    intro x y
    rw [edist_dist, edist_dist, hdist]
    simp
  exact hlip.continuous

/--
A simple complex root of the special fiber of a bivariate polynomial lifts
to a unique local complex-analytic root branch.
-/
theorem exists_analytic_complexBivPolynomial_root_of_simple_specialFiber
    (R : Polynomial (Polynomial ℂ)) (c : ℂ)
    (hroot : complexBivEval R 0 c = 0)
    (hsimple :
      complexBivEval (Polynomial.derivative R) 0 c ≠ 0) :
    ∃ z : ℂ → ℂ,
      AnalyticAt ℂ z 0 ∧
      z 0 = c ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        complexBivEval R x (z x) = 0) ∧
      ∀ᶠ w in 𝓝 ((0, c) : ℂ × ℂ),
        complexBivEval R w.1 w.2 = 0 ↔ z w.1 = w.2 := by
  let u : ℂ × ℂ := (0, c)
  let f : ℂ → ℂ → ℂ :=
    fun x y => complexBivEval R x y
  let f₁ : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
    fun x y =>
      ContinuousLinearMap.toSpanSingleton ℂ
        (complexBivEval (complexBivDerivX R) x y)
  let f₂ : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
    fun x y =>
      ContinuousLinearMap.toSpanSingleton ℂ
        (complexBivEval (Polynomial.derivative R) x y)
  have df₁ :
      ∀ᶠ v : ℂ × ℂ in 𝓝 u,
        HasFDerivAt (fun x => f x v.2)
          (f₁ v.1 v.2) v.1 :=
    Filter.Eventually.of_forall fun v =>
      (hasDerivAt_complexBivEval_left
        R v.1 v.2).hasFDerivAt
  have df₂ :
      ∀ᶠ v : ℂ × ℂ in 𝓝 u,
        HasFDerivAt (fun y => f v.1 y)
          (f₂ v.1 v.2) v.2 :=
    Filter.Eventually.of_forall fun v =>
      (hasDerivAt_complexBivEval_right
        R v.1 v.2).hasFDerivAt
  have cf₁ :
      ContinuousAt (Function.uncurry f₁) u :=
    (continuous_toSpanSingleton_complex.comp
      (continuous_complexBivEval
        (complexBivDerivX R))).continuousAt
  have cf₂ :
      ContinuousAt (Function.uncurry f₂) u :=
    (continuous_toSpanSingleton_complex.comp
      (continuous_complexBivEval
        (Polynomial.derivative R))).continuousAt
  have he :
      (ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.mk0 _ hsimple) : ℂ →L[ℂ] ℂ) =
        f₂ u.1 u.2 := by
    ext
    simp [f₂, u,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply]
  have hinv : (f₂ u.1 u.2).IsInvertible := ⟨_, he⟩
  let z :=
    implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ hinv
  have hf_analytic :
      AnalyticAt ℂ (Function.uncurry f) u := by
    change
      AnalyticAt ℂ
        (fun w : ℂ × ℂ =>
          complexBivEval R w.1 w.2) (0, c)
    exact analyticAt_complexBivEval R (0, c)
  have hz_analytic : AnalyticAt ℂ z 0 := by
    simpa [z, u] using
      analyticAt_implicitFunctionOfBivariate_complex
        df₁ df₂ cf₁ cf₂ hinv hf_analytic
  have hz_zero : z 0 = c := by
    have hiff :=
      (eventually_apply_eq_iff_implicitFunctionOfBivariate
        df₁ df₂ cf₁ cf₂ hinv).self_of_nhds
    exact hiff.mp rfl
  have hunique :
      ∀ᶠ w in 𝓝 ((0, c) : ℂ × ℂ),
        complexBivEval R w.1 w.2 = 0 ↔ z w.1 = w.2 := by
    simpa [f, u, z, hroot] using
      (eventually_apply_eq_iff_implicitFunctionOfBivariate
        df₁ df₂ cf₁ cf₂ hinv)
  have hsolve :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        f x (z x) = f u.1 u.2 :=
    eventually_apply_implicitFunctionOfBivariate
      df₁ df₂ cf₁ cf₂ hinv
  refine ⟨z, hz_analytic, hz_zero, ?_, hunique⟩
  filter_upwards [hsolve] with x hx
  simpa [f, u, hroot] using hx

/--
Finite-tail convergence of a nonsingular complex formal algebraic branch.

Besides the analytic branch itself, the conclusion retains the normalized
polynomial identity and the local uniqueness statement needed to identify
nearby sampled roots with this branch.
-/
theorem exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero
    (Q : Polynomial (Polynomial ℂ))
    (s : PowerSeries ℂ)
    (hroot :
      (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (hD :
      (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0) :
    ∃ (k n : ℕ) (A : Polynomial ℂ) (c : ℂ)
        (R : Polynomial (Polynomial ℂ)) (z : ℂ → ℂ),
      n = k + 1 ∧
      A = s.trunc n ∧
      c =
        (CurveSelection.TerminationScratch.formalTail n s).constantCoeff ∧
      R =
        CurveSelection.TerminationScratch.normalizedBivPolynomialTaylorTransform
          Q A n k ∧
      AnalyticAt ℂ z 0 ∧
      z 0 = c ∧
      A.eval 0 = s.constantCoeff ∧
      (∀ x w : ℂ,
        CurveSelection.TerminationScratch.bivEvalAt Q x
            (A.eval x + x ^ n * w) =
          x ^ (n + k) *
            CurveSelection.TerminationScratch.bivEvalAt R x w) ∧
      AnalyticAt ℂ
        (fun x => A.eval x + x ^ n * z x) 0 ∧
      (fun x => A.eval x + x ^ n * z x) 0 =
        s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x
          (A.eval x + x ^ n * z x) = 0) ∧
      (∀ᶠ w in 𝓝 ((0, c) : ℂ × ℂ),
        CurveSelection.TerminationScratch.bivEvalAt R w.1 w.2 = 0 ↔
          z w.1 = w.2) := by
  let f := bivPolynomialToPowerSeriesPolynomial Q
  let k := (f.derivative.eval s).order.toNat
  let n := k + 1
  let A := s.trunc n
  let tail := CurveSelection.TerminationScratch.formalTail n s
  let c := tail.constantCoeff
  let R :=
    CurveSelection.TerminationScratch.normalizedBivPolynomialTaylorTransform
      Q A n k
  obtain ⟨hA0, htransform, hface, hsimple⟩ :=
    CurveSelection.TerminationScratch.normalizedBivPolynomialTaylorTransform_has_simple_specialFiber
      Q s hroot hD
  obtain ⟨z, hzanalytic, hz0, hzroot, hzunique⟩ :=
    exists_analytic_complexBivPolynomial_root_of_simple_specialFiber
      R c (by
        simpa [complexBivEval,
          CurveSelection.TerminationScratch.bivEvalAt] using hface)
      (by
        simpa [complexBivEval,
          CurveSelection.TerminationScratch.bivEvalAt] using hsimple)
  have hzroot' :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt R x (z x) = 0 := by
    simpa [complexBivEval,
      CurveSelection.TerminationScratch.bivEvalAt] using hzroot
  have hzunique' :
      ∀ᶠ w in 𝓝 ((0, c) : ℂ × ℂ),
        CurveSelection.TerminationScratch.bivEvalAt R w.1 w.2 = 0 ↔
          z w.1 = w.2 := by
    simpa [complexBivEval,
      CurveSelection.TerminationScratch.bivEvalAt] using hzunique
  have hgamma :
      AnalyticAt ℂ
        (fun x => A.eval x + x ^ n * z x) 0 := by
    have hAanalytic :
        AnalyticAt ℂ (fun x => A.eval x) 0 :=
      (AnalyticOnNhd.eval_polynomial A) 0 (Set.mem_univ 0)
    exact hAanalytic.add ((analyticAt_id.pow n).mul hzanalytic)
  have hn : 0 < n := by simp [n]
  have hgamma0 :
      (fun x => A.eval x + x ^ n * z x) 0 =
        s.constantCoeff := by
    change A.eval 0 + 0 ^ n * z 0 = s.constantCoeff
    change A.eval 0 = s.constantCoeff at hA0
    rw [hA0, zero_pow (Nat.ne_of_gt hn)]
    simp
  have hQroot :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x
          (A.eval x + x ^ n * z x) = 0 := by
    filter_upwards [hzroot'] with x hx
    rw [htransform x (z x), hx, mul_zero]
  exact
    ⟨k, n, A, c, R, z, rfl, rfl, rfl, rfl,
      hzanalytic, hz0, hA0, htransform, hgamma, hgamma0,
      hQroot, hzunique'⟩

/--
Caller-chosen truncation version of the convergence theorem.  Any exponent
strictly larger than the derivative order works; this lets a finite family
of formal branches use one common truncation long enough to distinguish all
of them.
-/
theorem
    exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero_of_lt
    (Q : Polynomial (Polynomial ℂ))
    (s : PowerSeries ℂ)
    (k n : ℕ)
    (hkn : k < n)
    (hroot :
      (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s)
    (hD :
      (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0)
    (horder :
      ((bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s).order.toNat =
        k) :
    ∃ z : ℂ → ℂ,
      AnalyticAt ℂ z 0 ∧
      z 0 =
        (CurveSelection.TerminationScratch.formalTail n s).constantCoeff ∧
      AnalyticAt ℂ
        (fun x => (s.trunc n).eval x + x ^ n * z x) 0 ∧
      (fun x => (s.trunc n).eval x + x ^ n * z x) 0 =
        s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x
          ((s.trunc n).eval x + x ^ n * z x) = 0) := by
  let A := s.trunc n
  let c :=
    (CurveSelection.TerminationScratch.formalTail n s).constantCoeff
  let R :=
    CurveSelection.TerminationScratch.normalizedBivPolynomialTaylorTransform
      Q A n k
  obtain ⟨hA0, htransform, hface, hsimple⟩ :=
    normalizedBivPolynomialTaylorTransform_has_simple_specialFiber_of_lt
      Q s k n hkn hroot hD horder
  obtain ⟨z, hzanalytic, hz0, hzroot, _hzunique⟩ :=
    exists_analytic_complexBivPolynomial_root_of_simple_specialFiber
      R c
      (by
        simpa [complexBivEval,
          CurveSelection.TerminationScratch.bivEvalAt] using hface)
      (by
        simpa [complexBivEval,
          CurveSelection.TerminationScratch.bivEvalAt] using hsimple)
  have hzroot' :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt R x (z x) = 0 := by
    simpa [complexBivEval,
      CurveSelection.TerminationScratch.bivEvalAt] using hzroot
  have hgamma :
      AnalyticAt ℂ
        (fun x => A.eval x + x ^ n * z x) 0 := by
    have hAanalytic :
        AnalyticAt ℂ (fun x => A.eval x) 0 :=
      (AnalyticOnNhd.eval_polynomial A) 0 (Set.mem_univ 0)
    exact hAanalytic.add ((analyticAt_id.pow n).mul hzanalytic)
  have hn : 0 < n := Nat.zero_lt_of_lt hkn
  have hgamma0 :
      (fun x => A.eval x + x ^ n * z x) 0 =
        s.constantCoeff := by
    change A.eval 0 + 0 ^ n * z 0 = s.constantCoeff
    rw [hA0, zero_pow (Nat.ne_of_gt hn)]
    simp
  have hQroot :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x
          (A.eval x + x ^ n * z x) = 0 := by
    filter_upwards [hzroot'] with x hx
    rw [htransform x (z x), hx, mul_zero]
  exact
    ⟨z, hzanalytic, hz0, by simpa [A] using hgamma,
      by simpa [A] using hgamma0,
      by simpa [A] using hQroot⟩

/--
An irreducible bivariate polynomial of positive outer degree is separable
over the rational-function field.  Consequently none of its formal
power-series roots can also annihilate its outer derivative.
-/
theorem derivative_eval_ne_zero_of_irreducible_bivPolynomial
    (Q : Polynomial (Polynomial ℂ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s) :
    (bivPolynomialToPowerSeriesPolynomial Q).derivative.eval s ≠ 0 := by
  let coeffHom : Polynomial ℂ →+* PowerSeries ℂ :=
    Polynomial.coeToPowerSeries.ringHom
  let intoFrac :
      Polynomial ℂ →+* FractionRing (PowerSeries ℂ) :=
    (algebraMap (PowerSeries ℂ)
      (FractionRing (PowerSeries ℂ))).comp coeffHom
  have hcoeffHom : Function.Injective coeffHom := by
    intro p q hpq
    apply Polynomial.ext
    intro n
    have h :=
      congrArg (PowerSeries.coeff n) hpq
    simpa [coeffHom] using h
  have hintoFrac : Function.Injective intoFrac := by
    exact
      (IsFractionRing.injective (PowerSeries ℂ)
        (FractionRing (PowerSeries ℂ))).comp hcoeffHom
  let liftFrac :
      FractionRing (Polynomial ℂ) →+*
        FractionRing (PowerSeries ℂ) :=
    IsFractionRing.lift hintoFrac
  let Qfrac :
      Polynomial (FractionRing (Polynomial ℂ)) :=
    Q.map
      (algebraMap (Polynomial ℂ)
        (FractionRing (Polynomial ℂ)))
  have hprimitive : Q.IsPrimitive :=
    hQirr.isPrimitive hQdegree
  have hQfracIrreducible : Irreducible Qfrac := by
    exact
      (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp
        hQirr
  have hcoprime :
      IsCoprime Qfrac Qfrac.derivative :=
    (Polynomial.separable_def Qfrac).mp
      hQfracIrreducible.separable
  have hcoprimeLift :
      IsCoprime (Qfrac.map liftFrac)
        (Qfrac.derivative.map liftFrac) :=
    hcoprime.map (Polynomial.mapRingHom liftFrac)
  let sFrac : FractionRing (PowerSeries ℂ) :=
    algebraMap (PowerSeries ℂ)
      (FractionRing (PowerSeries ℂ)) s
  have hmapQ :
      Qfrac.map liftFrac =
        Q.map intoFrac := by
    apply Polynomial.ext
    intro n
    simp [Qfrac, liftFrac, intoFrac,
      IsFractionRing.lift_algebraMap]
  have hmapDerivative :
      Qfrac.derivative.map liftFrac =
        (bivPolynomialToPowerSeriesPolynomial Q).derivative.map
          (algebraMap (PowerSeries ℂ)
            (FractionRing (PowerSeries ℂ))) := by
    rw [← Polynomial.derivative_map, hmapQ]
    apply Polynomial.ext
    intro n
    simp [intoFrac, coeffHom,
      bivPolynomialToPowerSeriesPolynomial]
  have hQzero :
      (Qfrac.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries ℂ →+* FractionRing (PowerSeries ℂ) :=
      algebraMap (PowerSeries ℂ)
        (FractionRing (PowerSeries ℂ))
    have hs0 :
        Q.eval₂ coeffHom s = 0 := by
      simpa [coeffHom, bivPolynomialToPowerSeriesPolynomial,
        Polynomial.IsRoot, Polynomial.eval_map] using hs
    calc
      (Qfrac.map liftFrac).eval sFrac =
          Q.eval₂ intoFrac sFrac := by
            rw [hmapQ, Polynomial.eval_map]
      _ = alg (Q.eval₂ coeffHom s) := by
        symm
        simpa [alg, intoFrac, sFrac] using
          (Polynomial.hom_eval₂ (p := Q) coeffHom alg s)
      _ = 0 := by rw [hs0, map_zero]
  intro hD
  have hDzero :
      (Qfrac.derivative.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries ℂ →+* FractionRing (PowerSeries ℂ) :=
      algebraMap (PowerSeries ℂ)
        (FractionRing (PowerSeries ℂ))
    let P :=
      (bivPolynomialToPowerSeriesPolynomial Q).derivative
    calc
      (Qfrac.derivative.map liftFrac).eval sFrac =
          (P.map alg).eval sFrac := by
            rw [hmapDerivative]
      _ = alg (P.eval s) := by
        rw [Polynomial.eval_map]
        change P.eval₂ alg (alg s) = alg (P.eval s)
        exact Polynomial.eval₂_hom (p := P) alg s
      _ = 0 := by rw [show P.eval s = 0 by exact hD, map_zero]
  rcases
      Polynomial.aeval_ne_zero_of_isCoprime
        hcoprimeLift sFrac with hne | hne
  · exact hne (by simpa [Polynomial.aeval_def] using hQzero)
  · exact hne (by simpa [Polynomial.aeval_def] using hDzero)

/-- Map both coefficient levels of a concrete bivariate polynomial along a
field embedding, putting the parameter coefficients in formal power series. -/
def mappedBivPolynomialToPowerSeriesPolynomial
    {K L : Type*} [Semiring K] [Semiring L]
    (σ : K →+* L) (Q : Polynomial (Polynomial K)) :
    Polynomial (PowerSeries L) :=
  Q.map
    (Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom σ))

/-- Substitute `X^p` for the parameter variable of every coefficient of a
concrete bivariate polynomial. -/
def ramifyBivPolynomial
    {K : Type*} [CommSemiring K]
    (p : ℕ) (Q : Polynomial (Polynomial K)) :
    Polynomial (Polynomial K) :=
  Q.map
    (Polynomial.compRingHom
      ((Polynomial.X : Polynomial K) ^ p))

theorem bivEvalAt_ramifyBivPolynomial
    {K : Type*} [Field K]
    (p : ℕ) (Q : Polynomial (Polynomial K)) (t y : K) :
    CurveSelection.TerminationScratch.bivEvalAt
        (ramifyBivPolynomial p Q) t y =
      CurveSelection.TerminationScratch.bivEvalAt Q (t ^ p) y := by
  have hhom :
      (Polynomial.evalRingHom t).comp
          (Polynomial.compRingHom
            ((Polynomial.X : Polynomial K) ^ p)) =
        Polynomial.evalRingHom (t ^ p) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  simp [CurveSelection.TerminationScratch.bivEvalAt,
    ramifyBivPolynomial, Polynomial.eval₂_map, hhom]

theorem mapped_ramifyBivPolynomial
    {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (p : ℕ) (hp : p ≠ 0)
    (Q : Polynomial (Polynomial K)) :
    mappedBivPolynomialToPowerSeriesPolynomial σ
        (ramifyBivPolynomial p Q) =
      ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial σ Q) := by
  let base :
      Polynomial K →+* PowerSeries L :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom σ)
  have hhom :
      base.comp
          (Polynomial.compRingHom
            ((Polynomial.X : Polynomial K) ^ p)) =
        (PowerSeries.expand p hp).toRingHom.comp base := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [base, PowerSeries.expand_C]
    · simp [base, PowerSeries.expand_X]
  simp only [mappedBivPolynomialToPowerSeriesPolynomial,
    ramifyBivPolynomial, ramifyPowerSeriesPolynomial,
    Polynomial.map_map]
  rw [hhom]

/-- Extend a formal Weierstrass factorization along a field embedding. -/
theorem isWeierstrassFactorization_map
    {K L : Type*} [Field K] [Field L]
    (σ : K →+* L)
    {g : PowerSeries (PowerSeries K)}
    {f : Polynomial (PowerSeries K)}
    {u : PowerSeries (PowerSeries K)}
    (H : g.IsWeierstrassFactorization f u) :
    (g.map (PowerSeries.map σ)).IsWeierstrassFactorization
      (mapPowerSeriesPolynomial σ f)
      (u.map (PowerSeries.map σ)) := by
  refine
    ⟨isDistinguishedAt_mapPowerSeriesPolynomial
        σ H.isDistinguishedAt,
      H.isUnit.map _, ?_⟩
  simp [H.eq_mul, mapPowerSeriesPolynomial,
    Polynomial.polynomial_map_coe]

theorem map_bivPolynomialToIteratedPowerSeries
    {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (Q : Polynomial (Polynomial K)) :
    (bivPolynomialToIteratedPowerSeries Q).map
        (PowerSeries.map σ) =
      (mappedBivPolynomialToPowerSeriesPolynomial σ Q :
        PowerSeries (PowerSeries L)) := by
  ext n m
  simp [bivPolynomialToIteratedPowerSeries,
    bivPolynomialToPowerSeriesPolynomial,
    mappedBivPolynomialToPowerSeriesPolynomial]

theorem ramifyIteratedPowerSeries_coe'
    {K : Type*} [Field K]
    (p : ℕ) (hp : p ≠ 0)
    (g : Polynomial (PowerSeries K)) :
    ramifyIteratedPowerSeries p hp
        (g : PowerSeries (PowerSeries K)) =
      (ramifyPowerSeriesPolynomial p hp g :
        PowerSeries (PowerSeries K)) := by
  simp [ramifyIteratedPowerSeries, ramifyPowerSeriesPolynomial,
    Polynomial.polynomial_map_coe]

theorem isRoot_of_isWeierstrassFactorization'
    {K : Type*} [Field K]
    (g f : Polynomial (PowerSeries K))
    (h : PowerSeries (PowerSeries K))
    (H :
      (g : PowerSeries (PowerSeries K)).IsWeierstrassFactorization f h)
    (s : PowerSeries K) (hs0 : s.constantCoeff = 0)
    (hs : f.IsRoot s) :
    g.IsRoot s := by
  letI : UniformSpace K := ⊥
  have hsub : PowerSeries.HasSubst s :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hs0
  have heval : PowerSeries.HasEval s := hsub.hasEval
  have heq := congrArg (PowerSeries.aeval heval) H.eq_mul
  rw [map_mul, PowerSeries.aeval_coe,
    PowerSeries.aeval_coe] at heq
  have hs' :
      f.eval₂ (algebraMap (PowerSeries K) (PowerSeries K)) s = 0 := by
    simpa using (show f.eval s = 0 from hs)
  rw [Polynomial.aeval_def, Polynomial.aeval_def] at heq
  rw [hs', zero_mul] at heq
  simpa using heq

/--
A multiple root of the distinguished factor would be a multiple root of the
original polynomial in a Weierstrass factorization.
-/
theorem derivative_isRoot_of_isWeierstrassFactorization'
    {K : Type*} [Field K]
    (g f : Polynomial (PowerSeries K))
    (h : PowerSeries (PowerSeries K))
    (H :
      (g : PowerSeries (PowerSeries K)).IsWeierstrassFactorization f h)
    (s : PowerSeries K) (hs0 : s.constantCoeff = 0)
    (hs : f.IsRoot s)
    (hsD : f.derivative.IsRoot s) :
    g.derivative.IsRoot s := by
  letI : UniformSpace K := ⊥
  have hsub : PowerSeries.HasSubst s :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hs0
  have heval : PowerSeries.HasEval s := hsub.hasEval
  have hderiv :=
    congrArg
      (PowerSeries.derivative (R := PowerSeries K))
      H.eq_mul
  simp only [PowerSeries.derivative_coe, Derivation.leibniz,
    smul_eq_mul] at hderiv
  have heq :=
    congrArg (PowerSeries.aeval heval) hderiv
  have hs' :
      f.eval₂ (algebraMap (PowerSeries K) (PowerSeries K)) s = 0 := by
    simpa using (show f.eval s = 0 from hs)
  have hsD' :
      f.derivative.eval₂
          (algebraMap (PowerSeries K) (PowerSeries K)) s = 0 := by
    simpa using (show f.derivative.eval s = 0 from hsD)
  simp only [map_add, map_mul, PowerSeries.aeval_coe,
    Polynomial.aeval_def] at heq
  rw [hsD', hs'] at heq
  simp only [zero_mul, mul_zero, zero_add] at heq
  simpa [Polynomial.IsRoot] using heq

/--
A centered root of the ramified, scalar-extended distinguished factor is a
root of the ramified concrete bivariate polynomial.
-/
theorem ramified_mapped_biv_isRoot_of_weierstrass_root
    (Q : Polynomial (Polynomial ℝ))
    {f : Polynomial (PowerSeries ℝ)}
    {u : PowerSeries (PowerSeries ℝ)}
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f u)
    (p : ℕ) (hp : p ≠ 0)
    (s : PowerSeries ℂ)
    (hs0 : s.constantCoeff = 0)
    (hs :
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f)).IsRoot s) :
    (ramifyPowerSeriesPolynomial p hp
      (mappedBivPolynomialToPowerSeriesPolynomial
        Complex.ofRealHom Q)).IsRoot s := by
  have Hmap :=
    isWeierstrassFactorization_map Complex.ofRealHom H
  have Hram :=
    isWeierstrassFactorization_ramify Hmap p hp
  have Hram' :
      (ramifyPowerSeriesPolynomial p hp
          (mappedBivPolynomialToPowerSeriesPolynomial
            Complex.ofRealHom Q) :
        PowerSeries (PowerSeries ℂ)).IsWeierstrassFactorization
          (ramifyPowerSeriesPolynomial p hp
            (mapPowerSeriesPolynomial Complex.ofRealHom f))
          (ramifyIteratedPowerSeries p hp
            (u.map (PowerSeries.map Complex.ofRealHom))) := by
    simpa only
      [map_bivPolynomialToIteratedPowerSeries,
        ramifyIteratedPowerSeries_coe'] using Hram
  exact
    isRoot_of_isWeierstrassFactorization'
      (ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom Q))
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f))
      (ramifyIteratedPowerSeries p hp
        (u.map (PowerSeries.map Complex.ofRealHom)))
      Hram' s hs0 hs

theorem mappedBivPolynomialToPowerSeriesPolynomial_eq
    {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (Q : Polynomial (Polynomial K)) :
    mappedBivPolynomialToPowerSeriesPolynomial σ Q =
      bivPolynomialToPowerSeriesPolynomial (K := L)
        (Q.map (Polynomial.mapRingHom σ)) := by
  simp [mappedBivPolynomialToPowerSeriesPolynomial,
    bivPolynomialToPowerSeriesPolynomial, Polynomial.map_map]

/--
Coefficient-extension version of
`derivative_eval_ne_zero_of_irreducible_bivPolynomial`.

In particular, an irreducible polynomial over `ℝ[X]` remains separable over
`ℝ(X)`, so a complex formal branch of its coefficient extension cannot also
annihilate its derivative.  The polynomial itself need not remain
irreducible after extending coefficients to `ℂ`.
-/
theorem derivative_eval_ne_zero_of_irreducible_bivPolynomial_map
    {K L : Type*}
    [Field K] [Field L] [CharZero K]
    (σ : K →+* L)
    (Q : Polynomial (Polynomial K))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (s : PowerSeries L)
    (hs :
      (mappedBivPolynomialToPowerSeriesPolynomial σ Q).IsRoot s) :
    (mappedBivPolynomialToPowerSeriesPolynomial σ Q).derivative.eval s ≠ 0 := by
  let coeffHom : Polynomial K →+* PowerSeries L :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom σ)
  let intoFrac :
      Polynomial K →+* FractionRing (PowerSeries L) :=
    (algebraMap (PowerSeries L)
      (FractionRing (PowerSeries L))).comp coeffHom
  have hcoeffHom : Function.Injective coeffHom := by
    intro p q hpq
    apply Polynomial.ext
    intro n
    apply σ.injective
    have h :=
      congrArg (PowerSeries.coeff n) hpq
    simpa [coeffHom] using h
  have hintoFrac : Function.Injective intoFrac := by
    exact
      (IsFractionRing.injective (PowerSeries L)
        (FractionRing (PowerSeries L))).comp hcoeffHom
  let liftFrac :
      FractionRing (Polynomial K) →+*
        FractionRing (PowerSeries L) :=
    IsFractionRing.lift hintoFrac
  let Qfrac :
      Polynomial (FractionRing (Polynomial K)) :=
    Q.map
      (algebraMap (Polynomial K)
        (FractionRing (Polynomial K)))
  have hprimitive : Q.IsPrimitive :=
    hQirr.isPrimitive hQdegree
  have hQfracIrreducible : Irreducible Qfrac := by
    exact
      (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp
        hQirr
  have hcoprime :
      IsCoprime Qfrac Qfrac.derivative :=
    (Polynomial.separable_def Qfrac).mp
      hQfracIrreducible.separable
  have hcoprimeLift :
      IsCoprime (Qfrac.map liftFrac)
        (Qfrac.derivative.map liftFrac) :=
    hcoprime.map (Polynomial.mapRingHom liftFrac)
  let sFrac : FractionRing (PowerSeries L) :=
    algebraMap (PowerSeries L)
      (FractionRing (PowerSeries L)) s
  have hmapQ :
      Qfrac.map liftFrac =
        Q.map intoFrac := by
    apply Polynomial.ext
    intro n
    simp [Qfrac, liftFrac, intoFrac,
      IsFractionRing.lift_algebraMap]
  have hmapDerivative :
      Qfrac.derivative.map liftFrac =
        (mappedBivPolynomialToPowerSeriesPolynomial σ Q).derivative.map
          (algebraMap (PowerSeries L)
            (FractionRing (PowerSeries L))) := by
    rw [← Polynomial.derivative_map, hmapQ]
    apply Polynomial.ext
    intro n
    simp [intoFrac, coeffHom,
      mappedBivPolynomialToPowerSeriesPolynomial]
  have hQzero :
      (Qfrac.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries L →+* FractionRing (PowerSeries L) :=
      algebraMap (PowerSeries L)
        (FractionRing (PowerSeries L))
    have hs0 :
        Q.eval₂ coeffHom s = 0 := by
      simpa [coeffHom,
        mappedBivPolynomialToPowerSeriesPolynomial,
        Polynomial.IsRoot, Polynomial.eval_map] using hs
    calc
      (Qfrac.map liftFrac).eval sFrac =
          Q.eval₂ intoFrac sFrac := by
            rw [hmapQ, Polynomial.eval_map]
      _ = alg (Q.eval₂ coeffHom s) := by
        symm
        simpa [alg, intoFrac, sFrac] using
          (Polynomial.hom_eval₂ (p := Q) coeffHom alg s)
      _ = 0 := by rw [hs0, map_zero]
  intro hD
  have hDzero :
      (Qfrac.derivative.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries L →+* FractionRing (PowerSeries L) :=
      algebraMap (PowerSeries L)
        (FractionRing (PowerSeries L))
    let P :=
      (mappedBivPolynomialToPowerSeriesPolynomial σ Q).derivative
    calc
      (Qfrac.derivative.map liftFrac).eval sFrac =
          (P.map alg).eval sFrac := by
            rw [hmapDerivative]
      _ = alg (P.eval s) := by
        rw [Polynomial.eval_map]
        change P.eval₂ alg (alg s) = alg (P.eval s)
        exact Polynomial.eval₂_hom (p := P) alg s
      _ = 0 := by rw [show P.eval s = 0 by exact hD, map_zero]
  rcases
      Polynomial.aeval_ne_zero_of_isCoprime
        hcoprimeLift sFrac with hne | hne
  · exact hne (by simpa [Polynomial.aeval_def] using hQzero)
  · exact hne (by simpa [Polynomial.aeval_def] using hDzero)

/--
Separability with an arbitrary injective realization of the parameter
polynomial ring in formal power series.  This is the form needed after a
ramification `X ↦ X^p`: irreducibility is retained over the original
rational-function field, even though the ramified concrete polynomial may
factor.
-/
theorem derivative_eval_ne_zero_of_irreducible_bivPolynomial_of_coeffHom
    {K L : Type*}
    [Field K] [Field L] [CharZero K]
    (coeffHom : Polynomial K →+* PowerSeries L)
    (hcoeffHom : Function.Injective coeffHom)
    (Q : Polynomial (Polynomial K))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (s : PowerSeries L)
    (hs : (Q.map coeffHom).IsRoot s) :
    (Q.map coeffHom).derivative.eval s ≠ 0 := by
  let intoFrac :
      Polynomial K →+* FractionRing (PowerSeries L) :=
    (algebraMap (PowerSeries L)
      (FractionRing (PowerSeries L))).comp coeffHom
  have hintoFrac : Function.Injective intoFrac := by
    exact
      (IsFractionRing.injective (PowerSeries L)
        (FractionRing (PowerSeries L))).comp hcoeffHom
  let liftFrac :
      FractionRing (Polynomial K) →+*
        FractionRing (PowerSeries L) :=
    IsFractionRing.lift hintoFrac
  let Qfrac :
      Polynomial (FractionRing (Polynomial K)) :=
    Q.map
      (algebraMap (Polynomial K)
        (FractionRing (Polynomial K)))
  have hprimitive : Q.IsPrimitive :=
    hQirr.isPrimitive hQdegree
  have hQfracIrreducible : Irreducible Qfrac := by
    exact
      (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp
        hQirr
  have hcoprime :
      IsCoprime Qfrac Qfrac.derivative :=
    (Polynomial.separable_def Qfrac).mp
      hQfracIrreducible.separable
  have hcoprimeLift :
      IsCoprime (Qfrac.map liftFrac)
        (Qfrac.derivative.map liftFrac) :=
    hcoprime.map (Polynomial.mapRingHom liftFrac)
  let sFrac : FractionRing (PowerSeries L) :=
    algebraMap (PowerSeries L)
      (FractionRing (PowerSeries L)) s
  have hmapQ :
      Qfrac.map liftFrac =
        Q.map intoFrac := by
    apply Polynomial.ext
    intro n
    simp [Qfrac, liftFrac, intoFrac,
      IsFractionRing.lift_algebraMap]
  have hmapDerivative :
      Qfrac.derivative.map liftFrac =
        (Q.map coeffHom).derivative.map
          (algebraMap (PowerSeries L)
            (FractionRing (PowerSeries L))) := by
    rw [← Polynomial.derivative_map, hmapQ]
    apply Polynomial.ext
    intro n
    simp [intoFrac]
  have hQzero :
      (Qfrac.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries L →+* FractionRing (PowerSeries L) :=
      algebraMap (PowerSeries L)
        (FractionRing (PowerSeries L))
    have hs0 :
        Q.eval₂ coeffHom s = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hs
    calc
      (Qfrac.map liftFrac).eval sFrac =
          Q.eval₂ intoFrac sFrac := by
            rw [hmapQ, Polynomial.eval_map]
      _ = alg (Q.eval₂ coeffHom s) := by
        symm
        simpa [alg, intoFrac, sFrac] using
          (Polynomial.hom_eval₂ (p := Q) coeffHom alg s)
      _ = 0 := by rw [hs0, map_zero]
  intro hD
  have hDzero :
      (Qfrac.derivative.map liftFrac).eval sFrac = 0 := by
    let alg :
        PowerSeries L →+* FractionRing (PowerSeries L) :=
      algebraMap (PowerSeries L)
        (FractionRing (PowerSeries L))
    let P := (Q.map coeffHom).derivative
    calc
      (Qfrac.derivative.map liftFrac).eval sFrac =
          (P.map alg).eval sFrac := by
            rw [hmapDerivative]
      _ = alg (P.eval s) := by
        rw [Polynomial.eval_map]
        change P.eval₂ alg (alg s) = alg (P.eval s)
        exact Polynomial.eval₂_hom (p := P) alg s
      _ = 0 := by rw [show P.eval s = 0 by exact hD, map_zero]
  rcases
      Polynomial.aeval_ne_zero_of_isCoprime
        hcoprimeLift sFrac with hne | hne
  · exact hne (by simpa [Polynomial.aeval_def] using hQzero)
  · exact hne (by simpa [Polynomial.aeval_def] using hDzero)

/--
An irreducible real bivariate factor and any one of its complex formal
branches produce a genuine complex-analytic branch of the coefficient
extension.  Irreducibility is used over `ℝ(X)`, before extending scalars.
-/
theorem exists_analytic_complexBranch_of_real_irreducible_formalRoot
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (mappedBivPolynomialToPowerSeriesPolynomial
        Complex.ofRealHom Q).IsRoot s) :
    ∃ γ : ℂ → ℂ,
      AnalyticAt ℂ γ 0 ∧
      γ 0 = s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt
          (Q.map (Polynomial.mapRingHom Complex.ofRealHom))
          x (γ x) = 0) := by
  let Qℂ : Polynomial (Polynomial ℂ) :=
    Q.map (Polynomial.mapRingHom Complex.ofRealHom)
  have hsℂ :
      (bivPolynomialToPowerSeriesPolynomial Qℂ).IsRoot s := by
    simpa [Qℂ,
      mappedBivPolynomialToPowerSeriesPolynomial_eq] using hs
  have hD :
      (bivPolynomialToPowerSeriesPolynomial Qℂ).derivative.eval s ≠ 0 := by
    simpa [Qℂ,
      mappedBivPolynomialToPowerSeriesPolynomial_eq] using
        derivative_eval_ne_zero_of_irreducible_bivPolynomial_map
          Complex.ofRealHom Q hQirr hQdegree s hs
  obtain
      ⟨k, n, A, c, R, z, hn, hA, hc, hR,
        hzanalytic, hz0, hA0, htransform, hγanalytic,
        hγ0, hQeventually, hunique⟩ :=
    exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero
      Qℂ s hsℂ hD
  exact
    ⟨fun x => A.eval x + x ^ n * z x,
      hγanalytic, hγ0, by simpa [Qℂ] using hQeventually⟩

/--
The ramified realization of a formal root of an irreducible real curve is
simple as a root over `ℂ⟦X⟧`.
-/
theorem
    derivative_eval_ne_zero_of_real_irreducible_ramified_formalRoot
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (p : ℕ) (hp : p ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom Q)).IsRoot s) :
    (bivPolynomialToPowerSeriesPolynomial
        ((ramifyBivPolynomial p Q).map
          (Polynomial.mapRingHom Complex.ofRealHom))).derivative.eval s ≠ 0 := by
  let base : Polynomial ℝ →+* PowerSeries ℂ :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom Complex.ofRealHom)
  let coeffHom : Polynomial ℝ →+* PowerSeries ℂ :=
    (PowerSeries.expand p hp).toRingHom.comp base
  have hbase : Function.Injective base := by
    intro a b hab
    apply Polynomial.ext
    intro n
    apply Complex.ofRealHom.injective
    have hn := congrArg (PowerSeries.coeff n) hab
    simpa [base] using hn
  have hcoeffHom : Function.Injective coeffHom :=
    (injective_powerSeries_expand p hp).comp hbase
  have hpoly :
      Q.map coeffHom =
        mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom (ramifyBivPolynomial p Q) := by
    rw [mapped_ramifyBivPolynomial Complex.ofRealHom p hp Q]
    simp [coeffHom, base, ramifyPowerSeriesPolynomial,
      mappedBivPolynomialToPowerSeriesPolynomial,
      Polynomial.map_map]
  have hs' : (Q.map coeffHom).IsRoot s := by
    rw [hpoly]
    rw [mapped_ramifyBivPolynomial Complex.ofRealHom p hp Q]
    exact hs
  have hD' : (Q.map coeffHom).derivative.eval s ≠ 0 :=
    derivative_eval_ne_zero_of_irreducible_bivPolynomial_of_coeffHom
      coeffHom hcoeffHom Q hQirr hQdegree s hs'
  rw [hpoly] at hD'
  simpa [mappedBivPolynomialToPowerSeriesPolynomial_eq] using hD'

/--
The roots of the ramified, complexified Weierstrass polynomial attached to an
irreducible real bivariate polynomial are pairwise distinct.

Indeed, a repeated root of the distinguished factor would, after evaluating
the differentiated Weierstrass factorization, be a common root of the
ramified concrete polynomial and its derivative.  This contradicts
separability over the original rational-function field.
-/
theorem roots_nodup_ramified_map_weierstrassFactor_of_irreducible
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    {f : Polynomial (PowerSeries ℝ)}
    {u : PowerSeries (PowerSeries ℝ)}
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f u)
    (p : ℕ) (hp : p ≠ 0) :
    (ramifyPowerSeriesPolynomial p hp
      (mapPowerSeriesPolynomial Complex.ofRealHom f)).roots.Nodup := by
  classical
  let F : Polynomial (PowerSeries ℂ) :=
    ramifyPowerSeriesPolynomial p hp
      (mapPowerSeriesPolynomial Complex.ofRealHom f)
  let G : Polynomial (PowerSeries ℂ) :=
    ramifyPowerSeriesPolynomial p hp
      (mappedBivPolynomialToPowerSeriesPolynomial
        Complex.ofRealHom Q)
  let U : PowerSeries (PowerSeries ℂ) :=
    ramifyIteratedPowerSeries p hp
      (u.map (PowerSeries.map Complex.ofRealHom))
  have Hmap :=
    isWeierstrassFactorization_map Complex.ofRealHom H
  have Hram :=
    isWeierstrassFactorization_ramify Hmap p hp
  have Hram' :
      (G : PowerSeries (PowerSeries ℂ)).IsWeierstrassFactorization
        F U := by
    simpa only [F, G, U, map_bivPolynomialToIteratedPowerSeries,
      ramifyIteratedPowerSeries_coe'] using Hram
  have hFne : F ≠ 0 :=
    Hram'.isDistinguishedAt.monic.ne_zero
  have hG :
      G =
        bivPolynomialToPowerSeriesPolynomial
          ((ramifyBivPolynomial p Q).map
            (Polynomial.mapRingHom Complex.ofRealHom)) := by
    rw [← mappedBivPolynomialToPowerSeriesPolynomial_eq]
    exact (mapped_ramifyBivPolynomial
      Complex.ofRealHom p hp Q).symm
  change F.roots.Nodup
  rw [Multiset.nodup_iff_count_le_one]
  intro s
  rw [Polynomial.count_roots]
  by_contra hle
  have hmult : 1 < F.rootMultiplicity s :=
    Nat.lt_of_not_ge hle
  obtain ⟨hs, hsD⟩ :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hFne).mp hmult
  have hs0 : s.constantCoeff = 0 :=
    constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
      Hram'.isDistinguishedAt hs
  have hGroot : G.IsRoot s :=
    isRoot_of_isWeierstrassFactorization'
      G F U Hram' s hs0 hs
  have hGDroot : G.derivative.IsRoot s :=
    derivative_isRoot_of_isWeierstrassFactorization'
      G F U Hram' s hs0 hs hsD
  have hDne :=
    derivative_eval_ne_zero_of_real_irreducible_ramified_formalRoot
      Q hQirr hQdegree p hp s hGroot
  exact hDne (by simpa [Polynomial.IsRoot, hG] using hGDroot)

/--
Convergence of a ramified formal branch of an irreducible real curve.

The irreducibility hypothesis belongs to the original polynomial `Q`; it is
deliberately *not* imposed on `Q(X^p,Y)`, which commonly becomes reducible.
Separability is transported through the injective embedding
`ℝ[X] → ℂ⟦X⟧`, `X ↦ X^p`.
-/
theorem
    exists_analytic_complexBranch_of_real_irreducible_ramified_formalRoot
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (p : ℕ) (hp : p ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom Q)).IsRoot s) :
    ∃ γ : ℂ → ℂ,
      AnalyticAt ℂ γ 0 ∧
      γ 0 = s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt
          ((ramifyBivPolynomial p Q).map
            (Polynomial.mapRingHom Complex.ofRealHom))
          x (γ x) = 0) := by
  let base : Polynomial ℝ →+* PowerSeries ℂ :=
    Polynomial.coeToPowerSeries.ringHom.comp
      (Polynomial.mapRingHom Complex.ofRealHom)
  let coeffHom : Polynomial ℝ →+* PowerSeries ℂ :=
    (PowerSeries.expand p hp).toRingHom.comp base
  have hbase : Function.Injective base := by
    intro a b hab
    apply Polynomial.ext
    intro n
    apply Complex.ofRealHom.injective
    have hn := congrArg (PowerSeries.coeff n) hab
    simpa [base] using hn
  have hcoeffHom : Function.Injective coeffHom :=
    (injective_powerSeries_expand p hp).comp hbase
  have hpoly :
      Q.map coeffHom =
        mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom (ramifyBivPolynomial p Q) := by
    rw [mapped_ramifyBivPolynomial Complex.ofRealHom p hp Q]
    simp [coeffHom, base, ramifyPowerSeriesPolynomial,
      mappedBivPolynomialToPowerSeriesPolynomial,
      Polynomial.map_map]
  have hs' : (Q.map coeffHom).IsRoot s := by
    rw [hpoly]
    rw [mapped_ramifyBivPolynomial Complex.ofRealHom p hp Q]
    exact hs
  have hD' : (Q.map coeffHom).derivative.eval s ≠ 0 :=
    derivative_eval_ne_zero_of_irreducible_bivPolynomial_of_coeffHom
      coeffHom hcoeffHom Q hQirr hQdegree s hs'
  let Qramℂ : Polynomial (Polynomial ℂ) :=
    (ramifyBivPolynomial p Q).map
      (Polynomial.mapRingHom Complex.ofRealHom)
  have hsram :
      (bivPolynomialToPowerSeriesPolynomial Qramℂ).IsRoot s := by
    simpa [Qramℂ,
      mappedBivPolynomialToPowerSeriesPolynomial_eq] using
        (show
          (mappedBivPolynomialToPowerSeriesPolynomial
            Complex.ofRealHom (ramifyBivPolynomial p Q)).IsRoot s by
              rw [mapped_ramifyBivPolynomial
                Complex.ofRealHom p hp Q]
              exact hs)
  have hDram :
      (bivPolynomialToPowerSeriesPolynomial Qramℂ).derivative.eval s ≠ 0 := by
    rw [hpoly] at hD'
    simpa [Qramℂ,
      mappedBivPolynomialToPowerSeriesPolynomial_eq] using hD'
  obtain
      ⟨k, n, A, c, R, z, hn, hA, hc, hR,
        hzanalytic, hz0, hA0, htransform, hγanalytic,
        hγ0, hQeventually, hunique⟩ :=
    exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero
      Qramℂ s hsram hDram
  exact
    ⟨fun x => A.eval x + x ^ n * z x,
      hγanalytic, hγ0, by simpa [Qramℂ] using hQeventually⟩

/--
Caller-chosen common truncation for a ramified branch.  This is the finite
family interface: choose `n` beyond every derivative order and beyond every
first differing coefficient, then all branches use `s.trunc n`.
-/
theorem
    exists_analytic_complexBranch_of_real_irreducible_ramified_formalRoot_of_lt
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    (p : ℕ) (hp : p ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom Q)).IsRoot s)
    (n : ℕ)
    (hlarge :
      ((bivPolynomialToPowerSeriesPolynomial
          ((ramifyBivPolynomial p Q).map
            (Polynomial.mapRingHom Complex.ofRealHom))).derivative.eval s).order.toNat <
        n) :
    ∃ z : ℂ → ℂ,
      AnalyticAt ℂ z 0 ∧
      z 0 =
        (CurveSelection.TerminationScratch.formalTail n s).constantCoeff ∧
      AnalyticAt ℂ
        (fun x => (s.trunc n).eval x + x ^ n * z x) 0 ∧
      (fun x => (s.trunc n).eval x + x ^ n * z x) 0 =
        s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt
          ((ramifyBivPolynomial p Q).map
            (Polynomial.mapRingHom Complex.ofRealHom))
          x ((s.trunc n).eval x + x ^ n * z x) = 0) := by
  let Qramℂ : Polynomial (Polynomial ℂ) :=
    (ramifyBivPolynomial p Q).map
      (Polynomial.mapRingHom Complex.ofRealHom)
  have hsram :
      (bivPolynomialToPowerSeriesPolynomial Qramℂ).IsRoot s := by
    simpa [Qramℂ,
      mappedBivPolynomialToPowerSeriesPolynomial_eq] using
        (show
          (mappedBivPolynomialToPowerSeriesPolynomial
            Complex.ofRealHom (ramifyBivPolynomial p Q)).IsRoot s by
              rw [mapped_ramifyBivPolynomial
                Complex.ofRealHom p hp Q]
              exact hs)
  have hDram :
      (bivPolynomialToPowerSeriesPolynomial Qramℂ).derivative.eval s ≠ 0 := by
    simpa [Qramℂ] using
      derivative_eval_ne_zero_of_real_irreducible_ramified_formalRoot
        Q hQirr hQdegree p hp s hs
  exact
    exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero_of_lt
      Qramℂ s
      ((bivPolynomialToPowerSeriesPolynomial Qramℂ).derivative.eval s).order.toNat
      n (by simpa [Qramℂ] using hlarge)
      hsram hDram rfl

/--
Two common-truncation analytic representatives are distinct on a punctured
neighborhood as soon as their polynomial truncations differ.  The proof
factors the first nonzero term of the truncation difference; all analytic
tail terms occur only at order `n`.
-/
theorem eventually_ne_of_trunc_ne
    (s t : PowerSeries ℂ) (n : ℕ)
    (hst : s.trunc n ≠ t.trunc n)
    (zs zt : ℂ → ℂ)
    (hzs : ContinuousAt zs 0)
    (hzt : ContinuousAt zt 0) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ),
      (s.trunc n).eval x + x ^ n * zs x ≠
        (t.trunc n).eval x + x ^ n * zt x := by
  let P : Polynomial ℂ := s.trunc n - t.trunc n
  have hP : P ≠ 0 := by
    simpa [P, sub_ne_zero] using hst
  let m := P.natTrailingDegree
  have hPm : P.coeff m ≠ 0 := by
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hP
  have hm : m < n := by
    by_contra hmn
    have hnm : n ≤ m := Nat.le_of_not_gt hmn
    apply hPm
    simp [P, PowerSeries.coeff_trunc,
      not_lt_of_ge hnm]
  have hdiv : (Polynomial.X : Polynomial ℂ) ^ m ∣ P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      (show d < P.natTrailingDegree by simpa [m] using hd)
  obtain ⟨q, hq⟩ := hdiv
  have hPm_eq : P.coeff m = q.coeff 0 := by
    rw [hq]
    simpa using Polynomial.coeff_X_pow_mul q m 0
  have hq0 : q.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hPm_eq ▸ hPm
  let B : ℂ → ℂ :=
    fun x => q.eval x + x ^ (n - m) * (zs x - zt x)
  have hBcontinuous : ContinuousAt B 0 := by
    have hqcontinuous :
        ContinuousAt (fun x : ℂ => q.eval x) 0 :=
      (Polynomial.continuous_eval₂ q (RingHom.id ℂ)).continuousAt
    exact hqcontinuous.add
      ((continuousAt_id.pow _).mul (hzs.sub hzt))
  have hnm_pos : 0 < n - m := Nat.sub_pos_of_lt hm
  have hB0 : B 0 ≠ 0 := by
    simpa [B, zero_pow (Nat.ne_of_gt hnm_pos)] using hq0
  have hBeventually : ∀ᶠ x in 𝓝 (0 : ℂ), B x ≠ 0 :=
    hBcontinuous.eventually_ne hB0
  filter_upwards
    [hBeventually.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
    with x hBx hx
  have hx0 : x ≠ 0 := by simpa using hx
  intro heq
  have hpow : x ^ n = x ^ m * x ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hm)]
  have hfactor :
      ((s.trunc n).eval x + x ^ n * zs x) -
          ((t.trunc n).eval x + x ^ n * zt x) =
        x ^ m * B x := by
    calc
      ((s.trunc n).eval x + x ^ n * zs x) -
            ((t.trunc n).eval x + x ^ n * zt x) =
          P.eval x + x ^ n * (zs x - zt x) := by
            simp [P]
            ring
      _ =
          x ^ m * q.eval x +
            x ^ m * x ^ (n - m) * (zs x - zt x) := by
            rw [hq, Polynomial.eval_mul,
              Polynomial.eval_pow, Polynomial.eval_X, hpow]
      _ = x ^ m * B x := by
        change
          x ^ m * q.eval x +
              x ^ m * x ^ (n - m) * (zs x - zt x) =
            x ^ m *
              (q.eval x + x ^ (n - m) * (zs x - zt x))
        ring
  have hzero : x ^ m * B x = 0 := by
    rw [← hfactor, heq, sub_self]
  exact (mul_ne_zero (pow_ne_zero m hx0) hBx) hzero

/--
Every formal root supplied by the common ramified splitting of a
Weierstrass factor converges to a complex-analytic branch of the original
irreducible real curve after the same ramification.
-/
theorem exists_analytic_complexBranch_of_ramified_weierstrass_root
    (Q : Polynomial (Polynomial ℝ))
    (hQirr : Irreducible Q)
    (hQdegree : Q.natDegree ≠ 0)
    {f : Polynomial (PowerSeries ℝ)}
    {u : PowerSeries (PowerSeries ℝ)}
    (H :
      (bivPolynomialToIteratedPowerSeries Q).IsWeierstrassFactorization
        f u)
    (p : ℕ) (hp : p ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial Complex.ofRealHom f)).IsRoot s) :
    ∃ γ : ℂ → ℂ,
      AnalyticAt ℂ γ 0 ∧
      γ 0 = 0 ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt
          ((ramifyBivPolynomial p Q).map
            (Polynomial.mapRingHom Complex.ofRealHom))
          x (γ x) = 0) := by
  have hs0 : s.constantCoeff = 0 :=
    constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
      (isDistinguishedAt_ramifyPowerSeriesPolynomial
        (isDistinguishedAt_mapPowerSeriesPolynomial
          Complex.ofRealHom H.isDistinguishedAt)
        p hp)
      hs
  have hQroot :
      (ramifyPowerSeriesPolynomial p hp
        (mappedBivPolynomialToPowerSeriesPolynomial
          Complex.ofRealHom Q)).IsRoot s :=
    ramified_mapped_biv_isRoot_of_weierstrass_root
      Q H p hp s hs0 hs
  obtain ⟨γ, hγanalytic, hγ0, hγroot⟩ :=
    exists_analytic_complexBranch_of_real_irreducible_ramified_formalRoot
      Q hQirr hQdegree p hp s hQroot
  exact ⟨γ, hγanalytic, hγ0.trans hs0, hγroot⟩

/-- Synchronize the ramification indices for a finite family after extending
the coefficient field. -/
theorem exists_commonRamification_centeredSplittingsOver'
    {K L J : Type*} [Field K] [Field L] [Fintype J]
    (σ : K →+* L)
    (Hroot : HasRamifiedRootProperty L)
    (f : J → Polynomial (PowerSeries K))
    (Hdist :
      ∀ j,
        (f j).IsDistinguishedAt
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
  choose p hp hsplit using fun j =>
    hasRamifiedPowerSeriesSplittingOver_of_hasRamifiedRootProperty
      σ Hroot (Hdist j).monic
  let q : ℕ := ∏ j, p j
  have hq : q ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _hj => hp j
  refine ⟨q, hq, fun j => ?_⟩
  have hp_dvd : p j ∣ q := by
    exact Finset.dvd_prod_of_mem (fun k => p k)
      (Finset.mem_univ j)
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

/--
Finite-coordinate convergence package.  A common ramification splits all
local Weierstrass polynomials, and every formal root in every coordinate
comes with a centered complex-analytic representative satisfying the
corresponding ramified concrete equation.
-/
theorem exists_commonRamified_analyticBranches
    {J : Type*} [Fintype J]
    (Hroot : HasRamifiedRootProperty ℂ)
    (Q : J → Polynomial (Polynomial ℝ))
    (hQirr : ∀ j, Irreducible (Q j))
    (hQdegree : ∀ j, (Q j).natDegree ≠ 0) :
    ∃ (f : J → Polynomial (PowerSeries ℝ))
        (u : J → PowerSeries (PowerSeries ℝ))
        (p : ℕ) (hp : p ≠ 0),
      (∀ j,
        (bivPolynomialToIteratedPowerSeries
          (Q j)).IsWeierstrassFactorization (f j) (u j)) ∧
      (∀ j,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).Splits) ∧
      ∀ j s,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).IsRoot s →
        ∃ γ : ℂ → ℂ,
          AnalyticAt ℂ γ 0 ∧
          γ 0 = 0 ∧
          (∀ᶠ x in 𝓝 (0 : ℂ),
            CurveSelection.TerminationScratch.bivEvalAt
              ((ramifyBivPolynomial p (Q j)).map
                (Polynomial.mapRingHom Complex.ofRealHom))
              x (γ x) = 0) := by
  classical
  have hprimitive : ∀ j, (Q j).IsPrimitive :=
    fun j => (hQirr j).isPrimitive (hQdegree j)
  choose f u H using fun j =>
    exists_weierstrassFactorization_bivPolynomial_primPart (Q j)
  have H' :
      ∀ j,
        (bivPolynomialToIteratedPowerSeries
          (Q j)).IsWeierstrassFactorization (f j) (u j) := by
    intro j
    simpa [(hprimitive j).primPart_eq] using H j
  obtain ⟨p, hp, hsplit⟩ :=
    exists_commonRamification_centeredSplittingsOver'
      Complex.ofRealHom Hroot f
      (fun j => (H' j).isDistinguishedAt)
  refine ⟨f, u, p, hp, H', fun j => (hsplit j).1, ?_⟩
  intro j s hs
  exact
    exists_analytic_complexBranch_of_ramified_weierstrass_root
      (Q j) (hQirr j) (hQdegree j) (H' j) p hp s hs

/--
Coupled sampled-sequence package: first synchronize one irreducible factor in
each coordinate along a common subsequence, then synchronize all Puiseux
ramifications, and finally converge every resulting formal branch.
-/
theorem
    exists_factorTuple_commonRamified_analyticBranches
    {J : Type*} [Fintype J]
    (Hroot : HasRamifiedRootProperty ℂ)
    (Q : J → Polynomial (Polynomial ℝ))
    (hQ : ∀ j, Q j ≠ 0)
    (hprimitive : ∀ j, (Q j).IsPrimitive)
    (x : ℕ → ℝ)
    (y : ℕ → J → ℝ)
    {l : Filter (ℝ × (J → ℝ))}
    (hlim : Tendsto (fun n => (x n, y n)) atTop l)
    (hroot :
      ∀ n j,
        CurveSelection.TerminationScratch.bivEvalAt
          (Q j) (x n) (y n j) = 0) :
    ∃ (q : J → Polynomial (Polynomial ℝ))
        (ns : ℕ → ℕ)
        (f : J → Polynomial (PowerSeries ℝ))
        (u : J → PowerSeries (PowerSeries ℝ))
        (p : ℕ) (hp : p ≠ 0),
      (∀ j,
        q j ∈
            CurveSelection.FactorCoverageScratch.irreducibleFactors (Q j) ∧
        Irreducible (q j) ∧
        0 < (q j).natDegree ∧
        q j ∣ Q j) ∧
      Tendsto (fun n => (x (ns n), y (ns n))) atTop l ∧
      (∀ n j,
        CurveSelection.TerminationScratch.bivEvalAt
          (q j) (x (ns n)) (y (ns n) j) = 0) ∧
      (∀ j,
        (bivPolynomialToIteratedPowerSeries
          (q j)).IsWeierstrassFactorization (f j) (u j)) ∧
      (∀ j,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).Splits) ∧
      ∀ j s,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial Complex.ofRealHom (f j))).IsRoot s →
        ∃ γ : ℂ → ℂ,
          AnalyticAt ℂ γ 0 ∧
          γ 0 = 0 ∧
          (∀ᶠ t in 𝓝 (0 : ℂ),
            CurveSelection.TerminationScratch.bivEvalAt
              ((ramifyBivPolynomial p (q j)).map
                (Polynomial.mapRingHom Complex.ofRealHom))
              t (γ t) = 0) := by
  obtain ⟨q, ns, hq, hlimsub, hqroot⟩ :=
    exists_irreducibleFactorTuple_subsequence_isRoot
      Q hQ hprimitive x y hlim hroot
  obtain ⟨f, u, p, hp, H, hsplit, hbranch⟩ :=
    exists_commonRamified_analyticBranches Hroot q
      (fun j => (hq j).2.1)
      (fun j => Nat.ne_of_gt (hq j).2.2.1)
  exact
    ⟨q, ns, f, u, p, hp, hq, hlimsub, hqroot,
      H, hsplit, hbranch⟩

/--
If a nonzero concrete bivariate polynomial vanishes at a formal branch, then
one of its irreducible factors of positive value-variable degree already
vanishes at that branch.
-/
theorem exists_irreducible_bivFactor_of_formalRoot
    (Q : Polynomial (Polynomial ℂ))
    (hQ : Q ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s) :
    ∃ q : Polynomial (Polynomial ℂ),
      Irreducible q ∧
      q.natDegree ≠ 0 ∧
      q ∣ Q ∧
      (bivPolynomialToPowerSeriesPolynomial q).IsRoot s := by
  let coeffHom : Polynomial ℂ →+* PowerSeries ℂ :=
    Polynomial.coeToPowerSeries.ringHom
  let ev : Polynomial (Polynomial ℂ) →+* PowerSeries ℂ :=
    (Polynomial.evalRingHom s).comp
      (Polynomial.mapRingHom coeffHom)
  let factors :=
    UniqueFactorizationMonoid.normalizedFactors Q
  have hQev : ev Q = 0 := by
    simpa [ev, coeffHom, bivPolynomialToPowerSeriesPolynomial,
      Polynomial.IsRoot] using hs
  have hprodEv : ev factors.prod = 0 := by
    have hQdvd :
        Q ∣ factors.prod :=
      (UniqueFactorizationMonoid.prod_normalizedFactors hQ).symm.dvd
    obtain ⟨u, hu⟩ := hQdvd
    rw [hu, map_mul, hQev, zero_mul]
  have hmappedProd :
      (factors.map ev).prod = 0 := by
    exact
      (ev.toMonoidHom.map_multiset_prod factors).symm.trans hprodEv
  have hzeroMem : 0 ∈ factors.map ev :=
    Multiset.prod_eq_zero_iff.mp hmappedProd
  obtain ⟨q, hqmem, hqev⟩ :=
    Multiset.mem_map.mp hzeroMem
  have hqroot :
      (bivPolynomialToPowerSeriesPolynomial q).IsRoot s := by
    simpa [ev, coeffHom, bivPolynomialToPowerSeriesPolynomial,
      Polynomial.IsRoot] using hqev
  have hqirr : Irreducible q :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqmem
  have hcoeffHom : Function.Injective coeffHom := by
    intro p r hpr
    apply Polynomial.ext
    intro n
    have hn := congrArg (PowerSeries.coeff n) hpr
    simpa [coeffHom] using hn
  have hqdegree : q.natDegree ≠ 0 := by
    intro hdegree
    have hqC : q = Polynomial.C (q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdegree
    have hcoeffzero : coeffHom (q.coeff 0) = 0 := by
      calc
        coeffHom (q.coeff 0) =
            ev (Polynomial.C (q.coeff 0)) := by
              simp [ev]
        _ = ev q := (congrArg ev hqC).symm
        _ = 0 := hqev
    have : q.coeff 0 = 0 :=
      hcoeffHom (by simpa using hcoeffzero)
    apply hqirr.ne_zero
    rw [hqC, this, map_zero]
  exact
    ⟨q, hqirr, hqdegree,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hqmem,
      hqroot⟩

/--
Every formal root of a nonzero concrete complex bivariate polynomial is the
formal germ of a genuine local complex-analytic root curve.  The curve is
constructed on an irreducible positive-degree factor, so repeated factors of
the original polynomial cause no loss of simplicity.
-/
theorem exists_analytic_complexBivPolynomial_root_of_formalRoot
    (Q : Polynomial (Polynomial ℂ))
    (hQ : Q ≠ 0)
    (s : PowerSeries ℂ)
    (hs :
      (bivPolynomialToPowerSeriesPolynomial Q).IsRoot s) :
    ∃ (q : Polynomial (Polynomial ℂ)) (γ : ℂ → ℂ),
      Irreducible q ∧
      q.natDegree ≠ 0 ∧
      q ∣ Q ∧
      AnalyticAt ℂ γ 0 ∧
      γ 0 = s.constantCoeff ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt q x (γ x) = 0) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x (γ x) = 0) := by
  obtain ⟨q, hqirr, hqdegree, hqdiv, hqroot⟩ :=
    exists_irreducible_bivFactor_of_formalRoot Q hQ s hs
  have hqD :
      (bivPolynomialToPowerSeriesPolynomial q).derivative.eval s ≠ 0 :=
    derivative_eval_ne_zero_of_irreducible_bivPolynomial
      q hqirr hqdegree s hqroot
  obtain
      ⟨k, n, A, c, R, z, hn, hA, hc, hR,
        hzanalytic, hz0, hA0, htransform, hγanalytic,
        hγ0, hqeventually, hunique⟩ :=
    exists_analytic_complexBranch_of_formalRoot_of_derivative_ne_zero
      q s hqroot hqD
  let γ : ℂ → ℂ := fun x => A.eval x + x ^ n * z x
  have hQeventually :
      ∀ᶠ x in 𝓝 (0 : ℂ),
        CurveSelection.TerminationScratch.bivEvalAt Q x (γ x) = 0 := by
    obtain ⟨T, hQT⟩ := hqdiv
    filter_upwards [hqeventually] with x hx
    change
      CurveSelection.TerminationScratch.bivEvalAt q x (γ x) = 0 at hx
    calc
      CurveSelection.TerminationScratch.bivEvalAt Q x (γ x) =
          CurveSelection.TerminationScratch.bivEvalAt (q * T) x (γ x) := by
            rw [hQT]
      _ =
          CurveSelection.TerminationScratch.bivEvalAt q x (γ x) *
            CurveSelection.TerminationScratch.bivEvalAt T x (γ x) := by
              simp [CurveSelection.TerminationScratch.bivEvalAt]
      _ = 0 := by rw [hx, zero_mul]
  exact
    ⟨q, γ, hqirr, hqdegree, hqdiv,
      hγanalytic, hγ0, hqeventually, hQeventually⟩

end CurveSelection.ConvergenceScratch
end Math
