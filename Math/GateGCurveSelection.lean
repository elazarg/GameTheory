/- Gate G: assembly of the algebraic and analytic curve-selection steps. -/
import Math.GateGAlgebraicReduction
import Math.GateGAnalyticSign
import Math.GateGConvergence
import Math.GateGFiniteBranchCoverage
import Math.GateGPuiseux
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Polynomial Set Topology
open Math.PolynomialSignCell

namespace Math
namespace GateGCurveSelection

open GateGAlgebraicReductionScratch
open GateGAnalyticSignScratch
open GateGConvergenceScratch
open GateGFiniteBranchCoverage

/--
After translating each value coordinate to its limiting value, removal of
parameter-only content preserves every equation eventually.  Finiteness of
the coordinate family makes the same tail work for all coordinates.
-/
theorem eventually_centered_primPart_isRoot
    {J : Type*} [Finite J]
    (relation : J → Polynomial (Polynomial ℝ))
    (hrelation : ∀ j, relation j ≠ 0)
    (lam : ℕ → ℝ)
    (hlam_pos : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0))
    (y : ℕ → J → ℝ)
    (center : J → ℝ)
    (hroot :
      ∀ n j,
        bivEval (relation j) (lam n) (y n j) = 0) :
    ∀ᶠ n in atTop, ∀ j,
      bivEval
        (translateBivPolynomialValue
          (relation j) (center j)).primPart
        (lam n) (y n j - center j) = 0 := by
  apply Filter.eventually_all.2
  intro j
  let R :=
    translateBivPolynomialValue (relation j) (center j)
  have hR : R ≠ 0 := by
    exact
      (Polynomial.comp_X_add_C_ne_zero_iff
        (p := relation j)
        (t := Polynomial.C (center j))).2
        (hrelation j)
  obtain ⟨ρ, hρ, hcontent⟩ :=
    exists_interval_content_eval_ne_zero R hR
  have hlt : ∀ᶠ n in atTop, lam n < ρ :=
    hlam.eventually (Iio_mem_nhds hρ)
  filter_upwards [hlt] with n hn
  apply bivEval_primPart_eq_zero R
  · exact hcontent (lam n) ⟨hlam_pos n, hn⟩
  · dsimp only [R]
    rw [bivEval_translateBivPolynomialValue]
    simpa using hroot n j

/--
The finite-branch sign-cell theorem only needs coverage on a tail.  Reindexing
that tail by `n ↦ n + N` preserves convergence to the positive side.
-/
theorem hasAnalyticPowerCurveAt_of_eventually_finite_complexAnalytic_branches
    {I σ : Type*}
    {κ : σ → Type*}
    [Fintype I] [Fintype σ] [∀ v, Fintype (κ v)]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (hq : 0 < q)
    (branch : ∀ v, κ v → ℂ → ℂ)
    (hbranch_analytic :
      ∀ v k, AnalyticAt ℂ (branch v k) 0)
    (hbranch_zero :
      ∀ v k, (branch v k 0).re = x₀ v)
    (hbranch_coordinate :
      ∀ (k : ∀ v, κ v) (t : ℝ),
        coordinate (fun v => (branch v (k v) t).re) = t ^ q)
    (x : ℕ → Assignment σ)
    (t : ℕ → ℝ)
    (hx : ∀ n, x n ∈ signCell P τ)
    (ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hcovered :
      ∀ᶠ n in atTop,
        ∀ v, ∃ k, (branch v k (t n)).re = x n v) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  rw [Filter.eventually_atTop] at hcovered
  obtain ⟨N, hN⟩ := hcovered
  apply
    hasAnalyticPowerCurveAt_of_finite_complexAnalytic_branches
      P τ coordinate x₀ q hq branch
      hbranch_analytic hbranch_zero hbranch_coordinate
      (fun n => x (n + N)) (fun n => t (n + N))
  · exact fun n => hx (n + N)
  · exact ht.comp (tendsto_add_atTop_nat N)
  · intro n v
    exact hN (n + N) (Nat.le_add_left N n) v

/--
List-indexed form of finite complex branch synchronization.  This is the
direct interface produced by finite formal-root lists: `Fin (length ...)`
supplies the finite branch index type, while eventual list membership is
converted to an index by `List.exists_mem_iff_get`.
-/
theorem
    hasAnalyticPowerCurveAt_of_eventually_finite_complexAnalytic_branchLists
    {I σ : Type*}
    [Fintype I] [Fintype σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I)
    (coordinate : Assignment σ →L[ℝ] ℝ)
    (x₀ : Assignment σ)
    (q : ℕ)
    (hq : 0 < q)
    (branches : σ → List (ℂ → ℂ))
    (hbranch_analytic :
      ∀ v γ, γ ∈ branches v → AnalyticAt ℂ γ 0)
    (hbranch_zero :
      ∀ v γ, γ ∈ branches v → (γ 0).re = x₀ v)
    (hbranch_coordinate :
      ∀ (k : ∀ v, Fin (branches v).length) (t : ℝ),
        coordinate
          (fun v => ((branches v).get (k v) (t : ℂ)).re) =
            t ^ q)
    (x : ℕ → Assignment σ)
    (t : ℕ → ℝ)
    (hx : ∀ n, x n ∈ signCell P τ)
    (ht :
      Tendsto t atTop
        (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hcovered :
      ∀ᶠ n in atTop,
        ∀ v, ∃ γ ∈ branches v,
          (γ (t n : ℂ)).re = x n v) :
    HasAnalyticPowerCurveAt (signCell P τ) coordinate x₀ := by
  let branch :
      ∀ v, Fin (branches v).length → ℂ → ℂ :=
    fun v k => (branches v).get k
  refine
    hasAnalyticPowerCurveAt_of_eventually_finite_complexAnalytic_branches
      P τ coordinate x₀ q hq branch ?_ ?_ ?_
        x t hx ht ?_
  · intro v k
    exact
      hbranch_analytic v ((branches v).get k)
        (List.get_mem _ k)
  · intro v k
    exact
      hbranch_zero v ((branches v).get k)
        (List.get_mem _ k)
  · exact hbranch_coordinate
  · filter_upwards [hcovered] with n hn
    intro v
    simpa [branch] using
      (List.exists_mem_iff_get.mp (hn v))

/--
An algebraic positive approach is sufficient for analytic curve selection
in a complete polynomial sign cell.

The input is one convergent sequence in the cell and one fixed nonzero
bivariate relation for every nonparameter coordinate.  The proof removes
parameter-only content on one common tail, chooses one irreducible factor per
coordinate, applies complex Newton--Puiseux with a common ramification, and
uses the sampled real roots to select a compatible finite tuple of analytic
branches.
-/
theorem hasAnalyticPowerCurveAt_signCell_of_algebraic_approach
    {I σ : Type*} [Fintype I] [Fintype σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I)
    (parameter : σ)
    (x₀ : Assignment σ)
    (hparameter : x₀ parameter = 0)
    (x : ℕ → Assignment σ)
    (relation :
      {j : σ // j ≠ parameter} →
        Polynomial (Polynomial ℝ))
    (hxcell : ∀ i, x i ∈ signCell P τ)
    (hxpos : ∀ i, 0 < x i parameter)
    (hxlim : Tendsto x atTop (𝓝 x₀))
    (hrelation : ∀ j, relation j ≠ 0)
    (hrelationRoot :
      ∀ i j,
        bivEval (relation j) (x i parameter) (x i j.1) = 0) :
    HasAnalyticPowerCurveAt
      (signCell P τ)
      (ContinuousLinearMap.proj parameter) x₀ := by
  classical
  have hxparameter :
      Tendsto (fun i => x i parameter) atTop (𝓝 0) := by
    simpa [hparameter] using
      (tendsto_pi_nhds.mp hxlim) parameter
  let J := {j : σ // j ≠ parameter}
  let Q : J → Polynomial (Polynomial ℝ) :=
    fun j =>
      (translateBivPolynomialValue
        (relation j) (x₀ j.1)).primPart
  have hQrootEventually :
      ∀ᶠ i in atTop, ∀ j : J,
        GateGTerminationScratch.bivEvalAt
          (Q j) (x i parameter) (x i j.1 - x₀ j.1) = 0 := by
    simpa [J, Q, bivEval,
      GateGTerminationScratch.bivEvalAt] using
      (eventually_centered_primPart_isRoot
        relation hrelation
        (fun i => x i parameter) hxpos hxparameter
        (fun i j => x i j.1) (fun j => x₀ j.1)
        hrelationRoot)
  rw [Filter.eventually_atTop] at hQrootEventually
  obtain ⟨N, hN⟩ := hQrootEventually
  let shift : ℕ → ℕ := fun i => i + N
  let sample : ℕ → Assignment σ := fun i => x (shift i)
  let lam : ℕ → ℝ := fun i => sample i parameter
  let centered : ℕ → J → ℝ :=
    fun i j => sample i j.1 - x₀ j.1
  have hshift : Tendsto shift atTop atTop := by
    simpa [shift] using tendsto_add_atTop_nat N
  have hsample :
      Tendsto sample atTop (𝓝 x₀) := by
    exact hxlim.comp hshift
  have hlam : Tendsto lam atTop (𝓝 0) := by
    simpa [lam, sample, hparameter] using
      (tendsto_pi_nhds.mp hsample) parameter
  have hcentered :
      ∀ j, Tendsto (fun i => centered i j) atTop (𝓝 0) := by
    intro j
    have hj := (tendsto_pi_nhds.mp hsample) j.1
    simpa [centered, sample] using hj.sub_const (x₀ j.1)
  have hlamPos : ∀ i, 0 < lam i := by
    exact fun i => hxpos (shift i)
  have hQne : ∀ j, Q j ≠ 0 := by
    intro j
    exact Polynomial.primPart_ne_zero _
  have hQprimitive : ∀ j, (Q j).IsPrimitive := by
    intro j
    exact Polynomial.isPrimitive_primPart _
  have hQroot :
      ∀ i j,
        GateGTerminationScratch.bivEvalAt
          (Q j) (lam i) (centered i j) = 0 := by
    intro i j
    exact hN (shift i) (Nat.le_add_left N i) j
  obtain
      ⟨q, ns, f, unit, p, hp, orders, branches, t,
        hq, hpairSub, hqroot, H, hsplit, hbranchData,
        htCanonical, ht, htPow, hcovered⟩ :=
    exists_factorTuple_finite_analytic_branches_covering_sequence
        GateGPuiseuxDegreeScratch.hasRamifiedRootProperty_algClosed
        Q hQne hQprimitive lam centered hlamPos hlam hcentered hQroot
  let parameterBranch : ℂ → ℂ := fun z => z ^ p
  let allBranches : σ → List (ℂ → ℂ) :=
    fun v =>
      if hv : v = parameter then
        [parameterBranch]
      else
        (branches ⟨v, hv⟩).map
          (fun γ z => (x₀ v : ℂ) + γ z)
  let sampledAssignment : ℕ → Assignment σ :=
    fun i => sample (ns i)
  have hAllAnalytic :
      ∀ v γ, γ ∈ allBranches v → AnalyticAt ℂ γ 0 := by
    intro v γ hγ
    by_cases hv : v = parameter
    · have hγeq : γ = parameterBranch := by
        simpa [allBranches, hv] using hγ
      rw [hγeq]
      exact analyticAt_id.pow p
    · have hγmem :
          γ ∈
            (branches ⟨v, hv⟩).map
              (fun b z => (x₀ v : ℂ) + b z) := by
        simpa [allBranches, hv] using hγ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hγmem
      exact analyticAt_const.add
        ((hbranchData ⟨v, hv⟩).2.2 b hb).1
  have hAllZero :
      ∀ v γ, γ ∈ allBranches v → (γ 0).re = x₀ v := by
    intro v γ hγ
    by_cases hv : v = parameter
    · subst v
      have hγeq : γ = parameterBranch := by
        simpa [allBranches] using hγ
      rw [hγeq]
      simp [parameterBranch, hp, hparameter]
    · have hγmem :
          γ ∈
            (branches ⟨v, hv⟩).map
              (fun b z => (x₀ v : ℂ) + b z) := by
        simpa [allBranches, hv] using hγ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hγmem
      have hb0 := ((hbranchData ⟨v, hv⟩).2.2 b hb).2.1
      simp [hb0]
  have hAllCoordinate :
      ∀ (k : ∀ v, Fin (allBranches v).length) (r : ℝ),
        (ContinuousLinearMap.proj parameter :
          Assignment σ →L[ℝ] ℝ)
            (fun v =>
              ((allBranches v).get (k v) (r : ℂ)).re) =
          r ^ p := by
    intro k r
    change
      ((allBranches parameter).get (k parameter) (r : ℂ)).re =
        r ^ p
    have hmem :
        (allBranches parameter).get (k parameter) ∈
          [parameterBranch] := by
      simpa [allBranches] using
        (List.get_mem (allBranches parameter) (k parameter))
    have heq :
        (allBranches parameter).get (k parameter) =
          parameterBranch :=
      List.mem_singleton.mp hmem
    rw [heq]
    rw [show
      parameterBranch (r : ℂ) = ((r ^ p : ℝ) : ℂ) by
        exact (Complex.ofReal_pow r p).symm]
    exact Complex.ofReal_re _
  have hSampleCell :
      ∀ i, sampledAssignment i ∈ signCell P τ := by
    exact fun i => hxcell (shift (ns i))
  have hAllCovered :
      ∀ᶠ i in atTop, ∀ v,
        ∃ γ ∈ allBranches v,
          (γ (t i : ℂ)).re = sampledAssignment i v := by
    filter_upwards [hcovered] with i hi
    intro v
    by_cases hv : v = parameter
    · subst v
      refine ⟨parameterBranch, ?_, ?_⟩
      · simp [allBranches]
      · rw [show sampledAssignment i parameter = lam (ns i) by rfl]
        rw [← htPow i]
        rw [show
          parameterBranch (t i : ℂ) = (((t i) ^ p : ℝ) : ℂ) by
            exact (Complex.ofReal_pow (t i) p).symm]
        exact Complex.ofReal_re _
    · obtain ⟨γ, hγ, hγeq⟩ := hi ⟨v, hv⟩
      refine
        ⟨fun z => (x₀ v : ℂ) + γ z, ?_, ?_⟩
      · simp only [allBranches, dif_neg hv, List.mem_map]
        exact ⟨γ, hγ, rfl⟩
      · have hγeqRe := congrArg Complex.re hγeq
        simp only [Complex.ofReal_re] at hγeqRe
        change x₀ v + (γ (t i : ℂ)).re =
          sampledAssignment i v
        rw [← hγeqRe]
        simp [centered, sampledAssignment]
  exact
    hasAnalyticPowerCurveAt_of_eventually_finite_complexAnalytic_branchLists
      P τ (ContinuousLinearMap.proj parameter) x₀ p
      (Nat.pos_of_ne_zero hp) allBranches
      hAllAnalytic hAllZero hAllCoordinate
      sampledAssignment t hSampleCell ht hAllCovered

/--
Generically finite saturated algebraic elimination supplies the algebraic
approach consumed by
`hasAnalyticPowerCurveAt_signCell_of_algebraic_approach`.
-/
theorem hasAnalyticPowerCurveAt_signCell_of_saturated_moduleFinite
    {I σ : Type*} [Fintype I] [Fintype σ]
    (P : I → MvPolynomial σ ℝ)
    (τ : SignPattern I)
    (parameter : σ)
    (x₀ : Assignment σ)
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
    HasAnalyticPowerCurveAt
      (signCell P τ)
      (ContinuousLinearMap.proj parameter) x₀ := by
  obtain
      ⟨x, relation, hxcell, _hxanti, hxpos, hxlim,
        _hxparameter, hrelation, hrelationRoot⟩ :=
    exists_algebraic_strictAnti_signCell_approach
      P τ parameter x₀ hparameter hclosure
  exact
    hasAnalyticPowerCurveAt_signCell_of_algebraic_approach
      P τ parameter x₀ hparameter x relation
      hxcell hxpos hxlim hrelation hrelationRoot

end GateGCurveSelection
end Math
