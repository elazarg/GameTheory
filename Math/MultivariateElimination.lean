/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Elimination of one multivariate polynomial variable

This module isolates one variable of a real multivariate polynomial as the
outer variable of a univariate polynomial. The resultant of two such
polynomials eliminates that variable.

The eliminant includes the leading coefficient of the first polynomial. This
factor covers specializations at which its degree drops: any common zero of
the original polynomials maps to a zero of the eliminant without a
specialization hypothesis. Nonvanishing of the eliminant is separated into
the exact algebraic condition that the formal resultant is nonzero.

## Main declarations

* `isolateVariable`: view a selected multivariate variable as a univariate
  polynomial variable.
* `eliminateVariable`: resultant eliminant, including the degree-drop locus.
* `eval_eliminateVariable_eq_zero`: common zeros descend through elimination.
* `eliminateVariable_ne_zero`: the formal resultant condition ensures that the
  eliminant carries information.
* `bivariateOfEquiv`: encode a polynomial whose variable type has two elements
  as a nested bivariate polynomial.
* `exists_nonunit_commonFactor_map_fractionRing_of_resultant_eq_zero`: interpret
  a zero resultant as a genuine common factor over the coefficient fraction
  field.
* `exists_nonzero_coordinateRelation_mem_of_moduleFinite_fractionRing`: a
  finite affine quotient over a coefficient fraction field gives a nonzero
  coordinate relation in the original ideal.
* `moduleFinite_quotient_of_monic_coordinateRelations`: monic relations for
  every affine coordinate give a finite quotient.
* `not_moduleFinite_quotient_of_le_span_X_sub_X`: an ideal contained in a
  diagonal hypersurface ideal has a positive-dimensional quotient.
-/

noncomputable section

namespace Math
namespace MultivariateElimination

/-- Resultant vanishing at the actual degrees persists when the determinant
uses any larger degree bounds. -/
theorem resultant_eq_zero_of_le_of_not_isCoprime
    {K : Type*} [Field K]
    {f g : Polynomial K} {m n : ℕ}
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n)
    (hfg : f ≠ 0 ∨ g ≠ 0) (h : ¬ IsCoprime f g) :
    Polynomial.resultant f g m n = 0 := by
  have hbase : Polynomial.resultant f g = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨hfg, h⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
    hk', Polynomial.resultant_add_right_deg _ _ _ _ k' le_rfl,
    hbase, mul_zero, mul_zero]

/-- Regard `i` as the outer univariate variable and all other variables as
coefficients. -/
noncomputable def isolateVariable
    {σ : Type*} (i : σ) :
    MvPolynomial σ ℝ ≃ₐ[ℝ]
      Polynomial (MvPolynomial {j : σ // j ≠ i} ℝ) := by
  classical
  exact
    (MvPolynomial.renameEquiv ℝ
        (Equiv.optionSubtypeNe i).symm).trans
      (MvPolynomial.optionEquivLeft ℝ _)

/-- Evaluation commutes with isolating a variable. -/
theorem eval_isolateVariable
    {σ : Type*} (i : σ) (P : MvPolynomial σ ℝ)
    (a : σ → ℝ) :
    MvPolynomial.eval a P =
      Polynomial.eval (a i)
        (Polynomial.map
          (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
          (isolateVariable i P)) := by
  classical
  let b : Option {j : σ // j ≠ i} → ℝ :=
    fun x => Option.elim x (a i) (fun j => a j)
  have hcomp :
      b ∘ (Equiv.optionSubtypeNe i).symm = a := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [b]
    · simp [b, Equiv.optionSubtypeNe_symm_of_ne hji]
  calc
    MvPolynomial.eval a P =
        MvPolynomial.eval b
          (MvPolynomial.rename
            (Equiv.optionSubtypeNe i).symm P) := by
      rw [MvPolynomial.eval_rename, hcomp]
    _ = Polynomial.eval (a i)
        (Polynomial.map
          (MvPolynomial.eval
            fun j : {j : σ // j ≠ i} => a j)
          (isolateVariable i P)) := by
      simpa [b, isolateVariable] using
        (MvPolynomial.optionEquivLeft_elim_eval
          (R := ℝ) (S₁ := {j : σ // j ≠ i})
          (fun j : {j : σ // j ≠ i} => a j) (a i)
          (MvPolynomial.rename
            (Equiv.optionSubtypeNe i).symm P))

/-- Eliminate `i` from two multivariate polynomials. The leading-coefficient
factor records the locus at which specialization lowers the degree of `P`. -/
noncomputable def eliminateVariable
    {σ : Type*} (i : σ)
    (P Q : MvPolynomial σ ℝ) :
    MvPolynomial {j : σ // j ≠ i} ℝ := by
  classical
  exact
    Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) *
      (isolateVariable i P).leadingCoeff

/-- A nonzero first polynomial and nonzero formal resultant give a nonzero
eliminant. -/
theorem eliminateVariable_ne_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ}
    (hP : P ≠ 0)
    (hresultant :
      Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) ≠ 0) :
    eliminateVariable i P Q ≠ 0 := by
  classical
  apply mul_ne_zero hresultant
  apply Polynomial.leadingCoeff_ne_zero.mpr
  exact (isolateVariable i).injective.ne hP

/-- Every common zero of `P` and `Q` descends to a zero of their eliminant
under the assignment with `i` removed. -/
theorem eval_eliminateVariable_eq_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ} (a : σ → ℝ)
    (hP : MvPolynomial.eval a P = 0)
    (hQ : MvPolynomial.eval a Q = 0) :
    MvPolynomial.eval
        (fun j : {j : σ // j ≠ i} => a j)
        (eliminateVariable i P Q) = 0 := by
  classical
  let f :=
    (isolateVariable i P).map
      (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
  let g :=
    (isolateVariable i Q).map
      (MvPolynomial.eval fun j : {j : σ // j ≠ i} => a j)
  have hfroot : f.eval (a i) = 0 := by
    rw [← eval_isolateVariable i P a]
    exact hP
  have hgroot : g.eval (a i) = 0 := by
    rw [← eval_isolateVariable i Q a]
    exact hQ
  by_cases hlead :
      MvPolynomial.eval
        (fun j : {j : σ // j ≠ i} => a j)
        (isolateVariable i P).leadingCoeff = 0
  · simp [eliminateVariable, hlead]
  · have hfne : f ≠ 0 := by
      intro hf
      apply hlead
      have hc : f.coeff (isolateVariable i P).natDegree = 0 := by
        rw [hf]
        simp
      simpa [f, Polynomial.coeff_map] using hc
    have hnotcop : ¬ IsCoprime f g := by
      intro hcop
      rcases Polynomial.aeval_ne_zero_of_isCoprime hcop (a i) with h | h
      · exact h (by simpa [Polynomial.aeval_def,
          Polynomial.eval₂_id] using hfroot)
      · exact h (by simpa [Polynomial.aeval_def,
          Polynomial.eval₂_id] using hgroot)
    have hm : f.natDegree ≤ (isolateVariable i P).natDegree := by
      exact Polynomial.natDegree_map_le
    have hn : g.natDegree ≤ (isolateVariable i Q).natDegree := by
      exact Polynomial.natDegree_map_le
    have hres :
        Polynomial.resultant f g
          (isolateVariable i P).natDegree
          (isolateVariable i Q).natDegree = 0 :=
      resultant_eq_zero_of_le_of_not_isCoprime
        hm hn (Or.inl hfne) hnotcop
    have hmap :
        Polynomial.resultant f g
            (isolateVariable i P).natDegree
            (isolateVariable i Q).natDegree =
          MvPolynomial.eval
            (fun j : {j : σ // j ≠ i} => a j)
            (Polynomial.resultant
              (isolateVariable i P)
              (isolateVariable i Q)) := by
      dsimp only [f, g]
      rw [Polynomial.resultant_map_map]
    rw [eliminateVariable, map_mul, ← hmap, hres, zero_mul]

/-- Encode a polynomial on any explicitly two-element variable type as a
nested polynomial. The `none` coordinate is the outer variable and the unique
`some` coordinate is the inner coefficient variable. -/
noncomputable def bivariateOfEquiv
    {σ : Type*} (e : σ ≃ Option Unit) :
    MvPolynomial σ ℝ ≃ₐ[ℝ] Polynomial (Polynomial ℝ) :=
  (MvPolynomial.renameEquiv ℝ e).trans
    ((MvPolynomial.optionEquivLeft ℝ Unit).trans
      (Polynomial.mapAlgEquiv
        (MvPolynomial.uniqueAlgEquiv ℝ Unit)))

/-- Evaluation commutes with `bivariateOfEquiv`. -/
theorem eval_bivariateOfEquiv
    {σ : Type*} (e : σ ≃ Option Unit)
    (P : MvPolynomial σ ℝ) (a : σ → ℝ) :
    Polynomial.eval (a (e.symm none))
        (Polynomial.map
          (Polynomial.evalRingHom
            (a (e.symm (some ()))))
          (bivariateOfEquiv e P)) =
      MvPolynomial.eval a P := by
  classical
  let b : Option Unit → ℝ := fun x => a (e.symm x)
  calc
    Polynomial.eval (a (e.symm none))
        (Polynomial.map
          (Polynomial.evalRingHom
            (a (e.symm (some ()))))
          (bivariateOfEquiv e P)) =
        Polynomial.eval (b none)
          (Polynomial.map
            (MvPolynomial.eval fun _ : Unit => b (some ()))
            (MvPolynomial.optionEquivLeft ℝ Unit
              (MvPolynomial.rename e P))) := by
      simp only [bivariateOfEquiv, AlgEquiv.trans_apply,
        Polynomial.coe_mapAlgEquiv, Polynomial.map_map]
      congr 2
      ext q
      · simp
      · rw [show q = () from Subsingleton.elim _ _]
        simp [MvPolynomial.uniqueAlgEquiv, b]
    _ = MvPolynomial.eval b
        (MvPolynomial.rename e P) := by
      rw [← MvPolynomial.optionEquivLeft_elim_eval
        (R := ℝ) (S₁ := Unit)]
      congr
      funext x
      cases x <;> simp [b]
    _ = MvPolynomial.eval a P := by
      rw [MvPolynomial.eval_rename]
      congr
      funext x
      simp [b]

/-- A zero formal resultant becomes non-coprimality after mapping the
coefficient ring to its fraction field. -/
theorem not_isCoprime_map_fractionRing_of_resultant_eq_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ} (hP : P ≠ 0)
    (hres :
      Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) = 0) :
    let A := MvPolynomial {j : σ // j ≠ i} ℝ
    let K := FractionRing A
    ¬ IsCoprime
      ((isolateVariable i P).map (algebraMap A K))
      ((isolateVariable i Q).map (algebraMap A K)) := by
  classical
  dsimp only
  let A := MvPolynomial {j : σ // j ≠ i} ℝ
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ :=
    IsFractionRing.injective A K
  have hPi : isolateVariable i P ≠ 0 :=
    (isolateVariable i).injective.ne hP
  have hfne : (isolateVariable i P).map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff hφ).mpr hPi
  have hmap := congrArg φ hres
  have hresK :
      Polynomial.resultant
        ((isolateVariable i P).map φ)
        ((isolateVariable i Q).map φ) = 0 := by
    simpa only [map_zero, Polynomial.resultant_map_map,
      Polynomial.natDegree_map_eq_of_injective hφ] using hmap
  exact (Polynomial.resultant_eq_zero_iff.mp hresK).2

/-- A zero formal resultant supplies a nonzero, nonunit common polynomial
factor after adjoining fractions of the remaining-variable coefficient ring. -/
theorem exists_nonunit_commonFactor_map_fractionRing_of_resultant_eq_zero
    {σ : Type*} (i : σ)
    {P Q : MvPolynomial σ ℝ} (hP : P ≠ 0)
    (hres :
      Polynomial.resultant
        (isolateVariable i P) (isolateVariable i Q) = 0) :
    let A := MvPolynomial {j : σ // j ≠ i} ℝ
    let K := FractionRing A
    ∃ H : Polynomial K,
      H ≠ 0 ∧ ¬ IsUnit H ∧
        H ∣ (isolateVariable i P).map (algebraMap A K) ∧
        H ∣ (isolateVariable i Q).map (algebraMap A K) := by
  classical
  dsimp only
  let A := MvPolynomial {j : σ // j ≠ i} ℝ
  let K := FractionRing A
  let f := (isolateVariable i P).map (algebraMap A K)
  let g := (isolateVariable i Q).map (algebraMap A K)
  have hf : f ≠ 0 := by
    apply (Polynomial.map_ne_zero_iff
      (IsFractionRing.injective A K)).mpr
    exact (isolateVariable i).injective.ne hP
  have hcop : ¬ IsCoprime f g := by
    exact
      not_isCoprime_map_fractionRing_of_resultant_eq_zero
        i hP hres
  let H := gcd f g
  refine ⟨H, ?_, ?_, gcd_dvd_left f g, gcd_dvd_right f g⟩
  · intro hH
    have hz : (0 : Polynomial K) ∣ f := by
      simpa [H, hH] using gcd_dvd_left f g
    exact hf (zero_dvd_iff.mp hz)
  · change ¬ IsUnit (gcd f g)
    rw [gcd_isUnit_iff_isRelPrime,
      isRelPrime_iff_isCoprime]
    exact hcop

/-- A finite affine coordinate ring makes every coordinate integral over the
coefficient field. The resulting monic relation is recorded back in the
defining ideal. -/
theorem exists_monic_coordinateRelation_of_moduleFinite
    {K κ : Type*} [Field K]
    (I : Ideal (MvPolynomial κ K))
    [Module.Finite K (MvPolynomial κ K ⧸ I)]
    (target : κ) :
    ∃ p : Polynomial K,
      p.Monic ∧
        Polynomial.aeval (MvPolynomial.X target) p ∈ I := by
  let x : MvPolynomial κ K ⧸ I :=
    Ideal.Quotient.mk I (MvPolynomial.X target)
  obtain ⟨p, hpmonic, hp⟩ := IsIntegral.of_finite K x
  refine ⟨p, hpmonic, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  dsimp only [x] at hp
  have hcoeff :
      (Ideal.Quotient.mk I).comp
          (algebraMap K (MvPolynomial κ K)) =
        algebraMap K (MvPolynomial κ K ⧸ I) := by
    exact Ideal.Quotient.mk_comp_algebraMap (R₁ := K) I
  rw [hcoeff]
  exact hp

/-- Monic relations for all affine coordinates make the quotient finite over
the coefficient field. Together with
`exists_monic_coordinateRelation_of_moduleFinite`, this gives a
certificate-level characterization of finite affine quotients when the
variable type is finite. -/
theorem moduleFinite_quotient_of_monic_coordinateRelations
    {K κ : Type*} [Field K] [Finite κ]
    (I : Ideal (MvPolynomial κ K))
    (p : κ → Polynomial K)
    (hpmonic : ∀ i, (p i).Monic)
    (hpmem : ∀ i,
      Polynomial.aeval (MvPolynomial.X i) (p i) ∈ I) :
    Module.Finite K (MvPolynomial κ K ⧸ I) := by
  let q : MvPolynomial κ K →ₐ[K]
      MvPolynomial κ K ⧸ I :=
    Ideal.Quotient.mkₐ K I
  have hcoordinate :
      ∀ i, IsIntegral K (q (MvPolynomial.X i)) := by
    intro i
    refine ⟨p i, hpmonic i, ?_⟩
    change Polynomial.aeval (q (MvPolynomial.X i)) (p i) = 0
    rw [Polynomial.aeval_algHom_apply q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpmem i)
  have hadjoin :
      Algebra.adjoin K
          (Set.range fun i => q (MvPolynomial.X i)) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    have haeval :
        MvPolynomial.aeval
            (fun i => q (MvPolynomial.X i)) = q := by
      ext i
      simp
    rw [haeval, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective K I
  have hclosure :
      integralClosure K (MvPolynomial κ K ⧸ I) = ⊤ := by
    apply top_unique
    rw [← hadjoin]
    exact Algebra.adjoin_le fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hcoordinate i
  letI : Algebra.IsIntegral K (MvPolynomial κ K ⧸ I) :=
    integralClosure_eq_top_iff.mp hclosure
  exact Algebra.IsIntegral.finite

/-- For finitely many affine coordinates, a quotient is finite over the
coefficient field exactly when every coordinate has a monic relation in the
defining ideal. -/
theorem moduleFinite_quotient_iff_exists_monic_coordinateRelations
    {K κ : Type*} [Field K] [Finite κ]
    (I : Ideal (MvPolynomial κ K)) :
    Module.Finite K (MvPolynomial κ K ⧸ I) ↔
      ∃ p : κ → Polynomial K,
        (∀ i, (p i).Monic) ∧
        ∀ i, Polynomial.aeval (MvPolynomial.X i) (p i) ∈ I := by
  constructor
  · intro hfinite
    letI : Module.Finite K (MvPolynomial κ K ⧸ I) := hfinite
    choose p hpmonic hpmem using
      fun i => exists_monic_coordinateRelation_of_moduleFinite I i
    exact ⟨p, hpmonic, hpmem⟩
  · rintro ⟨p, hpmonic, hpmem⟩
    exact
      moduleFinite_quotient_of_monic_coordinateRelations
        I p hpmonic hpmem

/-- Over a fraction field, finite-dimensionality supplies a nonzero coordinate
relation with coefficients in the original domain. -/
theorem exists_nonzero_coordinateRelation_of_moduleFinite_fractionRing
    {A κ : Type*} [CommRing A] [IsDomain A]
    (I : Ideal (MvPolynomial κ (FractionRing A)))
    [Module.Finite (FractionRing A)
      (MvPolynomial κ (FractionRing A) ⧸ I)]
    (target : κ) :
    ∃ q : Polynomial A,
      q ≠ 0 ∧
        Polynomial.aeval (MvPolynomial.X target)
          (q.map (algebraMap A (FractionRing A))) ∈ I := by
  obtain ⟨p, hpmonic, hpI⟩ :=
    exists_monic_coordinateRelation_of_moduleFinite I target
  let q : Polynomial A :=
    IsLocalization.integerNormalization
      (nonZeroDivisors A) p
  have hq : q ≠ 0 := by
    intro hqzero
    have hpzero : p = 0 := by
      apply (IsLocalization.integerNormalization_eq_zero_iff
        (M := nonZeroDivisors A) le_rfl p).mp
      exact hqzero
    exact hpmonic.ne_zero hpzero
  refine ⟨q, hq, ?_⟩
  obtain ⟨b, _hb, hmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors A) p
  rw [hmap]
  simpa [Algebra.smul_def, Polynomial.aeval_mul,
    Polynomial.aeval_C] using
      I.mul_mem_left
        (algebraMap A
          (MvPolynomial κ (FractionRing A)) b) hpI

/-- If extending an affine ideal to the coefficient fraction field gives a
finite quotient, then every coordinate satisfies a nonzero relation already
in the original ideal. Clearing the ideal-membership denominator, rather than
specializing it, covers all coefficient specializations. -/
theorem exists_nonzero_coordinateRelation_mem_of_moduleFinite_fractionRing
    {A κ : Type*} [CommRing A] [IsDomain A]
    (J : Ideal (MvPolynomial κ A))
    [Module.Finite (FractionRing A)
      (MvPolynomial κ (FractionRing A) ⧸
        J.map (MvPolynomial.map
          (algebraMap A (FractionRing A))))]
    (target : κ) :
    ∃ q : Polynomial A,
      q ≠ 0 ∧
        Polynomial.aeval (MvPolynomial.X target) q ∈ J := by
  letI : Algebra (MvPolynomial κ A)
      (MvPolynomial κ (FractionRing A)) :=
    MvPolynomial.algebraMvPolynomial
  letI : IsLocalization
      ((nonZeroDivisors A).map
        (MvPolynomial.C : A →+*
          MvPolynomial κ A).toMonoidHom)
      (MvPolynomial κ (FractionRing A)) :=
    MvPolynomial.isLocalization
      (σ := κ) (nonZeroDivisors A) (FractionRing A)
  let φ : MvPolynomial κ A →+*
      MvPolynomial κ (FractionRing A) :=
    MvPolynomial.map (algebraMap A (FractionRing A))
  obtain ⟨q, hq, hqI⟩ :=
    exists_nonzero_coordinateRelation_of_moduleFinite_fractionRing
      (J.map φ) target
  have hmapEval :
      φ (Polynomial.aeval (MvPolynomial.X target) q) =
        Polynomial.aeval (MvPolynomial.X target)
          (q.map (algebraMap A (FractionRing A))) := by
    have hcomp :
        (algebraMap (FractionRing A)
          (MvPolynomial κ (FractionRing A))).comp
            (algebraMap A (FractionRing A)) =
          φ.comp (algebraMap A (MvPolynomial κ A)) := by
      ext a
      simp [φ]
    simpa [φ] using
      (Polynomial.map_aeval_eq_aeval_map hcomp q
        (MvPolynomial.X target))
  have hlocalized :
      φ (Polynomial.aeval (MvPolynomial.X target) q) ∈
        J.map φ := by
    rw [hmapEval]
    exact hqI
  have hcleared :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (M := (nonZeroDivisors A).map
        (MvPolynomial.C : A →+*
          MvPolynomial κ A).toMonoidHom)
      (S := MvPolynomial κ (FractionRing A))
      J
      (Polynomial.aeval (MvPolynomial.X target) q)).mp
      hlocalized
  obtain ⟨m, hm, hmJ⟩ := hcleared
  obtain ⟨d, hd, rfl⟩ := hm
  let q' : Polynomial A := Polynomial.C d * q
  have hdne : d ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hq' : q' ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hdne) hq
  refine ⟨q', hq', ?_⟩
  simpa [q', Polynomial.aeval_mul, Polynomial.aeval_C] using hmJ

/-- Identifying two variables leaves a free polynomial coordinate, so the
corresponding hypersurface quotient is not finite over the coefficient
field. -/
theorem not_moduleFinite_quotient_span_X_sub_X
    {K κ : Type*} [Field K]
    (i j : κ) :
    ¬ Module.Finite K
      (MvPolynomial κ K ⧸
        Ideal.span {
          (MvPolynomial.X i : MvPolynomial κ K) -
            MvPolynomial.X j}) := by
  classical
  let I : Ideal (MvPolynomial κ K) :=
    Ideal.span {
      (MvPolynomial.X i : MvPolynomial κ K) -
        MvPolynomial.X j}
  let assign : κ → Polynomial K :=
    fun x => if x = i ∨ x = j then Polynomial.X else 0
  let f : MvPolynomial κ K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval assign
  have hI : I ≤ RingHom.ker f.toRingHom := by
    dsimp only [I]
    rw [Ideal.span_le]
    rintro P ⟨hP | hP, rfl⟩
    · simp [f, assign]
  let qf :
      (MvPolynomial κ K ⧸ I) →ₐ[K] Polynomial K :=
    Ideal.Quotient.liftₐ I f hI
  intro hfinite
  letI : Module.Finite K (MvPolynomial κ K ⧸ I) :=
    hfinite
  let xi : MvPolynomial κ K ⧸ I :=
    Ideal.Quotient.mk I (MvPolynomial.X i)
  have hxi : IsIntegral K xi :=
    IsIntegral.of_finite K xi
  have hmap : IsIntegral K (qf xi) :=
    hxi.map qf
  have hqf : qf xi = Polynomial.X := by
    simp [qf, xi, f, assign]
  rw [hqf] at hmap
  exact Polynomial.transcendental_X K hmap.isAlgebraic

/-- More generally, an ideal contained in a diagonal hypersurface ideal
cannot have finite-dimensional quotient. -/
theorem not_moduleFinite_quotient_of_le_span_X_sub_X
    {K κ : Type*} [Field K]
    (J : Ideal (MvPolynomial κ K))
    (i j : κ)
    (hJ : J ≤ Ideal.span {
      (MvPolynomial.X i : MvPolynomial κ K) -
        MvPolynomial.X j}) :
    ¬ Module.Finite K (MvPolynomial κ K ⧸ J) := by
  intro hfinite
  letI : Module.Finite K (MvPolynomial κ K ⧸ J) :=
    hfinite
  let I : Ideal (MvPolynomial κ K) :=
    Ideal.span {
      (MvPolynomial.X i : MvPolynomial κ K) -
        MvPolynomial.X j}
  have hJI : J ≤ I := by
    exact hJ
  let q : (MvPolynomial κ K ⧸ J) →ₗ[K]
      (MvPolynomial κ K ⧸ I) :=
    (Ideal.Quotient.factorₐ K hJI).toLinearMap
  letI : Module.Finite K (MvPolynomial κ K ⧸ I) :=
    Module.Finite.of_surjective q
      (Ideal.Quotient.factor_surjective hJI)
  exact
    (not_moduleFinite_quotient_span_X_sub_X
      (K := K) (κ := κ) i j) inferInstance

end MultivariateElimination
end Math
