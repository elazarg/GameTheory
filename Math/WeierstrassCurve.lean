/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Polynomial.Content
import Math.AlgebraicSelection

/-!
# Weierstrass normalization of bivariate polynomial curves

This file converts a bivariate polynomial, presented as a polynomial in a
value variable with polynomial coefficients in a parameter, into an iterated
formal power series. Weierstrass preparation then replaces its primitive part
by a distinguished polynomial times a formal unit.

For a nonzero real bivariate relation, taking the primitive part removes every
common parameter-only factor without changing its selected roots on a
sufficiently small punctured positive interval. Translating the value variable
centers the equation at a chosen endpoint.

The output is the formal input to Newton--Puiseux: a distinguished polynomial
over `K⟦λ⟧`. Ramified splitting of that polynomial is a separate theorem.
-/

noncomputable section

open Filter Polynomial Set Topology

namespace Math

variable {K : Type*} [Field K]

/-- Embed every parameter polynomial coefficient into formal power series. -/
def bivPolynomialToPowerSeriesPolynomial
    (P : Polynomial (Polynomial K)) :
    Polynomial (PowerSeries K) :=
  P.map Polynomial.coeToPowerSeries.ringHom

@[simp]
theorem coeff_bivPolynomialToPowerSeriesPolynomial
    (P : Polynomial (Polynomial K)) (i n : ℕ) :
    PowerSeries.coeff n
      ((bivPolynomialToPowerSeriesPolynomial P).coeff i) =
        (P.coeff i).coeff n := by
  simp [bivPolynomialToPowerSeriesPolynomial]

/-- Regard a bivariate polynomial as a formal power series in the value
variable whose coefficients are formal power series in the parameter. -/
def bivPolynomialToIteratedPowerSeries
    (P : Polynomial (Polynomial K)) :
    PowerSeries (PowerSeries K) :=
  (bivPolynomialToPowerSeriesPolynomial P : PowerSeries (PowerSeries K))

/-- A nonzero specialization at parameter zero remains nonzero after mapping
the parameter-series coefficients to their residue field. -/
theorem map_residue_bivPolynomialToIteratedPowerSeries_ne_zero
    (P : Polynomial (Polynomial K))
    (hP0 : P.map (Polynomial.evalRingHom 0) ≠ 0) :
    PowerSeries.map (IsLocalRing.residue (PowerSeries K))
      (bivPolynomialToIteratedPowerSeries P) ≠ 0 := by
  intro hzero
  apply hP0
  ext n
  have hn := congrArg (PowerSeries.coeff n) hzero
  have hn' :
      IsLocalRing.residue (PowerSeries K)
          (PowerSeries.coeff n
            (bivPolynomialToIteratedPowerSeries P)) = 0 := by
    simpa using hn
  rw [IsLocalRing.residue_eq_zero_iff,
    PowerSeries.maximalIdeal_eq_span_X,
    Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hn'
  simpa [bivPolynomialToIteratedPowerSeries,
    bivPolynomialToPowerSeriesPolynomial, Polynomial.eval] using hn'

/-- Weierstrass preparation for a bivariate polynomial whose specialization
at parameter zero is not the zero polynomial. -/
theorem exists_weierstrassFactorization_bivPolynomial
    (P : Polynomial (Polynomial K))
    (hP0 : P.map (Polynomial.evalRingHom 0) ≠ 0) :
    ∃ f h,
      (bivPolynomialToIteratedPowerSeries P).IsWeierstrassFactorization
        f h := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  exact PowerSeries.exists_isWeierstrassFactorization
    (map_residue_bivPolynomialToIteratedPowerSeries_ne_zero P hP0)

/-- The primitive part has a nonzero specialization at parameter zero.
Otherwise the parameter variable would divide every coefficient, contradicting
primitivity. -/
theorem map_evalRingHom_zero_primPart_ne_zero
    [NormalizedGCDMonoid K]
    (P : Polynomial (Polynomial K)) :
    P.primPart.map (Polynomial.evalRingHom 0) ≠ 0 := by
  intro hzero
  have hcoeff : ∀ i, Polynomial.X ∣ P.primPart.coeff i := by
    intro i
    rw [Polynomial.X_dvd_iff]
    have hi := congrArg (fun Q => Q.coeff i) hzero
    simpa [Polynomial.eval] using hi
  have hCX :
      Polynomial.C Polynomial.X ∣ P.primPart :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).2 hcoeff
  exact Polynomial.not_isUnit_X
    (P.isPrimitive_primPart Polynomial.X hCX)

/-- Every primitive bivariate polynomial has a Weierstrass factorization,
without a separate nonvanishing-specialization hypothesis. -/
theorem exists_weierstrassFactorization_bivPolynomial_primPart
    [NormalizedGCDMonoid K]
    (P : Polynomial (Polynomial K)) :
    ∃ f h,
      (bivPolynomialToIteratedPowerSeries P.primPart).IsWeierstrassFactorization
        f h :=
  exists_weierstrassFactorization_bivPolynomial P.primPart
    (map_evalRingHom_zero_primPart_ne_zero P)

/-- Translate the value variable by `L`, so the original endpoint `L`
becomes the new value coordinate `0`. -/
def translateBivPolynomialValue
    (P : Polynomial (Polynomial K)) (L : K) :
    Polynomial (Polynomial K) :=
  P.comp (Polynomial.X + Polynomial.C (Polynomial.C L))

/-- The translated primitive curve has a distinguished-polynomial
Weierstrass factorization. -/
theorem exists_weierstrassFactorization_translate_primPart
    [NormalizedGCDMonoid K]
    (P : Polynomial (Polynomial K)) (L : K) :
    ∃ f h,
      (bivPolynomialToIteratedPowerSeries
        (translateBivPolynomialValue P L).primPart).IsWeierstrassFactorization
          f h :=
  exists_weierstrassFactorization_bivPolynomial_primPart
    (translateBivPolynomialValue P L)

theorem bivEval_translateBivPolynomialValue
    (P : Polynomial (Polynomial ℝ)) (L lam y : ℝ) :
    bivEval (translateBivPolynomialValue P L) lam y =
      bivEval P lam (y + L) := by
  unfold bivEval translateBivPolynomialValue
  rw [Polynomial.eval₂_comp]
  simp

/-- Away from zeros of the parameter-only content, every root of a
bivariate polynomial is a root of its primitive part. -/
theorem bivEval_primPart_eq_zero
    (P : Polynomial (Polynomial ℝ)) {lam y : ℝ}
    (hcontent : P.content.eval lam ≠ 0)
    (hroot : bivEval P lam y = 0) :
    bivEval P.primPart lam y = 0 := by
  rw [P.eq_C_content_mul_primPart] at hroot
  simp only [bivEval, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.coe_evalRingHom] at hroot ⊢
  exact (mul_eq_zero.mp hroot).resolve_left hcontent

/-- A nonzero bivariate polynomial's parameter-only content has no roots on
some punctured positive interval. -/
theorem exists_interval_content_eval_ne_zero
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ, P.content.eval lam ≠ 0 := by
  have hcontent : P.content ≠ 0 :=
    fun h => hP (Polynomial.content_eq_zero_iff.mp h)
  let S : Set ℝ := {lam | P.content.IsRoot lam}
  have hSfinite : S.Finite := Polynomial.finite_setOf_isRoot hcontent
  have hopen : IsOpen ((S \ {0})ᶜ) :=
    hSfinite.sdiff.isClosed.isOpen_compl
  have hzero : (0 : ℝ) ∈ (S \ {0})ᶜ := by simp
  have hmem :
      (S \ {0})ᶜ ∩ Set.Ioi (0 : ℝ) ∈
        nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hzero))
      self_mem_nhdsWithin
  have hne :
      {lam : ℝ | P.content.eval lam ≠ 0} ∈
        nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine Filter.mem_of_superset hmem ?_
    rintro lam ⟨hcomp, hpos⟩ hroot
    apply hcomp
    refine ⟨hroot, ?_⟩
    simpa using ne_of_gt hpos
  obtain ⟨ρ, hρ, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hne
  exact ⟨ρ, hρ, fun lam hlam => hsub hlam⟩

/-- On a sufficiently small punctured interval, a selected root of a nonzero
bivariate polynomial also satisfies its primitive equation. -/
theorem exists_interval_bivEval_primPart_eq_zero
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    {w : ℝ → ℝ}
    (hroot : ∀ lam, 0 < lam → bivEval P lam (w lam) = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
        bivEval P.primPart lam (w lam) = 0 := by
  obtain ⟨ρ, hρ, hcontent⟩ :=
    exists_interval_content_eval_ne_zero P hP
  exact ⟨ρ, hρ, fun lam hlam =>
    bivEval_primPart_eq_zero P (hcontent lam hlam)
      (hroot lam hlam.1)⟩

/-- Centering a selected real branch at `L` and removing parameter content
preserves its polynomial equation on a smaller punctured interval. -/
theorem exists_interval_bivEval_translate_primPart_eq_zero
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    {w : ℝ → ℝ} (L : ℝ)
    (hroot : ∀ lam, 0 < lam → bivEval P lam (w lam) = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
        bivEval (translateBivPolynomialValue P L).primPart
          lam (w lam - L) = 0 := by
  have htranslate :
      translateBivPolynomialValue P L ≠ 0 := by
    exact (Polynomial.comp_X_add_C_ne_zero_iff
      (p := P) (t := Polynomial.C L)).2 hP
  apply exists_interval_bivEval_primPart_eq_zero
    (translateBivPolynomialValue P L) htranslate
  intro lam hlam
  rw [bivEval_translateBivPolynomialValue]
  simpa using hroot lam hlam

/-- Weierstrass-normalized formal boundary for a selected real algebraic
branch. The translated primitive equation factors as a distinguished
polynomial times a unit, and the centered selected branch satisfies that
primitive equation on a punctured positive interval. -/
theorem exists_weierstrassFactorization_and_centered_primitive_branch
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    {w : ℝ → ℝ} (L : ℝ)
    (hroot : ∀ lam, 0 < lam → bivEval P lam (w lam) = 0) :
    ∃ (f : Polynomial (PowerSeries ℝ))
        (h : PowerSeries (PowerSeries ℝ)) (ρ : ℝ),
      (bivPolynomialToIteratedPowerSeries
        (translateBivPolynomialValue P L).primPart).IsWeierstrassFactorization
          f h ∧
      0 < ρ ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
        bivEval (translateBivPolynomialValue P L).primPart
          lam (w lam - L) = 0 := by
  obtain ⟨f, h, hfactor⟩ :=
    exists_weierstrassFactorization_translate_primPart P L
  obtain ⟨ρ, hρ, hbranch⟩ :=
    exists_interval_bivEval_translate_primPart_eq_zero P hP L hroot
  exact ⟨f, h, ρ, hfactor, hρ, hbranch⟩

/-- Local-interval form of the Weierstrass boundary. The returned interval is
contained in the interval on which the selected branch equation is known. -/
theorem exists_weierstrassFactorization_and_centered_primitive_branch_on_Ioo
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    {w : ℝ → ℝ} (L R : ℝ) (hR : 0 < R)
    (hroot : ∀ lam ∈ Set.Ioo (0 : ℝ) R,
      bivEval P lam (w lam) = 0) :
    ∃ (f : Polynomial (PowerSeries ℝ))
        (h : PowerSeries (PowerSeries ℝ)) (ρ : ℝ),
      (bivPolynomialToIteratedPowerSeries
        (translateBivPolynomialValue P L).primPart).IsWeierstrassFactorization
          f h ∧
      ρ ∈ Set.Ioc (0 : ℝ) R ∧
      ∀ lam ∈ Set.Ioo (0 : ℝ) ρ,
        bivEval (translateBivPolynomialValue P L).primPart
          lam (w lam - L) = 0 := by
  obtain ⟨f, h, hfactor⟩ :=
    exists_weierstrassFactorization_translate_primPart P L
  have htranslate :
      translateBivPolynomialValue P L ≠ 0 := by
    exact (Polynomial.comp_X_add_C_ne_zero_iff
      (p := P) (t := Polynomial.C L)).2 hP
  obtain ⟨δ, hδ, hcontent⟩ :=
    exists_interval_content_eval_ne_zero
      (translateBivPolynomialValue P L) htranslate
  let ρ := min δ R
  have hρ : ρ ∈ Set.Ioc (0 : ℝ) R :=
    ⟨lt_min hδ hR, min_le_right δ R⟩
  refine ⟨f, h, ρ, hfactor, hρ, ?_⟩
  intro lam hlam
  apply bivEval_primPart_eq_zero
  · exact hcontent lam
      ⟨hlam.1, hlam.2.trans_le (min_le_left δ R)⟩
  · rw [bivEval_translateBivPolynomialValue]
    simpa using hroot lam
      ⟨hlam.1, hlam.2.trans_le (min_le_right δ R)⟩

end Math
