/- Kähler-differential finiteness and recursive algebraicity for Gate G. -/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Unramified.Field
import Math.GateGKaehlerAlgebraicity

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false

noncomputable section

open Set

namespace Math
namespace GateGLexDifferentialScratch

/-- Algebraic chain rule for a derivation evaluated on a multivariate
polynomial. -/
theorem derivation_eval₂
    {K L M σ : Type*}
    [CommRing K] [CommRing L]
    [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M]
    [Fintype σ]
    (D : Derivation K L M)
    (x : σ → L)
    (P : MvPolynomial σ K) :
    D (MvPolynomial.eval₂ (algebraMap K L) x P) =
      ∑ j : σ,
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv j P) •
          D (x j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add, D.map_add, hP, hQ]
      simp only [map_add, MvPolynomial.eval₂_add,
        add_smul,
        Finset.sum_add_distrib]
  | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, D.leibniz, hP]
      simp only [MvPolynomial.pderiv_mul,
        MvPolynomial.eval₂_add,
        MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X,
        MvPolynomial.pderiv_X,
        Pi.single_apply, add_smul,
        Finset.sum_add_distrib]
      rw [Finset.smul_sum]
      rw [add_comm]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        simp [smul_smul, mul_comm]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro i hi hij
          simp [Ne.symm hij]
        · simp

/-- A coefficientwise linear combination of formal gradients becomes the
same linear combination after applying any derivation. -/
theorem derivation_eval₂_eq_sum_of_gradientCombination
    {K L M σ I : Type*}
    [CommRing K] [CommRing L]
    [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M]
    [Fintype σ] [Fintype I]
    (D : Derivation K L M)
    (x : σ → L)
    (Q : MvPolynomial σ K)
    (P : I → MvPolynomial σ K)
    (Λ : I → L)
    (hgradient :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv k Q) =
          ∑ i : I,
            Λ i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) :
    D (MvPolynomial.eval₂ (algebraMap K L) x Q) =
      ∑ i : I,
        Λ i •
          D (MvPolynomial.eval₂
            (algebraMap K L) x (P i)) := by
  rw [derivation_eval₂ D x Q]
  conv_lhs =>
    enter [2, k]
    rw [hgradient k]
  simp only [Finset.sum_smul, Finset.smul_sum,
    mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [derivation_eval₂ D x (P i)]
  rw [Finset.smul_sum]

/-- Two-family version, convenient for the triangular critical equations
created by lexicographic optimization. -/
theorem derivation_eval₂_eq_sum_add_sum_of_gradientCombination
    {K L M σ I J : Type*}
    [CommRing K] [CommRing L]
    [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M]
    [Fintype σ] [Fintype I] [Fintype J]
    (D : Derivation K L M)
    (x : σ → L)
    (Q : MvPolynomial σ K)
    (P : I → MvPolynomial σ K)
    (R : J → MvPolynomial σ K)
    (Λ : I → L) (Μ : J → L)
    (hgradient :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv k Q) =
          (∑ i : I,
            Λ i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) +
          ∑ j : J,
            Μ j *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (R j))) :
    D (MvPolynomial.eval₂ (algebraMap K L) x Q) =
      (∑ i : I,
        Λ i •
          D (MvPolynomial.eval₂
            (algebraMap K L) x (P i))) +
      ∑ j : J,
        Μ j •
          D (MvPolynomial.eval₂
            (algebraMap K L) x (R j)) := by
  let S : I ⊕ J → MvPolynomial σ K :=
    Sum.elim P R
  let C : I ⊕ J → L :=
    Sum.elim Λ Μ
  have hgradient' :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv k Q) =
          ∑ z : I ⊕ J,
            C z *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (S z)) := by
    intro k
    rw [hgradient k]
    simp [S, C]
  rw [derivation_eval₂_eq_sum_of_gradientCombination
    D x Q S C hgradient']
  simp [S, C]

/-- Passing from a domain to its fraction field changes algebra generators
into field generators. -/
theorem fieldAdjoin_mapped_generators_eq_top
    {K A L ι : Type*}
    [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L] [Algebra A L]
    [IsScalarTower K A L]
    [IsFractionRing A L]
    (x : ι → A)
    (hgenerate :
      Algebra.adjoin K (Set.range x) = ⊤) :
    IntermediateField.adjoin K
        (Set.range fun i => algebraMap A L (x i)) =
      ⊤ := by
  let T : IntermediateField K L :=
    IntermediateField.adjoin K
      (Set.range fun i => algebraMap A L (x i))
  have halgebraMap_mem :
      ∀ a : A, algebraMap A L a ∈ T := by
    intro a
    have ha :
        a ∈ Algebra.adjoin K (Set.range x) := by
      rw [hgenerate]
      trivial
    refine Algebra.adjoin_induction
      (R := K) (A := A) (x := a) ?_ ?_ ?_ ?_ ha
    · intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin
        K _ (Set.mem_range_self i)
    · intro c
      rw [← IsScalarTower.algebraMap_apply K A L]
      exact T.algebraMap_mem c
    · intro a b ha hb hma hmb
      simpa using T.add_mem hma hmb
    · intro a b ha hb hma hmb
      simpa using T.mul_mem hma hmb
  apply top_unique
  intro z hz
  obtain ⟨a, b, hb, hab⟩ :=
    IsFractionRing.div_surjective A z
  rw [← hab]
  exact T.div_mem
    (halgebraMap_mem a) (halgebraMap_mem b)

/-- A derivation of a field is zero if it vanishes on a family which
generates the field as a field.  The use of `IntermediateField.adjoin`,
rather than `Algebra.adjoin`, is important here because the function field
also contains inverses of regular functions. -/
theorem derivation_eq_zero_of_fieldAdjoin_eq_top
    {K L M ι : Type*}
    [Field K] [Field L]
    [AddCommGroup M]
    [Algebra K L]
    [Module L M] [Module K M]
    (x : ι → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (D : Derivation K L M)
    (hD : ∀ i, D (x i) = 0) :
    D = 0 := by
  ext z
  have hz :
      z ∈ IntermediateField.adjoin K (Set.range x) := by
    rw [hgenerate]
    trivial
  have hzD : D z = 0 := by
    refine IntermediateField.adjoin_induction
      (F := K) (E := L) (x := z) ?_ ?_ ?_ ?_ ?_ hz
    · intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact hD i
    · intro a
      exact D.map_algebraMap a
    · intro a b ha hb hDa hDb
      simp [hDa, hDb]
    · intro a ha hDa
      simp [D.leibniz_inv, hDa]
    · intro a b ha hb hDa hDb
      simp [D.leibniz, hDa, hDb]
  simpa using hzD

/-- If the universal relative differentials of field generators vanish,
then the entire Kähler-differential module vanishes. -/
theorem subsingleton_kaehlerDifferential_of_fieldGenerators
    {K L ι : Type*}
    [Field K] [Field L]
    [Algebra K L]
    (x : ι → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (hD :
      ∀ i,
        KaehlerDifferential.D K L (x i) = 0) :
    Subsingleton Ω[L⁄K] := by
  have hderivation :
      KaehlerDifferential.D K L = 0 :=
    derivation_eq_zero_of_fieldAdjoin_eq_top
      x hgenerate (KaehlerDifferential.D K L) hD
  have hspan :
      (⊤ : Submodule L Ω[L⁄K]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation]
    simp [hderivation]
  constructor
  intro a b
  have ha : a ∈ (⊥ : Submodule L Ω[L⁄K]) := by
    rw [← hspan]
    exact Submodule.mem_top
  have hb : b ∈ (⊥ : Submodule L Ω[L⁄K]) := by
    rw [← hspan]
    exact Submodule.mem_top
  have ha0 : a = 0 := by simpa using ha
  have hb0 : b = 0 := by simpa using hb
  exact ha0.trans hb0.symm

/-- **Lexicographic differential finiteness certificate.**

For an essentially finite-type function field, it is enough to prove that
the universal relative differential vanishes on any family of field
generators.  The extension is then module-finite over the parameter field.
This is the exact algebraic conclusion needed after successively taking
fiberwise extrema of all affine coordinates. -/
theorem moduleFinite_of_vanishingDifferentials_on_fieldGenerators
    {K L ι : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [Algebra.EssFiniteType K L]
    (x : ι → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (hD :
      ∀ i,
        KaehlerDifferential.D K L (x i) = 0) :
    Module.Finite K L := by
  letI : Algebra.FormallyUnramified K L :=
    ⟨subsingleton_kaehlerDifferential_of_fieldGenerators
      x hgenerate hD⟩
  exact Algebra.FormallyUnramified.finite_of_free K L

/-- Finite field generators automatically supply the essentially-finite-type
hypothesis, so the differential certificate alone implies finiteness. -/
theorem moduleFinite_of_vanishingDifferentials_on_finite_fieldGenerators
    {K L ι : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [Finite ι]
    (x : ι → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (hD :
      ∀ i,
        KaehlerDifferential.D K L (x i) = 0) :
    Module.Finite K L := by
  have hfg :
      (⊤ : IntermediateField K L).FG := by
    rw [← hgenerate]
    exact IntermediateField.fg_adjoin_of_finite
      (Set.finite_range x)
  letI : Algebra.EssFiniteType K L :=
    IntermediateField.fg_top_iff.mp hfg
  exact
    moduleFinite_of_vanishingDifferentials_on_fieldGenerators
      x hgenerate hD

/-- A convenient fraction-field form: if a finite family generates the
coordinate domain as an algebra and its images have zero relative
differential in the function field, then that function field is finite over
the parameter field. -/
theorem moduleFinite_fractionRing_of_vanishingDifferentials
    {K A L ι : Type*}
    [Field K] [CommRing A] [IsDomain A] [Field L]
    [Algebra K A] [Algebra K L] [Algebra A L]
    [IsScalarTower K A L]
    [IsFractionRing A L]
    [Finite ι]
    (x : ι → A)
    (hgenerate :
      Algebra.adjoin K (Set.range x) = ⊤)
    (hD :
      ∀ i,
        KaehlerDifferential.D K L
          (algebraMap A L (x i)) = 0) :
    Module.Finite K L := by
  exact
    moduleFinite_of_vanishingDifferentials_on_finite_fieldGenerators
      (fun i => algebraMap A L (x i))
      (fieldAdjoin_mapped_generators_eq_top x hgenerate)
      hD

/-- **Polynomial Lagrange/Jacobian finiteness certificate.**

Suppose `x` generates a finite-type function field, all equations `P i`
vanish at `x`, and the gradients of these equations span every coordinate
covector over the function field.  Then every relative derivation vanishes
on every coordinate, hence the function field is finite over the base
field.

The coefficients `Λ j i` are precisely normalized Lagrange multipliers.
Unlike a Fritz--John certificate, the coefficient of the objective
coordinate is fixed to one, so this statement has no abnormal branch. -/
theorem moduleFinite_of_equations_and_gradientSpanning
    {K L σ I : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [Fintype σ] [DecidableEq σ] [Fintype I]
    (x : σ → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (P : I → MvPolynomial σ K)
    (hzero :
      ∀ i,
        MvPolynomial.eval₂ (algebraMap K L) x (P i) = 0)
    (Λ : σ → I → L)
    (hspan :
      ∀ j k,
        (if k = j then 1 else 0 : L) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) :
    Module.Finite K L := by
  apply
    moduleFinite_of_vanishingDifferentials_on_finite_fieldGenerators
      x hgenerate
  intro j
  let D : Derivation K L Ω[L⁄K] :=
    KaehlerDifferential.D K L
  have hrelation :
      ∀ i : I,
        (∑ k : σ,
          MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i)) •
            D (x k)) = 0 := by
    intro i
    rw [← derivation_eval₂ D x (P i), hzero i]
    exact D.map_zero
  change D (x j) = 0
  calc
    D (x j) =
        ∑ k : σ,
          (if k = j then 1 else 0 : L) •
            D (x k) := by
      classical
      rw [Finset.sum_eq_single j]
      · simp
      · intro k hk hkj
        simp [hkj]
      · simp
    _ =
        ∑ k : σ,
          (∑ i : I,
            Λ j i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) •
            D (x k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hspan j k]
    _ =
        ∑ i : I,
          Λ j i •
            (∑ k : σ,
              MvPolynomial.eval₂ (algebraMap K L) x
                    (MvPolynomial.pderiv k (P i)) •
                D (x k)) := by
      simp_rw [Finset.sum_smul, Finset.smul_sum,
        mul_smul]
      rw [Finset.sum_comm]
    _ = 0 := by
      simp_rw [hrelation]
      simp

/-- **Triangular lexicographic criticality certificate.**

At stage `j`, the gradient of the current objective may use gradients of
the permanent equations and of all earlier objectives.  Induction kills
the earlier objective differentials.  If the objective list contains every
coordinate polynomial, the function field is finite over the base.

This is the algebraic shape produced by first maximizing the squared strict
slack product and then successively extremizing all coordinates on the
preceding level sets. -/
theorem moduleFinite_of_triangularLexCriticality
    {K L σ I : Type*} {n : ℕ}
    [Field K] [Field L]
    [Algebra K L]
    [Fintype σ] [Fintype I]
    (x : σ → L)
    (hgenerate :
      IntermediateField.adjoin K (Set.range x) = ⊤)
    (P : I → MvPolynomial σ K)
    (hzero :
      ∀ i,
        MvPolynomial.eval₂ (algebraMap K L) x (P i) = 0)
    (Q : Fin n → MvPolynomial σ K)
    (Λ : Fin n → I → L)
    (Μ :
      ∀ j : Fin n,
        {l : Fin n // l < j} → L)
    (hcritical :
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv k (Q j)) =
          (∑ i : I,
            Λ j i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) +
          ∑ l : {l : Fin n // l < j},
            Μ j l *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (Q l.1)))
    (objective : σ → Fin n)
    (hcoordinate :
      ∀ k, Q (objective k) = MvPolynomial.X k) :
    Module.Finite K L := by
  apply
    moduleFinite_of_vanishingDifferentials_on_finite_fieldGenerators
      x hgenerate
  let D : Derivation K L Ω[L⁄K] :=
    KaehlerDifferential.D K L
  have hP :
      ∀ i : I,
        D (MvPolynomial.eval₂
          (algebraMap K L) x (P i)) = 0 := by
    intro i
    rw [hzero i]
    exact D.map_zero
  have hQ :
      ∀ j : Fin n,
        D (MvPolynomial.eval₂
          (algebraMap K L) x (Q j)) = 0 := by
    intro j
    induction j using Fin.strong_induction_on with
    | h j ih =>
        rw [
          derivation_eval₂_eq_sum_add_sum_of_gradientCombination
            D x (Q j) P
              (fun l : {l : Fin n // l < j} => Q l.1)
              (Λ j) (Μ j) (hcritical j)]
        simp only [hP, smul_zero, Finset.sum_const_zero,
          zero_add]
        apply Finset.sum_eq_zero
        intro l hl
        rw [ih l.1 l.2]
        simp
  intro k
  have hk := hQ (objective k)
  rw [hcoordinate k, MvPolynomial.eval₂_X] at hk
  exact hk

/-- One normalized critical equation already makes the corresponding
objective algebraic over the parameter field.  This is the recursive
version used in lexicographic selection: after obtaining a separable
relation for this objective, local root isolation makes its level condition
automatic at the next stage. -/
theorem isAlgebraic_of_equations_and_normalCriticality
    {K L σ I : Type*}
    [Field K] [Field L] [CharZero K]
    [Algebra K L] [Algebra.EssFiniteType K L]
    [Fintype σ] [Fintype I]
    (x : σ → L)
    (P : I → MvPolynomial σ K)
    (hzero :
      ∀ i,
        MvPolynomial.eval₂ (algebraMap K L) x (P i) = 0)
    (Q : MvPolynomial σ K)
    (Λ : I → L)
    (hcritical :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K L) x
            (MvPolynomial.pderiv k Q) =
          ∑ i : I,
            Λ i *
              MvPolynomial.eval₂ (algebraMap K L) x
                (MvPolynomial.pderiv k (P i))) :
    IsAlgebraic K
      (MvPolynomial.eval₂ (algebraMap K L) x Q) := by
  let D : Derivation K L Ω[L⁄K] :=
    KaehlerDifferential.D K L
  have hP :
      ∀ i : I,
        D (MvPolynomial.eval₂
          (algebraMap K L) x (P i)) = 0 := by
    intro i
    rw [hzero i]
    exact D.map_zero
  have hQ :
      D (MvPolynomial.eval₂
        (algebraMap K L) x Q) = 0 := by
    rw [
      derivation_eval₂_eq_sum_of_gradientCombination
        D x Q P Λ hcritical]
    simp only [hP, smul_zero, Finset.sum_const_zero]
  exact
    Math.GateGKaehlerAlgebraicity.isAlgebraic_of_kaehlerDifferential_eq_zero
      (MvPolynomial.eval₂ (algebraMap K L) x Q)
      hQ

end GateGLexDifferentialScratch
end Math
