import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Field

set_option autoImplicit false
set_option linter.unnecessarySimpa false

noncomputable section

open Algebra Set TensorProduct

namespace Math
namespace CurveSelection.KaehlerAlgebraicity

/-- The universal differential of a polynomial variable is nonzero. -/
theorem mvPolynomial_D_X_ne_zero
    (K : Type*) [Field K] :
    KaehlerDifferential.D K
        (MvPolynomial Unit K) (MvPolynomial.X ()) ≠ 0 := by
  intro h
  have hrepr :=
    congrArg
      (fun z =>
        (KaehlerDifferential.mvPolynomialBasis K Unit).repr z ())
      h
  have hone : (1 : MvPolynomial Unit K) = 0 := by
    simpa using hrepr
  exact one_ne_zero hone

/-- Localizing a one-variable polynomial algebra does not kill the
differential of its variable. -/
theorem fractionRing_D_X_ne_zero
    (K : Type*) [Field K] :
    KaehlerDifferential.D K
        (FractionRing (MvPolynomial Unit K))
        (algebraMap
          (MvPolynomial Unit K)
          (FractionRing (MvPolynomial Unit K))
          (MvPolynomial.X ())) ≠ 0 := by
  let A := MvPolynomial Unit K
  let F := FractionRing A
  let d :=
    KaehlerDifferential.D K A (MvPolynomial.X ())
  have hd : d ≠ 0 := by
    simpa [d, A] using mvPolynomial_D_X_ne_zero K
  have hmap :
      Function.Injective
        (KaehlerDifferential.map K K A F) := by
    rw [IsLocalizedModule.injective_iff_isRegular
      (nonZeroDivisors A)]
    intro c
    exact IsSMulRegular.of_ne_zero
      (mem_nonZeroDivisors_iff_ne_zero.mp c.property)
  intro hzero
  apply hd
  apply hmap
  simpa [d, A, F] using hzero

/-- If `S/K` is a purely transcendental one-generator field extension, the
generator has nonzero universal differential. -/
theorem adjoin_singleton_D_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (q : L) (hq : Transcendental K q) :
    let S := IntermediateField.adjoin K ({q} : Set L)
    KaehlerDifferential.D K S
      (⟨q, IntermediateField.mem_adjoin_simple_self K q⟩ : S) ≠ 0 := by
  dsimp only
  let x : Unit → L := fun _ => q
  have hx : AlgebraicIndependent K x := by
    exact (algebraicIndependent_unique_type_iff).2 hq
  have hrange : Set.range x = {q} := by
    ext y
    simp [x]
  let A := MvPolynomial Unit K
  let F := FractionRing A
  let S := IntermediateField.adjoin K ({q} : Set L)
  let e : F ≃ₐ[K] S :=
    hx.aevalEquivField.trans
      (IntermediateField.equivOfEq
        (congrArg (IntermediateField.adjoin K) hrange))
  letI : Algebra A S :=
    (e.toRingHom.comp (algebraMap A F)).toAlgebra
  let eA : F ≃ₐ[A] S :=
    { e with
      commutes' := fun a => rfl }
  letI : IsFractionRing A S :=
    IsFractionRing.of_algEquiv eA
  haveI : IsScalarTower K A S := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    change algebraMap K S k =
      e (algebraMap A F (MvPolynomial.C k))
    rw [MvPolynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply K A F]
    exact (e.commutes k).symm
  have hmap :
      Function.Injective
        (KaehlerDifferential.map K K A S) := by
    rw [IsLocalizedModule.injective_iff_isRegular
      (nonZeroDivisors A)]
    intro c
    exact IsSMulRegular.of_ne_zero
      (mem_nonZeroDivisors_iff_ne_zero.mp c.property)
  have hDX :
      KaehlerDifferential.D K S
          (algebraMap A S (MvPolynomial.X ())) ≠ 0 := by
    intro hzero
    apply mvPolynomial_D_X_ne_zero K
    have hbase :
        KaehlerDifferential.D K A (MvPolynomial.X ()) = 0 := by
      apply hmap
      simpa using hzero
    simpa [A] using hbase
  have hqS : q ∈ S := by
    exact IntermediateField.mem_adjoin_simple_self K q
  have halgebraMapX :
      algebraMap A S (MvPolynomial.X ()) =
        (⟨q, hqS⟩ : S) := by
    apply Subtype.ext
    change e (algebraMap A F (MvPolynomial.X ())) = q
    simpa [e, A, F, S, x] using
      hx.aevalEquivField_algebraMap_apply_coe
        (MvPolynomial.X ())
  simpa [halgebraMapX] using hDX

/-- In an essentially finite-type extension of fields over a perfect base,
the kernel of the universal derivation is exactly the relative algebraic
closure of the base field. -/
theorem isAlgebraic_of_kaehlerDifferential_eq_zero
    {K L : Type*} [Field K] [Field L]
    [CharZero K] [Algebra K L]
    [Algebra.EssFiniteType K L]
    (q : L)
    (hq :
      KaehlerDifferential.D K L q = 0) :
    IsAlgebraic K q := by
  by_contra hqalg
  have htrans : Transcendental K q := hqalg
  let S := IntermediateField.adjoin K ({q} : Set L)
  let qS : S :=
    ⟨q, IntermediateField.mem_adjoin_simple_self K q⟩
  have hDqS :
      KaehlerDifferential.D K S qS ≠ 0 := by
    simpa [S, qS] using
      adjoin_singleton_D_ne_zero q htrans
  letI : Algebra S L := S.toSubalgebra.toAlgebra
  haveI : IsScalarTower K S L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.EssFiniteType S L :=
    Algebra.EssFiniteType.of_comp K S L
  letI : Algebra.FormallySmooth S L :=
    Algebra.FormallySmooth.of_perfectField
  have hbaseChange :
      Function.Injective
        (KaehlerDifferential.mapBaseChange K S L) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ :=
      (Algebra.H1Cotangent.exact_δ_mapBaseChange K S L z).mp hz
    rw [Subsingleton.elim w 0, map_zero]
  have htensor :
      Function.Injective
        (fun z : Ω[S⁄K] => (1 : L) ⊗ₜ[S] z) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective Ω[S⁄K]
  have hmap :
      Function.Injective
        (KaehlerDifferential.map K K S L) := by
    intro a b hab
    apply htensor
    apply hbaseChange
    simpa using hab
  apply hDqS
  apply hmap
  simpa [qS, S] using hq

end CurveSelection.KaehlerAlgebraicity
end Math
