import Math.CurveSelection.LexDifferential

noncomputable section

namespace Math
namespace CurveSelection.AmbientCriticalAlgebraicity

/--
A normalized polynomial critical equation makes the objective algebraic
even when it is witnessed in an arbitrary ambient field.

Only the finitely many point coordinates and multiplier coefficients are
needed: adjoining them gives an essentially finite-type intermediate field,
where the Kähler-differential criterion applies.
-/
theorem isAlgebraic_of_equations_and_normalCriticality_in_ambient
    {K H σ I : Type*}
    [Field K] [Field H] [CharZero K]
    [Algebra K H]
    [Finite σ] [Fintype I]
    (x : σ → H)
    (P : I → MvPolynomial σ K)
    (hzero :
      ∀ i,
        MvPolynomial.eval₂ (algebraMap K H) x (P i) = 0)
    (Q : MvPolynomial σ K)
    (Λ : I → H)
    (hcritical :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K H) x
            (MvPolynomial.pderiv k Q) =
          ∑ i : I,
            Λ i *
              MvPolynomial.eval₂ (algebraMap K H) x
                (MvPolynomial.pderiv k (P i))) :
    IsAlgebraic K
      (MvPolynomial.eval₂ (algebraMap K H) x Q) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let generator : σ ⊕ I → H :=
    Sum.elim x Λ
  let E : IntermediateField K H :=
    IntermediateField.adjoin K (Set.range generator)
  let xE : σ → E :=
    fun k =>
      ⟨x k,
        IntermediateField.subset_adjoin K
          (Set.range generator)
          ⟨Sum.inl k, rfl⟩⟩
  let ΛE : I → E :=
    fun i =>
      ⟨Λ i,
        IntermediateField.subset_adjoin K
          (Set.range generator)
          ⟨Sum.inr i, rfl⟩⟩
  letI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr
      (IntermediateField.fg_adjoin_of_finite
        (Set.finite_range generator))
  have heval :
      ∀ R : MvPolynomial σ K,
        E.val.toRingHom
            (MvPolynomial.eval₂ (algebraMap K E) xE R) =
          MvPolynomial.eval₂ (algebraMap K H) x R := by
    intro R
    calc
      E.val.toRingHom
          (MvPolynomial.eval₂ (algebraMap K E) xE R) =
        MvPolynomial.eval₂
          (E.val.toRingHom.comp (algebraMap K E))
          (E.val.toRingHom ∘ xE) R :=
            MvPolynomial.eval₂_comp_left
              E.val.toRingHom (algebraMap K E) xE R
      _ = MvPolynomial.eval₂ (algebraMap K H) x R := by
        congr
  have hzeroE :
      ∀ i,
        MvPolynomial.eval₂ (algebraMap K E) xE (P i) = 0 := by
    intro i
    apply E.val.injective
    rw [map_zero, heval]
    exact hzero i
  have hcriticalE :
      ∀ k,
        MvPolynomial.eval₂ (algebraMap K E) xE
            (MvPolynomial.pderiv k Q) =
          ∑ i : I,
            ΛE i *
              MvPolynomial.eval₂ (algebraMap K E) xE
                (MvPolynomial.pderiv k (P i)) := by
    intro k
    apply E.val.injective
    rw [heval, map_sum]
    simp_rw [map_mul, heval]
    change
      MvPolynomial.eval₂ (algebraMap K H) x
          (MvPolynomial.pderiv k Q) =
        ∑ i : I,
          Λ i *
            MvPolynomial.eval₂ (algebraMap K H) x
              (MvPolynomial.pderiv k (P i))
    exact hcritical k
  have hqE :
      IsAlgebraic K
        (MvPolynomial.eval₂ (algebraMap K E) xE Q) :=
    CurveSelection.LexDifferentialScratch.isAlgebraic_of_equations_and_normalCriticality
      xE P hzeroE Q ΛE hcriticalE
  have hqH :
      IsAlgebraic K
        (E.val
          (MvPolynomial.eval₂ (algebraMap K E) xE Q)) :=
    (isAlgebraic_algHom_iff E.val E.val.injective).mpr hqE
  change
    IsAlgebraic K
      (E.val.toRingHom
        (MvPolynomial.eval₂ (algebraMap K E) xE Q)) at hqH
  rw [heval] at hqH
  exact hqH

end CurveSelection.AmbientCriticalAlgebraicity
end Math
