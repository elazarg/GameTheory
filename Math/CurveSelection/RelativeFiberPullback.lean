import Math.CurveSelection.RelativePresentation

noncomputable section

open Set

namespace Math
namespace CurveSelection.RelativeFiberPullback

open CurveSelection.RelativePresentation

/-- Evaluation of an `ℝ[t]`-polynomial commutes with every real point of a
specialized presentation fiber. -/
theorem eval₂_presentationSectionMap_eq_rep
    {S ι κ ν : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (z : ι → ℝ)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) z
          (P.relation j) = 0)
    (Q : MvPolynomial ν (Polynomial ℝ))
    (s : S)
    (hQ :
      MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ) S)
        coordinate Q = s) :
    MvPolynomial.eval₂
        (Polynomial.evalRingHom t)
        (presentationSectionMap P t coordinate z) Q =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) z
        (P.σ s) := by
  let ψ : S →+* ℝ :=
    presentationPointRingHom
      P (Polynomial.evalRingHom t) z hrelation
  have hψbase :
      ψ.comp (algebraMap (Polynomial ℝ) S) =
        Polynomial.evalRingHom t := by
    apply DFunLike.ext _ _
    intro p
    exact
      presentationPointRingHom_algebraMap
        P (Polynomial.evalRingHom t) z
        hrelation p
  have hψcoordinate :
      ∀ k : ν,
        ψ (coordinate k) =
          presentationSectionMap P t coordinate z k := by
    intro k
    rw [presentationPointRingHom_apply]
    exact
      (eval_specializeParameterPolynomial
        (P.σ (coordinate k)) t z).symm
  calc
    MvPolynomial.eval₂
        (Polynomial.evalRingHom t)
        (presentationSectionMap P t coordinate z) Q =
      ψ
        (MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ) S)
          coordinate Q) := by
            rw [MvPolynomial.hom_eval₂]
            simp only [hψbase, hψcoordinate]
    _ = ψ s := by rw [hQ]
    _ =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) z
        (P.σ s) :=
          presentationPointRingHom_apply
            P (Polynomial.evalRingHom t) z
            hrelation s

/-- Every specialized presentation fiber maps into the specialized zero
locus of every relative polynomial identity in the presented algebra. -/
theorem presentationSectionMap_mem_relativeZeroLocus
    {S ι κ ν E : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation :
      E → MvPolynomial ν (Polynomial ℝ))
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ) S)
          coordinate (equation e) = 0)
    {z : ι → ℝ}
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) z
          (P.relation j) = 0) :
    ∀ e : E,
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t)
        (presentationSectionMap P t coordinate z)
        (equation e) = 0 := by
  intro e
  rw [eval₂_presentationSectionMap_eq_rep
    P t coordinate z hrelation
    (equation e) 0 (hzero e)]
  rw [← presentationPointRingHom_apply
    P (Polynomial.evalRingHom t) z hrelation (0 : S)]
  exact map_zero _

/--
A local extremum on a specialized relative zero locus pulls back to the
regular presentation fiber.  This version treats the distinguished
parameter as a coefficient, which is the form needed for the fixed-radius
curve-selection optimization.
-/
theorem isLocalExtrOn_presentationFiber_relative
    {S ι κ ν E : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Finite ι]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation :
      E → MvPolynomial ν (Polynomial ℝ))
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap (Polynomial ℝ) S)
          coordinate (equation e) = 0)
    (objective :
      MvPolynomial ν (Polynomial ℝ))
    (objectiveValue : S)
    (hobjective :
      MvPolynomial.eval₂
        (algebraMap (Polynomial ℝ) S)
        coordinate objective = objectiveValue)
    (x : ι → ℝ) (y : ν → ℝ)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) x
          (P.relation j) = 0)
    (hsection :
      presentationSectionMap
        P t coordinate x = y)
    (hlocal :
      IsLocalExtrOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) w objective)
        {w |
          ∀ e : E,
            MvPolynomial.eval₂
              (Polynomial.evalRingHom t) w
              (equation e) = 0}
        y) :
    IsLocalExtrOn
      (fun z : ι → ℝ =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ objectiveValue)))
      {z |
        ∀ j : κ,
          MvPolynomial.eval z
              (specializeParameterPolynomial t
                (P.relation j)) =
            MvPolynomial.eval x
              (specializeParameterPolynomial t
                (P.relation j))}
      x := by
  letI : Fintype ι := Fintype.ofFinite ι
  let fiber : Set (ι → ℝ) :=
    {z |
      ∀ j : κ,
        MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.relation j)) =
          MvPolynomial.eval x
            (specializeParameterPolynomial t
              (P.relation j))}
  let zeroLocus : Set (ν → ℝ) :=
    {w |
      ∀ e : E,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) w
          (equation e) = 0}
  have hxmem : x ∈ fiber := by
    intro j
    rfl
  have hrelation_of_mem :
      ∀ z ∈ fiber,
        ∀ j : κ,
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) z
            (P.relation j) = 0 := by
    intro z hz j
    rw [← eval_specializeParameterPolynomial]
    exact
      (hz j).trans
        (by
          rw [eval_specializeParameterPolynomial]
          exact hrelation j)
  have hmaps :
      fiber ⊆
        presentationSectionMap P t coordinate ⁻¹'
          zeroLocus := by
    intro z hz
    exact
      presentationSectionMap_mem_relativeZeroLocus
        P t coordinate equation hzero
        (hrelation_of_mem z hz)
  have hlocalAt :
      IsLocalExtrOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t) w objective)
        zeroLocus
        (presentationSectionMap P t coordinate x) := by
    simpa [zeroLocus, hsection] using hlocal
  have hpull :
      IsLocalExtrOn
        ((fun w : ν → ℝ =>
            MvPolynomial.eval₂
              (Polynomial.evalRingHom t) w objective) ∘
          presentationSectionMap P t coordinate)
        fiber x :=
    hlocalAt.comp_continuousOn
      (presentationSectionMap P t coordinate)
      hmaps
      (continuous_presentationSectionMap
        P t coordinate).continuousOn
      hxmem
  have heq :
      ((fun z : ι → ℝ =>
          MvPolynomial.eval₂
            (Polynomial.evalRingHom t)
            (presentationSectionMap
              P t coordinate z) objective) :
        (ι → ℝ) → ℝ) =ᶠ[nhdsWithin x fiber]
        (fun z : ι → ℝ =>
          MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.σ objectiveValue))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [eval_specializeParameterPolynomial] using
      eval₂_presentationSectionMap_eq_rep
        P t coordinate z
        (hrelation_of_mem z hz)
        objective objectiveValue hobjective
  change
    IsLocalExtrOn
      (fun z : ι → ℝ =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ objectiveValue)))
      fiber x
  exact hpull.congr heq hxmem

end CurveSelection.RelativeFiberPullback
end Math
