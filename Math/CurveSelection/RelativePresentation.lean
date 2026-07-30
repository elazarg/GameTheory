/- Real polynomial charts attached to relative standard-smooth presentations. -/
import Math.CurveSelection.AssignmentLagrange
import Math.CurveSelection.GermChart
import Math.CurveSelection.RelativeSmoothGerm
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Math
namespace CurveSelection.RelativePresentation

open CurveSelection.AssignmentLagrange

/--
Every common zero of the relations of a presentation defines a ring map
out of the presented algebra.  This is the algebraic reason that the real
presentation chart lies in the zero locus of every equation true in the
prime quotient, not merely of a chosen generating family.
-/
def presentationPointRingHom
    {R S T ι κ : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S]
    (P : Algebra.Presentation R S ι κ)
    (f : R →+* T) (z : ι → T)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂ f z (P.relation j) = 0) :
    S →+* T := by
  let ev : MvPolynomial ι R →+* T :=
    MvPolynomial.eval₂Hom f z
  have hker : P.ker ≤ RingHom.ker ev := by
    rw [← P.span_range_relation_eq_ker,
      Ideal.span_le]
    intro Q hQ
    obtain ⟨j, rfl⟩ := hQ
    exact RingHom.mem_ker.mpr (hrelation j)
  let quotientHom : P.Quotient →+* T :=
    Ideal.Quotient.lift P.ker ev hker
  exact
    quotientHom.comp
      P.quotientEquiv.symm.toRingHom

@[simp]
theorem presentationPointRingHom_apply
    {R S T ι κ : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S]
    (P : Algebra.Presentation R S ι κ)
    (f : R →+* T) (z : ι → T)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂ f z (P.relation j) = 0)
    (s : S) :
    presentationPointRingHom P f z hrelation s =
      MvPolynomial.eval₂ f z (P.σ s) := by
  simp [presentationPointRingHom]

theorem eval₂_eq_zero_of_mem_presentationKer
    {R S T ι κ : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S]
    (P : Algebra.Presentation R S ι κ)
    (f : R →+* T) (z : ι → T)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂ f z (P.relation j) = 0)
    {Q : MvPolynomial ι R} (hQ : Q ∈ P.ker) :
    MvPolynomial.eval₂ f z Q = 0 := by
  have hspan :
      Ideal.span (Set.range P.relation) ≤
        RingHom.ker (MvPolynomial.eval₂Hom f z) := by
    rw [Ideal.span_le]
    intro A hA
    obtain ⟨j, rfl⟩ := hA
    exact RingHom.mem_ker.mpr (hrelation j)
  exact
    RingHom.mem_ker.mp
      (hspan (P.span_range_relation_eq_ker ▸ hQ))

@[simp]
theorem presentationPointRingHom_val
    {R S T ι κ : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S]
    (P : Algebra.Presentation R S ι κ)
    (f : R →+* T) (z : ι → T)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂ f z (P.relation j) = 0)
    (i : ι) :
    presentationPointRingHom P f z hrelation (P.val i) =
      z i := by
  rw [presentationPointRingHom_apply]
  have hmem :
      P.σ (P.val i) - MvPolynomial.X i ∈ P.ker := by
    rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    simp
  have hzero :=
    eval₂_eq_zero_of_mem_presentationKer
      P f z hrelation hmem
  apply sub_eq_zero.mp
  simpa only [MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_X] using hzero

@[simp]
theorem presentationPointRingHom_algebraMap
    {R S T ι κ : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S]
    (P : Algebra.Presentation R S ι κ)
    (f : R →+* T) (z : ι → T)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂ f z (P.relation j) = 0)
    (r : R) :
    presentationPointRingHom P f z hrelation
        (algebraMap R S r) =
      f r := by
  rw [presentationPointRingHom_apply]
  have hmem :
      P.σ (algebraMap R S r) -
          MvPolynomial.C r ∈ P.ker := by
    rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    simp
  have hzero :=
    eval₂_eq_zero_of_mem_presentationKer
      P f z hrelation hmem
  apply sub_eq_zero.mp
  simpa only [MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_C] using hzero

/-- Specialize the parameter coefficients of an `ℝ[t]`-polynomial at one
real value. -/
def specializeParameterPolynomial
    {ι : Type*} (t : ℝ) :
    MvPolynomial ι (Polynomial ℝ) →+*
      MvPolynomial ι ℝ :=
  MvPolynomial.map (Polynomial.evalRingHom t)

@[simp]
theorem eval_specializeParameterPolynomial
    {ι : Type*}
    (P : MvPolynomial ι (Polynomial ℝ))
    (t : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x
        (specializeParameterPolynomial t P) =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) x P := by
  simp [specializeParameterPolynomial]

@[simp]
theorem pderiv_specializeParameterPolynomial
    {ι : Type*} (i : ι)
    (P : MvPolynomial ι (Polynomial ℝ))
    (t : ℝ) :
    MvPolynomial.pderiv i
        (specializeParameterPolynomial t P) =
      specializeParameterPolynomial t
        (MvPolynomial.pderiv i P) := by
  exact MvPolynomial.pderiv_map

/-- Evaluate chosen presentation representatives of a family of elements.
At a common relation zero this is the corresponding real point of the
presented algebra. -/
def presentationSectionMap
    {S ι κ ν : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S) :
    (ι → ℝ) → (ν → ℝ) :=
  fun z k =>
    MvPolynomial.eval z
      (specializeParameterPolynomial t
        (P.σ (coordinate k)))

theorem continuous_presentationSectionMap
    {S ι κ ν : Type*}
    [CommRing S] [Algebra (Polynomial ℝ) S]
    [Fintype ι]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S) :
    Continuous (presentationSectionMap P t coordinate) := by
  rw [continuous_pi_iff]
  intro k
  exact
    MvPolynomial.continuous_eval
      (specializeParameterPolynomial t
        (P.σ (coordinate k)))

/--
Every polynomial identity among chosen elements of the presented algebra
holds at every real zero of the presentation relations after specializing
the parameter.
-/
theorem eval_presentationSectionMap_eq_zero
    {S ι κ ν : Type*}
    [CommRing S]
    [Algebra ℝ S]
    [Algebra (Polynomial ℝ) S]
    [IsScalarTower ℝ (Polynomial ℝ) S]
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
    (Q : MvPolynomial ν ℝ)
    (hQ :
      MvPolynomial.eval₂
        (algebraMap ℝ S) coordinate Q = 0) :
    MvPolynomial.eval
        (presentationSectionMap P t coordinate z) Q = 0 := by
  let ψ : S →+* ℝ :=
    presentationPointRingHom
      P (Polynomial.evalRingHom t) z hrelation
  have hψbase :
      ψ.comp (algebraMap ℝ S) = RingHom.id ℝ := by
    ext r
    change ψ (algebraMap ℝ S r) = r
    rw [IsScalarTower.algebraMap_apply
      ℝ (Polynomial ℝ) S]
    rw [presentationPointRingHom_algebraMap]
    simp
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
    MvPolynomial.eval
        (presentationSectionMap P t coordinate z) Q =
      ψ
        (MvPolynomial.eval₂
          (algebraMap ℝ S) coordinate Q) := by
            rw [MvPolynomial.hom_eval₂]
            simp only [hψbase, RingHom.id_apply,
              hψcoordinate, MvPolynomial.eval₂_id]
    _ = 0 := by rw [hQ, map_zero]

/--
Evaluation of a real polynomial in chosen elements of the presented algebra
commutes with the real point of any specialized presentation fiber.
-/
theorem eval_presentationSectionMap_eq_rep
    {S ι κ ν : Type*}
    [CommRing S]
    [Algebra ℝ S]
    [Algebra (Polynomial ℝ) S]
    [IsScalarTower ℝ (Polynomial ℝ) S]
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
    (Q : MvPolynomial ν ℝ) (s : S)
    (hQ :
      MvPolynomial.eval₂
        (algebraMap ℝ S) coordinate Q = s) :
    MvPolynomial.eval
        (presentationSectionMap P t coordinate z) Q =
      MvPolynomial.eval z
        (specializeParameterPolynomial t (P.σ s)) := by
  let ψ : S →+* ℝ :=
    presentationPointRingHom
      P (Polynomial.evalRingHom t) z hrelation
  have hψbase :
      ψ.comp (algebraMap ℝ S) = RingHom.id ℝ := by
    ext r
    change ψ (algebraMap ℝ S r) = r
    rw [IsScalarTower.algebraMap_apply
      ℝ (Polynomial ℝ) S]
    rw [presentationPointRingHom_algebraMap]
    simp
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
    MvPolynomial.eval
        (presentationSectionMap P t coordinate z) Q =
      ψ
        (MvPolynomial.eval₂
          (algebraMap ℝ S) coordinate Q) := by
            rw [MvPolynomial.hom_eval₂]
            simp only [hψbase, hψcoordinate,
              MvPolynomial.eval₂_id]
    _ = ψ s := by rw [hQ]
    _ =
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) z
          (P.σ s) := by
            exact
              presentationPointRingHom_apply
                P (Polynomial.evalRingHom t) z
                hrelation s
    _ =
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ s)) := by
              exact
                (eval_specializeParameterPolynomial
                  (P.σ s) t z).symm

/-- The whole specialized presentation fiber maps into the real zero locus
of any family of equations already zero in the presented algebra. -/
theorem presentationSectionMap_mem_zeroLocus
    {S ι κ ν E : Type*}
    [CommRing S]
    [Algebra ℝ S]
    [Algebra (Polynomial ℝ) S]
    [IsScalarTower ℝ (Polynomial ℝ) S]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation : E → MvPolynomial ν ℝ)
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap ℝ S) coordinate
          (equation e) = 0)
    {z : ι → ℝ}
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) z
          (P.relation j) = 0) :
    presentationSectionMap P t coordinate z ∈
      {w | ∀ e : E,
        MvPolynomial.eval w (equation e) = 0} := by
  intro e
  exact
    eval_presentationSectionMap_eq_zero
      P t coordinate z hrelation
      (equation e) (hzero e)

/--
A local maximum on a polynomial zero locus pulls back to the specialized
fiber of any presentation of the coordinate algebra.  The objective is
rewritten as the chosen presentation representative of its value in the
algebra, so the conclusion is immediately usable by the presentation
Lagrange theorem below.
-/
theorem isLocalMaxOn_presentationFiber
    {S ι κ ν E : Type*}
    [CommRing S]
    [Algebra ℝ S]
    [Algebra (Polynomial ℝ) S]
    [IsScalarTower ℝ (Polynomial ℝ) S]
    [Fintype ι]
    (P :
      Algebra.Presentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation : E → MvPolynomial ν ℝ)
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap ℝ S) coordinate
          (equation e) = 0)
    (objective : MvPolynomial ν ℝ)
    (objectiveValue : S)
    (hobjective :
      MvPolynomial.eval₂
        (algebraMap ℝ S) coordinate
        objective = objectiveValue)
    (x : ι → ℝ) (y : ν → ℝ)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) x
          (P.relation j) = 0)
    (hsection :
      presentationSectionMap P t coordinate x = y)
    (hlocal :
      IsLocalMaxOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval w objective)
        {w | ∀ e : E,
          MvPolynomial.eval w (equation e) = 0}
        y) :
    IsLocalMaxOn
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
    {w | ∀ e : E,
      MvPolynomial.eval w (equation e) = 0}
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
      presentationSectionMap_mem_zeroLocus
        P t coordinate equation hzero
        (hrelation_of_mem z hz)
  have hlocalAt :
      IsLocalMaxOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval w objective)
        zeroLocus
        (presentationSectionMap P t coordinate x) := by
    simpa [zeroLocus, hsection] using hlocal
  have hpull :
      IsLocalMaxOn
        ((fun w : ν → ℝ =>
            MvPolynomial.eval w objective) ∘
          presentationSectionMap P t coordinate)
        fiber x :=
    hlocalAt.comp_continuousOn
      hmaps
      (continuous_presentationSectionMap
        P t coordinate).continuousOn
      hxmem
  have heq :
      ((fun z : ι → ℝ =>
          MvPolynomial.eval
            (presentationSectionMap
              P t coordinate z) objective) :
        (ι → ℝ) → ℝ) =ᶠ[nhdsWithin x fiber]
        (fun z : ι → ℝ =>
          MvPolynomial.eval z
            (specializeParameterPolynomial t
              (P.σ objectiveValue))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact
      eval_presentationSectionMap_eq_rep
        P t coordinate z
        (hrelation_of_mem z hz)
        objective objectiveValue hobjective
  change
    IsLocalMaxOn
      (fun z : ι → ℝ =>
        MvPolynomial.eval z
          (specializeParameterPolynomial t
            (P.σ objectiveValue)))
      fiber x
  exact hpull.congr heq hxmem

/-- Flatten a polynomial in variables `ι` with coefficients in `ℝ[t]` to
one real multivariate polynomial.  The new `none` coordinate is `t`, while
`some i` is the old variable `i`. -/
def flattenParameterPolynomial
    {ι : Type*} :
    MvPolynomial ι (Polynomial ℝ) →ₐ[ℝ]
      MvPolynomial (Option ι) ℝ :=
  (MvPolynomial.optionEquivRight ℝ ι).symm

@[simp]
theorem flattenParameterPolynomial_X
    {ι : Type*} (i : ι) :
    flattenParameterPolynomial
        (MvPolynomial.X i :
          MvPolynomial ι (Polynomial ℝ)) =
      MvPolynomial.X (some i) := by
  apply (MvPolynomial.optionEquivRight ℝ ι).injective
  simp [flattenParameterPolynomial]

@[simp]
theorem flattenParameterPolynomial_C
    {ι : Type*} (p : Polynomial ℝ) :
    flattenParameterPolynomial
        (MvPolynomial.C p :
          MvPolynomial ι (Polynomial ℝ)) =
      Polynomial.toMvPolynomial none p := by
  apply (MvPolynomial.optionEquivRight ℝ ι).injective
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [
        flattenParameterPolynomial]

@[simp]
theorem eval_flattenParameterPolynomial
    {ι : Type*}
    (P : MvPolynomial ι (Polynomial ℝ))
    (t : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval (fun o => o.elim t x)
        (flattenParameterPolynomial P) =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) x P := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      simp
  | add P Q hP hQ =>
      simp [hP, hQ]
  | mul_X P i hP =>
      simp [hP]

@[simp]
theorem pderiv_some_flattenParameterPolynomial
    {ι : Type*} (i : ι)
    (P : MvPolynomial ι (Polynomial ℝ)) :
    MvPolynomial.pderiv (some i)
        (flattenParameterPolynomial P) =
      flattenParameterPolynomial
        (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C p =>
      rw [flattenParameterPolynomial_C]
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simp only [map_add, Derivation.map_add, hp, hq,
            add_zero]
      | monomial n a =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          simp
  | add P Q hP hQ =>
      simp [hP, hQ]
  | mul_X P j hP =>
      simp only [map_mul, flattenParameterPolynomial_X,
        Derivation.leibniz, hP, MvPolynomial.pderiv_X,
        Pi.single_apply]
      by_cases hij : j = i
      · subst j
        simp
      · have hji : i ≠ j := Ne.symm hij
        simp [hij, hji]

@[simp]
theorem eval_pderiv_some_flattenParameterPolynomial
    {ι : Type*} (i : ι)
    (P : MvPolynomial ι (Polynomial ℝ))
    (t : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval (fun o => o.elim t x)
        (MvPolynomial.pderiv (some i)
          (flattenParameterPolynomial P)) =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) x
        (MvPolynomial.pderiv i P) := by
  rw [pderiv_some_flattenParameterPolynomial,
    eval_flattenParameterPolynomial]

/-- The square Jacobian minor selected by a pre-submersive presentation,
evaluated at one real point of one fixed parameter fiber. -/
def evaluatedJacobiMatrix
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ) :
    Matrix κ κ ℝ :=
  fun i j =>
    MvPolynomial.eval₂
      (Polynomial.evalRingHom t) x
      (MvPolynomial.pderiv (P.map i)
        (P.relation j))

theorem evaluatedJacobiMatrix_eq_mapMatrix
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ) :
    evaluatedJacobiMatrix P t x =
      (MvPolynomial.eval₂Hom
        (Polynomial.evalRingHom t) x).mapMatrix
          P.jacobiMatrix := by
  ext i j
  simp [evaluatedJacobiMatrix,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]

theorem det_evaluatedJacobiMatrix
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ) :
    (evaluatedJacobiMatrix P t x).det =
      MvPolynomial.eval₂
        (Polynomial.evalRingHom t) x
        P.jacobiMatrix.det := by
  rw [evaluatedJacobiMatrix_eq_mapMatrix,
    ← RingHom.map_det]
  rfl

/--
Nonvanishing of the presentation's chosen Jacobian minor makes the complete
real gradients of its relations linearly independent.  No choice of
Euclidean coordinates is involved: restriction to the pivot coordinates
already gives the invertible square matrix.
-/
theorem linearIndependent_evalGradient_specialize_relations
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ)
    (hdet :
      (evaluatedJacobiMatrix P t x).det ≠ 0) :
    LinearIndependent ℝ
      (fun j : κ =>
        evalGradient
          (specializeParameterPolynomial t
            (P.relation j)) x) := by
  classical
  have hcolumns :
      LinearIndependent ℝ
        (evaluatedJacobiMatrix P t x).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  rw [Fintype.linearIndependent_iff] at hcolumns ⊢
  intro c hc j
  apply hcolumns c
  · funext i
    have hsingle :
        ∀ j : κ,
          evalGradient
              (specializeParameterPolynomial t
                (P.relation j)) x
              (Pi.single (P.map i) 1) =
            MvPolynomial.eval₂
              (Polynomial.evalRingHom t) x
              (MvPolynomial.pderiv (P.map i)
                (P.relation j)) := by
      intro j
      rw [evalGradient_single,
        pderiv_specializeParameterPolynomial,
        eval_specializeParameterPolynomial]
    have hi :=
      congrArg
        (fun L : (ι → ℝ) →L[ℝ] ℝ =>
          L (Pi.single (P.map i) 1))
        hc
    simpa only [Finset.sum_apply, Pi.smul_apply,
      Pi.zero_apply, Matrix.col_apply, sum_apply,
      smul_apply, zero_apply, smul_eq_mul, hsingle,
      evaluatedJacobiMatrix] using hi

/--
Fixed-parameter normalized Lagrange multipliers for a submersive
presentation.  The result is stated in the original `ℝ[t]` polynomial
coordinates, ready to pass to the ultrafilter germ field.
-/
theorem exists_multipliers_of_localExtrOn_presentationFiber
    {S ι κ : Type*}
    [CommRing S]
    [Algebra (Polynomial ℝ) S]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (x : ι → ℝ)
    (Q : MvPolynomial ι (Polynomial ℝ))
    (hlocal :
      IsLocalExtrOn
        (fun z : ι → ℝ =>
          MvPolynomial.eval z
            (specializeParameterPolynomial t Q))
        {z |
          ∀ j : κ,
            MvPolynomial.eval z
                (specializeParameterPolynomial t
                  (P.relation j)) =
              MvPolynomial.eval x
                (specializeParameterPolynomial t
                  (P.relation j))}
        x)
    (hdet :
      (evaluatedJacobiMatrix P t x).det ≠ 0) :
    ∃ Λ : κ → ℝ,
      ∀ k : ι,
        MvPolynomial.eval₂
            (Polynomial.evalRingHom t) x
            (MvPolynomial.pderiv k Q) =
          ∑ j : κ,
            Λ j *
              MvPolynomial.eval₂
                (Polynomial.evalRingHom t) x
                (MvPolynomial.pderiv k
                  (P.relation j)) := by
  classical
  let relation : κ → MvPolynomial ι ℝ :=
    fun j =>
      specializeParameterPolynomial t (P.relation j)
  let objective : Fin 1 → MvPolynomial ι ℝ :=
    fun _ => specializeParameterPolynomial t Q
  have hlocal' :
      ∀ j : Fin 1,
        IsLocalExtrOn
          (fun z : ι → ℝ =>
            MvPolynomial.eval z (objective j))
          {z |
            ∀ i : κ,
              MvPolynomial.eval z (relation i) =
                MvPolynomial.eval x (relation i)}
          x := by
    intro j
    simpa [relation, objective] using hlocal
  have hindependent :
      LinearIndependent ℝ
        (fun j : κ => evalGradient (relation j) x) := by
    simpa [relation] using
      linearIndependent_evalGradient_specialize_relations
        P t x hdet
  obtain ⟨Λ, hΛ⟩ :=
    CurveSelection.AssignmentLagrange.exists_permanentMultipliers_of_localExtrOn
      x relation objective hlocal' hindependent
  refine ⟨Λ 0, ?_⟩
  intro k
  simpa [relation, objective] using hΛ 0 k

/--
One-shot relative-chart Lagrange theorem.  A local maximum of a polynomial
objective on the original permanent zero locus, together with an exact
regular real point of a presentation fiber, yields the normalized
presentation-coordinate critical identity.
-/
theorem exists_multipliers_of_localMaxOn_zeroLocus
    {S ι κ ν E : Type*}
    [CommRing S]
    [Algebra ℝ S]
    [Algebra (Polynomial ℝ) S]
    [IsScalarTower ℝ (Polynomial ℝ) S]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P :
      Algebra.PreSubmersivePresentation
        (Polynomial ℝ) S ι κ)
    (t : ℝ) (coordinate : ν → S)
    (equation : E → MvPolynomial ν ℝ)
    (hzero :
      ∀ e : E,
        MvPolynomial.eval₂
          (algebraMap ℝ S) coordinate
          (equation e) = 0)
    (objective : MvPolynomial ν ℝ)
    (objectiveValue : S)
    (hobjective :
      MvPolynomial.eval₂
        (algebraMap ℝ S) coordinate
        objective = objectiveValue)
    (x : ι → ℝ) (y : ν → ℝ)
    (hrelation :
      ∀ j : κ,
        MvPolynomial.eval₂
          (Polynomial.evalRingHom t) x
          (P.relation j) = 0)
    (hsection :
      presentationSectionMap
        P.toPresentation t coordinate x = y)
    (hlocal :
      IsLocalMaxOn
        (fun w : ν → ℝ =>
          MvPolynomial.eval w objective)
        {w | ∀ e : E,
          MvPolynomial.eval w (equation e) = 0}
        y)
    (hdet :
      (evaluatedJacobiMatrix P t x).det ≠ 0) :
    ∃ Λ : κ → ℝ,
      ∀ k : ι,
        MvPolynomial.eval₂
            (Polynomial.evalRingHom t) x
            (MvPolynomial.pderiv k
              (P.σ objectiveValue)) =
          ∑ j : κ,
            Λ j *
              MvPolynomial.eval₂
                (Polynomial.evalRingHom t) x
                (MvPolynomial.pderiv k
                  (P.relation j)) := by
  have hpull :
      IsLocalMaxOn
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
        x :=
    isLocalMaxOn_presentationFiber
      P.toPresentation t coordinate
      equation hzero objective objectiveValue
      hobjective x y hrelation hsection hlocal
  exact
    exists_multipliers_of_localExtrOn_presentationFiber
      P t x (P.σ objectiveValue)
      hpull.isExtr hdet

end CurveSelection.RelativePresentation
end Math
