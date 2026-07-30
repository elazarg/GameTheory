import Math.MultivariateElimination
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.NoetherNormalization

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGGermComponentScratch

/-- The free ultrafilter used to retain one coherent algebraic germ of a
sequence. -/
abbrev sequenceUltrafilter : Ultrafilter ℕ :=
  hyperfilter ℕ

/-- Constant real germs. -/
def germConstRingHom :
    ℝ →+* Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ :=
  (Filter.Germ.coeRingHom
    (sequenceUltrafilter : Filter ℕ)).comp
      (Pi.constRingHom ℕ ℝ)

local instance germAlgebra :
    Algebra ℝ (Filter.Germ
      (sequenceUltrafilter : Filter ℕ) ℝ) :=
  germConstRingHom.toAlgebra

/-- Evaluate a multivariate polynomial on a sequence and retain only its
germ along a free ultrafilter. -/
def sequenceGermEval
    {σ : Type*} (x : ℕ → (σ → ℝ)) :
    MvPolynomial σ ℝ →ₐ[ℝ]
      Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ :=
  MvPolynomial.aeval fun j =>
    ((fun n => x n j) :
      Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ)

theorem sequenceGermEval_apply
    {σ : Type*} (x : ℕ → (σ → ℝ))
    (P : MvPolynomial σ ℝ) :
    sequenceGermEval x P =
      ((fun n => MvPolynomial.eval (x n) P) :
        Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.C_eq_algebraMap,
        (sequenceGermEval x).commutes a]
      change
        ((fun _ : ℕ => a) :
          Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ) =
        ((fun n => MvPolynomial.eval (x n) (MvPolynomial.C a)) :
          Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ)
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun n => by simp
  | add P Q hP hQ =>
      rw [map_add, hP, hQ]
      rw [← Filter.Germ.coe_add]
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun n => by simp
  | mul_X P j hP =>
      rw [map_mul, hP]
      have hX :
          sequenceGermEval x (MvPolynomial.X j) =
            ((fun n => x n j) :
              Filter.Germ
                (sequenceUltrafilter : Filter ℕ) ℝ) := by
        simp [sequenceGermEval]
      rw [hX, ← Filter.Germ.coe_mul]
      apply Filter.Germ.coe_eq.mpr
      exact Eventually.of_forall fun n => by simp

/-- The prime ideal of polynomial identities satisfied by the selected
sequence along one free ultrafilter. -/
def sequenceGermIdeal
    {σ : Type*} (x : ℕ → (σ → ℝ)) :
    Ideal (MvPolynomial σ ℝ) :=
  RingHom.ker (sequenceGermEval x).toRingHom

theorem sequenceGermIdeal_isPrime
    {σ : Type*} (x : ℕ → (σ → ℝ)) :
    (sequenceGermIdeal x).IsPrime :=
  RingHom.ker_isPrime (sequenceGermEval x).toRingHom

theorem mem_sequenceGermIdeal_iff
    {σ : Type*} (x : ℕ → (σ → ℝ))
    (P : MvPolynomial σ ℝ) :
    P ∈ sequenceGermIdeal x ↔
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        MvPolynomial.eval (x n) P = 0 := by
  rw [sequenceGermIdeal, RingHom.mem_ker]
  change sequenceGermEval x P = 0 ↔ _
  rw [sequenceGermEval_apply]
  change
    (((fun n => MvPolynomial.eval (x n) P) :
      Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ) =
      ((fun _ : ℕ => (0 : ℝ)) :
        Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ)) ↔ _
  exact Filter.Germ.coe_eq

/-- Polynomial equations that hold at every selected point lie in the prime
germ ideal. -/
theorem span_range_le_sequenceGermIdeal
    {I σ : Type*}
    (P : I → MvPolynomial σ ℝ)
    (x : ℕ → (σ → ℝ))
    (hzero : ∀ n i, MvPolynomial.eval (x n) (P i) = 0) :
    Ideal.span (Set.range P) ≤ sequenceGermIdeal x := by
  rw [Ideal.span_le]
  rintro Q ⟨i, rfl⟩
  apply (mem_sequenceGermIdeal_iff x (P i)).mpr
  exact Eventually.of_forall fun n => hzero n i

/-- Evaluation of a univariate polynomial at the distinguished parameter
germ. -/
def parameterGermEval
    {σ : Type*} (x : ℕ → (σ → ℝ)) (parameter : σ) :
    Polynomial ℝ →ₐ[ℝ]
      Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ :=
  (sequenceGermEval x).comp
    (Polynomial.aeval (MvPolynomial.X parameter))

theorem parameterGermEval_apply
    {σ : Type*} (x : ℕ → (σ → ℝ)) (parameter : σ)
    (p : Polynomial ℝ) :
    parameterGermEval x parameter p =
      ((fun n => p.eval (x n parameter)) :
        Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ) := by
  rw [parameterGermEval, AlgHom.comp_apply,
    sequenceGermEval_apply]
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall fun n => by
    simpa only [MvPolynomial.aeval_eq_eval,
      Polynomial.coe_aeval_eq_eval,
      MvPolynomial.aeval_X] using
      (Polynomial.aeval_algHom_apply
        (MvPolynomial.aeval (x n))
        (MvPolynomial.X parameter) p).symm

/-- Distinct parameter values remain transcendental in the free-ultrafilter
germ field: a nonzero real polynomial has only finitely many roots, whereas
the ultrafilter contains no finite set. -/
theorem parameterGermEval_injective_of_injective
    {σ : Type*} (x : ℕ → (σ → ℝ)) (parameter : σ)
    (hinjective :
      Function.Injective (fun n => x n parameter)) :
    Function.Injective (parameterGermEval x parameter) := by
  intro p q hpq
  have hsub :
      parameterGermEval x parameter (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  by_contra hpne
  have hpoly_ne : p - q ≠ 0 := by
    exact sub_ne_zero.mpr hpne
  have hevent :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
        (p - q).eval (x n parameter) = 0 := by
    rw [parameterGermEval_apply] at hsub
    change
      (((fun n => (p - q).eval (x n parameter)) :
        Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ) =
        ((fun _ : ℕ => (0 : ℝ)) :
          Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ)) at hsub
    exact Filter.Germ.coe_eq.mp hsub
  have hfinite :
      {n : ℕ | (p - q).eval (x n parameter) = 0}.Finite := by
    have hroots :
        {r : ℝ | (p - q).IsRoot r}.Finite :=
      Polynomial.finite_setOf_isRoot hpoly_ne
    have heq :
        {n : ℕ | (p - q).eval (x n parameter) = 0} =
          (fun n => x n parameter) ⁻¹'
            {r : ℝ | (p - q).IsRoot r} := by
      ext n
      simp [Polynomial.IsRoot]
    rw [heq]
    exact hroots.preimage hinjective.injOn
  exact hfinite.notMem_hyperfilter hevent

theorem parameterGerm_transcendental_of_strictAnti
    {σ : Type*} (x : ℕ → (σ → ℝ)) (parameter : σ)
    (hanti : StrictAnti (fun n => x n parameter)) :
    Transcendental ℝ
      (((fun n => x n parameter) :
        Filter.Germ (sequenceUltrafilter : Filter ℕ) ℝ)) := by
  rw [transcendental_iff_injective]
  have hcoordinate :
      sequenceGermEval x (MvPolynomial.X parameter) =
        ((fun n => x n parameter) :
          Filter.Germ
            (sequenceUltrafilter : Filter ℕ) ℝ) := by
    simp [sequenceGermEval]
  rw [← hcoordinate, Polynomial.aeval_algHom]
  exact parameterGermEval_injective_of_injective
    x parameter hanti.injective

/-- No nonzero polynomial in the distinguished parameter belongs to the
prime germ ideal.  This is the quotient-free formulation that the parameter
remains transcendental on the selected irreducible germ component. -/
theorem aeval_X_mem_sequenceGermIdeal_iff_of_strictAnti
    {σ : Type*} (x : ℕ → (σ → ℝ)) (parameter : σ)
    (hanti : StrictAnti (fun n => x n parameter))
    (p : Polynomial ℝ) :
    Polynomial.aeval (MvPolynomial.X parameter) p ∈
        sequenceGermIdeal x ↔
      p = 0 := by
  rw [sequenceGermIdeal, RingHom.mem_ker]
  change parameterGermEval x parameter p = 0 ↔ p = 0
  constructor
  · intro hp
    apply parameterGermEval_injective_of_injective
      x parameter hanti.injective
    simpa using hp
  · rintro rfl
    exact map_zero _

/-- An unconditional algebraic component selected by a strict parameter
sequence.  It is prime, contains every equation holding along the sequence,
and its distinguished parameter is still transcendental.  Membership in the
component records exactly an identity holding eventually along the chosen
free ultrafilter. -/
theorem exists_prime_germComponent_preserving_strictParameter
    {I σ : Type*}
    (P : I → MvPolynomial σ ℝ)
    (x : ℕ → (σ → ℝ))
    (parameter : σ)
    (hzero : ∀ n i, MvPolynomial.eval (x n) (P i) = 0)
    (hanti : StrictAnti (fun n => x n parameter)) :
    ∃ J : Ideal (MvPolynomial σ ℝ),
      J.IsPrime ∧
      Ideal.span (Set.range P) ≤ J ∧
      (∀ p : Polynomial ℝ,
        Polynomial.aeval (MvPolynomial.X parameter) p ∈ J ↔
          p = 0) ∧
      (∀ Q : MvPolynomial σ ℝ,
        Q ∈ J ↔
          ∀ᶠ n in (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (x n) Q = 0) := by
  refine ⟨sequenceGermIdeal x,
    sequenceGermIdeal_isPrime x,
    span_range_le_sequenceGermIdeal P x hzero,
    ?_, mem_sequenceGermIdeal_iff x⟩
  exact fun p =>
    aeval_X_mem_sequenceGermIdeal_iff_of_strictAnti
      x parameter hanti p

end GateGGermComponentScratch
end Math
