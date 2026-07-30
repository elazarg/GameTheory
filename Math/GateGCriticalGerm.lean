import Math.GateGGermComponent
import Math.GateGNormalLagrange
import Math.GateGLexDifferential

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace GateGCriticalGermScratch

open GateGGermComponentScratch
open GateGNormalLagrangeScratch
open GateGLexDifferentialScratch

/-- Original geometric coordinates together with normalized Lagrange
multiplier coordinates for all objectives and permanent equations. -/
abbrev CriticalVar (σ I : Type*) (n : ℕ) :=
  σ ⊕ (Fin n × I)

/-- Extend an original assignment by the chosen normalized multipliers. -/
def criticalAssignment
    {σ I : Type*} {n : ℕ}
    (x : σ → ℝ) (Λ : Fin n → I → ℝ) :
    CriticalVar σ I n → ℝ
  | Sum.inl k => x k
  | Sum.inr ji => Λ ji.1 ji.2

/-- Include a polynomial in the original geometric coordinates into the
larger polynomial ring which also contains multiplier coordinates. -/
def liftOriginalPolynomial
    {σ I : Type*} {n : ℕ}
    (P : MvPolynomial σ ℝ) :
    MvPolynomial (CriticalVar σ I n) ℝ :=
  MvPolynomial.rename Sum.inl P

@[simp]
theorem eval_liftOriginalPolynomial
    {σ I : Type*} {n : ℕ}
    (x : σ → ℝ) (Λ : Fin n → I → ℝ)
    (P : MvPolynomial σ ℝ) :
    MvPolynomial.eval (criticalAssignment x Λ)
        (liftOriginalPolynomial (I := I) (n := n) P) =
      MvPolynomial.eval x P := by
  rw [liftOriginalPolynomial, MvPolynomial.eval_rename]
  congr

/-- The polynomial recording one coordinate of one normalized Lagrange
gradient identity. -/
def permanentCriticalPolynomial
    {σ I : Type*} [Fintype I] {n : ℕ}
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (j : Fin n) (k : σ) :
    MvPolynomial (CriticalVar σ I n) ℝ :=
  liftOriginalPolynomial (I := I) (n := n)
      (MvPolynomial.pderiv k (Q j)) -
    ∑ i : I,
      MvPolynomial.X (Sum.inr (j, i)) *
        liftOriginalPolynomial (I := I) (n := n)
          (MvPolynomial.pderiv k (P i))

theorem eval_permanentCriticalPolynomial_eq_zero
    {σ I : Type*} [Fintype I] {n : ℕ}
    (x : σ → ℝ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (Λ : Fin n → I → ℝ)
    (hcritical :
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x
                (MvPolynomial.pderiv k (P i)))
    (j : Fin n) (k : σ) :
    MvPolynomial.eval (criticalAssignment x Λ)
        (permanentCriticalPolynomial P Q j k) = 0 := by
  classical
  simp only [permanentCriticalPolynomial, map_sub, map_sum,
    map_mul, MvPolynomial.eval_X, eval_liftOriginalPolynomial,
    criticalAssignment]
  exact sub_eq_zero.mpr (hcritical j k)

/-- Permanent equations and all normalized critical equations, collected
as one finite polynomial family. -/
def criticalEquation
    {σ I : Type*} [Fintype I] {n : ℕ}
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ) :
    I ⊕ (Fin n × σ) →
      MvPolynomial (CriticalVar σ I n) ℝ
  | Sum.inl i =>
      liftOriginalPolynomial (I := I) (n := n) (P i)
  | Sum.inr jk =>
      permanentCriticalPolynomial P Q jk.1 jk.2

theorem eval_criticalEquation_eq_zero
    {σ I : Type*} [Fintype I] {n : ℕ}
    (x : σ → ℝ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (Λ : Fin n → I → ℝ)
    (hzero :
      ∀ i : I, MvPolynomial.eval x (P i) = 0)
    (hcritical :
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x
                (MvPolynomial.pderiv k (P i)))
    (a : I ⊕ (Fin n × σ)) :
    MvPolynomial.eval (criticalAssignment x Λ)
        (criticalEquation P Q a) = 0 := by
  cases a with
  | inl i =>
      simpa [criticalEquation] using hzero i
  | inr jk =>
      exact
        eval_permanentCriticalPolynomial_eq_zero
          x P Q Λ hcritical jk.1 jk.2

/-- The selected real sequence, augmented with all of its normalized
Lagrange multipliers, determines a prime polynomial germ component.  Every
permanent and critical equation lies in that prime, and a strictly monotone
original parameter remains transcendental. -/
theorem exists_prime_criticalGermComponent
    {σ I : Type*} [Fintype I] {n : ℕ}
    (x : ℕ → (σ → ℝ))
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (Λ : ℕ → Fin n → I → ℝ)
    (parameter : σ)
    (hzero :
      ∀ m i, MvPolynomial.eval (x m) (P i) = 0)
    (hcritical :
      ∀ m (j : Fin n) (k : σ),
        MvPolynomial.eval (x m)
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ m j i *
              MvPolynomial.eval (x m)
                (MvPolynomial.pderiv k (P i)))
    (hanti : StrictAnti (fun m => x m parameter)) :
    let z : ℕ → (CriticalVar σ I n → ℝ) :=
      fun m => criticalAssignment (x m) (Λ m)
    ∃ J : Ideal
        (MvPolynomial (CriticalVar σ I n) ℝ),
      J.IsPrime ∧
      Ideal.span (Set.range (criticalEquation P Q)) ≤ J ∧
      (∀ p : Polynomial ℝ,
        Polynomial.aeval
            (MvPolynomial.X
              (Sum.inl parameter :
                CriticalVar σ I n)) p ∈ J ↔
          p = 0) ∧
      (∀ R : MvPolynomial (CriticalVar σ I n) ℝ,
        R ∈ J ↔
          ∀ᶠ m in
              (sequenceUltrafilter : Filter ℕ),
            MvPolynomial.eval (z m) R = 0) := by
  dsimp only
  let z : ℕ → (CriticalVar σ I n → ℝ) :=
    fun m => criticalAssignment (x m) (Λ m)
  have hz :
      ∀ m a,
        MvPolynomial.eval (z m)
          (criticalEquation P Q a) = 0 := by
    intro m a
    exact
      eval_criticalEquation_eq_zero
        (x m) P Q (Λ m) (hzero m)
          (hcritical m) a
  have hparameter :
      StrictAnti
        (fun m =>
          z m
            (Sum.inl parameter :
              CriticalVar σ I n)) := by
    simpa [z, criticalAssignment] using hanti
  exact
    exists_prime_germComponent_preserving_strictParameter
      (criticalEquation P Q) z
      (Sum.inl parameter) hz hparameter

end GateGCriticalGermScratch
end Math
