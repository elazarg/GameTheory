import Math.GateGAssignmentLagrange
import Math.GateGLexIsolation

set_option autoImplicit false

noncomputable section

open Set

namespace Math
namespace GateGAssignmentLexIsolation

open GateGLexIsolationScratch
open GateGLocalRootIsolation

/--
Assignment-space form of the valid lexicographic induction step.

Every earlier objective has a fixed separable relation over the parameter.
On a fixed-parameter fiber those objectives are therefore locally constant,
so the current lexicographic extremum is an extremum on the unchanged
regular polynomial fiber.  Normalized Lagrange multipliers can consequently
be taken only against the permanent equations.
-/
theorem exists_permanentMultipliers_of_separableLexRelations
    {σ I : Type*} [Fintype σ]
    [Fintype I] {n : ℕ}
    (x : σ → ℝ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (relation : Fin n → Polynomial (Polynomial ℝ))
    (parameter : (σ → ℝ) → ℝ)
    (hparameter :
      ∀ z,
        (∀ i : I,
          MvPolynomial.eval z (P i) =
            MvPolynomial.eval x (P i)) →
        parameter z = parameter x)
    (hrelation :
      ∀ l : Fin n, ∀ z,
        (∀ i : I,
          MvPolynomial.eval z (P i) =
            MvPolynomial.eval x (P i)) →
        bivEval (relation l) (parameter z)
          (MvPolynomial.eval z (Q l)) = 0)
    (hderiv :
      ∀ l : Fin n,
        bivEval (relation l).derivative
          (parameter x)
          (MvPolynomial.eval x (Q l)) ≠ 0)
    (hlex :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun z : σ → ℝ =>
            MvPolynomial.eval z (Q j))
          ({z |
              ∀ i : I,
                MvPolynomial.eval z (P i) =
                  MvPolynomial.eval x (P i)} ∩
            previousObjectiveLevelSet
              (fun l z =>
                MvPolynomial.eval z (Q l))
              x j)
          x)
    (hindependent :
      LinearIndependent ℝ
        (fun i : I =>
          GateGAssignmentLagrange.evalGradient
            (P i) x)) :
    ∃ Λ : Fin n → I → ℝ,
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x
                (MvPolynomial.pderiv k (P i)) := by
  classical
  let S : Set (σ → ℝ) :=
    {z |
      ∀ i : I,
        MvPolynomial.eval z (P i) =
          MvPolynomial.eval x (P i)}
  have hcontinuous :
      ∀ l : Fin n,
        ContinuousAt
          (fun z : σ → ℝ =>
            MvPolynomial.eval z (Q l)) x := by
    intro l
    exact
      (GateGAssignmentLagrange.hasStrictFDerivAt_eval
        (Q l) x).continuousAt
  have hlocal :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun z : σ → ℝ =>
            MvPolynomial.eval z (Q j))
          S x := by
    intro j
    apply
      isLocalExtrOn_base_of_separablePreviousRelations
        relation parameter
          (fun l z =>
            MvPolynomial.eval z (Q l))
        S x j hcontinuous
    · intro z hz
      exact hparameter z hz
    · intro l z hz
      exact hrelation l z hz
    · intro l
      exact hderiv l.1
    · exact hlex j
  exact
    GateGAssignmentLagrange.exists_permanentMultipliers_of_localExtrOn
      x P Q hlocal hindependent

end GateGAssignmentLexIsolation
end Math
