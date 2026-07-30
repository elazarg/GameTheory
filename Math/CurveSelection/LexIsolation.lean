import Math.CurveSelection.LocalRootIsolation
import Math.CurveSelection.NormalLagrange

set_option autoImplicit false
set_option linter.unusedDecidableInType false

noncomputable section

open Filter Set Topology

namespace Math
namespace CurveSelection.LexIsolationScratch

open CurveSelection.LocalRootIsolation

/-- The level set of all objectives strictly preceding a lexicographic
stage, through the selected point. -/
def previousObjectiveLevelSet
    {E : Type*} {n : ℕ}
    (objective : Fin n → E → ℝ)
    (x : E) (j : Fin n) : Set E :=
  {z |
    ∀ l : {l : Fin n // l < j},
      objective l.1 z = objective l.1 x}

/-- A local extremum on a lexicographically restricted set is already a
local extremum on the base set if all preceding level conditions are
automatic near the selected point. -/
theorem isLocalExtrOn_of_eventually_previousObjective_eq
    {E : Type*} [TopologicalSpace E] {n : ℕ}
    (objective : Fin n → E → ℝ)
    (S : Set E) (x : E) (j : Fin n)
    (hlex :
      IsLocalExtrOn (objective j)
        (S ∩ previousObjectiveLevelSet objective x j) x)
    (hautomatic :
      ∀ l : {l : Fin n // l < j},
        ∀ᶠ z in 𝓝 x,
          z ∈ S →
            objective l.1 z = objective l.1 x) :
    IsLocalExtrOn (objective j) S x := by
  have hall :
      ∀ᶠ z in 𝓝 x,
        ∀ l : {l : Fin n // l < j},
          z ∈ S →
            objective l.1 z = objective l.1 x :=
    Filter.eventually_all.mpr hautomatic
  rcases hlex with hmin | hmax
  · left
    change
      ∀ᶠ z in
        𝓝[S ∩ previousObjectiveLevelSet objective x j] x,
        objective j x ≤ objective j z at hmin
    change
      ∀ᶠ z in 𝓝[S] x,
        objective j x ≤ objective j z
    rw [eventually_nhdsWithin_iff] at hmin ⊢
    filter_upwards [hmin, hall] with z hz hza hzS
    apply hz
    exact ⟨hzS, fun l => hza l hzS⟩
  · right
    change
      ∀ᶠ z in
        𝓝[S ∩ previousObjectiveLevelSet objective x j] x,
        objective j z ≤ objective j x at hmax
    change
      ∀ᶠ z in 𝓝[S] x,
        objective j z ≤ objective j x
    rw [eventually_nhdsWithin_iff] at hmax ⊢
    filter_upwards [hmax, hall] with z hz hza hzS
    apply hz
    exact ⟨hzS, fun l => hza l hzS⟩

/-- A separable bivariate relation makes an objective locally automatic on
a set on which the parameter is fixed and the relation holds. -/
theorem eventually_objective_eq_on_of_separableRelation
    {E : Type*} [TopologicalSpace E]
    (R : Polynomial (Polynomial ℝ))
    (parameter objective : E → ℝ)
    (S : Set E) (x : E)
    (hobjective : ContinuousAt objective x)
    (hparameter :
      ∀ z ∈ S, parameter z = parameter x)
    (hrelation :
      ∀ z ∈ S,
        bivEval R
          (parameter z) (objective z) = 0)
    (hderiv :
      bivEval R.derivative
        (parameter x) (objective x) ≠ 0) :
    ∀ᶠ z in 𝓝 x,
      z ∈ S → objective z = objective x := by
  have hisolated :=
    eventually_objective_eq_of_relation_of_parameter_eq
      R parameter objective x hobjective hderiv
  filter_upwards [hisolated] with z hz hzS
  exact hz (hparameter z hzS) (hrelation z hzS)

/-- Valid lexicographic induction step.  Separable relations for all earlier
objectives make their level conditions locally redundant, so the current
lexicographic extremum is an extremum on the unchanged smooth base fiber.
This is the form that avoids the false independence claim for the gradients
of earlier objectives. -/
theorem isLocalExtrOn_base_of_separablePreviousRelations
    {E : Type*} [TopologicalSpace E] {n : ℕ}
    (relation : Fin n → Polynomial (Polynomial ℝ))
    (parameter : E → ℝ)
    (objective : Fin n → E → ℝ)
    (S : Set E) (x : E) (j : Fin n)
    (hobjective :
      ∀ l : Fin n, ContinuousAt (objective l) x)
    (hparameter :
      ∀ z ∈ S, parameter z = parameter x)
    (hrelation :
      ∀ l : Fin n, ∀ z ∈ S,
        bivEval (relation l)
          (parameter z) (objective l z) = 0)
    (hderiv :
      ∀ l : {l : Fin n // l < j},
        bivEval
            (relation l.1).derivative
            (parameter x) (objective l.1 x) ≠ 0)
    (hlex :
      IsLocalExtrOn (objective j)
        (S ∩ previousObjectiveLevelSet objective x j) x) :
    IsLocalExtrOn (objective j) S x := by
  apply
    isLocalExtrOn_of_eventually_previousObjective_eq
      objective S x j hlex
  intro l
  exact
    eventually_objective_eq_on_of_separableRelation
      (relation l.1) parameter (objective l.1)
      S x (hobjective l.1) hparameter
      (hrelation l.1) (hderiv l)

/-- End-to-end regular lexicographic Lagrange step for polynomial data.
Fixed separable parameter relations make every preceding objective level
locally automatic; the current lexicographic extremum therefore lives on
the unchanged regular permanent fiber, where normalized Lagrange
multipliers apply. -/
theorem exists_permanentMultipliers_of_separableLexRelations
    {σ I : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype I] {n : ℕ}
    (x : EuclideanSpace ℝ σ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (relation : Fin n → Polynomial (Polynomial ℝ))
    (parameter : EuclideanSpace ℝ σ → ℝ)
    (hparameter :
      ∀ z,
        (∀ i : I,
          MvPolynomial.eval z.ofLp (P i) =
            MvPolynomial.eval x.ofLp (P i)) →
        parameter z = parameter x)
    (hrelation :
      ∀ l : Fin n, ∀ z,
        (∀ i : I,
          MvPolynomial.eval z.ofLp (P i) =
            MvPolynomial.eval x.ofLp (P i)) →
        bivEval (relation l) (parameter z)
          (MvPolynomial.eval z.ofLp (Q l)) = 0)
    (hderiv :
      ∀ l : Fin n,
        bivEval (relation l).derivative
          (parameter x)
          (MvPolynomial.eval x.ofLp (Q l)) ≠ 0)
    (hlex :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun z : EuclideanSpace ℝ σ =>
            MvPolynomial.eval z.ofLp (Q j))
          ({z |
              ∀ i : I,
                MvPolynomial.eval z.ofLp (P i) =
                  MvPolynomial.eval x.ofLp (P i)} ∩
            previousObjectiveLevelSet
              (fun l z =>
                MvPolynomial.eval z.ofLp (Q l))
              x j)
          x)
    (hindependent :
      LinearIndependent ℝ
        (fun i : I =>
          CurveSelection.NormalLagrangeScratch.evalGradient
            (P i) x)) :
    ∃ Λ : Fin n → I → ℝ,
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x.ofLp
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x.ofLp
                (MvPolynomial.pderiv k (P i)) := by
  let S : Set (EuclideanSpace ℝ σ) :=
    {z |
      ∀ i : I,
        MvPolynomial.eval z.ofLp (P i) =
          MvPolynomial.eval x.ofLp (P i)}
  have hcontinuous :
      ∀ l : Fin n,
        ContinuousAt
          (fun z : EuclideanSpace ℝ σ =>
            MvPolynomial.eval z.ofLp (Q l)) x := by
    intro l
    exact
      (CurveSelection.NormalLagrangeScratch.hasStrictFDerivAt_eval
        (Q l) x).continuousAt
  have hlocal :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun z : EuclideanSpace ℝ σ =>
            MvPolynomial.eval z.ofLp (Q j))
          S x := by
    intro j
    apply
      isLocalExtrOn_base_of_separablePreviousRelations
        relation parameter
          (fun l z =>
            MvPolynomial.eval z.ofLp (Q l))
        S x j hcontinuous
    · intro z hz
      exact hparameter z hz
    · intro l z hz
      exact hrelation l z hz
    · intro l
      exact hderiv l.1
    · exact hlex j
  exact
    Math.CurveSelection.NormalLagrangeScratch.exists_permanentMultipliers_of_localExtrOn
      x P Q hlocal hindependent

end CurveSelection.LexIsolationScratch
end Math
