import Math.AlgebraicSelection

set_option autoImplicit false
set_option linter.style.show false

noncomputable section

open Filter Set Topology

namespace Math
namespace GateGLocalRootIsolation

/--
A nonzero derivative in the value variable isolates a specialized root of a
bivariate polynomial.  This deliberately uses only finiteness of the roots
of the specialized univariate polynomial; no implicit-function theorem is
needed.
-/
theorem eventually_eq_of_bivEval_eq_zero
    (Q : Polynomial (Polynomial ℝ)) (lam₀ y₀ : ℝ)
    (hderiv : bivEval Q.derivative lam₀ y₀ ≠ 0) :
    ∀ᶠ y in 𝓝 y₀, bivEval Q lam₀ y = 0 → y = y₀ := by
  let p : Polynomial ℝ :=
    Q.map (Polynomial.evalRingHom lam₀)
  have hpderiv : p.derivative.eval y₀ ≠ 0 := by
    simpa [p, Polynomial.derivative_map, bivEval_eq_eval_map] using hderiv
  have hp : p ≠ 0 := by
    intro hpzero
    apply hpderiv
    simp [hpzero]
  let bad : Set ℝ := {y | p.IsRoot y} \ {y₀}
  have hbadFinite : bad.Finite := by
    exact
      (Polynomial.finite_setOf_isRoot hp).subset
        Set.sdiff_subset
  have hy₀ : y₀ ∈ badᶜ := by
    simp [bad]
  have hnhds : badᶜ ∈ 𝓝 y₀ :=
    hbadFinite.isClosed.isOpen_compl.mem_nhds hy₀
  filter_upwards [hnhds] with y hy hroot
  by_contra hne
  apply hy
  refine ⟨?_, hne⟩
  show p.eval y = 0
  simpa [p, bivEval_eq_eval_map] using hroot

/--
Pull root isolation back along a continuous objective.  On nearby points
with the same parameter value, a fixed separable algebraic relation makes
the objective value locally constant.
-/
theorem eventually_objective_eq_of_relation_of_parameter_eq
    {E : Type*} [TopologicalSpace E]
    (Q : Polynomial (Polynomial ℝ))
    (parameter objective : E → ℝ) (x : E)
    (hobjective : ContinuousAt objective x)
    (hderiv :
      bivEval Q.derivative (parameter x) (objective x) ≠ 0) :
    ∀ᶠ z in 𝓝 x,
      parameter z = parameter x →
      bivEval Q (parameter z) (objective z) = 0 →
      objective z = objective x := by
  have hisolated :=
    eventually_eq_of_bivEval_eq_zero
      Q (parameter x) (objective x) hderiv
  have hpullback : ∀ᶠ z in 𝓝 x, objective z ∈
      {y | bivEval Q (parameter x) y = 0 → y = objective x} := by
    exact hobjective.eventually hisolated
  filter_upwards [hpullback] with z hz hparameter hroot
  apply hz
  simpa [hparameter] using hroot

end GateGLocalRootIsolation
end Math
