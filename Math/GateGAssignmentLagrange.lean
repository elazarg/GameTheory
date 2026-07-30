import Math.GateGNormalLagrange
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

noncomputable section

open Set

namespace Math
namespace GateGAssignmentLagrange

/- The finite Pi type has both its algebraic/product-topology instances and
its finite-dimensional normed-space instances available.  Calculus must use
the latter consistently; these local high-priority aliases make that choice
definitionally stable throughout this file. -/
private abbrev assignmentAddCommGroup
    {σ : Type*} [Fintype σ] :
    AddCommGroup (σ → ℝ) :=
  Pi.normedAddCommGroup.toAddCommGroup

private abbrev assignmentModule
    {σ : Type*} [Fintype σ] :
    Module ℝ (σ → ℝ) :=
  Pi.normedSpace.toModule

private abbrev assignmentTopology
    {σ : Type*} [Fintype σ] :
    TopologicalSpace (σ → ℝ) :=
  (show PseudoMetricSpace (σ → ℝ) from
    inferInstance).toUniformSpace.toTopologicalSpace

private abbrev realAddCommGroup : AddCommGroup ℝ :=
  Real.normedAddCommGroup.toAddCommGroup

private abbrev realModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

attribute [local instance 10000] assignmentAddCommGroup
  assignmentModule assignmentTopology realAddCommGroup realModule

/-- Formal polynomial gradient on the ordinary finite assignment space
`σ → ℝ`, whose norm topology is the one used throughout the Gate G
sign-cell construction. -/
def evalGradient
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    (σ → ℝ) →L[ℝ] ℝ :=
  ∑ j : σ,
    MvPolynomial.eval x (MvPolynomial.pderiv j P) •
      (ContinuousLinearMap.proj j)

@[simp]
theorem evalGradient_apply
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x d : σ → ℝ) :
    evalGradient P x d =
      ∑ j : σ,
        MvPolynomial.eval x
          (MvPolynomial.pderiv j P) * d j := by
  simp [evalGradient]

@[simp]
theorem evalGradient_C
    {σ : Type*} [Fintype σ] (a : ℝ)
    (x : σ → ℝ) :
    evalGradient (MvPolynomial.C a) x = 0 := by
  ext d
  simp

@[simp]
theorem evalGradient_add
    {σ : Type*} [Fintype σ]
    (P Q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    evalGradient (P + Q) x =
      evalGradient P x + evalGradient Q x := by
  ext d
  simp only [evalGradient_apply, map_add, add_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

theorem evalGradient_mul_X
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (j : σ)
    (x : σ → ℝ) :
    evalGradient (P * MvPolynomial.X j) x =
      MvPolynomial.eval x P •
          (ContinuousLinearMap.proj j) +
        x j • evalGradient P x := by
  classical
  ext d
  simp only [evalGradient_apply,
    MvPolynomial.pderiv_mul, map_add, map_mul,
    MvPolynomial.eval_X, add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_proj]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, ContinuousLinearMap.proj_apply]
  have hfactor :
      (∑ i : σ,
          MvPolynomial.eval x (MvPolynomial.pderiv i P) *
            x j * d i) =
        x j *
          ∑ i : σ,
            MvPolynomial.eval x
                (MvPolynomial.pderiv i P) * d i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfactor]
  ring

/-- Strict Fréchet derivative of polynomial evaluation on ordinary finite
assignments. -/
theorem hasStrictFDerivAt_eval
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasStrictFDerivAt
      (fun y : σ → ℝ => MvPolynomial.eval y P)
      (evalGradient P x) x := by
  unfold assignmentAddCommGroup assignmentModule
    assignmentTopology realAddCommGroup realModule
  classical
  let e : EuclideanSpace ℝ σ ≃L[ℝ] (σ → ℝ) :=
    EuclideanSpace.equiv σ ℝ
  have hEuclidean :=
    GateGNormalLagrangeScratch.hasStrictFDerivAt_eval
      P (e.symm x)
  have hcomp :=
    hEuclidean.comp x e.symm.hasStrictFDerivAt
  convert hcomp using 1
  · funext y
    rfl
  · ext d
    simp only [evalGradient_apply,
      GateGNormalLagrangeScratch.evalGradient_apply,
      ContinuousLinearMap.comp_apply]
    rfl

@[simp]
theorem evalGradient_single
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (k : σ) :
    evalGradient P x (Pi.single k 1) =
      MvPolynomial.eval x
        (MvPolynomial.pderiv k P) := by
  simp only [evalGradient_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hne
    simp [Pi.single_apply, hne]
  · simp

/-- Normalized polynomial Lagrange multipliers directly on the assignment
type used by the square-lift construction. -/
theorem exists_permanentMultipliers_of_localExtrOn
    {σ I : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype I] {n : ℕ}
    (x : σ → ℝ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (hlocal :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun y : σ → ℝ =>
            MvPolynomial.eval y (Q j))
          {y |
            ∀ i : I,
              MvPolynomial.eval y (P i) =
                MvPolynomial.eval x (P i)}
          x)
    (hindependent :
      LinearIndependent ℝ
        (fun i : I => evalGradient (P i) x)) :
    ∃ Λ : Fin n → I → ℝ,
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x
                (MvPolynomial.pderiv k (P i)) := by
  classical
  have hstage :
      ∀ j : Fin n,
        ∃ c : I → ℝ,
          (∑ i : I, c i • evalGradient (P i) x) +
            evalGradient (Q j) x = 0 := by
    intro j
    exact
      Math.GateGNormalLagrangeScratch.IsLocalExtrOn.exists_normalMultipliers_of_hasStrictFDerivAt
        (hlocal j)
        (fun i => hasStrictFDerivAt_eval (P i) x)
        (hasStrictFDerivAt_eval (Q j) x)
        hindependent
  choose c hc using hstage
  refine ⟨fun j i => -c j i, ?_⟩
  intro j k
  have heval :=
    congrArg
      (fun f : (σ → ℝ) →L[ℝ] ℝ =>
        f (Pi.single k 1))
      (hc j)
  simp only [add_apply, zero_apply, sum_apply,
    smul_apply, smul_eq_mul, evalGradient_single] at heval
  have hneg :=
    eq_neg_of_add_eq_zero_right heval
  rw [hneg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => by
    rw [neg_mul]

end GateGAssignmentLagrange
end Math
