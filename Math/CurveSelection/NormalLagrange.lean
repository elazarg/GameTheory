/- Normalized polynomial Lagrange multipliers for analytic curve selection. -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Set

namespace Math
namespace CurveSelection.NormalLagrangeScratch

/-- At a regular equality-constrained extremum the objective multiplier can
be normalized to one.  This is the form that excludes the abnormal
Fritz--John branch. -/
theorem IsLocalExtrOn.exists_normalMultiplier_of_hasStrictFDerivAt
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {φ : E → ℝ} {x₀ : E}
    {f' : E →L[ℝ] F} {φ' : StrongDual ℝ E}
    (hextr :
      IsLocalExtrOn φ {x | f x = f x₀} x₀)
    (hf' : HasStrictFDerivAt f f' x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀)
    (hsurj : Function.Surjective f') :
    ∃ Λ : Module.Dual ℝ F,
      ∀ x, Λ (f' x) + φ' x = 0 := by
  obtain ⟨Λ, Λ₀, hnonzero, heq⟩ :=
    hextr.exists_linear_map_of_hasStrictFDerivAt hf' hφ'
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro hΛ₀
    have hΛ : Λ = 0 := by
      ext y
      obtain ⟨x, rfl⟩ := hsurj y
      simpa [hΛ₀] using heq x
    exact hnonzero (Prod.ext hΛ hΛ₀)
  refine ⟨Λ₀⁻¹ • Λ, fun x => ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc
    Λ₀⁻¹ * Λ (f' x) + φ' x =
        Λ₀⁻¹ * (Λ (f' x) + Λ₀ * φ' x) := by
          field_simp
    _ = 0 := by
      have heqx :
          Λ (f' x) + Λ₀ * φ' x = 0 := by
        simpa only [smul_eq_mul] using heq x
      rw [heqx]
      simp

/-- Coordinate form of the regular Lagrange multiplier theorem.  Linear
independence of the constraint gradients rules out the abnormal branch and
normalizes the objective coefficient to one. -/
theorem IsLocalExtrOn.exists_normalMultipliers_of_hasStrictFDerivAt
    {E : Type*} {ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Fintype ι]
    {f : ι → E → ℝ}
    {φ : E → ℝ} {x₀ : E}
    {f' : ι → StrongDual ℝ E}
    {φ' : StrongDual ℝ E}
    (hextr :
      IsLocalExtrOn φ
        {x | ∀ i, f i x = f i x₀} x₀)
    (hf' : ∀ i,
      HasStrictFDerivAt (f i) (f' i) x₀)
    (hφ' : HasStrictFDerivAt φ φ' x₀)
    (hindependent : LinearIndependent ℝ f') :
    ∃ Λ : ι → ℝ,
      (∑ i, Λ i • f' i) + φ' = 0 := by
  obtain ⟨Λ, Λ₀, hnonzero, heq⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt
      hf' hφ'
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro hΛ₀
    have hsum :
        (∑ i, Λ i • f' i) = 0 := by
      simpa [hΛ₀] using heq
    have hΛ : Λ = 0 := by
      funext i
      exact
        (Fintype.linearIndependent_iff.mp
          hindependent Λ hsum i)
    exact hnonzero (Prod.ext hΛ hΛ₀)
  refine ⟨fun i => Λ₀⁻¹ * Λ i, ?_⟩
  calc
    (∑ i, (Λ₀⁻¹ * Λ i) • f' i) + φ' =
        Λ₀⁻¹ •
          ((∑ i, Λ i • f' i) + Λ₀ • φ') := by
      rw [smul_add, Finset.smul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [smul_smul]
      · rw [smul_smul]
        field_simp
        simp
    _ = 0 := by rw [heq]; simp

private abbrev euclideanAddCommGroup
    {σ : Type*} [Fintype σ] :
    AddCommGroup (EuclideanSpace ℝ σ) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : σ => ℝ)).toAddCommGroup

private abbrev euclideanModule
    {σ : Type*} [Fintype σ] :
    Module ℝ (EuclideanSpace ℝ σ) :=
  (PiLp.normedSpace 2 ℝ
    (fun _ : σ => ℝ)).toModule

private abbrev euclideanTopology
    {σ : Type*} [Fintype σ] :
    TopologicalSpace (EuclideanSpace ℝ σ) :=
  (show PseudoMetricSpace (EuclideanSpace ℝ σ) from
    inferInstance).toUniformSpace.toTopologicalSpace

private abbrev realAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toCommRing.toAddCommGroup

private abbrev realModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

attribute [local instance 10000] euclideanAddCommGroup
  euclideanModule euclideanTopology realAddCommGroup realModule

/-- Formal gradient of a multivariate polynomial on the finite-dimensional
coordinate space, expressed using its partial derivatives. -/
def evalGradient
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    EuclideanSpace ℝ σ →L[ℝ] ℝ :=
  ∑ j : σ,
    MvPolynomial.eval x.ofLp (MvPolynomial.pderiv j P) •
      (EuclideanSpace.proj (𝕜 := ℝ) j)

@[simp]
theorem evalGradient_apply
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ)
    (x d : EuclideanSpace ℝ σ) :
    evalGradient P x d =
      ∑ j : σ,
        MvPolynomial.eval x.ofLp
          (MvPolynomial.pderiv j P) * d.ofLp j := by
  simp [evalGradient]

@[simp]
theorem evalGradient_C
    {σ : Type*} [Fintype σ] (a : ℝ)
    (x : EuclideanSpace ℝ σ) :
    evalGradient (MvPolynomial.C a) x = 0 := by
  ext d
  simp

@[simp]
theorem evalGradient_add
    {σ : Type*} [Fintype σ]
    (P Q : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    evalGradient (P + Q) x =
      evalGradient P x + evalGradient Q x := by
  ext d
  simp only [evalGradient_apply, map_add, add_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

theorem evalGradient_mul_X
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (j : σ)
    (x : EuclideanSpace ℝ σ) :
    evalGradient (P * MvPolynomial.X j) x =
      MvPolynomial.eval x.ofLp P •
          (EuclideanSpace.proj (𝕜 := ℝ) j) +
        x.ofLp j • evalGradient P x := by
  classical
  ext d
  simp only [evalGradient_apply,
    MvPolynomial.pderiv_mul, map_add, map_mul,
    MvPolynomial.eval_X,
    add_apply, smul_apply, smul_eq_mul,
    EuclideanSpace.coe_proj]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  have hfactor :
      (∑ i : σ,
          MvPolynomial.eval x.ofLp (MvPolynomial.pderiv i P) *
            x.ofLp j * d.ofLp i) =
        x.ofLp j *
          ∑ i : σ,
            MvPolynomial.eval x.ofLp
                (MvPolynomial.pderiv i P) *
              d.ofLp i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfactor]
  ring

/-- Polynomial evaluation is strictly differentiable and its Fréchet
derivative is the formal gradient. -/
theorem hasStrictFDerivAt_eval
    {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) :
    HasStrictFDerivAt
      (fun y : EuclideanSpace ℝ σ =>
        MvPolynomial.eval y.ofLp P)
      (evalGradient P x) x := by
  unfold euclideanAddCommGroup euclideanModule
    euclideanTopology realAddCommGroup realModule
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      simpa only [MvPolynomial.eval_C, evalGradient_C] using
        (hasStrictFDerivAt_const (x := x) (c := a))
  | add P Q hP hQ =>
      have hadd := hP.add hQ
      rw [← evalGradient_add] at hadd
      convert hadd using 1
      · rfl
      · funext y
        simp
  | mul_X P j hP =>
      have hX :
          HasStrictFDerivAt
            (fun y : EuclideanSpace ℝ σ => y.ofLp j)
            (EuclideanSpace.proj (𝕜 := ℝ) j) x := by
        simpa only [EuclideanSpace.coe_proj] using
          (EuclideanSpace.proj (𝕜 := ℝ) j).hasStrictFDerivAt
      have hmul := hP.mul hX
      rw [← evalGradient_mul_X] at hmul
      convert hmul using 1
      funext y
      simp

@[simp]
theorem evalGradient_single
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ ℝ)
    (x : EuclideanSpace ℝ σ) (k : σ) :
    evalGradient P x (EuclideanSpace.single k 1) =
      MvPolynomial.eval x.ofLp
        (MvPolynomial.pderiv k P) := by
  simp [evalGradient_apply]

/-- Pointwise regularity at all stages of a lexicographic optimization
produces the triangular polynomial gradient identities used by the
algebraic finiteness argument.  Earlier objectives are included among the
equality constraints at each stage. -/
theorem exists_triangularMultipliers_of_lexCritical
    {σ I : Type*} [Fintype σ]
    [Fintype I] {n : ℕ}
    (x : EuclideanSpace ℝ σ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (hlocal :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun y : EuclideanSpace ℝ σ =>
            MvPolynomial.eval y.ofLp (Q j))
          {y |
            ∀ a : I ⊕ {l : Fin n // l < j},
              MvPolynomial.eval y.ofLp
                  (Sum.elim P
                    (fun l : {l : Fin n // l < j} =>
                      Q l.1) a) =
                MvPolynomial.eval x.ofLp
                  (Sum.elim P
                    (fun l : {l : Fin n // l < j} =>
                      Q l.1) a)}
          x)
    (hindependent :
      ∀ j : Fin n,
        LinearIndependent ℝ
          (fun a : I ⊕ {l : Fin n // l < j} =>
            evalGradient
              (Sum.elim P
                (fun l : {l : Fin n // l < j} =>
                  Q l.1) a) x)) :
    ∃ (Λ : Fin n → I → ℝ)
        (Μ : ∀ j : Fin n,
          {l : Fin n // l < j} → ℝ),
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x.ofLp
            (MvPolynomial.pderiv k (Q j)) =
          (∑ i : I,
            Λ j i *
              MvPolynomial.eval x.ofLp
                (MvPolynomial.pderiv k (P i))) +
          ∑ l : {l : Fin n // l < j},
            Μ j l *
              MvPolynomial.eval x.ofLp
                (MvPolynomial.pderiv k (Q l.1)) := by
  classical
  have hstage :
      ∀ j : Fin n,
        ∃ c : I ⊕ {l : Fin n // l < j} → ℝ,
          (∑ a : I ⊕ {l : Fin n // l < j},
              c a •
                evalGradient
                  (Sum.elim P
                    (fun l : {l : Fin n // l < j} =>
                      Q l.1) a) x) +
            evalGradient (Q j) x = 0 := by
    intro j
    exact
      IsLocalExtrOn.exists_normalMultipliers_of_hasStrictFDerivAt
        (hlocal j)
        (fun a =>
          hasStrictFDerivAt_eval
            (Sum.elim P
              (fun l : {l : Fin n // l < j} =>
                Q l.1) a) x)
        (hasStrictFDerivAt_eval (Q j) x)
        (hindependent j)
  choose c hc using hstage
  refine
    ⟨fun j i => -c j (Sum.inl i),
      fun j l => -c j (Sum.inr l), ?_⟩
  intro j k
  have hsplit :
      ((∑ i : I,
          c j (Sum.inl i) • evalGradient (P i) x) +
        ∑ l : {l : Fin n // l < j},
          c j (Sum.inr l) • evalGradient (Q l.1) x) +
        evalGradient (Q j) x = 0 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr] using hc j
  have heval :=
    congrArg
      (fun f : EuclideanSpace ℝ σ →L[ℝ] ℝ =>
        f (EuclideanSpace.single k 1))
      hsplit
  simp only [add_apply, zero_apply, sum_apply,
    smul_apply, smul_eq_mul,
    evalGradient_single] at heval
  have hneg :=
    eq_neg_of_add_eq_zero_right heval
  rw [hneg]
  simp only [neg_add_rev, Finset.sum_neg_distrib,
    neg_mul]
  ac_rfl

/-- Sequence form of `exists_triangularMultipliers_of_lexCritical`.  It
chooses normalized real multipliers simultaneously at every selected
point, so the resulting critical identities hold pointwise (and hence
eventually in any filter germ). -/
theorem exists_triangularMultiplierSequences_of_lexCritical
    {σ I : Type*} [Fintype σ]
    [Fintype I] {n : ℕ}
    (x : ℕ → EuclideanSpace ℝ σ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (hlocal :
      ∀ m (j : Fin n),
        IsLocalExtrOn
          (fun y : EuclideanSpace ℝ σ =>
            MvPolynomial.eval y.ofLp (Q j))
          {y |
            ∀ a : I ⊕ {l : Fin n // l < j},
              MvPolynomial.eval y.ofLp
                  (Sum.elim P
                    (fun l : {l : Fin n // l < j} =>
                      Q l.1) a) =
                MvPolynomial.eval (x m).ofLp
                  (Sum.elim P
                    (fun l : {l : Fin n // l < j} =>
                      Q l.1) a)}
          (x m))
    (hindependent :
      ∀ m (j : Fin n),
        LinearIndependent ℝ
          (fun a : I ⊕ {l : Fin n // l < j} =>
            evalGradient
              (Sum.elim P
                (fun l : {l : Fin n // l < j} =>
                  Q l.1) a) (x m))) :
    ∃ (Λ : ℕ → Fin n → I → ℝ)
        (Μ : ∀ _m : ℕ, ∀ j : Fin n,
          {l : Fin n // l < j} → ℝ),
      ∀ m (j : Fin n) (k : σ),
        MvPolynomial.eval (x m).ofLp
            (MvPolynomial.pderiv k (Q j)) =
          (∑ i : I,
            Λ m j i *
              MvPolynomial.eval (x m).ofLp
                (MvPolynomial.pderiv k (P i))) +
          ∑ l : {l : Fin n // l < j},
            Μ m j l *
              MvPolynomial.eval (x m).ofLp
                (MvPolynomial.pderiv k (Q l.1)) := by
  have hm :
      ∀ m : ℕ,
        ∃ (Λ : Fin n → I → ℝ)
            (Μ : ∀ j : Fin n,
              {l : Fin n // l < j} → ℝ),
          ∀ (j : Fin n) (k : σ),
            MvPolynomial.eval (x m).ofLp
                (MvPolynomial.pderiv k (Q j)) =
              (∑ i : I,
                Λ j i *
                  MvPolynomial.eval (x m).ofLp
                    (MvPolynomial.pderiv k (P i))) +
              ∑ l : {l : Fin n // l < j},
                Μ j l *
                  MvPolynomial.eval (x m).ofLp
                    (MvPolynomial.pderiv k (Q l.1)) :=
    fun m =>
      exists_triangularMultipliers_of_lexCritical
        (x m) P Q (hlocal m) (hindependent m)
  choose Λ Μ hcritical using hm
  exact ⟨Λ, Μ, hcritical⟩

/-- If earlier lexicographic objectives have already been shown locally
automatic on a smooth fiber, every later stage is an extremum on the same
regular permanent fiber.  In that situation no (necessarily redundant)
earlier-objective constraints are introduced, and normalized Lagrange
multipliers express every objective gradient using only the independent
permanent equations. -/
theorem exists_permanentMultipliers_of_localExtrOn
    {σ I : Type*} [Fintype σ]
    [Fintype I] {n : ℕ}
    (x : EuclideanSpace ℝ σ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (hlocal :
      ∀ j : Fin n,
        IsLocalExtrOn
          (fun y : EuclideanSpace ℝ σ =>
            MvPolynomial.eval y.ofLp (Q j))
          {y |
            ∀ i : I,
              MvPolynomial.eval y.ofLp (P i) =
                MvPolynomial.eval x.ofLp (P i)}
          x)
    (hindependent :
      LinearIndependent ℝ
        (fun i : I => evalGradient (P i) x)) :
    ∃ Λ : Fin n → I → ℝ,
      ∀ (j : Fin n) (k : σ),
        MvPolynomial.eval x.ofLp
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ j i *
              MvPolynomial.eval x.ofLp
                (MvPolynomial.pderiv k (P i)) := by
  classical
  have hstage :
      ∀ j : Fin n,
        ∃ c : I → ℝ,
          (∑ i : I, c i • evalGradient (P i) x) +
            evalGradient (Q j) x = 0 := by
    intro j
    exact
      IsLocalExtrOn.exists_normalMultipliers_of_hasStrictFDerivAt
        (hlocal j)
        (fun i => hasStrictFDerivAt_eval (P i) x)
        (hasStrictFDerivAt_eval (Q j) x)
        hindependent
  choose c hc using hstage
  refine ⟨fun j i => -c j i, ?_⟩
  intro j k
  have heval :=
    congrArg
      (fun f : EuclideanSpace ℝ σ →L[ℝ] ℝ =>
        f (EuclideanSpace.single k 1))
      (hc j)
  simp only [add_apply, zero_apply, sum_apply,
    smul_apply, smul_eq_mul,
    evalGradient_single] at heval
  have hneg :=
    eq_neg_of_add_eq_zero_right heval
  rw [hneg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => by
    rw [neg_mul]

/-- Pointwise version on a selected sequence.  Its output gives identities
at every term, stronger than the eventual identities needed for the germ
ideal. -/
theorem exists_permanentMultiplierSequences_of_localExtrOn
    {σ I : Type*} [Fintype σ]
    [Fintype I] {n : ℕ}
    (x : ℕ → EuclideanSpace ℝ σ)
    (P : I → MvPolynomial σ ℝ)
    (Q : Fin n → MvPolynomial σ ℝ)
    (hlocal :
      ∀ m (j : Fin n),
        IsLocalExtrOn
          (fun y : EuclideanSpace ℝ σ =>
            MvPolynomial.eval y.ofLp (Q j))
          {y |
            ∀ i : I,
              MvPolynomial.eval y.ofLp (P i) =
                MvPolynomial.eval (x m).ofLp (P i)}
          (x m))
    (hindependent :
      ∀ m,
        LinearIndependent ℝ
          (fun i : I => evalGradient (P i) (x m))) :
    ∃ Λ : ℕ → Fin n → I → ℝ,
      ∀ m (j : Fin n) (k : σ),
        MvPolynomial.eval (x m).ofLp
            (MvPolynomial.pderiv k (Q j)) =
          ∑ i : I,
            Λ m j i *
              MvPolynomial.eval (x m).ofLp
                (MvPolynomial.pderiv k (P i)) := by
  have hm :
      ∀ m : ℕ,
        ∃ Λ : Fin n → I → ℝ,
          ∀ (j : Fin n) (k : σ),
            MvPolynomial.eval (x m).ofLp
                (MvPolynomial.pderiv k (Q j)) =
              ∑ i : I,
                Λ j i *
                  MvPolynomial.eval (x m).ofLp
                    (MvPolynomial.pderiv k (P i)) :=
    fun m =>
      exists_permanentMultipliers_of_localExtrOn
        (x m) P Q (hlocal m) (hindependent m)
  choose Λ hcritical using hm
  exact ⟨Λ, hcritical⟩

end CurveSelection.NormalLagrangeScratch
end Math
