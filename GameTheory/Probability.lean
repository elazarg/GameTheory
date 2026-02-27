import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# GameTheory.Probability

Stochastic kernels and expected-value infrastructure for discrete game theory.

Provides:
- `Kernel α β` — stochastic kernels (Markov kernels) using Mathlib's `PMF`
- `Kernel.id`, `Kernel.comp`, `Kernel.linExt`, `Kernel.ofFun` — basic operations
- `expect` — expected value of a real-valued function under a `PMF`
- Utility lemmas: `expect_pure`, `expect_bind`, `expect_const`, `expect_eq_sum`

## Scope-outs

- **Continuous distributions** — the library is discrete (`PMF`) by design.
- **`expect_add` (linearity)** — requires summability side-conditions that add
  significant overhead for finite games where `expect_eq_sum` suffices.
-/

namespace GameTheory

-- ============================================================================
-- § 1. Kernels (using Mathlib's PMF)
-- ============================================================================

/-- A stochastic kernel from `α` to `β`: maps each input to a PMF over outputs. -/
abbrev Kernel (α β : Type) : Type := α → PMF β

namespace Kernel

/-- Identity kernel. -/
noncomputable def id (α : Type) : Kernel α α := PMF.pure

/-- Kernel composition (Kleisli composition). -/
noncomputable def comp (k₁ : Kernel α β) (k₂ : Kernel β γ) : Kernel α γ :=
  fun a => (k₁ a).bind k₂

/-- Linear extension / pushforward of a kernel to input distributions. -/
noncomputable def linExt (k : Kernel α β) : PMF α → PMF β :=
  fun μ => μ.bind k

/-- Pushforward along a pure function (deterministic kernel). -/
noncomputable def ofFun (f : α → β) : Kernel α β := fun a => PMF.pure (f a)


@[simp] theorem comp_apply (k₁ : Kernel α β) (k₂ : Kernel β γ) (a : α) :
    Kernel.comp k₁ k₂ a = (k₁ a).bind k₂ := rfl

@[simp] theorem comp_assoc (k₁ : Kernel α β) (k₂ : Kernel β γ) (k₃ : Kernel γ δ) :
    Kernel.comp (Kernel.comp k₁ k₂) k₃ = Kernel.comp k₁ (Kernel.comp k₂ k₃) := by
  funext a
  simp_all only [comp_apply, PMF.bind_bind]
  rfl

@[simp] theorem comp_id_left (k : Kernel α β) :
    Kernel.comp (Kernel.id α) k = k := by
  funext a
  simp [Kernel.comp, Kernel.id]

@[simp] theorem comp_id_right (k : Kernel α β) :
    Kernel.comp k (Kernel.id β) = k := by
  funext a
  simp [Kernel.comp, Kernel.id]

/-- Linear extension is just `bind` at the PMF level. -/
@[simp] theorem linExt_apply (k : Kernel α β) (μ : PMF α) :
    Kernel.linExt k μ = μ.bind k := rfl

/-- `linExt` along a deterministic kernel is exactly `mapPMF`. -/
@[simp] theorem linExt_ofFun (f : α → β) (μ : PMF α) :
    Kernel.linExt (Kernel.ofFun f) μ = μ.bind (fun a => PMF.pure (f a)) := by
  rfl

/-- Linear extension respects Kleisli composition. -/
@[simp] theorem linExt_comp (k₁ : Kernel α β) (k₂ : Kernel β γ) (μ : PMF α) :
    Kernel.linExt (Kernel.comp k₁ k₂) μ = Kernel.linExt k₂ (Kernel.linExt k₁ μ) := by
  -- μ.bind (fun a => (k₁ a).bind k₂) = (μ.bind k₁).bind k₂
  simp_all only [linExt_apply, PMF.bind_bind]
  rfl

end Kernel

-- ============================================================================
-- § 2. Expected value
-- ============================================================================

/-- Expected value of a real-valued function under a PMF. -/
noncomputable def expect {Ω : Type} (d : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑' ω, (d ω).toReal * f ω

/--
For finite `Ω`, `expect` is literally a finite sum.
This is a *huge* simplification for many game models (EFG/NFG/MAID with finite outcomes).
-/
theorem expect_eq_sum {Ω : Type} [Fintype Ω] (d : PMF Ω) (f : Ω → ℝ) :
    expect d f = (∑ ω : Ω, (d ω).toReal * f ω) := by
  simp [expect]

-- ============================================================================
-- § 3. Utility lemmas for expect
-- ============================================================================

/-- Expected value under a point mass is just function evaluation. -/
@[simp] theorem expect_pure {Ω : Type} (f : Ω → ℝ) (ω : Ω) :
    expect (PMF.pure ω) f = f ω := by
  simp only [expect, PMF.pure_apply]
  rw [tsum_eq_single ω]
  · simp
  · intro ω' hne; simp [hne]

/-- Expected value of a constant function. -/
@[simp] theorem expect_const {Ω : Type} [Nonempty Ω] (d : PMF Ω) (c : ℝ) :
    expect d (fun _ => c) = c := by
  simp only [expect]
  have hfact : (fun ω => (d ω).toReal * c) = (fun ω => c * (d ω).toReal) := by ext; ring
  rw [hfact, tsum_mul_left]
  suffices hs : ∑' ω, (d ω).toReal = 1 by rw [hs, mul_one]
  have key := @ENNReal.tsum_toReal_eq Ω (fun ω => d ω) (fun a => PMF.apply_ne_top d a)
  rw [show ∑' ω, (d ω).toReal = ∑' ω, ((fun ω => d ω) ω).toReal from rfl]
  rw [← key, PMF.tsum_coe]; norm_num

set_option linter.unusedFintypeInType false in
/-- Expected value distributes over `PMF.bind`. -/
theorem expect_bind {α β : Type} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  simp only [expect, PMF.bind_apply, tsum_fintype]
  have hne : ∀ (a : α) (b : β), p a * q a b ≠ ⊤ := fun a b =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hne a _), ENNReal.toReal_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GameTheory
