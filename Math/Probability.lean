import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Math.Probability

Stochastic kernels and expected-value infrastructure for discrete game theory.

Provides:
- `Kernel α β` — stochastic kernels (Markov kernels) using Mathlib's `PMF`
- `Kernel.id`, `Kernel.comp`, `Kernel.pushforward`, `Kernel.linExt`,
  `Kernel.ofFun` — basic operations
- `expect` — expected value of a real-valued function under a `PMF`
- Utility lemmas: `expect_pure`, `expect_bind`, `expect_const`, `expect_eq_sum`

-/

namespace Math
namespace Probability

-- ============================================================================
-- Kernels (using Mathlib's PMF)
-- ============================================================================

/-- A stochastic kernel from `α` to `β`: maps each input to a PMF over outputs. -/
abbrev Kernel (α β : Type) : Type := α → PMF β

namespace Kernel

/-- Identity kernel. -/
noncomputable def id (α : Type) : Kernel α α := PMF.pure

/-- Kernel composition (Kleisli composition). -/
noncomputable def comp (k₁ : Kernel α β) (k₂ : Kernel β γ) : Kernel α γ :=
  fun a => (k₁ a).bind k₂

/-- Pushforward of a kernel to input distributions. -/
noncomputable def pushforward (k : Kernel α β) : PMF α → PMF β :=
  fun μ => μ.bind k

/-- Linear-extension notation for `pushforward`. -/
noncomputable def linExt (k : Kernel α β) : PMF α → PMF β := Kernel.pushforward k

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

/-- Linear extension is just pushforward/bind at the PMF level. -/
@[simp] theorem linExt_apply (k : Kernel α β) (μ : PMF α) :
    Kernel.linExt k μ = μ.bind k := rfl

/-- `pushforward` is `bind` by definition. -/
@[simp] theorem pushforward_apply (k : Kernel α β) (μ : PMF α) :
    Kernel.pushforward k μ = μ.bind k := rfl

/-- `linExt` along a deterministic kernel is exactly `mapPMF`. -/
@[simp] theorem linExt_ofFun (f : α → β) (μ : PMF α) :
    Kernel.linExt (Kernel.ofFun f) μ = μ.bind (fun a => PMF.pure (f a)) := by
  rfl

@[simp] theorem pushforward_ofFun (f : α → β) (μ : PMF α) :
    Kernel.pushforward (Kernel.ofFun f) μ = μ.bind (fun a => PMF.pure (f a)) := by
  rfl

/-- Linear extension respects Kleisli composition. -/
@[simp] theorem linExt_comp (k₁ : Kernel α β) (k₂ : Kernel β γ) (μ : PMF α) :
    Kernel.linExt (Kernel.comp k₁ k₂) μ = Kernel.linExt k₂ (Kernel.linExt k₁ μ) := by
  -- μ.bind (fun a => (k₁ a).bind k₂) = (μ.bind k₁).bind k₂
  simp_all only [linExt_apply, PMF.bind_bind]
  rfl

/-- Pushforward respects Kleisli composition. -/
@[simp] theorem pushforward_comp (k₁ : Kernel α β) (k₂ : Kernel β γ) (μ : PMF α) :
    Kernel.pushforward (Kernel.comp k₁ k₂) μ =
      Kernel.pushforward k₂ (Kernel.pushforward k₁ μ) := by
  simpa [Kernel.pushforward] using (Kernel.linExt_comp k₁ k₂ μ)

end Kernel

-- ============================================================================
-- Expected value
-- ============================================================================

/-- Expected value of a real-valued function under a PMF. -/
noncomputable def expect {Ω : Type*} (d : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑' ω, (d ω).toReal * f ω

/--
For finite `Ω`, `expect` is literally a finite sum.
This is a *huge* simplification for many game models (EFG/NFG/MAID with finite outcomes).
-/
theorem expect_eq_sum {Ω : Type*} [Fintype Ω] (d : PMF Ω) (f : Ω → ℝ) :
    expect d f = (∑ ω : Ω, (d ω).toReal * f ω) := by
  simp [expect]

-- ============================================================================
-- PMF utility lemmas
-- ============================================================================

/-- The tsum of a PMF's real-valued weights is 1. -/
theorem pmf_toReal_tsum_one {Ω : Type*} (d : PMF Ω) : ∑' ω, (d ω).toReal = 1 := by
  have key := @ENNReal.tsum_toReal_eq Ω (fun ω => d ω) (fun a => PMF.apply_ne_top d a)
  rw [show ∑' ω, (d ω).toReal = ∑' ω, ((fun ω => d ω) ω).toReal from rfl]
  rw [← key, PMF.tsum_coe]; norm_num

/-- The finite sum of a PMF's real-valued weights is 1. -/
theorem pmf_toReal_sum_one {Ω : Type*} [Fintype Ω] (d : PMF Ω) :
    ∑ ω : Ω, (d ω).toReal = 1 := by
  simpa [tsum_fintype] using (pmf_toReal_tsum_one d)

-- ============================================================================
-- Utility lemmas for expect
-- ============================================================================

/-- Expected value under a point mass is just function evaluation. -/
@[simp] theorem expect_pure {Ω : Type*} (f : Ω → ℝ) (ω : Ω) :
    expect (PMF.pure ω) f = f ω := by
  simp only [expect, PMF.pure_apply]
  rw [tsum_eq_single ω]
  · simp
  · intro ω' hne; simp [hne]

/-- Expected value of a constant function. -/
@[simp] theorem expect_const {Ω : Type*} [Nonempty Ω] (d : PMF Ω) (c : ℝ) :
    expect d (fun _ => c) = c := by
  simp only [expect]
  have hfact : (fun ω => (d ω).toReal * c) = (fun ω => c * (d ω).toReal) := by ext; ring
  rw [hfact, tsum_mul_left]
  rw [pmf_toReal_tsum_one d, mul_one]

/-- Expected value distributes over `PMF.bind`. -/
theorem expect_bind {α β : Type*} [Finite α] [Finite β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  simp only [expect, PMF.bind_apply, tsum_fintype]
  have hne : ∀ (a : α) (b : β), p a * q a b ≠ ⊤ := fun a b =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hne a _), ENNReal.toReal_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Expected value over a pushforward from a finite source.

The target type need not be finite: the pushforward support is contained in the
finite image of the source. -/
theorem expect_map_fintype_source {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (u : β → ℝ) :
    expect (PMF.map f p) u = ∑ a : α, (p a).toReal * u (f a) := by
  classical
  rw [expect]
  rw [tsum_eq_sum (s := (Finset.univ.image f))]
  · calc
      ∑ b ∈ Finset.univ.image f, ((PMF.map f p) b).toReal * u b
        = ∑ b ∈ Finset.univ.image f,
            ((∑ a : α, if b = f a then p a else 0).toReal) * u b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [PMF.map_apply, tsum_fintype]
      _ = ∑ b ∈ Finset.univ.image f,
            (∑ a : α, if b = f a then (p a).toReal else 0) * u b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            congr 1
            rw [show (∑ a : α, if b = f a then p a else 0).toReal =
                ∑ a : α, (if b = f a then p a else 0).toReal by
              exact ENNReal.toReal_sum (s := (Finset.univ : Finset α))
                (f := fun a => if b = f a then p a else 0)
                (by
                  intro a _
                  by_cases h : b = f a <;> simp [h, PMF.apply_ne_top])]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases h : b = f a <;> simp [h]
      _ = ∑ b ∈ Finset.univ.image f,
            ∑ a : α, if b = f a then (p a).toReal * u b else 0 := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases h : b = f a <;> simp [h]
      _ = ∑ a : α, ∑ b ∈ Finset.univ.image f,
            if b = f a then (p a).toReal * u b else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ a : α, (p a).toReal * u (f a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.sum_eq_single (f a)]
            · simp
            · intro b _ hne
              simp [hne]
            · intro hnot
              exact (hnot (Finset.mem_image.2 ⟨a, by simp, rfl⟩)).elim
  · intro b hb
    have hmap : PMF.map f p b = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      refine Finset.sum_eq_zero ?_
      intro a _
      have hne : b ≠ f a := by
        intro h
        exact hb (Finset.mem_image.2 ⟨a, by simp, h.symm⟩)
      simp [hne]
    simp [hmap]

/-- Expected value over a pushforward to a finite target.

The source type need not be finite. This is useful for trace distributions
whose trace carrier is an unbounded list type, but whose utility factors
through a finite state or observation projection. -/
theorem expect_map_fintype_target {α β : Type*} [Finite β]
    (p : PMF α) (f : α → β) (u : β → ℝ) :
    expect (PMF.map f p) u = expect p (fun a => u (f a)) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  have hp : Summable fun a : α => (p a).toReal := by
    apply ENNReal.summable_toReal
    rw [PMF.tsum_coe]
    exact ENNReal.one_ne_top
  rw [expect_eq_sum]
  unfold expect
  simp only [PMF.map_apply]
  rw [show
      (∑ b : β, ((∑' a : α, if b = f a then p a else 0).toReal) * u b) =
        ∑ b : β, (∑' a : α,
          (if b = f a then (p a).toReal else 0) * u b) from by
        congr
        funext b
        rw [tsum_mul_right]
        congr 1
        have hto :
            (∑' a : α, (if b = f a then p a else 0 : ENNReal)).toReal =
              ∑' a : α,
                ((if b = f a then p a else 0 : ENNReal).toReal) := by
          exact ENNReal.tsum_toReal_eq
            (f := fun a : α => if b = f a then p a else 0) (by
              intro a
              by_cases h : b = f a
              · simp [h, PMF.apply_ne_top p a]
              · simp [h])
        rw [hto]
        congr
        funext a
        by_cases h : b = f a
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
          exact ENNReal.toReal_zero]
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset β))]
  · congr
    funext a
    rw [Finset.sum_eq_single (f a)]
    · rw [if_pos rfl]
    · intro b _ hne
      have h : ¬ b = f a := by exact hne
      rw [if_neg h]
      exact zero_mul (u b)
    · intro hnot
      exact (hnot (Finset.mem_univ (f a))).elim
  · intro b _
    have hs :
        Summable fun a : α => if b = f a then (p a).toReal else 0 := by
      simpa [Set.indicator, eq_comm] using
        (hp.indicator {a : α | f a = b})
    exact hs.mul_right (u b)

end Probability
end Math
