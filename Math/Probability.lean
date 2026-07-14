/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Math.Probability

Stochastic kernels and expected-value infrastructure for discrete game theory.

Provides:
- `Kernel α β` — stochastic kernels (Markov kernels) using Mathlib's `PMF`
- `Kernel.id`, `Kernel.comp`, `Kernel.pushforward`,
  `Kernel.ofFun` — basic operations
- `expect` — expected value of a real-valued function under a `PMF`
- Utility lemmas: `expect_pure`, `expect_bind`, `expect_const`, `expect_eq_sum`

-/

namespace Math
namespace Probability

open Filter

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

/-- `pushforward` is `bind` by definition. -/
@[simp] theorem pushforward_apply (k : Kernel α β) (μ : PMF α) :
    Kernel.pushforward k μ = μ.bind k := rfl

@[simp] theorem pushforward_ofFun (f : α → β) (μ : PMF α) :
    Kernel.pushforward (Kernel.ofFun f) μ = μ.bind (fun a => PMF.pure (f a)) := by
  rfl

/-- Pushforward respects Kleisli composition. -/
@[simp] theorem pushforward_comp (k₁ : Kernel α β) (k₂ : Kernel β γ) (μ : PMF α) :
  Kernel.pushforward (Kernel.comp k₁ k₂) μ =
      Kernel.pushforward k₂ (Kernel.pushforward k₁ μ) := by
  simp_all only [pushforward_apply, PMF.bind_bind]
  rfl

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

theorem pmf_apply_toReal_tendsto_of_tendsto {Ω : Type*}
    {μs : ℕ → PMF Ω} {μ : PMF Ω} {ω : Ω}
    (h : Tendsto (fun n : ℕ => μs n ω) atTop (nhds (μ ω))) :
    Tendsto (fun n : ℕ => (μs n ω).toReal) atTop (nhds ((μ ω).toReal)) :=
  (ENNReal.continuousAt_toReal (PMF.apply_ne_top μ ω)).tendsto.comp h

/--
Finite expectations are continuous under pointwise convergence of real-valued
PMF weights.
-/
theorem expect_tendsto_of_forall_toReal_tendsto {Ω : Type*} [Finite Ω]
    {μs : ℕ → PMF Ω} {μ : PMF Ω} (f : Ω → ℝ)
    (h : ∀ ω : Ω,
      Tendsto (fun n : ℕ => (μs n ω).toReal) atTop (nhds ((μ ω).toReal))) :
    Tendsto (fun n : ℕ => expect (μs n) f) atTop (nhds (expect μ f)) := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [show (fun n : ℕ => expect (μs n) f) =
      fun n : ℕ => ∑ ω : Ω, (μs n ω).toReal * f ω by
        funext n
        rw [expect_eq_sum]]
  rw [expect_eq_sum]
  exact tendsto_finsetSum (s := Finset.univ)
    (fun ω _ => (h ω).mul_const (f ω))

/--
Finite expectations are continuous under pointwise convergence of PMF weights
in `ENNReal`.
-/
theorem expect_tendsto_of_forall_tendsto {Ω : Type*} [Finite Ω]
    {μs : ℕ → PMF Ω} {μ : PMF Ω} (f : Ω → ℝ)
    (h : ∀ ω : Ω, Tendsto (fun n : ℕ => μs n ω) atTop (nhds (μ ω))) :
    Tendsto (fun n : ℕ => expect (μs n) f) atTop (nhds (expect μ f)) :=
  expect_tendsto_of_forall_toReal_tendsto f
    (fun ω => pmf_apply_toReal_tendsto_of_tendsto (h ω))

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

/-- A real-valued function on a finite type has a uniform absolute bound. -/
theorem exists_abs_bound_of_finite {Ω : Type*} [Finite Ω] (f : Ω → ℝ) :
    ∃ C : ℝ, ∀ ω, |f ω| ≤ C := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  refine ⟨∑ ω : Ω, |f ω|, ?_⟩
  intro ω
  exact Finset.single_le_sum (fun x _ => abs_nonneg (f x)) (Finset.mem_univ ω)

/-! ### Coordinate independence

A general utility (not probability-specific), collected here as the common base of
the mechanism-design files: a function on a product type is *independent of
coordinate `i`* when changing the `i`-th component never changes its value. This
names the recurring "does not depend on agent `i`'s own report/bid" condition. -/

/-- `F` is **independent of coordinate `i`** if updating the `i`-th argument never
changes its value. -/
def IndependentOfCoordinate {ι : Type*} [DecidableEq ι] {α : ι → Type*} {β : Type*}
    (i : ι) (F : (∀ j, α j) → β) : Prop :=
  ∀ (θ : ∀ j, α j) (θᵢ : α i), F θ = F (Function.update θ i θᵢ)

/-- An independent-of-`i` function agrees on any two inputs that agree off `i`. -/
theorem IndependentOfCoordinate.eq_of_agree {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} {β : Type*} {i : ι} {F : (∀ j, α j) → β}
    (hF : IndependentOfCoordinate i F) {θ θ' : ∀ j, α j}
    (h : ∀ j, j ≠ i → θ j = θ' j) : F θ = F θ' := by
  rw [hF θ (θ' i)]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj]; exact h j hj

/-- A PMF's real-valued weight function is summable. The summability comes
    from `PMF.tsum_coe = 1` in `ENNReal` plus `ENNReal.summable_toReal`. -/
theorem pmf_toReal_summable {Ω : Type*} (d : PMF Ω) :
    Summable (fun ω => (d ω).toReal) := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe]; exact ENNReal.one_ne_top

/-- For bounded `f`, the integrand of `expect d f` is summable. -/
theorem expect_summable_of_bounded {Ω : Type*}
    (d : PMF Ω) (f : Ω → ℝ) {C : ℝ} (hbd : ∀ ω, |f ω| ≤ C) :
    Summable (fun ω => (d ω).toReal * f ω) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le
      (g := fun ω => |(d ω).toReal * f ω|)
      (f := fun ω => (d ω).toReal * C)
      (fun _ => abs_nonneg _)
  · intro ω
    have hd : 0 ≤ (d ω).toReal := ENNReal.toReal_nonneg
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left (hbd ω) hd
  · exact (pmf_toReal_summable d).mul_right C

/--
The overlap mass `∑ min μₙ μ` converges to `1` when `μₙ` converges pointwise to `μ`.
This is the dominated-convergence core of Scheffé's lemma for PMFs.
-/
theorem pmf_overlap_tendsto_of_forall_toReal_tendsto {Ω : Type*}
    {μs : ℕ → PMF Ω} {μ : PMF Ω}
    (h : ∀ ω : Ω,
      Tendsto (fun n : ℕ => (μs n ω).toReal) atTop (nhds ((μ ω).toReal))) :
    Tendsto (fun n : ℕ => ∑' ω : Ω, min ((μs n ω).toReal) ((μ ω).toReal)) atTop
      (nhds 1) := by
  have hsum : Summable (fun ω : Ω => (μ ω).toReal) := pmf_toReal_summable μ
  have ht := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun n ω => min ((μs n ω).toReal) ((μ ω).toReal))
    (g := fun ω => (μ ω).toReal)
    (bound := fun ω => (μ ω).toReal)
    hsum
    (fun ω => by
      have hconst : Tendsto (fun _ : ℕ => (μ ω).toReal) atTop (nhds ((μ ω).toReal)) :=
        tendsto_const_nhds
      have hmin := (h ω).min hconst
      simpa using hmin)
    (Eventually.of_forall (fun n ω => by
      have hnonneg : 0 ≤ min ((μs n ω).toReal) ((μ ω).toReal) :=
        le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hle : min ((μs n ω).toReal) ((μ ω).toReal) ≤ (μ ω).toReal := min_le_right _ _
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg, hle]))
  simpa [pmf_toReal_tsum_one μ] using ht

/--
The difference of expectations of a bounded function is controlled by the
non-overlap mass of the two PMFs.
-/
theorem abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap {Ω : Type*}
    (μ ν : PMF Ω) (f : Ω → ℝ) {C : ℝ} (hbd : ∀ ω, |f ω| ≤ C) :
    |expect μ f - expect ν f| ≤
      2 * C * (1 - ∑' ω : Ω, min ((μ ω).toReal) ((ν ω).toReal)) := by
  let r : Ω → ℝ := fun ω => min ((μ ω).toReal) ((ν ω).toReal)
  have hr_nonneg : ∀ ω, 0 ≤ r ω := fun ω => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hr_le_μ : ∀ ω, r ω ≤ (μ ω).toReal := fun ω => min_le_left _ _
  have hr_le_ν : ∀ ω, r ω ≤ (ν ω).toReal := fun ω => min_le_right _ _
  have hμ_sum : Summable (fun ω : Ω => (μ ω).toReal) := pmf_toReal_summable μ
  have hν_sum : Summable (fun ω : Ω => (ν ω).toReal) := pmf_toReal_summable ν
  have hr_sum_μ : Summable r := by
    refine Summable.of_norm_bounded hμ_sum ?_
    intro ω
    simp [r, Real.norm_eq_abs, abs_of_nonneg (hr_nonneg ω), hr_le_μ ω]
  have hr_sum_ν : Summable r := by
    refine Summable.of_norm_bounded hν_sum ?_
    intro ω
    simp [r, Real.norm_eq_abs, abs_of_nonneg (hr_nonneg ω), hr_le_ν ω]
  have hrf_sum : Summable (fun ω : Ω => r ω * f ω) := by
    refine Summable.of_norm_bounded (hr_sum_μ.mul_left C) ?_
    intro ω
    have hr0 := hr_nonneg ω
    have hf_abs := hbd ω
    calc ‖r ω * f ω‖
        = |r ω * f ω| := Real.norm_eq_abs _
      _ = r ω * |f ω| := by rw [abs_mul, abs_of_nonneg hr0]
      _ ≤ r ω * C := mul_le_mul_of_nonneg_left hf_abs hr0
      _ = C * r ω := by ring
  have hμf_sum : Summable (fun ω : Ω => (μ ω).toReal * f ω) :=
    expect_summable_of_bounded μ f hbd
  have hνf_sum : Summable (fun ω : Ω => (ν ω).toReal * f ω) :=
    expect_summable_of_bounded ν f hbd
  have hμ_tail_hasSum : HasSum (fun ω : Ω => ((μ ω).toReal - r ω) * f ω)
      (expect μ f - ∑' ω : Ω, r ω * f ω) := by
    have h := hμf_sum.hasSum.sub hrf_sum.hasSum
    have hfun : (fun b : Ω => (μ b).toReal * f b - r b * f b) =
        (fun ω : Ω => ((μ ω).toReal - r ω) * f ω) := by
      funext ω
      ring
    rw [hfun] at h
    simpa [expect] using h
  have hν_tail_hasSum : HasSum (fun ω : Ω => ((ν ω).toReal - r ω) * f ω)
      (expect ν f - ∑' ω : Ω, r ω * f ω) := by
    have h := hνf_sum.hasSum.sub hrf_sum.hasSum
    have hfun : (fun b : Ω => (ν b).toReal * f b - r b * f b) =
        (fun ω : Ω => ((ν ω).toReal - r ω) * f ω) := by
      funext ω
      ring
    rw [hfun] at h
    simpa [expect] using h
  have hμ_tail_mass : HasSum (fun ω : Ω => C * ((μ ω).toReal - r ω))
      (C * (1 - ∑' ω : Ω, r ω)) := by
    have hbase := hμ_sum.hasSum.sub hr_sum_μ.hasSum
    have hbase' : HasSum (fun ω : Ω => (μ ω).toReal - r ω)
        (1 - ∑' ω : Ω, r ω) := by
      simpa [pmf_toReal_tsum_one μ] using hbase
    simpa [mul_sub] using hbase'.mul_left C
  have hν_tail_mass : HasSum (fun ω : Ω => C * ((ν ω).toReal - r ω))
      (C * (1 - ∑' ω : Ω, r ω)) := by
    have hbase := hν_sum.hasSum.sub hr_sum_ν.hasSum
    have hbase' : HasSum (fun ω : Ω => (ν ω).toReal - r ω)
        (1 - ∑' ω : Ω, r ω) := by
      simpa [pmf_toReal_tsum_one ν] using hbase
    simpa [mul_sub] using hbase'.mul_left C
  have hμ_tail_bound : |expect μ f - ∑' ω : Ω, r ω * f ω| ≤
      C * (1 - ∑' ω : Ω, r ω) := by
    have hle := hμ_tail_hasSum.norm_le_of_bounded hμ_tail_mass ?_
    · simpa [Real.norm_eq_abs] using hle
    intro ω
    have htail_nonneg : 0 ≤ (μ ω).toReal - r ω := sub_nonneg.2 (hr_le_μ ω)
    calc ‖(((μ ω).toReal - r ω) * f ω)‖
        = |((μ ω).toReal - r ω) * f ω| := Real.norm_eq_abs _
      _ = ((μ ω).toReal - r ω) * |f ω| := by rw [abs_mul, abs_of_nonneg htail_nonneg]
      _ ≤ ((μ ω).toReal - r ω) * C := mul_le_mul_of_nonneg_left (hbd ω) htail_nonneg
      _ = C * ((μ ω).toReal - r ω) := by ring
  have hν_tail_bound : |expect ν f - ∑' ω : Ω, r ω * f ω| ≤
      C * (1 - ∑' ω : Ω, r ω) := by
    have hle := hν_tail_hasSum.norm_le_of_bounded hν_tail_mass ?_
    · simpa [Real.norm_eq_abs] using hle
    intro ω
    have htail_nonneg : 0 ≤ (ν ω).toReal - r ω := sub_nonneg.2 (hr_le_ν ω)
    calc ‖(((ν ω).toReal - r ω) * f ω)‖
        = |((ν ω).toReal - r ω) * f ω| := Real.norm_eq_abs _
      _ = ((ν ω).toReal - r ω) * |f ω| := by rw [abs_mul, abs_of_nonneg htail_nonneg]
      _ ≤ ((ν ω).toReal - r ω) * C := mul_le_mul_of_nonneg_left (hbd ω) htail_nonneg
      _ = C * ((ν ω).toReal - r ω) := by ring
  calc |expect μ f - expect ν f|
      = |(expect μ f - ∑' ω : Ω, r ω * f ω) -
          (expect ν f - ∑' ω : Ω, r ω * f ω)| := by ring_nf
    _ ≤ |expect μ f - ∑' ω : Ω, r ω * f ω| +
          |expect ν f - ∑' ω : Ω, r ω * f ω| := abs_sub _ _
    _ ≤ C * (1 - ∑' ω : Ω, r ω) + C * (1 - ∑' ω : Ω, r ω) :=
      add_le_add hμ_tail_bound hν_tail_bound
    _ = 2 * C * (1 - ∑' ω : Ω, r ω) := by ring

/--
Expectations of a bounded real-valued function are continuous under pointwise
convergence of PMF weights. This is the PMF/Scheffé bridge for arbitrary sample
spaces; no finiteness or countability assumption on `Ω` is needed.
-/
theorem expect_tendsto_of_forall_toReal_tendsto_of_bounded {Ω : Type*}
    {μs : ℕ → PMF Ω} {μ : PMF Ω} (f : Ω → ℝ) {C : ℝ}
    (hbd : ∀ ω : Ω, |f ω| ≤ C)
    (h : ∀ ω : Ω,
      Tendsto (fun n : ℕ => (μs n ω).toReal) atTop (nhds ((μ ω).toReal))) :
    Tendsto (fun n : ℕ => expect (μs n) f) atTop (nhds (expect μ f)) := by
  have hoverlap :=
    pmf_overlap_tendsto_of_forall_toReal_tendsto (μs := μs) (μ := μ) h
  have hgap : Tendsto
      (fun n : ℕ => 2 * C *
        (1 - ∑' ω : Ω, min ((μs n ω).toReal) ((μ ω).toReal)))
      atTop (nhds 0) := by
    have hsub : Tendsto
        (fun n : ℕ => 1 - ∑' ω : Ω, min ((μs n ω).toReal) ((μ ω).toReal))
        atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have h := hconst.sub hoverlap
      simpa using h
    simpa [mul_assoc] using hsub.const_mul (2 * C)
  have habs : Tendsto (fun n : ℕ => |expect (μs n) f - expect μ f|) atTop (nhds 0) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hgap
    intro n
    exact abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap (μs n) μ f hbd
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/--
Expectations of a bounded real-valued function are continuous under pointwise
convergence of PMF weights in `ENNReal`.
-/
theorem expect_tendsto_of_forall_tendsto_of_bounded {Ω : Type*}
    {μs : ℕ → PMF Ω} {μ : PMF Ω} (f : Ω → ℝ) {C : ℝ}
    (hbd : ∀ ω : Ω, |f ω| ≤ C)
    (h : ∀ ω : Ω, Tendsto (fun n : ℕ => μs n ω) atTop (nhds (μ ω))) :
    Tendsto (fun n : ℕ => expect (μs n) f) atTop (nhds (expect μ f)) :=
  expect_tendsto_of_forall_toReal_tendsto_of_bounded f hbd
    (fun ω => pmf_apply_toReal_tendsto_of_tendsto (h ω))

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
@[simp] theorem expect_const {Ω : Type*} (d : PMF Ω) (c : ℝ) :
    expect d (fun _ => c) = c := by
  simp only [expect]
  have hfact : (fun ω => (d ω).toReal * c) = (fun ω => c * (d ω).toReal) := by ext; ring
  rw [hfact, tsum_mul_left]
  rw [pmf_toReal_tsum_one d, mul_one]

/-! ### Finite-sample expectation algebra

`expect` is linear and monotone. On a finite sample space it is a finite sum, so
these are immediate; they are collected here so concept-level files do not re-prove
them privately. -/

/-- `expect` is additive. -/
theorem expect_add {Ω : Type*} [Finite Ω] (d : PMF Ω) (f g : Ω → ℝ) :
    expect d (fun ω => f ω + g ω) = expect d f + expect d g := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- `expect` is additive whenever both weighted integrands are (absolutely)
summable. This is the weakest natural hypothesis: with the tsum convention that a
non-summable family sums to `0`, additivity can genuinely fail when a summand is not
summable, since the individual expectations collapse to `0` while their combination
need not. -/
theorem expect_add_of_summable {Ω : Type*} (d : PMF Ω) (f g : Ω → ℝ)
    (hf : Summable fun ω => (d ω).toReal * f ω)
    (hg : Summable fun ω => (d ω).toReal * g ω) :
    expect d (fun ω => f ω + g ω) = expect d f + expect d g := by
  simp only [expect]
  rw [← hf.tsum_add hg]
  exact tsum_congr fun ω => by ring

/-- `expect` commutes with subtraction. -/
theorem expect_sub {Ω : Type*} [Finite Ω] (d : PMF Ω) (f g : Ω → ℝ) :
    expect d (fun ω => f ω - g ω) = expect d f - expect d g := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- `expect` pulls out a scalar factor. -/
theorem expect_const_mul {Ω : Type*} (d : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    expect d (fun ω => c * f ω) = c * expect d f := by
  unfold expect
  rw [← tsum_mul_left]
  exact tsum_congr fun ω => by ring

/-- A nonnegative integrand has nonnegative expectation. -/
theorem expect_nonneg {Ω : Type*} (d : PMF Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect d f := by
  unfold expect
  exact tsum_nonneg fun ω => mul_nonneg ENNReal.toReal_nonneg (hf ω)

/-- `expect` is monotone in the integrand. -/
theorem expect_mono {Ω : Type*} [Finite Ω] (d : PMF Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : expect d f ≤ expect d g := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expect_eq_sum, expect_eq_sum]
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) ENNReal.toReal_nonneg

/-- If `f ≤ g` everywhere and `f < g` at a positive-probability point, then
the expectation of `f` is strictly less than the expectation of `g`. -/
theorem expect_lt_of_le_of_exists_lt {Ω : Type*} [Finite Ω]
    (d : PMF Ω) (f g : Ω → ℝ)
    (hle : ∀ ω, f ω ≤ g ω)
    (hlt : ∃ ω, d ω ≠ 0 ∧ f ω < g ω) :
    expect d f < expect d g := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  obtain ⟨ω₀, hdω₀, hltω₀⟩ := hlt
  have hpos :
      0 < ∑ ω : Ω, (d ω).toReal * (g ω - f ω) := by
    refine Finset.sum_pos' ?_ ?_
    · intro ω _
      exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hle ω))
    · refine ⟨ω₀, Finset.mem_univ ω₀, ?_⟩
      exact mul_pos
        (ENNReal.toReal_pos hdω₀ (PMF.apply_ne_top d ω₀))
        (sub_pos.mpr hltω₀)
  have hdiff :
      expect d g - expect d f =
        ∑ ω : Ω, (d ω).toReal * (g ω - f ω) := by
    rw [expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  linarith

/-- A pointwise strict inequality gives a strict expectation inequality. -/
theorem expect_lt_of_forall_lt {Ω : Type*} [Finite Ω]
    (d : PMF Ω) (f g : Ω → ℝ) (hlt : ∀ ω, f ω < g ω) :
    expect d f < expect d g := by
  classical
  obtain ⟨ω₀, hω₀⟩ := d.support_nonempty
  exact expect_lt_of_le_of_exists_lt d f g
    (fun ω => le_of_lt (hlt ω))
    ⟨ω₀, by simpa [PMF.mem_support_iff] using hω₀, hlt ω₀⟩

/-- If a function is bounded above by a constant everywhere and strictly below
it at a positive-probability point, then its expectation is strictly below that
constant. -/
theorem expect_lt_const_of_le_of_exists_lt {Ω : Type*} [Finite Ω]
    (d : PMF Ω) (f : Ω → ℝ) {c : ℝ}
    (hle : ∀ ω, f ω ≤ c)
    (hlt : ∃ ω, d ω ≠ 0 ∧ f ω < c) :
    expect d f < c := by
  have h := expect_lt_of_le_of_exists_lt d f (fun _ => c) hle hlt
  simpa using h

/-- A finite sum of integrands commutes with `expect`. -/
theorem expect_sum_comm {Ω κ : Type*} [Finite Ω] [Fintype κ]
    (d : PMF Ω) (f : κ → Ω → ℝ) :
    ∑ i, expect d (fun ω => f i ω) = expect d (fun ω => ∑ i, f i ω) := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  simp only [expect_eq_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ =>
    (Finset.mul_sum Finset.univ (fun i => f i ω) ((d ω).toReal)).symm

/-! ### Finite total-variation duality -/

/-- Positive total variation between two finite PMFs, in the convention
`∑ω max (μ ω - ν ω) 0`. For probability measures this is also
`(1 / 2) * ∑ω |μ ω - ν ω|`, but the positive-part convention is the one whose
dual statement is literally `sup_{0≤u≤1} (E_μ u - E_ν u)`. -/
noncomputable def pmfPositiveVariation {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) : ℝ :=
  ∑ ω : Ω, max ((μ ω).toReal - (ν ω).toReal) 0

theorem pmfPositiveVariation_nonneg {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    0 ≤ pmfPositiveVariation μ ν := by
  unfold pmfPositiveVariation
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem max_eq_abs_add_self_div_two (x : ℝ) :
    max x 0 = (|x| + x) / 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hxle, abs_of_nonpos hxle]
    ring

/-- On finite probability spaces, positive variation is the usual
half-`L¹` total variation distance. -/
theorem pmfPositiveVariation_eq_half_sum_abs {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    pmfPositiveVariation μ ν =
      (1 / 2 : ℝ) * ∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal| := by
  have hsumdiff :
      (∑ ω : Ω, ((μ ω).toReal - (ν ω).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib, pmf_toReal_sum_one, pmf_toReal_sum_one]
    ring
  calc
    pmfPositiveVariation μ ν
        = ∑ ω : Ω,
            (|((μ ω).toReal - (ν ω).toReal)| +
              ((μ ω).toReal - (ν ω).toReal)) / 2 := by
          unfold pmfPositiveVariation
          exact Finset.sum_congr rfl fun ω _ =>
            max_eq_abs_add_self_div_two ((μ ω).toReal - (ν ω).toReal)
    _ = (1 / 2 : ℝ) *
          (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal| +
            ∑ ω : Ω, ((μ ω).toReal - (ν ω).toReal)) := by
          rw [show
              (∑ ω : Ω,
                (|((μ ω).toReal - (ν ω).toReal)| +
                  ((μ ω).toReal - (ν ω).toReal)) / 2) =
                ∑ ω : Ω,
                  (1 / 2 : ℝ) *
                    (|((μ ω).toReal - (ν ω).toReal)| +
                      ((μ ω).toReal - (ν ω).toReal)) from by
                exact Finset.sum_congr rfl fun _ _ => by ring]
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = (1 / 2 : ℝ) * ∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal| := by
          rw [hsumdiff]
          ring

theorem expect_sub_le_mul_pmfPositiveVariation {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (f : Ω → ℝ) {U : ℝ}
    (hf_nonneg : ∀ ω, 0 ≤ f ω) (hf_le : ∀ ω, f ω ≤ U) :
    expect μ f - expect ν f ≤ U * pmfPositiveVariation μ ν := by
  rw [expect_eq_sum, expect_eq_sum, pmfPositiveVariation, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum ?_
  intro ω _
  set d : ℝ := (μ ω).toReal - (ν ω).toReal
  have hdiff :
      (μ ω).toReal * f ω - (ν ω).toReal * f ω = d * f ω := by
    simp [d]
    ring
  by_cases hd : 0 ≤ d
  · have hterm : d * f ω ≤ d * U := mul_le_mul_of_nonneg_left (hf_le ω) hd
    have hmax : max d 0 = d := max_eq_left hd
    calc
      (μ ω).toReal * f ω - (ν ω).toReal * f ω = d * f ω := hdiff
      _ ≤ d * U := hterm
      _ = U * max d 0 := by rw [hmax]; ring
  · have hdle : d ≤ 0 := le_of_not_ge hd
    have hterm : d * f ω ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdle (hf_nonneg ω)
    have hmax : max d 0 = 0 := max_eq_right hdle
    calc
      (μ ω).toReal * f ω - (ν ω).toReal * f ω = d * f ω := hdiff
      _ ≤ 0 := hterm
      _ = U * max d 0 := by rw [hmax]; ring

/-- The indicator of the positive part of `μ - ν`, scaled by `U`. -/
noncomputable def pmfPositiveVariationWitness {Ω : Type*}
    (μ ν : PMF Ω) (U : ℝ) : Ω → ℝ :=
  fun ω => if 0 < (μ ω).toReal - (ν ω).toReal then U else 0

theorem pmfPositiveVariationWitness_nonneg {Ω : Type*}
    (μ ν : PMF Ω) {U : ℝ} (hU : 0 ≤ U) :
    ∀ ω, 0 ≤ pmfPositiveVariationWitness μ ν U ω := by
  intro ω
  unfold pmfPositiveVariationWitness
  split_ifs <;> linarith

theorem pmfPositiveVariationWitness_le {Ω : Type*}
    (μ ν : PMF Ω) {U : ℝ} (hU : 0 ≤ U) :
    ∀ ω, pmfPositiveVariationWitness μ ν U ω ≤ U := by
  intro ω
  unfold pmfPositiveVariationWitness
  split_ifs <;> linarith

theorem expect_sub_pmfPositiveVariationWitness {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (U : ℝ) :
    expect μ (pmfPositiveVariationWitness μ ν U) -
        expect ν (pmfPositiveVariationWitness μ ν U) =
      U * pmfPositiveVariation μ ν := by
  rw [expect_eq_sum, expect_eq_sum, pmfPositiveVariation, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ω _
  set d : ℝ := (μ ω).toReal - (ν ω).toReal
  unfold pmfPositiveVariationWitness
  by_cases hd : 0 < d
  · have hmax : max d 0 = d := max_eq_left hd.le
    have hcond : (ν ω).toReal < (μ ω).toReal := by simpa [d] using hd
    simp [hcond, hmax]
    ring
  · have hdle : d ≤ 0 := le_of_not_gt hd
    have hmax : max d 0 = 0 := max_eq_right hdle
    have hcond : ¬ (ν ω).toReal < (μ ω).toReal := by
      simpa [d, sub_pos] using hd
    simp [hcond, hmax]

theorem expect_le_mul_expect_iff_pmf_le_mul {Ω : Type*} [Finite Ω]
    (μ ν : PMF Ω) {c : ℝ} :
    (∀ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) → expect μ f ≤ c * expect ν f) ↔
      ∀ ω, (μ ω).toReal ≤ c * (ν ω).toReal := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  constructor
  · intro h ω
    have hnonneg : ∀ x, 0 ≤ (if x = ω then (1 : ℝ) else 0) := by
      intro x
      split_ifs <;> norm_num
    have hw := h (fun x => if x = ω then (1 : ℝ) else 0) hnonneg
    rw [expect_eq_sum, expect_eq_sum] at hw
    have hμ :
        (∑ x : Ω, (μ x).toReal * (if x = ω then (1 : ℝ) else 0)) =
          (μ ω).toReal := by
      rw [Finset.sum_eq_single ω]
      · simp
      · intro x _ hx
        simp [hx]
      · intro hnot
        exact (hnot (Finset.mem_univ ω)).elim
    have hν :
        (∑ x : Ω, (ν x).toReal * (if x = ω then (1 : ℝ) else 0)) =
          (ν ω).toReal := by
      rw [Finset.sum_eq_single ω]
      · simp
      · intro x _ hx
        simp [hx]
      · intro hnot
        exact (hnot (Finset.mem_univ ω)).elim
    rwa [hμ, hν] at hw
  · intro h f hf
    rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ =>
      calc
        (μ ω).toReal * f ω ≤ (c * (ν ω).toReal) * f ω :=
          mul_le_mul_of_nonneg_right (h ω) (hf ω)
        _ = c * ((ν ω).toReal * f ω) := by ring

/-- The joint integrand `(p a).toReal * (q a b).toReal * f b` is summable when `f` is bounded.
    This is the absolute-summability hypothesis behind Fubini for `expect_bind`. -/
theorem expect_bind_summable_of_bounded {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) {C : ℝ} (hbd : ∀ b, |f b| ≤ C) :
    Summable (fun ab : α × β =>
      (p ab.1).toReal * (q ab.1 ab.2).toReal * f ab.2) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le
      (g := fun ab : α × β => |(p ab.1).toReal * (q ab.1 ab.2).toReal * f ab.2|)
      (f := fun ab : α × β => (p ab.1).toReal * (q ab.1 ab.2).toReal * C)
      (fun _ => abs_nonneg _)
  · intro ⟨a, b⟩
    have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ (q a b).toReal := ENNReal.toReal_nonneg
    have hpq : 0 ≤ (p a).toReal * (q a b).toReal := mul_nonneg hp hq
    rw [abs_mul, abs_of_nonneg hpq]
    exact mul_le_mul_of_nonneg_left (hbd b) hpq
  · -- ∑'_{(a,b)} (p a).toReal * (q a b).toReal * C is summable
    have hbind : Summable (fun ab : α × β =>
        (p ab.1).toReal * (q ab.1 ab.2).toReal) := by
      have h_ennreal : ∑' ab : α × β, (p ab.1 * q ab.1 ab.2 : ENNReal) = 1 := by
        rw [ENNReal.tsum_prod']
        calc
          ∑' a, ∑' b, p a * q a b
              = ∑' a, p a * ∑' b, q a b := by
                simp [ENNReal.tsum_mul_left]
          _ = ∑' a, p a := by simp [PMF.tsum_coe]
          _ = 1 := PMF.tsum_coe p
      have h_ne_top : ∀ ab : α × β, (p ab.1 * q ab.1 ab.2 : ENNReal) ≠ ⊤ := fun ab =>
        ENNReal.mul_ne_top (PMF.apply_ne_top p ab.1) (PMF.apply_ne_top (q ab.1) ab.2)
      have h_summable_pq :
          Summable (fun ab : α × β => (p ab.1 * q ab.1 ab.2 : ENNReal).toReal) := by
        apply ENNReal.summable_toReal
        rw [h_ennreal]; exact ENNReal.one_ne_top
      have h_eq : (fun ab : α × β => (p ab.1).toReal * (q ab.1 ab.2).toReal) =
          (fun ab : α × β => (p ab.1 * q ab.1 ab.2 : ENNReal).toReal) := by
        funext ab; exact (ENNReal.toReal_mul (a := p ab.1) (b := q ab.1 ab.2)).symm
      rw [h_eq]; exact h_summable_pq
    exact hbind.mul_right C

/-- Expected value distributes over `PMF.bind`, under a bounded-`f` hypothesis. -/
theorem expect_bind_of_bounded {α β : Type*}
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) {C : ℝ} (hbd : ∀ b, |f b| ≤ C) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  -- Define the joint integrand (with `(a, b)` argument order matching uncurry).
  set F : α → β → ℝ := fun a b => (p a).toReal * (q a b).toReal * f b with hF
  -- Joint summability (over α × β).
  have h_summable_ab : Summable (Function.uncurry F) := by
    have := expect_bind_summable_of_bounded p q f hbd
    exact this
  -- For each `a`, inner sum over `b` is summable.
  have h_inner_a : ∀ a, Summable (F a) := by
    intro a
    have := expect_summable_of_bounded (q a) f hbd
    -- `(q a b).toReal * f b` is summable; multiply by `(p a).toReal` (a constant).
    simpa [hF, mul_assoc] using this.mul_left ((p a).toReal)
  -- For each `b`, inner sum over `a` is summable.
  have h_inner_b : ∀ b, Summable (fun a => F a b) := by
    intro b
    have h_pq_summable : Summable (fun a => (p a).toReal * (q a b).toReal) := by
      -- Bound: (p a).toReal * (q a b).toReal ≤ (p a).toReal.
      apply Summable.of_nonneg_of_le
          (g := fun a => (p a).toReal * (q a b).toReal)
          (f := fun a => (p a).toReal)
          (fun a => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      · intro a
        have hqb_le_one : (q a b).toReal ≤ 1 := by
          have := PMF.coe_le_one (q a) b
          exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top (q a) b)
            (by norm_num)).mpr this |>.trans_eq (by simp)
        exact (mul_le_of_le_one_right ENNReal.toReal_nonneg hqb_le_one)
      · exact pmf_toReal_summable p
    simpa [hF, mul_assoc] using h_pq_summable.mul_right (f b)
  -- Now: expand bind, use tsum_comm', and refold.
  have h_inner_real : ∀ b,
      ((∑' a, p a * q a b : ENNReal)).toReal =
        ∑' a, (p a).toReal * (q a b).toReal := by
    intro b
    rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top p a)
      (PMF.apply_ne_top (q a) b))]
    apply tsum_congr; intro a; exact ENNReal.toReal_mul
  -- LHS = ∑' b, (∑' a, p a * q a b).toReal * f b
  --     = ∑' b, (∑' a, (p a).toReal * (q a b).toReal) * f b
  --     = ∑' b, ∑' a, F a b
  -- RHS = ∑' a, (p a).toReal * ∑' b, (q a b).toReal * f b
  --     = ∑' a, ∑' b, F a b
  -- Fubini: ∑' b, ∑' a, F a b = ∑' a, ∑' b, F a b.
  simp only [expect, PMF.bind_apply]
  simp_rw [h_inner_real, ← tsum_mul_right]
  rw [h_summable_ab.tsum_comm' h_inner_a h_inner_b]
  apply tsum_congr; intro a
  rw [← tsum_mul_left]
  apply tsum_congr; intro b
  change F a b = (p a).toReal * ((q a b).toReal * f b)
  simp [hF, mul_assoc]

/-- Expected value distributes over `PMF.bind` for finite target types. -/
theorem expect_bind {α β : Type*} [Finite β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    expect (p.bind q) f = expect p (fun a => expect (q a) f) := by
  classical
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite f
  exact expect_bind_of_bounded p q f hC

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
      change Summable ({a : α | b = f a}.indicator (fun a => (p a).toReal))
      exact hp.indicator {a : α | b = f a}
    exact hs.mul_right (u b)

/-- Pushforward identity for weighted `ℝ≥0∞`-sums: summing `v` weighted by the
pushforward `PMF.map f p` equals summing `v ∘ f` weighted by `p`. This is the
finiteness-free engine behind `expect_map`: it holds unconditionally because
`ℝ≥0∞`-sums are reindexed without any summability side-condition. -/
theorem tsum_map_mul {α β : Type*} (f : α → β) (p : PMF α) (v : β → ENNReal) :
    ∑' b, (PMF.map f p) b * v b = ∑' a, p a * v (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  rw [tsum_eq_single (f a) (fun b hb => by simp [hb])]
  simp

/-- For a nonnegative integrand, `expect` is the real part of the `ℝ≥0∞`-valued
sum. This bridges `expect` to the unconditional `ℝ≥0∞` calculus. -/
theorem expect_eq_toReal_of_nonneg {Ω : Type*} (d : PMF Ω) (g : Ω → ℝ)
    (hg : ∀ ω, 0 ≤ g ω) :
    expect d g = (∑' ω, d ω * ENNReal.ofReal (g ω)).toReal := by
  rw [expect, ENNReal.tsum_toReal_eq
    (fun ω => ENNReal.mul_ne_top (PMF.apply_ne_top d ω) ENNReal.ofReal_ne_top)]
  refine tsum_congr (fun ω => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg ω)]

/-- Change of variables for `expect` along a pushforward, for a nonnegative
integrand. The finiteness-free special case of `expect_map`. -/
theorem expect_map_of_nonneg {α β : Type*} (f : α → β) (p : PMF α) (u : β → ℝ)
    (hu : ∀ b, 0 ≤ u b) :
    expect (PMF.map f p) u = expect p (fun a => u (f a)) := by
  rw [expect_eq_toReal_of_nonneg _ _ hu,
    expect_eq_toReal_of_nonneg _ _ (fun a => hu (f a))]
  congr 1
  exact tsum_map_mul f p (fun b => ENNReal.ofReal (u b))

/-- A family of finite `ℝ≥0∞` values has real-summable `toReal` parts iff its
`ℝ≥0∞`-sum is finite. -/
theorem summable_toReal_iff {γ : Type*} (H : γ → ENNReal) (hH : ∀ x, H x ≠ ⊤) :
    Summable (fun x => (H x).toReal) ↔ (∑' x, H x) ≠ ⊤ := by
  constructor
  · intro hs
    rw [show (∑' x, H x) = ∑' x, ENNReal.ofReal ((H x).toReal) from
      tsum_congr (fun x => (ENNReal.ofReal_toReal (hH x)).symm)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  · exact fun hne => ENNReal.summable_toReal hne

/-- Summability of a nonnegative weighted pushforward transfers across the map;
the summability counterpart of `tsum_map_mul`. -/
theorem summable_map_mul_iff_of_nonneg {α β : Type*} (f : α → β) (p : PMF α)
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    Summable (fun b => (PMF.map f p b).toReal * g b) ↔
      Summable (fun a => (p a).toReal * g (f a)) := by
  have hmap : (fun b => (PMF.map f p b).toReal * g b)
      = (fun b => (PMF.map f p b * ENNReal.ofReal (g b)).toReal) := by
    funext b; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg b)]
  have hp : (fun a => (p a).toReal * g (f a))
      = (fun a => (p a * ENNReal.ofReal (g (f a))).toReal) := by
    funext a; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg (f a))]
  rw [hmap, hp,
    summable_toReal_iff (fun b => PMF.map f p b * ENNReal.ofReal (g b))
      (fun b => ENNReal.mul_ne_top (PMF.apply_ne_top _ b) ENNReal.ofReal_ne_top),
    summable_toReal_iff (fun a => p a * ENNReal.ofReal (g (f a)))
      (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ a) ENNReal.ofReal_ne_top),
    tsum_map_mul f p (fun b => ENNReal.ofReal (g b))]

/-- When both nonnegative parts have summable weights, `expect` splits as the
difference of the expectations of the positive and negative parts. -/
theorem expect_split {Ω : Type*} (d : PMF Ω) (u : Ω → ℝ)
    (hpos : Summable (fun ω => (d ω).toReal * max (u ω) 0))
    (hneg : Summable (fun ω => (d ω).toReal * max (-(u ω)) 0)) :
    expect d u
      = expect d (fun ω => max (u ω) 0) - expect d (fun ω => max (-(u ω)) 0) := by
  simp only [expect]
  rw [← Summable.tsum_sub hpos hneg]
  refine tsum_congr (fun ω => ?_)
  rw [← mul_sub]
  congr 1
  rcases le_total 0 (u ω) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), sub_neg_eq_add, zero_add]

/-- **Change of variables for `expect` along a pushforward.** The expectation of
`u` under the pushforward `PMF.map f p` equals the expectation of `u ∘ f` under
`p`. This holds with no finiteness or boundedness hypotheses: the positive and
negative parts are handled through the unconditional `ℝ≥0∞` calculus, and the
non-summable case makes both sides vanish. -/
theorem expect_map {α β : Type*} (f : α → β) (p : PMF α) (u : β → ℝ) :
    expect (PMF.map f p) u = expect p (fun a => u (f a)) := by
  by_cases hsum : Summable (fun a => (p a).toReal * u (f a))
  · have habs : Summable (fun a => (p a).toReal * |u (f a)|) :=
      (summable_abs_iff.mpr hsum).congr
        (fun a => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
    have hpos_p : Summable (fun a => (p a).toReal * max (u (f a)) 0) :=
      Summable.of_nonneg_of_le
        (fun a => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
        (fun a => mul_le_mul_of_nonneg_left
          (max_le (le_abs_self _) (abs_nonneg _)) ENNReal.toReal_nonneg) habs
    have hneg_p : Summable (fun a => (p a).toReal * max (-(u (f a))) 0) :=
      Summable.of_nonneg_of_le
        (fun a => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
        (fun a => mul_le_mul_of_nonneg_left
          (max_le (neg_le_abs _) (abs_nonneg _)) ENNReal.toReal_nonneg) habs
    have hpos_map : Summable (fun b => (PMF.map f p b).toReal * max (u b) 0) :=
      (summable_map_mul_iff_of_nonneg f p (fun b => max (u b) 0)
        (fun b => le_max_right _ _)).mpr hpos_p
    have hneg_map : Summable (fun b => (PMF.map f p b).toReal * max (-(u b)) 0) :=
      (summable_map_mul_iff_of_nonneg f p (fun b => max (-(u b)) 0)
        (fun b => le_max_right _ _)).mpr hneg_p
    rw [expect_split (PMF.map f p) u hpos_map hneg_map,
      expect_split p (fun a => u (f a)) hpos_p hneg_p,
      expect_map_of_nonneg f p (fun b => max (u b) 0) (fun b => le_max_right _ _),
      expect_map_of_nonneg f p (fun b => max (-(u b)) 0) (fun b => le_max_right _ _)]
  · simp only [expect]
    rw [tsum_eq_zero_of_not_summable hsum]
    refine tsum_eq_zero_of_not_summable (fun hmapsum => hsum ?_)
    have habsmap : Summable (fun b => (PMF.map f p b).toReal * |u b|) :=
      (summable_abs_iff.mpr hmapsum).congr
        (fun b => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
    have habsp : Summable (fun a => (p a).toReal * |u (f a)|) :=
      (summable_map_mul_iff_of_nonneg f p (fun b => |u b|)
        (fun b => abs_nonneg _)).mp habsmap
    exact summable_abs_iff.mp
      (habsp.congr (fun a => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]))

end Probability
end Math
