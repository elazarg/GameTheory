/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Math.Probability.ResetActivation

/-!
# Stitched concentration for bounded martingales

This file proves a concrete horizon-free concentration boundary for a
real-valued martingale with pointwise bounded increments.

The proof has four layers:

* conditional Hoeffding turns centered increments in `[-L, L]` into
  sub-Gaussian increments;
* conditional Jensen makes the exponential of a martingale a nonnegative
  submartingale;
* Doob's maximal inequality yields a finite-horizon Chernoff bound;
* dyadic stitching with a summable geometric budget yields one bound for
  every positive time.

The final theorems are valid conditionally after a finite stopping-time reset.
They use the regular conditional law at the stopping-time sigma-algebra, so
history-dependent reset times and history-selected post-reset monitors are
covered whenever the stated conditional martingale and increment hypotheses
hold.
-/

open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

open Filter MeasureTheory Real Set Function
open ProbabilityTheory

namespace Math.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}

theorem exp_smul_submartingale [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (t : ℝ)
    (hint : ∀ n, Integrable (fun ω => exp (t * M n ω)) μ) :
    Submartingale (fun n ω => exp (t * M n ω)) 𝒢 μ := by
  let scaled : ℕ → Ω → ℝ := t • M
  have hscaled : Martingale scaled 𝒢 μ := hM.smul t
  have hint' : ∀ n, Integrable (fun ω => exp (scaled n ω)) μ := by
    simpa [scaled, Pi.smul_apply, smul_eq_mul] using hint
  refine ⟨?_, ?_, hint⟩
  · intro n
    simpa [scaled, Pi.smul_apply, smul_eq_mul] using
      continuous_exp.comp_stronglyMeasurable (hscaled.stronglyMeasurable n)
  · intro i j hij
    have hjensen :
        exp ∘ μ[scaled j | 𝒢 i] ≤ᵐ[μ] μ[exp ∘ scaled j | 𝒢 i] :=
      convexOn_exp.map_condExp_le_univ (𝒢.le i)
        continuous_exp.lowerSemicontinuous (hscaled.integrable j) (hint' j)
    change
      (fun ω => exp ((μ[scaled j | 𝒢 i]) ω)) ≤ᵐ[μ]
        μ[(fun ω => exp (scaled j ω)) | 𝒢 i] at hjensen
    filter_upwards [hscaled.condExp_ae_eq hij, hjensen] with ω heq hle
    rw [heq] at hle
    simpa [scaled, Pi.smul_apply, smul_eq_mul] using hle

theorem measure_max_ge_le_exp_add [IsProbabilityMeasure μ]
    [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (c : ℕ → ℝ≥0)
    (hsubG : ∀ n, HasSubgaussianMGF (M n) (c n) μ)
    (N : ℕ) {x t : ℝ} (ht : 0 < t) :
    μ.real {ω |
        x ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => M k ω)} ≤
      exp (-t * x + c N * t ^ 2 / 2) := by
  let e : ℝ≥0 := ⟨exp (t * x), (exp_pos _).le⟩
  let X : ℕ → Ω → ℝ := fun n ω => exp (t * M n ω)
  have hX : Submartingale X 𝒢 μ := by
    apply exp_smul_submartingale hM t
    intro n
    exact (hsubG n).integrable_exp_mul t
  let A : Set Ω := {ω |
    x ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => M k ω)}
  let B : Set Ω := {ω |
    (e : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => X k ω)}
  have hAB : A ⊆ B := by
    intro ω hω
    simp only [A, Set.mem_setOf_eq] at hω
    simp only [B, Set.mem_setOf_eq]
    rw [Finset.le_sup'_iff] at hω ⊢
    obtain ⟨k, hk, hkx⟩ := hω
    exact ⟨k, hk, by
      change exp (t * x) ≤ exp (t * M k ω)
      rw [exp_le_exp]
      exact mul_le_mul_of_nonneg_left hkx ht.le⟩
  have hmax := maximal_ineq hX (fun _ _ => (exp_pos _).le) (ε := e) N
  have hset :
      ∫ ω in B, X N ω ∂μ ≤ ∫ ω, X N ω ∂μ := by
    exact setIntegral_le_integral (hX.integrable N)
      (ae_of_all _ fun _ => (exp_pos _).le)
  have hmono : μ A ≤ μ B := measure_mono hAB
  have hleft : (e : ℝ≥0∞) * μ A ≤
      ENNReal.ofReal (∫ ω, X N ω ∂μ) := by
    calc
      (e : ℝ≥0∞) * μ A ≤ (e : ℝ≥0∞) * μ B := by
        gcongr
      _ ≤ ENNReal.ofReal (∫ ω in B, X N ω ∂μ) := by simpa [B] using hmax
      _ ≤ ENNReal.ofReal (∫ ω, X N ω ∂μ) := ENNReal.ofReal_le_ofReal hset
  have hreal :
      ((e : ℝ≥0∞) * μ A).toReal ≤
        (ENNReal.ofReal (∫ ω, X N ω ∂μ)).toReal :=
    ENNReal.toReal_mono (by simp) hleft
  have hmgf : ∫ ω, X N ω ∂μ ≤ exp (c N * t ^ 2 / 2) := by
    simpa [X, mgf] using (hsubG N).mgf_le t
  have hposint : 0 ≤ ∫ ω, X N ω ∂μ :=
    integral_nonneg fun _ => (exp_pos _).le
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal hposint] at hreal
  change exp (t * x) * μ.real A ≤ ∫ ω, X N ω ∂μ at hreal
  have hdiv :
      μ.real A ≤ exp (-t * x) * ∫ ω, X N ω ∂μ := by
    calc
      μ.real A =
          exp (-t * x) * (exp (t * x) * μ.real A) := by
            rw [← mul_assoc, ← exp_add]
            ring_nf
            simp
      _ ≤ exp (-t * x) * ∫ ω, X N ω ∂μ :=
        mul_le_mul_of_nonneg_left hreal (exp_pos _).le
  calc
    μ.real A ≤ exp (-t * x) * ∫ ω, X N ω ∂μ := hdiv
    _ ≤ exp (-t * x) * exp (c N * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (-t * x + c N * t ^ 2 / 2) := (exp_add _ _).symm

/-- A Chernoff threshold written so that substitution into the exponential
bound returns exactly the requested probability budget. -/
noncomputable def chernoffThreshold (c t alpha : ℝ) : ℝ :=
  (log (1 / alpha) + c * t ^ 2 / 2) / t

theorem measure_max_ge_chernoffThreshold_le [IsProbabilityMeasure μ]
    [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (c : ℕ → ℝ≥0)
    (hsubG : ∀ n, HasSubgaussianMGF (M n) (c n) μ)
    (N : ℕ) {alpha t : ℝ} (halpha : 0 < alpha) (ht : 0 < t) :
    μ.real {ω |
        chernoffThreshold (c N) t alpha ≤
          (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
            (fun k => M k ω)} ≤ alpha := by
  calc
    μ.real {ω |
        chernoffThreshold (c N) t alpha ≤
          (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
            (fun k => M k ω)}
        ≤ exp (-t * chernoffThreshold (c N) t alpha +
            c N * t ^ 2 / 2) :=
      measure_max_ge_le_exp_add hM c hsubG N ht
    _ = alpha := by
      rw [show -t * chernoffThreshold (c N) t alpha +
          c N * t ^ 2 / 2 = log alpha by
        rw [chernoffThreshold, show log (1 / alpha) = -log alpha by
          simp [one_div]]
        field_simp [ht.ne']
        ring]
      exact exp_log halpha

/-- Conditional Hoeffding lemma in the form needed by bounded martingale
increments. Pointwise bounds avoid any exceptional-set transport through the
regular conditional kernel. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable[mΩ] X) (hbound : ∀ ω, X ω ∈ Set.Icc a b)
    (hcenter : μ[X | m] =ᵐ[μ.trim hm] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  rw [HasCondSubgaussianMGF]
  refine ⟨?_, ?_⟩
  · have hi : ∀ t, Integrable (fun ω => exp (t * X ω)) μ :=
      fun t => integrable_exp_mul_of_mem_Icc
        (hX.aemeasurable (μ := μ)) (ae_of_all _ hbound)
    rw [condExpKernel_comp_trim (mΩ := mΩ) (μ := μ) hm]
    exact hi
  · have hXint : Integrable X μ :=
      Integrable.of_mem_Icc a b (hX.aemeasurable (μ := μ))
        (ae_of_all _ hbound)
    have hcondKernel :=
      condExp_ae_eq_trim_integral_condExpKernel
        (mΩ := mΩ) (m := m) hm hXint
    filter_upwards [hcenter, hcondKernel] with root hcenter_root hkernel_root
    have hintegral :
        ∫ x, X x ∂(condExpKernel (mΩ := mΩ) μ m root) = 0 := by
      rw [← hkernel_root, hcenter_root]
      rfl
    exact
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hX.aemeasurable
          (μ := condExpKernel (mΩ := mΩ) μ m root))
        (ae_of_all _ hbound) hintegral).mgf_le

/-- Filtration shifted forward by one time step. -/
def filtrationSucc (filtration : Filtration ℕ mΩ) : Filtration ℕ mΩ where
  seq n := filtration (n + 1)
  mono' _ _ h := filtration.mono (Nat.add_le_add_right h 1)
  le' n := filtration.le (n + 1)

/-- One-step difference of a real process. -/
def processIncrement (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  M (n + 1) ω - M n ω

theorem sum_processIncrement_eq
    (hzero : ∀ ω, M 0 ω = 0) (n : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range n, processIncrement M i ω = M n ω := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [processIncrement]

theorem condExp_processIncrement_eq_zero
    [IsFiniteMeasure μ]
    (hM : Martingale M 𝒢 μ) (n : ℕ) :
    μ[processIncrement M n | 𝒢 n] =ᵐ[μ] 0 := by
  have hsub :
      μ[(fun ω => M (n + 1) ω - M n ω) | 𝒢 n] =ᵐ[μ]
        μ[M (n + 1) | 𝒢 n] - μ[M n | 𝒢 n] :=
    condExp_sub (hM.integrable (n + 1)) (hM.integrable n) (𝒢 n)
  have hnext := hM.condExp_ae_eq (Nat.le_succ n)
  have hcurrent :
      μ[M n | 𝒢 n] =ᵐ[μ] M n :=
    Filter.Eventually.of_forall fun ω =>
      congrFun (condExp_of_stronglyMeasurable (𝒢.le n)
        (hM.stronglyMeasurable n) (hM.integrable n)) ω
  filter_upwards [hsub, hnext, hcurrent] with ω hsubω hnextω hcurrentω
  change
    (μ[(fun x => M (n + 1) x - M n x) | 𝒢 n]) ω = 0
  rw [hsubω, Pi.sub_apply]
  have hnextω' : μ[M (n + 1) | 𝒢 n] ω = M n ω := by
    simpa [Nat.succ_eq_add_one] using hnextω
  rw [hnextω', hcurrentω, sub_self]

theorem hasSubgaussianMGF_martingale_of_boundedIncrements
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hM : Martingale M 𝒢 μ) (hzero : ∀ ω, M 0 ω = 0)
    {L : ℝ}
    (hbound : ∀ n ω, processIncrement M n ω ∈ Set.Icc (-L) L)
    (n : ℕ) :
    HasSubgaussianMGF (M n)
      ((n : ℝ≥0) * ((‖L - -L‖₊ / 2) ^ 2)) μ := by
  let difference : ℕ → Ω → ℝ := processIncrement M
  let variance : ℝ≥0 := (‖L - -L‖₊ / 2) ^ 2
  let shifted := filtrationSucc 𝒢
  have hdifference_measurable (i : ℕ) :
      Measurable[mΩ] (difference i) := by
    exact ((hM.stronglyMeasurable (i + 1)).sub
      ((hM.stronglyMeasurable i).mono
        (𝒢.mono (Nat.le_succ i)))).measurable.le (𝒢.le (i + 1))
  have hdifference_adapted : StronglyAdapted shifted difference := by
    intro i
    exact ((hM.stronglyMeasurable (i + 1)).sub
      ((hM.stronglyMeasurable i).mono
        (𝒢.mono (Nat.le_succ i)))).mono le_rfl
  have hmean_zero :
      ∫ ω, difference 0 ω ∂μ = 0 := by
    rw [show difference 0 = fun ω => M 1 ω - M 0 ω by
      funext ω
      simp [difference, processIncrement]]
    rw [integral_sub (hM.integrable 1) (hM.integrable 0)]
    apply sub_eq_zero.mpr
    simpa using
      (hM.setIntegral_eq (Nat.zero_le 1) MeasurableSet.univ).symm
  have hfirst : HasSubgaussianMGF (difference 0) variance μ := by
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hdifference_measurable 0).aemeasurable
      (ae_of_all _ (hbound 0)) hmean_zero
  have hconditional (i : ℕ) :
      HasCondSubgaussianMGF (shifted i) (shifted.le i)
        (difference (i + 1)) variance μ := by
    have hcenter_mu :
        μ[difference (i + 1) | shifted i] =ᵐ[μ] 0 := by
      simpa [difference, shifted, filtrationSucc] using
        condExp_processIncrement_eq_zero hM (i + 1)
    have hcenter_trim :
        μ[difference (i + 1) | shifted i] =ᵐ[μ.trim (shifted.le i)] 0 := by
      exact
        (stronglyMeasurable_condExp.ae_eq_trim_iff (shifted.le i)
          stronglyMeasurable_zero).mpr hcenter_mu
    exact hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
      (shifted.le i) (hdifference_measurable (i + 1))
      (hbound (i + 1)) hcenter_trim
  have hsum :
      HasSubgaussianMGF
        (fun ω => ∑ i ∈ Finset.range n, difference i ω)
        (∑ _i ∈ Finset.range n, variance) μ :=
    HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      hdifference_adapted hfirst n fun i _ => hconditional i
  have hsum_eq :
      (fun ω => ∑ i ∈ Finset.range n, difference i ω) = M n := by
    funext ω
    exact sum_processIncrement_eq hzero n ω
  simpa [variance] using hsum.congr (ae_of_all _ fun ω =>
    congr_fun hsum_eq ω)

/-- Crossing event for one half-open dyadic block. The boundary is constant
on the block and calibrated against the maximum through its right endpoint. -/
def dyadicBlockCrossing
    (M : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0)
    (rate budget : ℕ → ℝ) (j : ℕ) : Set Ω :=
  {ω | ∃ n, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧
    chernoffThreshold (c (2 ^ (j + 1))) (rate j) (budget j) ≤ M n ω}

/-- Pointwise stitched boundary obtained from the unique dyadic block
containing a positive time. -/
noncomputable def stitchedBoundary
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ) (n : ℕ) : ℝ :=
  let j := Nat.log 2 n
  chernoffThreshold (c (2 ^ (j + 1))) (rate j) (budget j)

theorem anytimeCrossing_subset_iUnion_dyadicBlockCrossing
    (M : ℕ → Ω → ℝ) (c : ℕ → ℝ≥0)
    (rate budget : ℕ → ℝ) :
    {ω | ∃ n, 0 < n ∧ stitchedBoundary c rate budget n ≤ M n ω} ⊆
      ⋃ j, dyadicBlockCrossing M c rate budget j := by
  intro ω hω
  rcases hω with ⟨n, hn, hcross⟩
  rw [Set.mem_iUnion]
  refine ⟨Nat.log 2 n, ?_⟩
  exact ⟨n,
    Nat.pow_log_le_self 2 hn.ne',
    Nat.lt_pow_succ_log_self one_lt_two n,
    by simpa [stitchedBoundary] using hcross⟩

theorem measurableSet_anytimeCrossing
    (hM : ∀ n, Measurable[mΩ] (M n))
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ) :
    MeasurableSet[mΩ]
      {ω | ∃ n, 0 < n ∧ stitchedBoundary c rate budget n ≤ M n ω} := by
  let positiveTime := {n : ℕ // 0 < n}
  have heq :
      {ω | ∃ n, 0 < n ∧ stitchedBoundary c rate budget n ≤ M n ω} =
        ⋃ n : positiveTime,
          {ω | stitchedBoundary c rate budget n ≤ M n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn, hcross⟩
      exact ⟨⟨n, hn⟩, hcross⟩
    · rintro ⟨⟨n, hn⟩, hcross⟩
      exact ⟨n, hn, hcross⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (hM n)

theorem measurableSet_dyadicBlockCrossing
    (hM : ∀ n, Measurable[mΩ] (M n))
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ) (j : ℕ) :
    MeasurableSet[mΩ] (dyadicBlockCrossing M c rate budget j) := by
  let block := {n : ℕ // 2 ^ j ≤ n ∧ n < 2 ^ (j + 1)}
  have heq :
      dyadicBlockCrossing M c rate budget j =
        ⋃ n : block,
          {ω | chernoffThreshold (c (2 ^ (j + 1)))
            (rate j) (budget j) ≤ M n ω} := by
    ext ω
    simp only [dyadicBlockCrossing, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hnleft, hnright, hn⟩
      exact ⟨⟨n, hnleft, hnright⟩, hn⟩
    · rintro ⟨⟨n, hnleft, hnright⟩, hn⟩
      exact ⟨n, hnleft, hnright, hn⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (hM n)

theorem measurableSet_iUnion_dyadicBlockCrossing
    (hM : ∀ n, Measurable[mΩ] (M n))
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ) :
    MeasurableSet[mΩ] (⋃ j, dyadicBlockCrossing M c rate budget j) :=
  MeasurableSet.iUnion fun j =>
    measurableSet_dyadicBlockCrossing hM c rate budget j

theorem measure_dyadicBlockCrossing_le [IsProbabilityMeasure μ]
    [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (c : ℕ → ℝ≥0)
    (hsubG : ∀ n, HasSubgaussianMGF (M n) (c n) μ)
    (rate budget : ℕ → ℝ) (j : ℕ)
    (hbudget : 0 < budget j) (hrate : 0 < rate j) :
    μ (dyadicBlockCrossing M c rate budget j) ≤
      ENNReal.ofReal (budget j) := by
  let N := 2 ^ (j + 1)
  let threshold := chernoffThreshold (c N) (rate j) (budget j)
  let A := dyadicBlockCrossing M c rate budget j
  let B : Set Ω := {ω |
    threshold ≤ (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun k => M k ω)}
  have hAB : A ⊆ B := by
    intro ω hω
    rcases hω with ⟨n, hnleft, hnright, hn⟩
    simp only [B, Set.mem_setOf_eq]
    rw [Finset.le_sup'_iff]
    exact ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hnright.le), hn⟩
  have hrealB : μ.real B ≤ budget j := by
    simpa [B, threshold, N] using
      measure_max_ge_chernoffThreshold_le hM c hsubG N hbudget hrate
  have hrealA : μ.real A ≤ budget j :=
    (ENNReal.toReal_mono (measure_ne_top μ B) (measure_mono hAB)).trans hrealB
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ A) hbudget.le]
  exact hrealA

/-- Dyadic stitching: if each positive block budget is calibrated by
`chernoffThreshold` and the budgets are summable, the probability of any
block crossing is at most their total budget. -/
theorem measure_iUnion_dyadicBlockCrossing_le [IsProbabilityMeasure μ]
    [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (c : ℕ → ℝ≥0)
    (hsubG : ∀ n, HasSubgaussianMGF (M n) (c n) μ)
    (rate budget : ℕ → ℝ)
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    μ (⋃ j, dyadicBlockCrossing M c rate budget j) ≤ delta := by
  calc
    μ (⋃ j, dyadicBlockCrossing M c rate budget j) ≤
        ∑' j, μ (dyadicBlockCrossing M c rate budget j) :=
      measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal (budget j) :=
      ENNReal.tsum_le_tsum fun j =>
        measure_dyadicBlockCrossing_le hM c hsubG rate budget j
          (hbudget j) (hrate j)
    _ ≤ delta := hsum

/-- Horizon-free stitched boundary: the probability of crossing at any
positive time is bounded by the sum of the dyadic block budgets. -/
theorem measure_exists_stitchedBoundary_le [IsProbabilityMeasure μ]
    [SigmaFiniteFiltration μ 𝒢]
    (hM : Martingale M 𝒢 μ) (c : ℕ → ℝ≥0)
    (hsubG : ∀ n, HasSubgaussianMGF (M n) (c n) μ)
    (rate budget : ℕ → ℝ)
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    μ {ω | ∃ n, 0 < n ∧ stitchedBoundary c rate budget n ≤ M n ω} ≤
      delta := by
  calc
    μ {ω | ∃ n, 0 < n ∧ stitchedBoundary c rate budget n ≤ M n ω} ≤
        μ (⋃ j, dyadicBlockCrossing M c rate budget j) :=
      measure_mono
        (anytimeCrossing_subset_iUnion_dyadicBlockCrossing M c rate budget)
    _ ≤ delta :=
      measure_iUnion_dyadicBlockCrossing_le hM c hsubG rate budget
        hbudget hrate hsum

/-- Cumulative Hoeffding variance proxy for increments in `[-L,L]`. -/
noncomputable def boundedIncrementVariance (L : ℝ) (n : ℕ) : ℝ≥0 :=
  (n : ℝ≥0) * ((‖L - -L‖₊ / 2) ^ 2)

/-- Geometric allocation of a total real error budget to dyadic blocks. -/
noncomputable def geometricBlockBudget (alpha : ℝ) (j : ℕ) : ℝ :=
  alpha / 2 / 2 ^ j

theorem geometricBlockBudget_pos {alpha : ℝ} (halpha : 0 < alpha) (j : ℕ) :
    0 < geometricBlockBudget alpha j := by
  unfold geometricBlockBudget
  positivity

theorem tsum_ofReal_geometricBlockBudget {alpha : ℝ} (halpha : 0 ≤ alpha) :
    ∑' j, ENNReal.ofReal (geometricBlockBudget alpha j) =
      ENNReal.ofReal alpha := by
  have hnonneg : ∀ j, 0 ≤ geometricBlockBudget alpha j := by
    intro j
    unfold geometricBlockBudget
    positivity
  have hsummable : Summable (geometricBlockBudget alpha) := by
    change Summable (fun j : ℕ => alpha / 2 / 2 ^ j)
    exact summable_geometric_two' alpha
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
  congr 1
  change (∑' j : ℕ, alpha / 2 / 2 ^ j) = alpha
  exact tsum_geometric_two' alpha

/-- Positive reciprocal-square-root rate used for the canonical stitched
boundary. -/
noncomputable def inverseSqrtDyadicRate (j : ℕ) : ℝ :=
  1 / sqrt (2 ^ (j + 1) : ℝ)

theorem inverseSqrtDyadicRate_pos (j : ℕ) :
    0 < inverseSqrtDyadicRate j := by
  unfold inverseSqrtDyadicRate
  positivity

/-- The canonical block threshold, divided by the left endpoint of the
dyadic block. This is the natural upper bound for the boundary-to-time ratio
inside that block. -/
noncomputable def geometricBlockRatio
    (L alpha : ℝ) (j : ℕ) : ℝ :=
  chernoffThreshold
      (boundedIncrementVariance L (2 ^ (j + 1)))
      (inverseSqrtDyadicRate j)
      (geometricBlockBudget alpha j) /
    (2 ^ j : ℕ)

theorem geometricBlockRatio_eq (L alpha : ℝ) (j : ℕ) :
    geometricBlockRatio L alpha j =
      2 *
        (Real.log (1 / geometricBlockBudget alpha j) +
          ((‖L - -L‖₊ / 2 : ℝ≥0) : ℝ) ^ 2 / 2) /
        Real.sqrt (2 ^ (j + 1) : ℝ) := by
  rw [geometricBlockRatio, chernoffThreshold,
    boundedIncrementVariance, inverseSqrtDyadicRate]
  have hpow : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have hsqrt : Real.sqrt (2 ^ (j + 1) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpow)
  have hratesq :
      (1 / Real.sqrt (2 ^ (j + 1) : ℝ)) ^ 2 =
        1 / (2 ^ (j + 1) : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hpow.le]
  rw [hratesq]
  push_cast
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring_nf

theorem log_inv_geometricBlockBudget
    {alpha : ℝ} (halpha : 0 < alpha) (j : ℕ) :
    Real.log (1 / geometricBlockBudget alpha j) =
      (j + 1 : ℕ) * Real.log 2 - Real.log alpha := by
  rw [geometricBlockBudget]
  have hid : 1 / (alpha / 2 / (2 : ℝ) ^ j) =
      (2 : ℝ) ^ (j + 1) / alpha := by
    rw [div_div, one_div_div, pow_succ]
    ring_nf
  rw [hid, Real.log_div (by positivity) halpha.ne', Real.log_pow]

theorem sqrt_two_pow (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ n) = Real.sqrt 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The canonical dyadic block ratio tends to zero. The proof reduces the
ratio to a linear numerator divided by `sqrt 2 ^ j`. -/
theorem tendsto_geometricBlockRatio
    (L : ℝ) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (geometricBlockRatio L alpha) atTop (𝓝 0) := by
  have hratio (j : ℕ) :
      geometricBlockRatio L alpha j =
        (2 / Real.sqrt 2) * Real.log 2 *
            ((j : ℝ) / Real.sqrt 2 ^ j) +
          (2 / Real.sqrt 2) *
            (Real.log 2 - Real.log alpha +
              ((‖L - -L‖₊ / 2 : ℝ≥0) : ℝ) ^ 2 / 2) *
            (1 / Real.sqrt 2 ^ j) := by
    rw [geometricBlockRatio_eq,
      log_inv_geometricBlockBudget halpha, sqrt_two_pow]
    push_cast
    have hsqrtTwo : Real.sqrt 2 ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hsqrtTwo]
    ring_nf
  have hlinear :
      Tendsto (fun j : ℕ => (j : ℝ) / Real.sqrt 2 ^ j)
        atTop (𝓝 0) := by
    simpa only [pow_one] using
      tendsto_pow_const_div_const_pow_of_one_lt 1
        Real.one_lt_sqrt_two
  have hconst :
      Tendsto (fun j : ℕ => (1 : ℝ) / Real.sqrt 2 ^ j)
        atTop (𝓝 0) := by
    simpa using
      tendsto_pow_const_div_const_pow_of_one_lt 0
        Real.one_lt_sqrt_two
  convert
    (((hlinear.const_mul ((2 / Real.sqrt 2) * Real.log 2)).add
      (hconst.const_mul
        ((2 / Real.sqrt 2) *
          (Real.log 2 - Real.log alpha +
            ((‖L - -L‖₊ / 2 : ℝ≥0) : ℝ) ^ 2 / 2))))) using 1
  · funext j
    rw [hratio]
  · ring_nf

theorem tendsto_natLog_two_atTop :
    Tendsto (Nat.log 2) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro j
  exact eventually_atTop.2
    ⟨2 ^ j, fun n hn => Nat.le_log_of_pow_le one_lt_two hn⟩

theorem geometricBlockThreshold_nonneg
    (L : ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) (j : ℕ) :
    0 ≤ chernoffThreshold
      (boundedIncrementVariance L (2 ^ (j + 1)))
      (inverseSqrtDyadicRate j)
      (geometricBlockBudget alpha j) := by
  have hbudget_pos := geometricBlockBudget_pos halpha j
  have hbudget_le : geometricBlockBudget alpha j ≤ 1 := by
    rw [geometricBlockBudget]
    have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    calc
      alpha / 2 / 2 ^ j ≤ alpha := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).2
        nlinarith
      _ ≤ 1 := halpha_one
  have hlog :
      0 ≤ Real.log (1 / geometricBlockBudget alpha j) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hbudget_pos).2 (by simpa using hbudget_le)
  rw [chernoffThreshold]
  exact div_nonneg
    (add_nonneg hlog (by
      exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
        (by norm_num)))
    (inverseSqrtDyadicRate_pos j).le

theorem geometricBlockRatio_nonneg
    (L : ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) (j : ℕ) :
    0 ≤ geometricBlockRatio L alpha j := by
  rw [geometricBlockRatio]
  exact div_nonneg
    (geometricBlockThreshold_nonneg L halpha halpha_one j)
    (by positivity)

theorem stitchedBoundary_div_le_geometricBlockRatio
    (L : ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) {n : ℕ} (hn : 0 < n) :
    stitchedBoundary (boundedIncrementVariance L)
          inverseSqrtDyadicRate (geometricBlockBudget alpha) n / n ≤
      geometricBlockRatio L alpha (Nat.log 2 n) := by
  let j := Nat.log 2 n
  have hpow_nat : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpow_real : (2 ^ j : ℕ) ≤ (n : ℝ) := by
    exact_mod_cast hpow_nat
  have hthreshold :
      0 ≤ chernoffThreshold
        (boundedIncrementVariance L (2 ^ (j + 1)))
        (inverseSqrtDyadicRate j)
        (geometricBlockBudget alpha j) :=
    geometricBlockThreshold_nonneg L halpha halpha_one j
  rw [stitchedBoundary, geometricBlockRatio]
  exact div_le_div_of_nonneg_left hthreshold (by positivity) hpow_real

/-- The explicit geometric stitched boundary is sublinear. This supplies the
rate hypothesis needed by the positive-drift activation lemmas. -/
theorem tendsto_geometricStitchedBoundary_div_natCast
    (L : ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        stitchedBoundary (boundedIncrementVariance L)
          inverseSqrtDyadicRate (geometricBlockBudget alpha) n / n)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun n : ℕ => geometricBlockRatio L alpha (Nat.log 2 n))
        atTop (𝓝 0) :=
    (tendsto_geometricBlockRatio L halpha).comp
      tendsto_natLog_two_atTop
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn_nonneg : (0 : ℝ) ≤ n := by positivity
    rw [stitchedBoundary]
    exact div_nonneg
      (geometricBlockThreshold_nonneg L halpha halpha_one
        (Nat.log 2 n))
      hn_nonneg
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact stitchedBoundary_div_le_geometricBlockRatio
      L halpha halpha_one hn
  · exact hupper

/-- An eventually linear signal eventually crosses the concrete geometric
stitched boundary. -/
theorem exists_geometricStitchedBoundary_lt_of_eventually_linear
    (signal : ℕ → ℝ) (L : ℝ) {alpha c : ℝ}
    (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) (hc : 0 < c)
    (hsignal : ∀ᶠ n in atTop, c * n ≤ signal n) :
    ∃ n,
      stitchedBoundary (boundedIncrementVariance L)
        inverseSqrtDyadicRate (geometricBlockBudget alpha) n <
          signal n :=
  exists_boundary_crossing_of_sublinear signal _ hc hsignal
    (tendsto_geometricStitchedBoundary_div_natCast
      L halpha halpha_one)

/-- Stitched maximal concentration for a martingale with pointwise bounded
increments. -/
theorem measure_iUnion_dyadicBlockCrossing_le_of_boundedIncrements
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hM : Martingale M 𝒢 μ) (hzero : ∀ ω, M 0 ω = 0)
    {L : ℝ}
    (hbound : ∀ n ω, processIncrement M n ω ∈ Set.Icc (-L) L)
    (rate budget : ℕ → ℝ)
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    μ (⋃ j, dyadicBlockCrossing M
      (boundedIncrementVariance L) rate budget j) ≤ delta := by
  apply measure_iUnion_dyadicBlockCrossing_le hM
  · intro n
    exact hasSubgaussianMGF_martingale_of_boundedIncrements
      hM hzero hbound n
  · exact hbudget
  · exact hrate
  · exact hsum

/-- Concrete anytime bound for a bounded-increment martingale. It uses
geometric block budgets and reciprocal-square-root Chernoff rates. -/
theorem measure_exists_geometricStitchedBoundary_le_of_boundedIncrements
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hM : Martingale M 𝒢 μ) (hzero : ∀ ω, M 0 ω = 0)
    {L alpha : ℝ} (halpha : 0 < alpha)
    (hbound : ∀ n ω, processIncrement M n ω ∈ Set.Icc (-L) L) :
    μ {ω | ∃ n, 0 < n ∧
        stitchedBoundary (boundedIncrementVariance L)
          inverseSqrtDyadicRate (geometricBlockBudget alpha) n ≤ M n ω} ≤
      ENNReal.ofReal alpha := by
  apply measure_exists_stitchedBoundary_le hM
  · intro n
    exact hasSubgaussianMGF_martingale_of_boundedIncrements
      hM hzero hbound n
  · exact geometricBlockBudget_pos halpha
  · exact inverseSqrtDyadicRate_pos
  · rw [tsum_ofReal_geometricBlockBudget halpha.le]

/-- Conditional stitched validity after a stopping time. The hypotheses say
that, under the regular conditional law at the reset sigma-algebra, the
post-reset process is a martingale with the displayed sub-Gaussian parameters.
The conclusion is therefore a pointwise conditional probability bound. -/
theorem ae_conditional_measure_iUnion_dyadicBlockCrossing_le
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (post : ℕ → Ω → ℝ) (postFiltration : Filtration ℕ mΩ)
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ)
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale post postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hsubG :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        ∀ n, HasSubgaussianMGF (post n) (c n)
          (condExpKernel μ hreset.measurableSpace root))
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
      (condExpKernel μ hreset.measurableSpace root)
          (⋃ j, dyadicBlockCrossing post c rate budget j) ≤ delta := by
  filter_upwards [hmartingale, hsubG] with root hmartingale_root hsubG_root
  letI : IsProbabilityMeasure
      (condExpKernel μ hreset.measurableSpace root) :=
    IsMarkovKernel.isProbabilityMeasure root
  exact measure_iUnion_dyadicBlockCrossing_le
    hmartingale_root c hsubG_root rate budget hbudget hrate hsum

/-- Integrating a regular-conditional probability bound gives the
corresponding unconditional bound. -/
theorem measure_le_of_ae_condExpKernel_le
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {event : Set Ω} (hevent : MeasurableSet[mΩ] event)
    {delta : ℝ≥0∞}
    (hconditional :
      ∀ᵐ root ∂μ.trim hm,
        condExpKernel (mΩ := mΩ) μ m root event ≤ delta) :
    μ event ≤ delta := by
  rw [← condExpKernel_comp_trim (mΩ := mΩ) (μ := μ) hm]
  rw [Measure.bind_apply hevent (Kernel.aemeasurable _)]
  calc
    ∫⁻ root, condExpKernel (mΩ := mΩ) μ m root event ∂μ.trim hm ≤
        ∫⁻ _root, delta ∂μ.trim hm :=
      lintegral_mono_ae hconditional
    _ = delta := by
      rw [lintegral_const]
      have huniv : (μ.trim hm) Set.univ = 1 := by
        rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]
      rw [huniv, mul_one]

/-- Increment of a process measured from a finite reset time. -/
def postResetIncrement
    (M : ℕ → Ω → ℝ) (reset : Ω → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  M (reset ω + n) ω - M (reset ω) ω

/-- Stopping-time conditional stitched bound stated directly for increments
from a reset. -/
theorem ae_conditional_measure_iUnion_postResetIncrement_le
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (postFiltration : Filtration ℕ mΩ)
    (c : ℕ → ℝ≥0) (rate budget : ℕ → ℝ)
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale (postResetIncrement M reset) postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hsubG :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        ∀ n, HasSubgaussianMGF (postResetIncrement M reset n) (c n)
          (condExpKernel μ hreset.measurableSpace root))
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
      (condExpKernel μ hreset.measurableSpace root)
          (⋃ j, dyadicBlockCrossing
            (postResetIncrement M reset) c rate budget j) ≤ delta :=
  ae_conditional_measure_iUnion_dyadicBlockCrossing_le hreset
    (postResetIncrement M reset) postFiltration c rate budget
    hmartingale hsubG hbudget hrate hsum

/-- Stopping-time-valid stitched concentration for post-reset martingale
increments with a pointwise increment bound. -/
theorem ae_conditional_measure_iUnion_postResetIncrement_le_of_boundedIncrements
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (postFiltration : Filtration ℕ mΩ)
    {L : ℝ} (rate budget : ℕ → ℝ)
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale (postResetIncrement M reset) postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hbound :
      ∀ n ω,
        processIncrement (postResetIncrement M reset) n ω ∈
          Set.Icc (-L) L)
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
      (condExpKernel μ hreset.measurableSpace root)
          (⋃ j, dyadicBlockCrossing
            (postResetIncrement M reset)
            (boundedIncrementVariance L) rate budget j) ≤ delta := by
  have hsubG :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        ∀ n, HasSubgaussianMGF (postResetIncrement M reset n)
          (boundedIncrementVariance L n)
          (condExpKernel μ hreset.measurableSpace root) := by
    filter_upwards [hmartingale] with root hmartingale_root
    letI : IsProbabilityMeasure
        (condExpKernel μ hreset.measurableSpace root) :=
      IsMarkovKernel.isProbabilityMeasure root
    intro n
    exact hasSubgaussianMGF_martingale_of_boundedIncrements
      hmartingale_root
      (fun ω => by simp [postResetIncrement])
      hbound n
  exact ae_conditional_measure_iUnion_postResetIncrement_le hreset
    postFiltration (boundedIncrementVariance L) rate budget
    hmartingale hsubG hbudget hrate hsum

/-- Concrete stopping-time conditional anytime bound with the canonical
geometric block allocation. -/
theorem ae_conditional_measure_exists_geometricStitchedBoundary_le
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (postFiltration : Filtration ℕ mΩ)
    {L alpha : ℝ} (halpha : 0 < alpha)
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale (postResetIncrement M reset) postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hbound :
      ∀ n ω,
        processIncrement (postResetIncrement M reset) n ω ∈
          Set.Icc (-L) L) :
    ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
      (condExpKernel μ hreset.measurableSpace root)
          {ω | ∃ n, 0 < n ∧
            stitchedBoundary (boundedIncrementVariance L)
              inverseSqrtDyadicRate (geometricBlockBudget alpha) n ≤
                postResetIncrement M reset n ω} ≤
        ENNReal.ofReal alpha := by
  have hblocks :=
    ae_conditional_measure_iUnion_postResetIncrement_le_of_boundedIncrements
      hreset postFiltration inverseSqrtDyadicRate
      (geometricBlockBudget alpha) hmartingale hbound
      (geometricBlockBudget_pos halpha) inverseSqrtDyadicRate_pos
      (le_of_eq (tsum_ofReal_geometricBlockBudget halpha.le))
  filter_upwards [hblocks] with root hblocks_root
  exact (measure_mono
    (anytimeCrossing_subset_iUnion_dyadicBlockCrossing
      (postResetIncrement M reset) (boundedIncrementVariance L)
      inverseSqrtDyadicRate (geometricBlockBudget alpha))).trans
        hblocks_root

/-- Unconditional per-reset failure bound obtained by integrating the
stopping-time conditional inequality. This is the form consumed by summable
reset ledgers. -/
theorem measure_iUnion_postResetIncrement_le_of_boundedIncrements
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (postFiltration : Filtration ℕ mΩ)
    {L : ℝ} (rate budget : ℕ → ℝ)
    (hpostMeasurable :
      ∀ n, Measurable[mΩ] (postResetIncrement M reset n))
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale (postResetIncrement M reset) postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hbound :
      ∀ n ω,
        processIncrement (postResetIncrement M reset) n ω ∈
          Set.Icc (-L) L)
    (hbudget : ∀ j, 0 < budget j) (hrate : ∀ j, 0 < rate j)
    {delta : ℝ≥0∞}
    (hsum : ∑' j, ENNReal.ofReal (budget j) ≤ delta) :
    μ (⋃ j, dyadicBlockCrossing
      (postResetIncrement M reset)
      (boundedIncrementVariance L) rate budget j) ≤ delta := by
  apply measure_le_of_ae_condExpKernel_le hreset.measurableSpace_le
  · exact measurableSet_iUnion_dyadicBlockCrossing hpostMeasurable
      (boundedIncrementVariance L) rate budget
  · exact
      ae_conditional_measure_iUnion_postResetIncrement_le_of_boundedIncrements
        hreset postFiltration rate budget hmartingale hbound
        hbudget hrate hsum

/-- Unconditional consequence of the concrete stopping-time conditional
anytime bound. -/
theorem measure_exists_geometricStitchedBoundary_postReset_le
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {reset : Ω → ℕ}
    (hreset : IsStoppingTime 𝒢 (fun ω => (reset ω : ℕ∞)))
    (postFiltration : Filtration ℕ mΩ)
    {L alpha : ℝ} (halpha : 0 < alpha)
    (hpostMeasurable :
      ∀ n, Measurable[mΩ] (postResetIncrement M reset n))
    (hmartingale :
      ∀ᵐ root ∂μ.trim hreset.measurableSpace_le,
        Martingale (postResetIncrement M reset) postFiltration
          (condExpKernel μ hreset.measurableSpace root))
    (hbound :
      ∀ n ω,
        processIncrement (postResetIncrement M reset) n ω ∈
          Set.Icc (-L) L) :
    μ {ω | ∃ n, 0 < n ∧
        stitchedBoundary (boundedIncrementVariance L)
          inverseSqrtDyadicRate (geometricBlockBudget alpha) n ≤
            postResetIncrement M reset n ω} ≤
      ENNReal.ofReal alpha := by
  let event : Set Ω := {ω | ∃ n, 0 < n ∧
    stitchedBoundary (boundedIncrementVariance L)
      inverseSqrtDyadicRate (geometricBlockBudget alpha) n ≤
        postResetIncrement M reset n ω}
  apply measure_le_of_ae_condExpKernel_le hreset.measurableSpace_le
  · exact measurableSet_anytimeCrossing hpostMeasurable
      (boundedIncrementVariance L) inverseSqrtDyadicRate
      (geometricBlockBudget alpha)
  · exact ae_conditional_measure_exists_geometricStitchedBoundary_le
      hreset postFiltration halpha hmartingale hbound

end Math.Probability
