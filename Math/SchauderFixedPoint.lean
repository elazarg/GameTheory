/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Sequences
import FixedPointTheorems.brouwer

/-!
# Schauder fixed-point theorem

Every continuous self-map of a nonempty compact convex subset of a real normed space has a
fixed point. This is the infinite-dimensional analogue of `brouwer_fixed_point`: we trade
`[FiniteDimensional ℝ V]` for compactness of the subset itself.

## Main statement

* `schauder_fixed_point`: for a real normed space `X`, a compact convex nonempty `K ⊆ X`,
  every continuous map `f : C(K, K)` has a fixed point.

## Proof outline

For each `n`, build an approximate fixed point `xₙ ∈ K` with `‖f xₙ - xₙ‖ ≤ 1/(n+1)`:

1. Pick a finite `(1/(n+1))`-net `y₀, …, y_{m-1} ∈ K` via `IsCompact.totallyBounded` and
   `finite_approx_of_totallyBounded`.
2. Build the **Schauder projection** `p : K → conv {yᵢ} ⊆ K` from the partition of unity
   `φᵢ(x) = max 0 (ε - ‖x - yᵢ‖)`. It satisfies `‖p x - x‖ ≤ ε`.
3. The composite `p ∘ f` lives on the finite-dimensional simplex (after barycentric
   coordinates) and has a fixed point by `brouwer_fixed_point`.
4. That fixed point `xₙ` satisfies `‖f xₙ - xₙ‖ = ‖p (f xₙ) - f xₙ‖ ≤ 1/(n+1)`.

Compactness then extracts a convergent subsequence `xₙₖ → x*`, and continuity of `f`
pushes the approximation bound to `f x* = x*`.

## Upstreaming

This file follows Mathlib conventions and is aimed at upstream contribution as
`Mathlib.Analysis.NormedSpace.SchauderFixedPoint`.
-/

namespace Math.Schauder

open Set Metric Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Schauder bump functions -/

section Bump

/-- The Schauder bump centred at `y` with radius `ε`. -/
noncomputable def bump (ε : ℝ) (y x : X) : ℝ := max 0 (ε - ‖x - y‖)

omit [NormedSpace ℝ X] in
@[simp] lemma bump_nonneg (ε : ℝ) (y x : X) : 0 ≤ bump ε y x := le_max_left _ _

omit [NormedSpace ℝ X] in
lemma bump_pos_iff {ε : ℝ} (y x : X) : 0 < bump ε y x ↔ ‖x - y‖ < ε := by
  simp only [bump, lt_max_iff, lt_self_iff_false, sub_pos, false_or]

omit [NormedSpace ℝ X] in
lemma bump_eq_zero_of_dist_ge {ε : ℝ} {y x : X} (h : ε ≤ ‖x - y‖) : bump ε y x = 0 := by
  simp only [bump]; grind

omit [NormedSpace ℝ X] in
lemma continuous_bump (ε : ℝ) (y : X) : Continuous (bump ε y) := by
  unfold bump; fun_prop

end Bump

/-! ### Schauder projection via barycentric coordinates -/

section Projection

variable {m : ℕ}

/-- Sum of Schauder bumps for a finite family `y : Fin m → X`. -/
noncomputable def bumpSum (ε : ℝ) (y : Fin m → X) (x : X) : ℝ :=
  ∑ i, bump ε (y i) x

omit [NormedSpace ℝ X] in
lemma bumpSum_nonneg (ε : ℝ) (y : Fin m → X) (x : X) : 0 ≤ bumpSum ε y x :=
  Finset.sum_nonneg fun _ _ => bump_nonneg _ _ _

omit [NormedSpace ℝ X] in
lemma continuous_bumpSum (ε : ℝ) (y : Fin m → X) : Continuous (bumpSum ε y) :=
  continuous_finset_sum _ fun i _ => continuous_bump ε (y i)

omit [NormedSpace ℝ X] in
/-- If `x` lies within `ε` of some `y i`, the bump sum is strictly positive at `x`. -/
lemma bumpSum_pos {ε : ℝ} {y : Fin m → X} {x : X} (h : ∃ i, ‖x - y i‖ < ε) :
    0 < bumpSum ε y x := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun _ _ => bump_nonneg _ _ _)
    ⟨i, Finset.mem_univ _, (bump_pos_iff _ _).2 hi⟩

/-- **Barycentric coordinates**: a point in the standard simplex over `Fin m` produces a
convex combination of points `y : Fin m → X`. -/
noncomputable def bary (y : Fin m → X) (w : Fin m → ℝ) : X := ∑ i, w i • y i

lemma continuous_bary (y : Fin m → X) : Continuous (bary y) :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

/-- A convex combination of points in a convex set `K` stays in `K`. -/
lemma bary_mem_of_simplex {K : Set X} (hK : Convex ℝ K) {y : Fin m → X}
    (hy : ∀ i, y i ∈ K) {w : Fin m → ℝ} (hw : w ∈ stdSimplex ℝ (Fin m)) :
    bary y w ∈ K :=
  hK.sum_mem (fun i _ => hw.1 i) hw.2 (fun i _ => hy i)

/-- The Schauder weight `i ↦ φᵢ(x) / S(x)`. -/
noncomputable def weights (ε : ℝ) (y : Fin m → X) (x : X) : Fin m → ℝ :=
  fun i => bump ε (y i) x / bumpSum ε y x

omit [NormedSpace ℝ X] in
lemma weights_mem_stdSimplex {ε : ℝ} {y : Fin m → X} {x : X}
    (hpos : 0 < bumpSum ε y x) : weights ε y x ∈ stdSimplex ℝ (Fin m) := by
  refine ⟨fun _ => div_nonneg (bump_nonneg _ _ _) hpos.le, ?_⟩
  rw [show (∑ i, weights ε y x i) = (∑ i, bump ε (y i) x) / bumpSum ε y x from
    (Finset.sum_div _ _ _).symm]
  exact div_self hpos.ne'

omit [NormedSpace ℝ X] in
lemma continuousOn_weights (ε : ℝ) (y : Fin m → X) :
    ContinuousOn (weights ε y) {x | 0 < bumpSum ε y x} :=
  continuousOn_pi.2 fun _ =>
    ContinuousOn.div (continuous_bump _ _).continuousOn
      (continuous_bumpSum _ _).continuousOn fun _ hx => hx.ne'

/-- The Schauder projection of `x` onto `conv {yᵢ}`. -/
noncomputable def proj (ε : ℝ) (y : Fin m → X) (x : X) : X := bary y (weights ε y x)

/-- **Schauder projection bound**: when `bumpSum ε y x > 0`, the projection sits within `ε`
of its input. -/
lemma norm_proj_sub_le (ε : ℝ) (y : Fin m → X) {x : X}
    (hpos : 0 < bumpSum ε y x) : ‖proj ε y x - x‖ ≤ ε := by
  have hw_mem := weights_mem_stdSimplex hpos
  have hw_nn : ∀ i, 0 ≤ weights ε y x i := hw_mem.1
  have hw_sum : ∑ i, weights ε y x i = 1 := hw_mem.2
  have h_diff : proj ε y x - x = ∑ i, weights ε y x i • (y i - x) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw_sum, one_smul]
    rfl
  rw [h_diff]
  refine (norm_sum_le _ _).trans ?_
  calc (∑ i, ‖weights ε y x i • (y i - x)‖)
      ≤ ∑ i, weights ε y x i * ε := Finset.sum_le_sum fun i _ => ?_
    _ = (∑ i, weights ε y x i) * ε := by rw [Finset.sum_mul]
    _ = ε := by rw [hw_sum, one_mul]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nn i)]
  by_cases hclose : ‖y i - x‖ < ε
  · exact mul_le_mul_of_nonneg_left hclose.le (hw_nn i)
  · push Not at hclose
    have hge : ε ≤ ‖x - y i‖ := by rwa [norm_sub_rev]
    have hwz : weights ε y x i = 0 := by
      simp [weights, bump_eq_zero_of_dist_ge hge]
    simp [hwz]

end Projection

/-! ### Approximate fixed points via Brouwer -/

section ApproxFixedPoint

variable {K : Set X}

/-- The approximate-fixed-point step: given a finite `ε`-net `y` of `K` inside `K`, produce
`x : K` with `‖f x - x‖ ≤ ε`. The fixed point of the Brouwer map on `stdSimplex ℝ (Fin m)`
gives the approximation; `norm_proj_sub_le` gives the bound. -/
lemma exists_approx_fixedPoint (hK_cvx : Convex ℝ K) (f : C(K, K))
    {ε : ℝ} {m : ℕ} [Nonempty (Fin m)] (y : Fin m → X)
    (hyK : ∀ i, y i ∈ K) (hcov : ∀ x ∈ K, ∃ i, ‖x - y i‖ < ε) :
    ∃ x : K, ‖(f x : X) - (x : X)‖ ≤ ε := by
  -- Setup.
  set Δ : Set (Fin m → ℝ) := stdSimplex ℝ (Fin m)
  have hΔ_cvx : Convex ℝ Δ := convex_stdSimplex ℝ _
  have hΔ_cpt : IsCompact Δ := isCompact_stdSimplex ℝ _
  have hΔ_ne : Δ.Nonempty := by
    obtain ⟨i₀⟩ := ‹Nonempty (Fin m)›
    refine ⟨fun i => if i = i₀ then 1 else 0,
      fun i => by by_cases h : i = i₀ <;> simp [h], by simp⟩
  have hbaryK : ∀ w ∈ Δ, bary y w ∈ K := fun _ hw => bary_mem_of_simplex hK_cvx hyK hw
  have hSpos : ∀ x ∈ K, 0 < bumpSum ε y x := fun x hx => bumpSum_pos (hcov x hx)
  -- The Brouwer self-map on the simplex.
  let baryK : Δ → K := fun w => ⟨bary y w.1, hbaryK w.1 w.2⟩
  let Φ : Δ → Δ := fun w =>
    ⟨weights ε y (f (baryK w)).1, weights_mem_stdSimplex (hSpos _ (f (baryK w)).2)⟩
  have hΦ_cont : Continuous Φ := by
    refine continuous_induced_rng.2 ?_
    have h_baryK : Continuous baryK :=
      continuous_induced_rng.2 ((continuous_bary y).comp continuous_subtype_val)
    have h_fx : Continuous (fun w : Δ => (f (baryK w) : X)) :=
      continuous_subtype_val.comp (f.continuous.comp h_baryK)
    exact (continuousOn_weights ε y).comp_continuous h_fx
      fun w => hSpos _ (f (baryK w)).2
  -- Apply Brouwer.
  obtain ⟨wFP, hw_fix⟩ :=
    brouwer_fixed_point Δ hΔ_cvx hΔ_cpt hΔ_ne ⟨Φ, hΦ_cont⟩
  refine ⟨baryK wFP, ?_⟩
  -- The fixed point equation: `weights ε y (f (baryK wFP)).1 = wFP.1`.
  have hw_eq : weights ε y (f (baryK wFP)).1 = wFP.1 := congrArg Subtype.val hw_fix
  -- Hence `(baryK wFP).1 = bary y wFP.1 = bary y (weights ε y ...) = proj ε y ...`.
  have hxval : (baryK wFP : X) = proj ε y (f (baryK wFP)).1 := by
    change bary y wFP.1 = bary y (weights ε y (f (baryK wFP)).1); rw [hw_eq]
  rw [hxval, ← neg_sub, norm_neg]
  exact norm_proj_sub_le ε y (hSpos _ (f (baryK wFP)).2)

end ApproxFixedPoint

/-! ### Main theorem -/

/-- **Schauder fixed-point theorem.** Every continuous self-map of a nonempty compact convex
subset of a real normed space has a fixed point. -/
theorem schauder_fixed_point {K : Set X}
    (hK_cvx : Convex ℝ K) (hK_cpt : IsCompact K) (hK_ne : K.Nonempty) (f : C(K, K)) :
    ∃ x : K, f x = x := by
  -- For each `n`, produce `xₙ : K` with `‖f xₙ - xₙ‖ ≤ 1/(n+1)`.
  have hTB : TotallyBounded K := hK_cpt.totallyBounded
  have h_approx : ∀ n : ℕ, ∃ x : K, ‖(f x : X) - (x : X)‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    set ε : ℝ := 1 / (n + 1 : ℝ)
    have hε : 0 < ε := by positivity
    obtain ⟨t, htK, htfin, htcov⟩ := finite_approx_of_totallyBounded hTB ε hε
    have htne : t.Nonempty := by
      obtain ⟨x₀, hx₀⟩ := hK_ne
      obtain ⟨c, hct, _⟩ := Set.mem_iUnion₂.1 (htcov hx₀)
      exact ⟨c, hct⟩
    have hm : 0 < htfin.toFinset.card := by
      obtain ⟨c, hc⟩ := htne
      exact Finset.card_pos.2 ⟨c, htfin.mem_toFinset.2 hc⟩
    haveI : Nonempty (Fin htfin.toFinset.card) := ⟨⟨0, hm⟩⟩
    let y : Fin htfin.toFinset.card → X := fun i => (htfin.toFinset.equivFin.symm i : X)
    have hyK : ∀ i, y i ∈ K := fun i =>
      htK (htfin.mem_toFinset.1 (htfin.toFinset.equivFin.symm i).2)
    have hcov : ∀ x ∈ K, ∃ i, ‖x - y i‖ < ε := fun x hx => by
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (htcov hx)
      refine ⟨htfin.toFinset.equivFin ⟨c, htfin.mem_toFinset.2 hct⟩, ?_⟩
      rw [show y _ = c from by simp [y], ← dist_eq_norm]
      exact mem_ball.1 hxc
    exact exists_approx_fixedPoint hK_cvx f y hyK hcov
  choose x hx using h_approx
  -- Extract a convergent subsequence and pass to the limit.
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_lim⟩ :=
    hK_cpt.tendsto_subseq (x := fun n => (x n : X)) fun n => (x n).2
  refine ⟨⟨a, ha_mem⟩, ?_⟩
  have hsub_lim : Tendsto (fun n => x (φ n)) atTop (𝓝 ⟨a, ha_mem⟩) :=
    tendsto_subtype_rng.2 hφ_lim
  have hfsub_lim : Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f ⟨a, ha_mem⟩)) :=
    (f.continuous.tendsto _).comp hsub_lim
  have h_diff_a :
      Tendsto (fun n => (f (x (φ n)) : X) - (x (φ n) : X)) atTop
        (𝓝 ((f ⟨a, ha_mem⟩ : X) - a)) :=
    ((continuous_subtype_val.tendsto _).comp hfsub_lim).sub hφ_lim
  have h_diff_zero :
      Tendsto (fun n => (f (x (φ n)) : X) - (x (φ n) : X)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bound : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hx (φ n)) h_bound
  exact Subtype.ext (sub_eq_zero.mp (tendsto_nhds_unique h_diff_a h_diff_zero))

end Math.Schauder
