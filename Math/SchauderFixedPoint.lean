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

Every continuous self-map of a nonempty compact convex subset of a real normed space has a fixed
point. This is the inf-dim analogue of `brouwer_fixed_point`: we trade `[FiniteDimensional ℝ V]`
for compactness of the subset itself.

## Main statement

* `schauder_fixed_point` — for a real normed space `X`, a compact convex nonempty `K ⊆ X`,
  every continuous map `f : C(K, K)` has a fixed point.

## Proof outline

For each `n`, build an approximate fixed point `xₙ ∈ K` with `‖f xₙ - xₙ‖ ≤ 1/(n+1)`:

1. Pick a finite `(1/(n+1))`-net `y₀, …, y_{m-1} ∈ K` of `K` using
   `IsCompact.totallyBounded` and `finite_approx_of_totallyBounded`.
2. Build the **Schauder projection** `p : K → conv(yᵢ) ⊆ K` via the partition of unity
   `φᵢ(x) = max 0 (1/(n+1) - ‖x - yᵢ‖)`.
3. The composite `p ∘ f` lives on the finite-dimensional simplex (after barycentric
   coordinates) and has a fixed point by `brouwer_fixed_point`.
4. That fixed point `xₙ` satisfies `‖f xₙ - xₙ‖ = ‖p (f xₙ) - f xₙ‖ ≤ 1/(n+1)`.

Then compactness of `K` lets us extract a convergent subsequence `xₙₖ → x*`, and continuity of
`f` pushes `‖f xₙₖ - xₙₖ‖ → 0` to `f x* = x*`.

## Aim

This file is structured to mirror Mathlib conventions and is aimed at eventual upstream
contribution as `Mathlib.Analysis.NormedSpace.SchauderFixedPoint`.
-/

namespace Math.Schauder

open Set Metric Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Schauder bump functions

The "tent" function `bump ε y x = max 0 (ε - ‖x - y‖)` is the building block of the
Schauder projection: it equals `ε` at `y`, decreases linearly out to the ball of radius
`ε`, and is zero outside. -/

section Bump

/-- The Schauder bump centred at `y` with radius `ε`. -/
noncomputable def bump (ε : ℝ) (y x : X) : ℝ := max 0 (ε - ‖x - y‖)

@[simp] lemma bump_nonneg (ε : ℝ) (y x : X) : 0 ≤ bump ε y x := le_max_left _ _

lemma bump_pos_iff {ε : ℝ} (y x : X) : 0 < bump ε y x ↔ ‖x - y‖ < ε := by
  simp only [bump, lt_max_iff, lt_self_iff_false, sub_pos, false_or]

lemma bump_le_of_nonneg {ε : ℝ} (hε : 0 ≤ ε) (y x : X) : bump ε y x ≤ ε := by
  unfold bump
  exact max_le hε (by linarith [norm_nonneg (x - y)])

lemma continuous_bump (ε : ℝ) (y : X) : Continuous (bump ε y) := by
  unfold bump; fun_prop

/-- If `‖x - y‖ < ε` and `bump ε y x = 0`, contradiction. -/
lemma bump_eq_zero_of_dist_ge {ε : ℝ} {y x : X} (h : ε ≤ ‖x - y‖) : bump ε y x = 0 := by
  unfold bump; grind

end Bump

/-! ### Schauder projection via barycentric coordinates -/

section Projection

variable {m : ℕ}

/-- Sum of Schauder bumps for a finite family `y : Fin m → X`. -/
noncomputable def bumpSum (ε : ℝ) (y : Fin m → X) (x : X) : ℝ :=
  ∑ i, bump ε (y i) x

lemma bumpSum_nonneg (ε : ℝ) (y : Fin m → X) (x : X) : 0 ≤ bumpSum ε y x :=
  Finset.sum_nonneg fun _ _ => bump_nonneg _ _ _

lemma continuous_bumpSum (ε : ℝ) (y : Fin m → X) : Continuous (bumpSum ε y) := by
  unfold bumpSum
  exact continuous_finset_sum _ fun i _ => continuous_bump ε (y i)

/-- If `x` lies within `ε` of some `y i`, the bump sum is strictly positive at `x`. -/
lemma bumpSum_pos {ε : ℝ} {y : Fin m → X} {x : X} (h : ∃ i, ‖x - y i‖ < ε) :
    0 < bumpSum ε y x := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos'
    (fun _ _ => bump_nonneg _ _ _)
    ⟨i, Finset.mem_univ _, (bump_pos_iff _ _).2 hi⟩

/-- **Barycentric coordinates**: a point in the standard simplex over `Fin m` produces a
convex combination of points `y : Fin m → X`. -/
noncomputable def bary (y : Fin m → X) (w : Fin m → ℝ) : X := ∑ i, w i • y i

lemma continuous_bary (y : Fin m → X) : Continuous (bary y) := by
  unfold bary
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

/-- A convex combination of points in a convex set `K` stays in `K`. -/
lemma bary_mem_of_simplex {K : Set X} (hK : Convex ℝ K) {y : Fin m → X}
    (hy : ∀ i, y i ∈ K) {w : Fin m → ℝ} (hw : w ∈ stdSimplex ℝ (Fin m)) :
    bary y w ∈ K :=
  hK.sum_mem (fun i _ => hw.1 i) hw.2 (fun i _ => hy i)

/-- The Schauder projection of `x ∈ K` onto `conv {yᵢ}`, given `bumpSum ε y x > 0`. -/
noncomputable def schauderProj (ε : ℝ) (y : Fin m → X) (x : X) : X :=
  bary y (fun i => bump ε (y i) x / bumpSum ε y x)

/-- The bound: the Schauder projection sits within `ε` of its input. -/
lemma norm_schauderProj_sub_le {ε : ℝ} (hε : 0 < ε) (y : Fin m → X) {x : X}
    (hpos : 0 < bumpSum ε y x) : ‖schauderProj ε y x - x‖ ≤ ε := by
  set S := bumpSum ε y x with hSdef
  set w : Fin m → ℝ := fun i => bump ε (y i) x / S with hwdef
  have hw_nn : ∀ i, 0 ≤ w i := fun i =>
    div_nonneg (bump_nonneg _ _ _) hpos.le
  have hw_sum : ∑ i, w i = 1 := by
    have hSsum : ∑ i, bump ε (y i) x = S := rfl
    change (∑ i, bump ε (y i) x / S) = 1
    rw [← Finset.sum_div, hSsum, div_self hpos.ne']
  have h_diff : schauderProj ε y x - x = ∑ i, w i • (y i - x) := by
    have hxeq : x = ∑ i, w i • x := by
      rw [← Finset.sum_smul, hw_sum, one_smul]
    have hproj : schauderProj ε y x = ∑ i, w i • y i := rfl
    rw [hproj]; conv_lhs => rw [hxeq]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _; rw [smul_sub]
  rw [h_diff]
  refine (norm_sum_le _ _).trans ?_
  have h_term : ∀ i, ‖w i • (y i - x)‖ ≤ w i * ε := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nn i)]
    by_cases hclose : ‖y i - x‖ < ε
    · exact mul_le_mul_of_nonneg_left hclose.le (hw_nn i)
    · push Not at hclose
      have hbz : bump ε (y i) x = 0 := bump_eq_zero_of_dist_ge (by rwa [norm_sub_rev])
      have hwz : w i = 0 := by simp [hwdef, hbz]
      simp [hwz]
  calc (∑ i, ‖w i • (y i - x)‖) ≤ ∑ i, w i * ε :=
          Finset.sum_le_sum (fun i _ => h_term i)
    _ = (∑ i, w i) * ε := by rw [Finset.sum_mul]
    _ = ε := by rw [hw_sum, one_mul]

end Projection

/-! ### Schauder weights map -/

section SchauderMap

variable {m : ℕ}

/-- The weight function `i ↦ φᵢ(x) / S(x)`. -/
noncomputable def schauderMap (ε : ℝ) (y : Fin m → X) (x : X) : Fin m → ℝ :=
  fun i => bump ε (y i) x / bumpSum ε y x

lemma schauderMap_mem_stdSimplex {ε : ℝ} {y : Fin m → X} {x : X}
    (hpos : 0 < bumpSum ε y x) : schauderMap ε y x ∈ stdSimplex ℝ (Fin m) := by
  refine ⟨fun i => div_nonneg (bump_nonneg _ _ _) hpos.le, ?_⟩
  change (∑ i, bump ε (y i) x / bumpSum ε y x) = 1
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- The Schauder weight map is continuous on the set where the bump sum is positive. -/
lemma continuousOn_schauderMap (ε : ℝ) (y : Fin m → X) :
    ContinuousOn (schauderMap ε y) {x | 0 < bumpSum ε y x} := by
  refine continuousOn_pi.2 fun i => ?_
  refine ContinuousOn.div (Continuous.continuousOn (continuous_bump ε (y i)))
    (Continuous.continuousOn (continuous_bumpSum ε y)) ?_
  intro x hx; exact hx.ne'

end SchauderMap

/-! ### Approximate fixed points via Brouwer on the simplex -/

section ApproxFixedPoint

variable {K : Set X}

/-- The approximate-fixed-point step: given a finite ε-net of `K` inside `K`, produce
`x ∈ K` with `‖f x - x‖ ≤ ε`. -/
lemma exists_approx_fixedPoint
    (hK_cvx : Convex ℝ K) (f : C(K, K))
    {ε : ℝ} (hε : 0 < ε) {m : ℕ} [Nonempty (Fin m)] (y : Fin m → X)
    (hyK : ∀ i, y i ∈ K) (hcov : ∀ x ∈ K, ∃ i, ‖x - y i‖ < ε) :
    ∃ x : K, ‖(f x : X) - (x : X)‖ ≤ ε := by
  set Δ : Set (Fin m → ℝ) := stdSimplex ℝ (Fin m) with hΔdef
  have hΔ_cvx : Convex ℝ Δ := convex_stdSimplex ℝ _
  have hΔ_cpt : IsCompact Δ := isCompact_stdSimplex ℝ _
  -- The Brouwer self-map: `w ↦ schauderMap ε y (f ⟨bary y w, _⟩)`.
  -- Build the underlying map and prove its key properties.
  -- Step 1: `bary y w ∈ K` for `w ∈ Δ`.
  have hbaryK : ∀ w ∈ Δ, bary y w ∈ K := fun w hw =>
    bary_mem_of_simplex hK_cvx hyK hw
  -- Step 2: For any `x ∈ K`, `bumpSum ε y x > 0`.
  have hSpos : ∀ x ∈ K, 0 < bumpSum ε y x := fun x hx => bumpSum_pos (hcov x hx)
  -- Step 3: Build a continuous self-map `g : Δ → Δ` (as a subtype function).
  -- For `w : Δ` (subtype): let `x = ⟨bary y w.val, hbaryK w.val w.2⟩ : K`; then
  -- `g w = ⟨schauderMap ε y (f x).val, schauderMap_mem_stdSimplex (hSpos _ (f x).2)⟩`.
  set Φ : Δ → Δ := fun w =>
    let x : K := ⟨bary y w.val, hbaryK w.val w.2⟩
    let fx : K := f x
    ⟨schauderMap ε y fx.val, schauderMap_mem_stdSimplex (hSpos fx.val fx.2)⟩
    with hΦdef
  -- Step 4: Continuity of Φ. We build it from continuous pieces.
  have hΦ_cont : Continuous Φ := by
    have h1 : Continuous (fun w : Δ => bary y w.val) :=
      (continuous_bary y).comp continuous_subtype_val
    have h2 : Continuous (fun w : Δ => (⟨bary y w.val, hbaryK w.val w.2⟩ : K)) :=
      continuous_induced_rng.2 h1
    have h3 : Continuous (fun w : Δ => (f ⟨bary y w.val, hbaryK w.val w.2⟩ : K)) :=
      f.continuous.comp h2
    have h4 : Continuous (fun w : Δ =>
        (f ⟨bary y w.val, hbaryK w.val w.2⟩ : X)) :=
      continuous_subtype_val.comp h3
    -- schauderMap composed with h4 is continuous on K (which is everywhere mapped to).
    have h5 : ContinuousOn (schauderMap ε y) (Set.range fun w : Δ =>
        (f ⟨bary y w.val, hbaryK w.val w.2⟩ : X)) := by
      refine (continuousOn_schauderMap ε y).mono ?_
      rintro x ⟨w, rfl⟩
      exact hSpos _ (f ⟨bary y w.val, hbaryK w.val w.2⟩).2
    refine continuous_induced_rng.2 ?_
    refine (h5.comp_continuous h4 ?_)
    intro w; exact ⟨w, rfl⟩
  -- Step 5: Apply Brouwer to Φ (as a ContinuousMap on Δ).
  have hΔ_ne : Δ.Nonempty := by
    obtain ⟨i₀⟩ := ‹Nonempty (Fin m)›
    refine ⟨fun i => if i = i₀ then 1 else 0, ?_, ?_⟩
    · intro i; by_cases h : i = i₀ <;> simp [h]
    · simp
  obtain ⟨wFP, hw_fix⟩ :=
    brouwer_fixed_point Δ hΔ_cvx hΔ_cpt hΔ_ne ⟨Φ, hΦ_cont⟩
  -- Step 6: Unpack the fixed point.
  let x : K := ⟨bary y wFP.val, hbaryK wFP.val wFP.2⟩
  let fx : K := f x
  refine ⟨x, ?_⟩
  -- The fixed point says: `schauderMap ε y fx.val = wFP.val` (as elements of Fin m → ℝ).
  have hw_eq : schauderMap ε y fx.val = wFP.val := by
    have := congrArg Subtype.val hw_fix
    -- congrArg gives (Φ wFP).val = wFP.val; (Φ wFP).val = schauderMap ε y fx.val by definition.
    simpa [Φ, x, fx] using this
  -- Now: x.val = bary y wFP.val = bary y (schauderMap ε y fx.val) = schauderProj ε y fx.val.
  have hxval : (x : X) = schauderProj ε y fx.val := by
    change bary y wFP.val = bary y (schauderMap ε y fx.val)
    rw [hw_eq]
  -- So ‖fx - x‖ = ‖fx - schauderProj ε y fx‖ ≤ ε.
  rw [hxval]
  have hpos : 0 < bumpSum ε y fx.val := hSpos fx.val fx.2
  rw [show ((f x : K) : X) - schauderProj ε y (f x).val =
      -((schauderProj ε y (f x).val) - (f x).val) from (neg_sub _ _).symm]
  rw [norm_neg]
  exact norm_schauderProj_sub_le hε y hpos

end ApproxFixedPoint

/-! ### Main theorem -/

/-- **Schauder fixed-point theorem.** Every continuous self-map of a nonempty compact convex
subset of a real normed space has a fixed point.

This is the inf-dim analogue of `brouwer_fixed_point`: we trade `[FiniteDimensional ℝ V]` for
compactness of the subset itself. -/
theorem schauder_fixed_point
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_cpt : IsCompact K) (hK_ne : K.Nonempty)
    (f : C(K, K)) : ∃ x : K, f x = x := by
  -- For each `n`, produce `xₙ : K` with `‖f xₙ - xₙ‖ ≤ 1/(n+1)`.
  have hTB : TotallyBounded K := hK_cpt.totallyBounded
  have h_approx : ∀ n : ℕ, ∃ x : K, ‖(f x : X) - (x : X)‖ ≤ 1 / (n + 1 : ℝ) := by
    intro n
    set ε : ℝ := 1 / (n + 1 : ℝ) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨t, htK, htfin, htcov⟩ := finite_approx_of_totallyBounded hTB ε hε
    -- Convert the cover to an indexed family over `Fin m`.
    have htne : t.Nonempty := by
      obtain ⟨x₀, hx₀⟩ := hK_ne
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (htcov hx₀)
      exact ⟨c, hct⟩
    set m : ℕ := htfin.toFinset.card
    have hm : 0 < m := Finset.card_pos.2 (by
      obtain ⟨c, hc⟩ := htne
      exact ⟨c, by simp [htfin.mem_toFinset, hc]⟩)
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    -- Enumerate `t.toFinset` as `Fin m → X`.
    let y : Fin m → X := fun i => (htfin.toFinset.equivFin.symm i : X)
    have hyK : ∀ i, y i ∈ K := fun i => htK (by
      have : (htfin.toFinset.equivFin.symm i : X) ∈ htfin.toFinset := Finset.coe_mem _
      rw [htfin.mem_toFinset] at this; exact this)
    have hcov : ∀ x ∈ K, ∃ i, ‖x - y i‖ < ε := by
      intro x hx
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (htcov hx)
      have hctF : c ∈ htfin.toFinset := htfin.mem_toFinset.2 hct
      refine ⟨htfin.toFinset.equivFin ⟨c, hctF⟩, ?_⟩
      have hyi : y (htfin.toFinset.equivFin ⟨c, hctF⟩) = c := by
        simp [y, Equiv.symm_apply_apply]
      rw [hyi, ← dist_eq_norm]
      exact mem_ball.1 hxc
    exact exists_approx_fixedPoint hK_cvx f hε y hyK hcov
  -- Step 2: extract the sequence.
  choose x hx using h_approx
  -- Step 3: extract a convergent subsequence using compactness.
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_lim⟩ :=
    hK_cpt.tendsto_subseq (x := fun n => (x n : X)) (fun n => (x n).2)
  refine ⟨⟨a, ha_mem⟩, ?_⟩
  -- The K-valued subsequence x ∘ φ converges in K to ⟨a, ha_mem⟩.
  have hsub_lim : Tendsto (fun n => x (φ n)) atTop (𝓝 ⟨a, ha_mem⟩) := by
    rw [tendsto_subtype_rng]; exact hφ_lim
  -- f ∘ (x ∘ φ) → f ⟨a, ha_mem⟩ by continuity.
  have hfsub_lim : Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f ⟨a, ha_mem⟩)) :=
    (f.continuous.tendsto _).comp hsub_lim
  -- `(f (x (φ n)) : X) - (x (φ n) : X) → (f ⟨a, ha_mem⟩ : X) - a` by continuity / arithmetic.
  have h_diff_lim_a :
      Tendsto (fun n => (f (x (φ n)) : X) - (x (φ n) : X)) atTop
        (𝓝 ((f ⟨a, ha_mem⟩ : X) - a)) :=
    ((continuous_subtype_val.tendsto _).comp hfsub_lim).sub hφ_lim
  -- The same sequence also tends to 0, by the approximation bound.
  have h_diff_lim_zero :
      Tendsto (fun n => (f (x (φ n)) : X) - (x (φ n) : X)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => hx (φ n)) ?_
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ_mono.tendsto_atTop
  -- By uniqueness of limits, the difference is 0.
  have h_zero : (f ⟨a, ha_mem⟩ : X) - a = 0 :=
    tendsto_nhds_unique h_diff_lim_a h_diff_lim_zero
  exact Subtype.ext (sub_eq_zero.mp h_zero)

end Math.Schauder
