/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Windowed decay with cofinal contraction

A nonnegative real sequence dominated on each boundary window by its value at
the window's left boundary converges to zero as soon as the boundary values
contract by a fixed factor `α < 1` cofinally often: the boundary values are
antitone, so they converge to their infimum, and the cofinal contraction
forces that infimum below `α` times itself.

The final counterexample records the sharpness of the cofinal fixed-factor
contraction hypothesis: strict monotone improvement alone does not imply it.
-/

namespace Math

open Filter
open scoped BigOperators

/-- The greatest boundary index whose boundary time is at most `t`, together
with its window containing `t`. -/
theorem exists_window_index {b : ℕ → ℕ} (hb0 : b 0 = 0)
    (htop : Tendsto b atTop atTop) {K t : ℕ} (ht : b K ≤ t) :
    ∃ k, K ≤ k ∧ b k ≤ t ∧ t < b (k + 1) := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (htop.eventually_gt_atTop t)
  have hPk : b (Nat.findGreatest (fun k => b k ≤ t) k₁) ≤ t :=
    Nat.findGreatest_spec (P := fun k => b k ≤ t) (Nat.zero_le k₁)
      (by rw [hb0]; exact Nat.zero_le t)
  refine ⟨Nat.findGreatest (fun k => b k ≤ t) k₁, ?_, hPk, ?_⟩
  · refine Nat.le_findGreatest (P := fun k => b k ≤ t) ?_ ht
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hk₁ K (le_of_lt hcon)) (not_lt.mpr ht)
  · rcases Nat.lt_or_ge k₁ (Nat.findGreatest (fun k => b k ≤ t) k₁ + 1) with
      hcase | hcase
    · exfalso
      have hkk₁ : Nat.findGreatest (fun k => b k ≤ t) k₁ = k₁ :=
        le_antisymm (Nat.findGreatest_le k₁) (Nat.lt_succ_iff.mp hcase)
      exact absurd (hk₁ k₁ le_rfl) (not_lt.mpr (hkk₁ ▸ hPk))
    · by_contra hcon
      rw [not_lt] at hcon
      exact Nat.findGreatest_is_greatest (P := fun k => b k ≤ t)
        (Nat.lt_succ_self _) hcase hcon

/-- An integral real strictly below another integral real sits at least one
below it. -/
theorem add_one_le_of_lt_of_int {x y : ℝ} (hx : ∃ m : ℤ, x = m)
    (hy : ∃ n : ℤ, y = n) (hxy : x < y) : x + 1 ≤ y := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hmn : m < n := by exact_mod_cast hxy
  exact_mod_cast Int.add_one_le_iff.mpr hmn

/-- The absolute difference of integral reals is integral. -/
theorem exists_int_abs_sub {x y : ℝ} (hx : ∃ m : ℤ, x = m)
    (hy : ∃ n : ℤ, y = n) : ∃ k : ℤ, |x - y| = k := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨|m - n|, by push_cast; rfl⟩

/-- A nonnegative sequence dominated on each boundary window by its value at
the window's left boundary, with cofinally many boundary steps contracting by
a factor `α < 1`, tends to zero. -/
theorem tendsto_zero_of_windowed_contraction
    {d : ℕ → ℝ} {b : ℕ → ℕ} {α : ℝ}
    (hd0 : ∀ t, 0 ≤ d t) (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Tendsto b atTop atTop)
    (hwindow : ∀ k, ∀ u, b k ≤ u → u ≤ b (k + 1) → d u ≤ d (b k))
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbig : ∀ k, ∃ k', k ≤ k' ∧ d (b (k' + 1)) ≤ α * d (b k')) :
    Tendsto d atTop (nhds 0) := by
  -- The boundary values are antitone and bounded below, so they converge to
  -- their infimum.
  set dB : ℕ → ℝ := fun k => d (b k) with hdB
  have hanti : Antitone dB := antitone_nat_of_succ_le fun k =>
    hwindow k (b (k + 1)) (hbmono (Nat.le_succ k)) le_rfl
  have hbdd : BddBelow (Set.range dB) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact hd0 (b k)
  have hL := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, dB k with hLdef
  have hL0 : 0 ≤ L := le_ciInf fun k => hd0 (b k)
  -- Cofinal contraction forces the infimum below `α` times itself.
  have hLα : L ≤ α * L := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL ε hε
    obtain ⟨k', hk'N, hk'⟩ := hbig N
    have hLle : L ≤ dB k' := ciInf_le hbdd k'
    have hdBk' : dB k' < L + ε := by
      have h := hN k' hk'N
      rw [Real.dist_eq, abs_of_nonneg (by linarith)] at h
      linarith
    have hLle1 : L ≤ dB (k' + 1) := ciInf_le hbdd (k' + 1)
    have hmul : α * dB k' ≤ α * (L + ε) :=
      mul_le_mul_of_nonneg_left (le_of_lt hdBk') hα0
    nlinarith
  have hLzero : L = 0 := by nlinarith
  rw [hLzero] at hL
  -- Squeeze the full sequence through the greatest boundary index below each
  -- time.
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hL ε hε
  refine ⟨b K, fun t ht => ?_⟩
  obtain ⟨k, hKk, hbk, htlt⟩ := exists_window_index hb0 htop ht
  have hd := hwindow k t hbk (le_of_lt htlt)
  have hdBk := hK k hKk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 _)] at hdBk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 t)]
  calc d t ≤ dB k := hd
    _ < ε := hdBk

/-- Variable-factor version of `tendsto_zero_of_windowed_contraction`.
If every boundary step contracts by a nonnegative factor `α k`, and the
finite products of those factors tend to zero, then the full windowed
sequence tends to zero. -/
theorem tendsto_zero_of_windowed_variable_contraction
    {d : ℕ → ℝ} {b : ℕ → ℕ} {α : ℕ → ℝ}
    (hd0 : ∀ t, 0 ≤ d t) (hb0 : b 0 = 0)
    (htop : Tendsto b atTop atTop)
    (hwindow : ∀ k, ∀ u, b k ≤ u → u ≤ b (k + 1) → d u ≤ d (b k))
    (hα0 : ∀ k, 0 ≤ α k)
    (hprod : Tendsto (fun n => ∏ i ∈ Finset.range n, α i) atTop (nhds 0))
    (hstep : ∀ k, d (b (k + 1)) ≤ α k * d (b k)) :
    Tendsto d atTop (nhds 0) := by
  set dB : ℕ → ℝ := fun k => d (b k) with hdB
  set A : ℕ → ℝ := fun n => ∏ i ∈ Finset.range n, α i with hA
  have hA0 : ∀ n, 0 ≤ A n := by
    intro n
    dsimp [A]
    exact Finset.prod_nonneg fun i _ => hα0 i
  have hdB_bound : ∀ n, dB n ≤ A n * dB 0 := by
    intro n
    induction n with
    | zero =>
        dsimp [A, dB]
        simp
    | succ n ih =>
        calc dB (n + 1)
            = d (b (n + 1)) := rfl
          _ ≤ α n * dB n := by simpa [dB] using hstep n
          _ ≤ α n * (A n * dB 0) := mul_le_mul_of_nonneg_left ih (hα0 n)
          _ = A (n + 1) * dB 0 := by
              dsimp [A]
              rw [Finset.prod_range_succ]
              ring
  have hupper : Tendsto (fun n => A n * dB 0) atTop (nhds 0) := by
    have hprodA : Tendsto A atTop (nhds 0) := by
      simpa [A] using hprod
    simpa [zero_mul] using hprodA.mul_const (dB 0)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hupper ε hε
  refine ⟨b K, fun t ht => ?_⟩
  obtain ⟨k, hKk, hbk, htlt⟩ := exists_window_index hb0 htop ht
  have hd := hwindow k t hbk (le_of_lt htlt)
  have hbound := hdB_bound k
  have hupper_lt := hK k hKk
  have hupper_nonneg : 0 ≤ A k * dB 0 :=
    mul_nonneg (hA0 k) (by simpa [dB] using hd0 (b 0))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hupper_nonneg] at hupper_lt
  have hdt_upper : d t ≤ A k * dB 0 := by
    calc d t ≤ dB k := by simpa [dB] using hd
      _ ≤ A k * dB 0 := hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 t)]
  exact lt_of_le_of_lt hdt_upper hupper_lt

/-- The finite products of the harmonic factors
`1 - 1/(k+2) = (k+1)/(k+2)` telescope to `1/(n+1)`. -/
theorem prod_harmonic_window_factors (n : ℕ) :
    (∏ i ∈ Finset.range n, ((1 : ℝ) - 1 / ((i : ℝ) + 2)))
      = 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      norm_num [Nat.cast_succ]
      field_simp [hn1, hn2]
      ring

/-- Windowed contraction with factors tending upward to one in the harmonic
way still drives the sequence to zero, because the factor products telescope
to `1/(n+1)`. -/
theorem tendsto_zero_of_windowed_harmonic_contraction
    {d : ℕ → ℝ} {b : ℕ → ℕ}
    (hd0 : ∀ t, 0 ≤ d t) (hb0 : b 0 = 0)
    (htop : Tendsto b atTop atTop)
    (hwindow : ∀ k, ∀ u, b k ≤ u → u ≤ b (k + 1) → d u ≤ d (b k))
    (hstep : ∀ k, d (b (k + 1))
      ≤ ((1 : ℝ) - 1 / ((k : ℝ) + 2)) * d (b k)) :
    Tendsto d atTop (nhds 0) := by
  refine tendsto_zero_of_windowed_variable_contraction hd0 hb0 htop hwindow ?_ ?_ hstep
  · intro k
    have hden : ((k : ℝ) + 2) ≠ 0 := by positivity
    rw [show (1 : ℝ) - 1 / ((k : ℝ) + 2)
        = ((k : ℝ) + 1) / ((k : ℝ) + 2) by
      field_simp [hden]
      ring]
    positivity
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
    ext n
    rw [prod_harmonic_window_factors]

/-- A nonnegative integral sequence dominated on each boundary window by its
left-boundary value, with strict boundary progress somewhere ahead whenever
nonzero, is eventually zero: the boundary values are antitone integers, so
only finitely many strict decreases fit. -/
theorem eventually_zero_of_windowed_decrease
    {d : ℕ → ℝ} {b : ℕ → ℕ}
    (hd0 : ∀ t, 0 ≤ d t) (hint : ∀ t, ∃ n : ℤ, d t = n)
    (hb0 : b 0 = 0) (hbmono : Monotone b)
    (htop : Tendsto b atTop atTop)
    (hwindow : ∀ k, ∀ u, b k ≤ u → u ≤ b (k + 1) → d u ≤ d (b k))
    (hdec : ∀ k, d (b k) ≠ 0 → ∃ k', k ≤ k' ∧ d (b (k' + 1)) < d (b k')) :
    ∀ᶠ t in atTop, d t = 0 := by
  set dB : ℕ → ℝ := fun k => d (b k) with hdB
  have hanti : Antitone dB := antitone_nat_of_succ_le fun k =>
    hwindow k (b (k + 1)) (hbmono (Nat.le_succ k)) le_rfl
  have hzero : ∃ K, dB K = 0 := by
    have hdesc : ∀ n : ℕ, ∀ k, dB k ≤ n → ∃ K, dB K = 0 := by
      intro n
      induction n with
      | zero =>
        intro k hk
        refine ⟨k, le_antisymm ?_ (hd0 (b k))⟩
        exact_mod_cast hk
      | succ n ih =>
        intro k hk
        by_cases h0 : dB k = 0
        · exact ⟨k, h0⟩
        · obtain ⟨k', hkk', hlt⟩ := hdec k h0
          have hle : dB (k' + 1) + 1 ≤ dB k' :=
            add_one_le_of_lt_of_int (hint (b (k' + 1))) (hint (b k')) hlt
          have hnext : dB (k' + 1) ≤ n := by
            have hmono := hanti hkk'
            push_cast at hk
            linarith
          exact ih (k' + 1) hnext
    obtain ⟨n, hn⟩ := hint (b 0)
    refine hdesc n.toNat 0 ?_
    have : dB 0 = (n : ℝ) := hn
    rw [this]
    exact_mod_cast Int.self_le_toNat n
  obtain ⟨K, hK⟩ := hzero
  rw [eventually_atTop]
  refine ⟨b K, fun t ht => ?_⟩
  obtain ⟨k, hKk, hbk, htlt⟩ := exists_window_index hb0 htop ht
  have hd := hwindow k t hbk (le_of_lt htlt)
  have hdBk : dB k ≤ 0 := hK ▸ hanti hKk
  exact le_antisymm (le_trans hd hdBk) (hd0 t)

/-- Strict positive improvement alone does not force the cofinal fixed-factor
contractions used by `tendsto_zero_of_windowed_contraction`.  The sequence
`1 + 1/(n+1)` strictly decreases and stays above `1`, so for every fixed
`α < 1` it eventually has no `α`-big successor step. -/
theorem slow_harmonic_no_cofinal_fixed_factor_contraction :
    let d : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
    (∀ n, 0 ≤ d n) ∧ (∀ n, d (n + 1) < d n) ∧ (∀ n, 1 < d n) ∧
      ∀ α, 0 ≤ α → α < 1 →
        ¬ (∀ k, ∃ k', k ≤ k' ∧ d (k' + 1) ≤ α * d k') := by
  intro d
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [d]
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro n
    dsimp [d]
    have hdiv : 1 / (((n + 1 : ℕ) : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
      Nat.one_div_lt_one_div (α := ℝ) (Nat.lt_succ_self n)
    linarith
  · intro n
    dsimp [d]
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro α hα0 hα1 hbig
    by_cases hαzero : α = 0
    · obtain ⟨k', -, hstep⟩ := hbig 0
      have hpos : 0 < d (k' + 1) := by
        dsimp [d]
        positivity
      rw [hαzero, zero_mul] at hstep
      linarith
    · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαzero)
      have hgap : 0 < (1 - α) / α := div_pos (sub_pos.mpr hα1) hαpos
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (K := ℝ) hgap
      obtain ⟨k', hkN, hstep⟩ := hbig N
      have hsmall : 1 / ((k' : ℝ) + 1) < (1 - α) / α := by
        exact (Nat.one_div_le_one_div (α := ℝ) hkN).trans_lt hN
      have hmul : α * (1 / ((k' : ℝ) + 1)) < 1 - α := by
        have hmul' := mul_lt_mul_of_pos_left hsmall hαpos
        have hcancel : α * ((1 - α) / α) = 1 - α := by
          field_simp [ne_of_gt hαpos]
        simpa [hcancel] using hmul'
      have hαd_lt_one : α * d k' < 1 := by
        dsimp [d]
        nlinarith
      have hnext_gt_one : 1 < d (k' + 1) := by
        dsimp [d]
        have hpos : 0 < 1 / (((k' + 1 : ℕ) : ℝ) + 1) := by positivity
        linarith
      linarith

end Math
