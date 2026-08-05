/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.StdSimplex
import Math.Simplex
import GameTheory.Basic

/-!
# The normalized singleton LCP

For a finite index type `ι` and a matrix `B : ι → ι → ℝ`, the **normalized
singleton linear complementarity problem** asks for `λ ∈ Δ(ι)` (the standard
simplex, `stdSimplex ℝ ι`) whose image `q = Bλ` is componentwise nonnegative
and complementary to `λ`: `λ i * q i = 0` at every coordinate.

This is the finite structure behind the "singleton" comparison matrices that
appear throughout the quitting-game reduction: for a coalition reward
`r : {S : Finset ι // S.Nonempty} → (ι → ℝ)`, the matrix
`Bᵢⱼ = r({j})ᵢ - r({i})ᵢ` compares player `i`'s payoff at `j`'s solo
termination against its own. Feasibility of this LCP is what several
recorded results (the absorption-vanishing equivalence, in particular) turn
on.

## Main definitions

* `singletonLCPResidual B λ` — the residual vector `q = Bλ` at a simplex point
* `SingletonLCPFeasible B` — the feasibility predicate itself
* `quittingSingletonMatrix reward` — the game-facing comparison matrix
* `quittingSingletonLCPFeasible reward` — the LCP instantiated at a quitting
  reward

## Main results

* `singletonLCPFeasible_iff_exists_supportPattern` — the support-pattern
  reduction: feasibility iff some nonempty `S` carries a simplex point
  vanishing off `S`, with residual zero on `S` and nonnegative off it. This
  is the finite alternative every downstream check uses.
* `singletonLCPFeasible_bool_iff` — the two-coordinate case, worked out as an
  explicit three-way disjunction of sign/algebraic conditions on the four
  matrix entries.
* `quittingSingletonLCPFeasible_iff` — the unfolding lemma bridging the
  game-facing predicate to the raw LCP.

## Design notes

`Math.LinearProgramming` is otherwise independent of `GameTheory`; this file
is the one place that bridges the two, since deliverable (3) of `LEAN-P1-5`
is explicitly the game-facing instantiation. The bridge is one-directional
(only `GameTheory.Basic`, the lightweight `Payoff` abbreviation, is needed)
and does not create an import cycle.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace LinearProgramming

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-! ## The feasibility predicate -/

/-- The residual `q = Bλ` at a simplex point, coordinate `i`: `q i = ∑ⱼ B i j · λ j`.
Definitionally `wsum λ (B i)`, the simplex-weighted row sum. -/
def singletonLCPResidual (B : ι → ι → ℝ) (lam : stdSimplex ℝ ι) (i : ι) : ℝ :=
  wsum lam (B i)

/-- Unfolding lemma for `singletonLCPResidual`, restating it as `wsum`. -/
@[simp] theorem singletonLCPResidual_def (B : ι → ι → ℝ) (lam : stdSimplex ℝ ι) (i : ι) :
    singletonLCPResidual B lam i = wsum lam (B i) := rfl

/-- **The normalized singleton LCP.** `B` admits a normalized singleton-LCP
solution: some `λ ∈ Δ(ι)` whose residual `q = Bλ` is componentwise
nonnegative and complementary to `λ` at every coordinate. -/
def SingletonLCPFeasible (B : ι → ι → ℝ) : Prop :=
  ∃ lam : stdSimplex ℝ ι,
    (∀ i, 0 ≤ singletonLCPResidual B lam i) ∧
    ∀ i, lam.val i * singletonLCPResidual B lam i = 0

/-! ## Basic API: monotonicity, scaling, trivial instances -/

/-- The residual is monotone in the matrix: entrywise `B ≤ B'` gives residual `≤`
at every simplex point, since simplex weights are nonnegative. -/
theorem singletonLCPResidual_mono {B B' : ι → ι → ℝ} (h : ∀ i j, B i j ≤ B' i j)
    (lam : stdSimplex ℝ ι) (i : ι) :
    singletonLCPResidual B lam i ≤ singletonLCPResidual B' lam i :=
  wsum_le_wsum lam (h i)

/-- The residual scales linearly with the matrix. -/
theorem singletonLCPResidual_smul (c : ℝ) (B : ι → ι → ℝ) (lam : stdSimplex ℝ ι) (i : ι) :
    singletonLCPResidual (fun i j => c * B i j) lam i = c * singletonLCPResidual B lam i := by
  simp [singletonLCPResidual, wsum, dotProduct, Finset.mul_sum, mul_left_comm]

/-- Positive scaling of the matrix preserves feasibility: the same witness `λ`
works throughout, since a positive scalar changes neither the sign of the
residual nor the vanishing of the complementarity products. -/
theorem singletonLCPFeasible_smul_iff {c : ℝ} (hc : 0 < c) (B : ι → ι → ℝ) :
    SingletonLCPFeasible (fun i j => c * B i j) ↔ SingletonLCPFeasible B := by
  constructor
  · rintro ⟨lam, hnn, hcomp⟩
    refine ⟨lam, fun i => ?_, fun i => ?_⟩
    · have := hnn i
      rw [singletonLCPResidual_smul] at this
      exact nonneg_of_mul_nonneg_right this hc
    · have := hcomp i
      rw [singletonLCPResidual_smul] at this
      have hc' : lam.val i * singletonLCPResidual B lam i * c = 0 := by linarith [this]
      rcases mul_eq_zero.mp hc' with h | h
      · exact h
      · exact absurd h hc.ne'
  · rintro ⟨lam, hnn, hcomp⟩
    refine ⟨lam, fun i => ?_, fun i => ?_⟩
    · rw [singletonLCPResidual_smul]
      exact mul_nonneg hc.le (hnn i)
    · rw [singletonLCPResidual_smul]
      have := hcomp i
      nlinarith [this]

/-- The zero matrix is trivially feasible: every simplex point is a witness,
since the residual vanishes identically. -/
theorem singletonLCPFeasible_zero [Nonempty ι] :
    SingletonLCPFeasible (fun _ _ : ι => (0 : ℝ)) := by
  classical
  refine ⟨Classical.arbitrary (stdSimplex ℝ ι), fun i => ?_, fun i => ?_⟩
  · simp [singletonLCPResidual, wsum, dotProduct]
  · simp [singletonLCPResidual, wsum, dotProduct]

/-- A pure-strategy witness: if some coordinate `i₀` has a zero diagonal entry
and every entry of its column is nonnegative, the point mass at `i₀` solves
the singleton LCP. This is the `S = {i₀}` case of the support-pattern
reduction (`singletonLCPFeasible_iff_exists_supportPattern`), spelled out
directly. -/
theorem singletonLCPFeasible_of_diag_eq_zero {B : ι → ι → ℝ} (i₀ : ι)
    (hdiag : B i₀ i₀ = 0) (hcol : ∀ j, 0 ≤ B j i₀) :
    SingletonLCPFeasible B := by
  classical
  refine ⟨stdSimplex.pure (𝕜 := ℝ) i₀, fun i => ?_, fun i => ?_⟩
  · rw [singletonLCPResidual_def, wsum_pure_apply]
    exact hcol i
  · rw [singletonLCPResidual_def, wsum_pure_apply, stdSimplex.pure_apply]
    by_cases h : i = i₀
    · simp [h, hdiag]
    · simp [h]

/-! ## Behaviour under permutation of `ι` -/

/-- Reindex a matrix along a bijection between index types. -/
def reindexMatrix (e : ι ≃ ι') (B : ι → ι → ℝ) : ι' → ι' → ℝ :=
  fun i' j' => B (e.symm i') (e.symm j')

/-- Transport a simplex point along a bijection between index types. -/
def reindexSimplex (e : ι ≃ ι') (lam : stdSimplex ℝ ι) : stdSimplex ℝ ι' :=
  ⟨fun i' => lam.val (e.symm i'), fun i' => lam.property.1 (e.symm i'),
    (Equiv.sum_comp e.symm lam.val).trans lam.property.2⟩

/-- Pointwise formula for the reindexed simplex point. -/
@[simp] theorem reindexSimplex_apply (e : ι ≃ ι') (lam : stdSimplex ℝ ι) (i' : ι') :
    (reindexSimplex e lam).val i' = lam.val (e.symm i') := rfl

/-- The residual transports along the reindexing: the residual of the
reindexed matrix at the reindexed witness, evaluated at `e i`, is the
original residual at `i`. -/
theorem singletonLCPResidual_reindexMatrix (e : ι ≃ ι') (B : ι → ι → ℝ)
    (lam : stdSimplex ℝ ι) (i : ι) :
    singletonLCPResidual (reindexMatrix e B) (reindexSimplex e lam) (e i) =
      singletonLCPResidual B lam i := by
  simp only [singletonLCPResidual_def, wsum, dotProduct, reindexMatrix, Equiv.symm_apply_apply]
  exact Equiv.sum_comp e.symm (fun j => lam.val j * B i j)

/-- Reindexing along a bijection preserves feasibility (one direction; the
biconditional is `singletonLCPFeasible_reindexMatrix_iff`). -/
theorem singletonLCPFeasible_reindexMatrix_of (e : ι ≃ ι') {B : ι → ι → ℝ}
    (h : SingletonLCPFeasible B) : SingletonLCPFeasible (reindexMatrix e B) := by
  obtain ⟨lam, hnn, hcomp⟩ := h
  refine ⟨reindexSimplex e lam, fun i' => ?_, fun i' => ?_⟩
  · rw [← Equiv.apply_symm_apply e i', singletonLCPResidual_reindexMatrix]
    exact hnn _
  · rw [← Equiv.apply_symm_apply e i', singletonLCPResidual_reindexMatrix, reindexSimplex_apply,
      Equiv.symm_apply_apply]
    exact hcomp _

/-- **Permutation invariance.** Reindexing the matrix along a bijection of
index types does not change feasibility of the singleton LCP. -/
theorem singletonLCPFeasible_reindexMatrix_iff (e : ι ≃ ι') (B : ι → ι → ℝ) :
    SingletonLCPFeasible (reindexMatrix e B) ↔ SingletonLCPFeasible B := by
  constructor
  · intro h
    have h' := singletonLCPFeasible_reindexMatrix_of e.symm h
    have hB : reindexMatrix e.symm (reindexMatrix e B) = B := by
      funext i j
      simp [reindexMatrix]
    rwa [hB] at h'
  · exact singletonLCPFeasible_reindexMatrix_of e

/-! ## The two-coordinate case

For `ι = Bool`, feasibility unfolds to an explicit finite disjunction of
sign/algebraic conditions on the four entries of `B`. -/

section BoolCase

/-- A single-equation building block: if `x` and `y` have opposite sign (or
either vanishes), the segment from `x` (at `t = 0`) to `y` (at `t = 1`) has an
interior-or-endpoint zero. -/
private theorem exists_unitMix_eq_zero_of_mul_nonpos {x y : ℝ} (h : x * y ≤ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t) * x + t * y = 0 := by
  have hmem : (0 : ℝ) ∈ Set.uIcc x y := by
    rcases mul_nonpos_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Set.mem_uIcc.mpr (Or.inr ⟨hy, hx⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hx, hy⟩)
  have hcont : ContinuousOn (fun t : ℝ => (1 - t) * x + t * y) (Set.uIcc (0 : ℝ) 1) :=
    (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).continuousOn
  have hsub := intermediate_value_uIcc hcont
  simp only [show (fun t : ℝ => (1 - t) * x + t * y) 0 = x by norm_num,
    show (fun t : ℝ => (1 - t) * x + t * y) 1 = y by norm_num] at hsub
  obtain ⟨t, ht, hft⟩ := hsub hmem
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact ⟨t, ht.1, ht.2, hft⟩

/-- If the `2 × 2` "cross" and "dot" conditions hold, the product `a * b` is
nonpositive. Proved unconditionally: at `a = 0` the product vanishes; at
`a ≠ 0`, multiplying the dot condition by `a ^ 2` and substituting the cross
identity factors it as `a * b * (a ^ 2 + c ^ 2) ≤ 0` with a positive second
factor. -/
private theorem ab_nonpos_of_cross_dot {a b c d : ℝ}
    (hcross : a * d = b * c) (hdot : a * b + c * d ≤ 0) : a * b ≤ 0 := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  · have hident : a ^ 2 * c * d = a * b * c ^ 2 := by
      rw [show a ^ 2 * c * d = a * c * (a * d) from by ring, hcross]; ring
    have hstep : a ^ 2 * (a * b + c * d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hdot
    have hexpand : a ^ 2 * (a * b + c * d) = a * b * (a ^ 2 + c ^ 2) := by
      rw [show a ^ 2 * (a * b + c * d) = a ^ 3 * b + a ^ 2 * c * d from by ring, hident]; ring
    rw [hexpand] at hstep
    have hpos : 0 < a ^ 2 + c ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    exact absurd hstep (not_le.mpr (mul_pos hcon hpos))

/-- **The full-support case of the two-coordinate reduction.** Given the cross
condition `ad = bc` and the dot condition `ab + cd ≤ 0`, some `t ∈ [0, 1]`
simultaneously zeroes `(1-t)a + tb` and `(1-t)c + td`. Split on `a = b`: if
so, `a = b = 0` is forced (else `d = c` from the cross condition and the dot
condition collapses to `a ^ 2 + c ^ 2 ≤ 0`), and the single-equation helper
solves the surviving equation in `c, d`. If `a ≠ b`, multiplying the first
equation by `d` and substituting the cross condition shows any solution of
the first equation solves the second; the single-equation helper (applied to
`a, b`, using `ab_nonpos_of_cross_dot`) supplies both the solution and its
bounds. -/
private theorem exists_unitMix_eq_zero_two_of_cross_dot {a b c d : ℝ}
    (hcross : a * d = b * c) (hdot : a * b + c * d ≤ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t) * a + t * b = 0 ∧ (1 - t) * c + t * d = 0 := by
  rcases eq_or_ne a b with hab | hab
  · subst hab
    have ha0 : a = 0 := by
      by_contra ha
      have hdc : d = c := by
        have hacd : a * (d - c) = 0 := by rw [mul_sub, hcross]; ring
        rcases mul_eq_zero.mp hacd with h | h
        · exact absurd h ha
        · linarith
      rw [hdc] at hdot
      exact ha (by nlinarith [sq_nonneg a, sq_nonneg c, hdot])
    have hcd : c * d ≤ 0 := by rw [ha0] at hdot; linarith
    obtain ⟨t, ht0, ht1, he2⟩ := exists_unitMix_eq_zero_of_mul_nonpos hcd
    exact ⟨t, ht0, ht1, by rw [ha0]; ring, he2⟩
  · have hab_nonpos : a * b ≤ 0 := ab_nonpos_of_cross_dot hcross hdot
    obtain ⟨t, ht0, ht1, he1⟩ := exists_unitMix_eq_zero_of_mul_nonpos hab_nonpos
    refine ⟨t, ht0, ht1, he1, ?_⟩
    have hmul : b * ((1 - t) * c + t * d) = 0 := by
      have hidentity : b * ((1 - t) * c + t * d) =
          d * ((1 - t) * a + t * b) + (1 - t) * (b * c - a * d) := by ring
      rw [hidentity, he1, hcross]; ring
    rcases mul_eq_zero.mp hmul with hb | hgoal
    · have ha : a ≠ 0 := fun ha0 => hab (ha0.trans hb.symm)
      have ht1' : t = 1 := by
        have : (1 - t) * a = 0 := by rw [hb] at he1; linarith [he1]
        rcases mul_eq_zero.mp this with h | h
        · linarith [h]
        · exact absurd h ha
      have hd0 : d = 0 := by
        have : a * d = 0 := by rw [hcross, hb]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h ha
        · exact h
      rw [ht1', hd0]; ring
    · exact hgoal

/-- The converse elimination: a common zero of the two affine combinations
forces the cross and dot conditions. `p·(ad-bc)` and `q·(ad-bc)` both vanish
(linear combinations of the two equations), and since `p + q = 1` they are
not both zero, forcing `ad = bc`. Similarly `p·(ab+cd)` and `q·(ab+cd)` are
each `≤ 0` (equal to `-q·(b²+d²)` and `-p·(a²+c²)` respectively), and their
sum is `(p+q)·(ab+cd) = ab+cd`. -/
private theorem cross_dot_of_exists_unitMix_eq_zero_two {a b c d p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1)
    (he1 : p * a + q * b = 0) (he2 : p * c + q * d = 0) :
    a * d = b * c ∧ a * b + c * d ≤ 0 := by
  have hp_ad : p * (a * d - b * c) = 0 := by linear_combination d * he1 - b * he2
  have hq_ad : q * (a * d - b * c) = 0 := by linear_combination a * he2 - c * he1
  have hcross : a * d = b * c := by
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      rw [hq1, one_mul] at hq_ad
      linarith [hq_ad]
    · rcases mul_eq_zero.mp hp_ad with h | h
      · exact absurd h hp0
      · linarith [h]
  have hq_dot : q * (a * b + c * d) = -(p * (a ^ 2 + c ^ 2)) := by
    linear_combination a * he1 + c * he2
  have hp_dot : p * (a * b + c * d) = -(q * (b ^ 2 + d ^ 2)) := by
    linear_combination b * he1 + d * he2
  have hq_dot_le : q * (a * b + c * d) ≤ 0 := by
    rw [hq_dot]; nlinarith [sq_nonneg a, sq_nonneg c, hp]
  have hp_dot_le : p * (a * b + c * d) ≤ 0 := by
    rw [hp_dot]; nlinarith [sq_nonneg b, sq_nonneg d, hq]
  refine ⟨hcross, ?_⟩
  nlinarith [hq_dot_le, hp_dot_le, hsum]

/-- **The two-coordinate characterization.** For `ι = Bool`, feasibility of
the singleton LCP is exactly a three-way disjunction: a pure witness at
`false` (needs a zero `(false, false)` entry and a nonnegative `(true,
false)` entry), a pure witness at `true` (symmetric), or a fully-mixed
witness, whose existence is exactly the cross/dot pair of algebraic
conditions on the four entries. -/
theorem singletonLCPFeasible_bool_iff (B : Bool → Bool → ℝ) :
    SingletonLCPFeasible B ↔
      (B false false = 0 ∧ 0 ≤ B true false) ∨
      (B true true = 0 ∧ 0 ≤ B false true) ∨
      (B false false * B true true = B false true * B true false ∧
        B false false * B false true + B true false * B true true ≤ 0) := by
  constructor
  · rintro ⟨lam, hnn, hcomp⟩
    have hsum : lam.val false + lam.val true = 1 := by
      have h2 := lam.property.2
      rw [Fintype.sum_bool] at h2
      linarith [h2]
    have hp0 : 0 ≤ lam.val false := lam.property.1 false
    have hq0 : 0 ≤ lam.val true := lam.property.1 true
    have hRfalse : singletonLCPResidual B lam false
        = lam.val false * B false false + lam.val true * B false true := by
      rw [singletonLCPResidual_def, wsum]
      simp only [dotProduct, Fintype.sum_bool]
      change lam.val true * B false true + lam.val false * B false false
          = lam.val false * B false false + lam.val true * B false true
      ring
    have hRtrue : singletonLCPResidual B lam true
        = lam.val false * B true false + lam.val true * B true true := by
      rw [singletonLCPResidual_def, wsum]
      simp only [dotProduct, Fintype.sum_bool]
      change lam.val true * B true true + lam.val false * B true false
          = lam.val false * B true false + lam.val true * B true true
      ring
    by_cases hq : lam.val true = 0
    · left
      have hp1 : lam.val false = 1 := by linarith [hsum, hq]
      have hcf := hcomp false
      rw [hRfalse, hp1, hq] at hcf
      have ha0 : B false false = 0 := by linarith [hcf]
      have hnt := hnn true
      rw [hRtrue, hp1, hq] at hnt
      have hc0 : 0 ≤ B true false := by linarith [hnt]
      exact ⟨ha0, hc0⟩
    · have hct := hcomp true
      rw [hRtrue] at hct
      have he2 : lam.val false * B true false + lam.val true * B true true = 0 := by
        rcases mul_eq_zero.mp hct with h | h
        · exact absurd h hq
        · exact h
      by_cases hp : lam.val false = 0
      · right; left
        have hq1 : lam.val true = 1 := by linarith [hsum, hp]
        have hd0 : B true true = 0 := by rw [hp, hq1] at he2; linarith [he2]
        have hnf := hnn false
        rw [hRfalse, hp, hq1] at hnf
        have hb0 : 0 ≤ B false true := by linarith [hnf]
        exact ⟨hd0, hb0⟩
      · right; right
        have hcf := hcomp false
        rw [hRfalse] at hcf
        have he1 : lam.val false * B false false + lam.val true * B false true = 0 := by
          rcases mul_eq_zero.mp hcf with h | h
          · exact absurd h hp
          · exact h
        exact cross_dot_of_exists_unitMix_eq_zero_two hp0 hq0 hsum he1 he2
  · rintro (⟨ha0, hc0⟩ | ⟨hd0, hb0⟩ | ⟨hcross, hdot⟩)
    · refine ⟨stdSimplex.pure (𝕜 := ℝ) false, fun i => ?_, fun i => ?_⟩
      · rw [singletonLCPResidual_def, wsum_pure_apply]
        cases i
        · simp [ha0]
        · simp [hc0]
      · rw [singletonLCPResidual_def, wsum_pure_apply, stdSimplex.pure_apply]
        cases i
        · simp [ha0]
        · simp
    · refine ⟨stdSimplex.pure (𝕜 := ℝ) true, fun i => ?_, fun i => ?_⟩
      · rw [singletonLCPResidual_def, wsum_pure_apply]
        cases i
        · simp [hb0]
        · simp [hd0]
      · rw [singletonLCPResidual_def, wsum_pure_apply, stdSimplex.pure_apply]
        cases i
        · simp
        · simp [hd0]
    · obtain ⟨t, ht0, ht1, he1, he2⟩ :=
        exists_unitMix_eq_zero_two_of_cross_dot hcross hdot
      have hmem : (fun i => if i then t else 1 - t) ∈ stdSimplex ℝ Bool := by
        refine ⟨fun i => ?_, ?_⟩
        · cases i <;> simp <;> linarith
        · rw [Fintype.sum_bool]; simp
      set lam : stdSimplex ℝ Bool := ⟨_, hmem⟩ with hlam_def
      have hlam_true : lam true = t := rfl
      have hlam_false : lam false = 1 - t := rfl
      have hlam_val_true : lam.val true = t := rfl
      have hlam_val_false : lam.val false = 1 - t := rfl
      refine ⟨lam, fun i => ?_, fun i => ?_⟩
      · rw [singletonLCPResidual_def, wsum]
        simp only [dotProduct, Fintype.sum_bool, hlam_true, hlam_false]
        cases i <;> nlinarith [he1, he2]
      · cases i
        · rw [singletonLCPResidual_def, wsum, hlam_val_false]
          simp only [dotProduct, Fintype.sum_bool, hlam_true, hlam_false]
          nlinarith [he1, he2]
        · rw [singletonLCPResidual_def, wsum, hlam_val_true]
          simp only [dotProduct, Fintype.sum_bool, hlam_true, hlam_false]
          nlinarith [he1, he2]

end BoolCase

/-! ## The support-pattern reduction

`SingletonLCPFeasible` is a single Prop over a real-valued witness `λ`, but
the complementarity condition forces its zero/nonzero pattern into a finite
alternative: `λ`'s support `S` is where the residual vanishes, and everywhere
else the residual only needs to stay nonnegative. This is the structure every
downstream finite check (in particular decidability, deliverable (4)) uses. -/

/-- **Support-pattern reduction.** `B` is singleton-LCP feasible iff there is
a nonempty coalition `S` and a simplex point `λ` supported on `S`
(`λ i = 0` off `S`) whose residual vanishes on `S` and stays nonnegative off
it. Given feasibility, `S` may be taken to be the exact support of the
witness `λ`; conversely, complementarity for any such `(S, λ)` pair is
automatic, since off `S` the factor `λ i` vanishes and on `S` the factor
`(Bλ) i` vanishes. -/
theorem singletonLCPFeasible_iff_exists_supportPattern (B : ι → ι → ℝ) :
    SingletonLCPFeasible B ↔
      ∃ (S : {S : Finset ι // S.Nonempty}) (lam : stdSimplex ℝ ι),
        (∀ i ∉ S.1, lam.val i = 0) ∧
        (∀ i ∈ S.1, singletonLCPResidual B lam i = 0) ∧
        (∀ i ∉ S.1, 0 ≤ singletonLCPResidual B lam i) := by
  classical
  constructor
  · rintro ⟨lam, hnn, hcomp⟩
    have hSne : (Finset.univ.filter (fun i => lam.val i ≠ 0)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
      have hzero : ∀ i, lam.val i = 0 := by
        intro i
        by_contra hne
        exact hempty (Finset.mem_univ i) hne
      have : (∑ i, lam.val i) = 0 := by simp [hzero]
      rw [lam.property.2] at this
      exact one_ne_zero this
    refine ⟨⟨Finset.univ.filter (fun i => lam.val i ≠ 0), hSne⟩, lam, ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases mul_eq_zero.mp (hcomp i) with h | h
      · exact absurd h hi
      · exact h
    · intro i _
      exact hnn i
  · rintro ⟨⟨S, hSne⟩, lam, hoff, hzero, hnnOff⟩
    refine ⟨lam, fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ S
      · rw [hzero i hi]
      · exact hnnOff i hi
    · by_cases hi : i ∈ S
      · rw [hzero i hi, mul_zero]
      · rw [hoff i hi, zero_mul]

/-! ## Game-facing instantiation

For a quitting weight assigning a payoff to every nonempty coalition (the
reward type used throughout, e.g. `QuittingZeroSoloDisjunct.lean`), the
singleton comparison matrix `Bᵢⱼ = r({j})ᵢ - r({i})ᵢ` measures player `i`'s
incentive to let `j` solo-terminate rather than solo-terminating itself.
Feasibility of its singleton LCP is the criterion the absorption-vanishing
equivalence of the pipeline record `exact-vs-relaxed` turns on. -/

variable {γ : Type} [Fintype γ]

/-- The singleton comparison matrix of a quitting reward: the `(i, j)` entry
is player `i`'s payoff when `j` solo-terminates minus player `i`'s payoff
when `i` itself solo-terminates. -/
def quittingSingletonMatrix
    (reward : {S : Finset γ // S.Nonempty} → GameTheory.Payoff γ) (i j : γ) : ℝ :=
  reward ⟨{j}, Finset.singleton_nonempty j⟩ i - reward ⟨{i}, Finset.singleton_nonempty i⟩ i

/-- **The normalized singleton LCP of a quitting reward.** Feasibility of the
singleton LCP for the reward's comparison matrix `quittingSingletonMatrix`. -/
def quittingSingletonLCPFeasible
    (reward : {S : Finset γ // S.Nonempty} → GameTheory.Payoff γ) : Prop :=
  SingletonLCPFeasible (quittingSingletonMatrix reward)

/-- Unfolding lemma: the game-facing predicate is exactly the singleton LCP
of the comparison matrix, spelled out in full. -/
theorem quittingSingletonLCPFeasible_iff
    (reward : {S : Finset γ // S.Nonempty} → GameTheory.Payoff γ) :
    quittingSingletonLCPFeasible reward ↔
      ∃ lam : stdSimplex ℝ γ,
        (∀ i, 0 ≤ singletonLCPResidual (quittingSingletonMatrix reward) lam i) ∧
        ∀ i, lam.val i * singletonLCPResidual (quittingSingletonMatrix reward) lam i = 0 :=
  Iff.rfl

end LinearProgramming
end Math
