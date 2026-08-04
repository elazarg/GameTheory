/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# A cyclic max-affine system and its survival-weighted bound

Fix a length `L`, rates `p k ≥ 0` and survival factors `q k ∈ [0, 1]`, and
consider the cyclic system

    C k = max (1 - p k) (q k * C (k + 1) + p k),   indices read mod `L`.

Write `P = ∏_{k < L} q k` for the *deleted survival product* and

    W = ∑_{k < L} (∏_{k' < k} q k') * p k

for the *survival-weighted accumulated rate* — each rate weighted by the
product of the survival factors strictly before it, not counted raw.  As soon
as `P < 1`, the value at the base point is pinned between

    W / (1 - P)  ≤  C 0  ≤  max (W / (1 - P)) (W + 1).

The consequence worth having is `CyclicSolution.le_max_of_sum_le`: if
`∑_{k < L} p k ≤ A` then

    C 0  ≤  max (A / (1 - P)) (A + 1),

a bound by the accumulated rate and the deleted survival product with **no
dependence on `L`**.

## Main results

* `CyclicSolution.weightedRate_div_le` — the lower bound.
* `CyclicSolution.le_max_weightedRate` — the upper bound.
* `CyclicSolution.le_max_of_sum_le` — the `L`-free corollary.
* `CyclicSolution.unique_at_zero` — the solution is unique at the base point.
* `fin_weightedRate_bounds`, `fin_le_max_of_sum_le` — both in genuinely cyclic
  `Fin L` form.

## Formalization notes

The cycle is unrolled as a *linear* chain of length `L` indexed by `ℕ`, with
the cyclic identification imposed only at the wrap point, as `C L = C 0`
(`CyclicSolution.wrap`).  This avoids all modular index arithmetic; the
`Fin L` phrasing is recovered in the last section.

Nothing here asserts that a solution exists: every statement is about an
arbitrary solution, which is the stronger form.

Neither `p k ≤ 1` nor `0 < q k` is ever needed.  `0 < L` is not assumed
either: `P < 1` already rules out `L = 0`, whose empty product is `1`.
-/

namespace Math.CyclicMaxAffine

open Finset

/-- The product of the survival factors strictly before phase `k`. -/
noncomputable def survivalProduct (q : ℕ → ℝ) (k : ℕ) : ℝ := ∏ i ∈ range k, q i

/-- The survival-weighted accumulated rate of the first `L` phases: each rate
`p k` is weighted by the product of the survival factors strictly before it. -/
noncomputable def weightedRate (p q : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ k ∈ range L, survivalProduct q k * p k

/-- A solution of the cyclic max-affine system of length `L`, unrolled as a
linear chain with the cyclic value substituted at the end.

Only the phases `k < L` are constrained, so `p`, `q`, `C` are unrestricted
beyond the cycle; the wrap condition `C L = C 0` is what closes the chain up
into a cycle. -/
structure CyclicSolution (p q C : ℕ → ℝ) (L : ℕ) : Prop where
  /-- The rates are nonnegative. -/
  rate_nonneg : ∀ k, 0 ≤ p k
  /-- The survival factors are nonnegative. -/
  survival_nonneg : ∀ k, 0 ≤ q k
  /-- The survival factors are at most one. -/
  survival_le_one : ∀ k, q k ≤ 1
  /-- Each phase of the cycle solves its max-affine equation. -/
  eq_max : ∀ k < L, C k = max (1 - p k) (q k * C (k + 1) + p k)
  /-- The chain closes up into a cycle. -/
  wrap : C L = C 0

section Basic

variable {p q : ℕ → ℝ}

@[simp] theorem survivalProduct_zero : survivalProduct q 0 = 1 := by
  simp [survivalProduct]

theorem survivalProduct_succ (k : ℕ) :
    survivalProduct q (k + 1) = survivalProduct q k * q k := by
  simp [survivalProduct, Finset.prod_range_succ]

theorem survivalProduct_nonneg (hq : ∀ i, 0 ≤ q i) (k : ℕ) :
    0 ≤ survivalProduct q k :=
  Finset.prod_nonneg fun i _ => hq i

theorem survivalProduct_le_one (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (k : ℕ) :
    survivalProduct q k ≤ 1 :=
  Finset.prod_le_one (fun i _ => hq0 i) fun i _ => hq1 i

@[simp] theorem weightedRate_zero : weightedRate p q 0 = 0 := by
  simp [weightedRate]

theorem weightedRate_succ (k : ℕ) :
    weightedRate p q (k + 1) = weightedRate p q k + survivalProduct q k * p k := by
  simp [weightedRate, Finset.sum_range_succ]

theorem weightedRate_nonneg (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (L : ℕ) :
    0 ≤ weightedRate p q L :=
  Finset.sum_nonneg fun k _ => mul_nonneg (survivalProduct_nonneg hq k) (hp k)

/-- A partial survival-weighted rate never exceeds the total. -/
theorem weightedRate_mono (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {m L : ℕ} (hm : m ≤ L) :
    weightedRate p q m ≤ weightedRate p q L :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset.mpr fun _ hx => Finset.mem_range.mpr (lt_of_lt_of_le hx hm))
    fun k _ _ => mul_nonneg (survivalProduct_nonneg hq k) (hp k)

/-- Weighting by survival can only shrink the accumulated rate. -/
theorem weightedRate_le_sum (hp : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (L : ℕ) : weightedRate p q L ≤ ∑ k ∈ range L, p k := by
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : survivalProduct q k ≤ 1 := survivalProduct_le_one hq0 hq1 k
  nlinarith [hp k, survivalProduct_nonneg hq0 k]

end Basic

section Unrolling

variable {p q C : ℕ → ℝ} {L : ℕ}

/-- **Affine unrolling.**  If the max is resolved to its affine branch at every
phase below `m`, the base value is exactly the weighted rate of the first `m`
phases plus the surviving remainder. -/
theorem prefix_eq (p q C : ℕ → ℝ) :
    ∀ m, (∀ k < m, C k = q k * C (k + 1) + p k) →
      C 0 = weightedRate p q m + survivalProduct q m * C m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro haffine
      have hm : C 0 = weightedRate p q m + survivalProduct q m * C m :=
        ih fun k hk => haffine k (by omega)
      rw [hm, weightedRate_succ, survivalProduct_succ, haffine m (by omega)]
      ring

/-- **Sub-affine unrolling.**  The `max` dominates its affine branch, so every
prefix of the chain bounds the base value from below. -/
theorem CyclicSolution.prefix_le (h : CyclicSolution p q C L) :
    ∀ m ≤ L, weightedRate p q m + survivalProduct q m * C m ≤ C 0 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      have hprev : weightedRate p q m + survivalProduct q m * C m ≤ C 0 := ih (by omega)
      have hstep : q m * C (m + 1) + p m ≤ C m := by
        rw [h.eq_max m hmL]
        exact le_max_right _ _
      have hsurv : 0 ≤ survivalProduct q m := survivalProduct_nonneg h.survival_nonneg m
      have hscaled := mul_le_mul_of_nonneg_left hstep hsurv
      rw [weightedRate_succ, survivalProduct_succ]
      nlinarith [hscaled]

/-- **The prefix dichotomy.**  Walking forward from the base point, either the
affine branch is taken all the way to `m` — and then the base value is the
weighted rate plus the surviving remainder — or some earlier phase `j` takes
the capped branch `1 - p j`, and the base value is pinned by that phase. -/
theorem CyclicSolution.prefix_dichotomy (h : CyclicSolution p q C L) :
    ∀ m ≤ L,
      C 0 = weightedRate p q m + survivalProduct q m * C m ∨
        ∃ j < m, C 0 = weightedRate p q j + survivalProduct q j * (1 - p j) := by
  intro m
  induction m with
  | zero => intro _; exact Or.inl (by simp)
  | succ m ih =>
      intro hm
      have hmL : m < L := by omega
      rcases ih (by omega) with haffine | ⟨j, hj, hjval⟩
      · by_cases hstep : C m = q m * C (m + 1) + p m
        · refine Or.inl ?_
          rw [weightedRate_succ, survivalProduct_succ, haffine, hstep]
          ring
        · have hcap : C m = 1 - p m := by
            have hmax := h.eq_max m hmL
            rcases max_choice (1 - p m) (q m * C (m + 1) + p m) with hc | hc
            · rw [hmax, hc]
            · exact absurd (hmax.trans hc) hstep
          exact Or.inr ⟨m, by omega, by rw [haffine, hcap]⟩
      · exact Or.inr ⟨j, by omega, hjval⟩

end Unrolling

section MainEstimate

variable {p q C : ℕ → ℝ} {L : ℕ}

/-- **Lower bound.**  The base value of any solution is at least the
survival-weighted accumulated rate divided by one minus the deleted survival
product. -/
theorem CyclicSolution.weightedRate_div_le (h : CyclicSolution p q C L)
    (hP : survivalProduct q L < 1) :
    weightedRate p q L / (1 - survivalProduct q L) ≤ C 0 := by
  have hchain := h.prefix_le L le_rfl
  rw [h.wrap] at hchain
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hchain]

/-- **Upper bound.**  The base value of any solution is at most the larger of
the purely affine value `W / (1 - P)` and the capped value `W + 1`. -/
theorem CyclicSolution.le_max_weightedRate (h : CyclicSolution p q C L)
    (hP : survivalProduct q L < 1) :
    C 0 ≤ max (weightedRate p q L / (1 - survivalProduct q L)) (weightedRate p q L + 1) := by
  have hne : (1 : ℝ) - survivalProduct q L ≠ 0 := by intro hc; linarith
  rcases h.prefix_dichotomy L le_rfl with haffine | ⟨j, hj, hjval⟩
  · rw [h.wrap] at haffine
    have hval : C 0 = weightedRate p q L / (1 - survivalProduct q L) := by
      rw [eq_div_iff hne]
      linear_combination haffine
    rw [hval]
    exact le_max_left _ _
  · refine le_trans (le_of_eq hjval) (le_trans ?_ (le_max_right _ _))
    have hpre : weightedRate p q j ≤ weightedRate p q L :=
      weightedRate_mono h.rate_nonneg h.survival_nonneg (by omega)
    have hs0 : 0 ≤ survivalProduct q j := survivalProduct_nonneg h.survival_nonneg j
    have hs1 : survivalProduct q j ≤ 1 :=
      survivalProduct_le_one h.survival_nonneg h.survival_le_one j
    have hcap : survivalProduct q j * (1 - p j) ≤ 1 := by
      nlinarith [mul_nonneg hs0 (h.rate_nonneg j), hs1]
    linarith

/-- If no phase caps — the max resolves to its affine branch everywhere — the
base value is exactly `W / (1 - P)`, the left endpoint of the estimate. -/
theorem CyclicSolution.eq_div_of_affine (h : CyclicSolution p q C L)
    (hP : survivalProduct q L < 1) (haffine : ∀ k < L, C k = q k * C (k + 1) + p k) :
    C 0 = weightedRate p q L / (1 - survivalProduct q L) := by
  have heq := prefix_eq p q C L haffine
  rw [h.wrap] at heq
  rw [eq_div_iff (by intro hc; linarith)]
  linear_combination heq

/-- **The main estimate**, both bounds at once. -/
theorem CyclicSolution.weightedRate_bounds (h : CyclicSolution p q C L)
    (hP : survivalProduct q L < 1) :
    weightedRate p q L / (1 - survivalProduct q L) ≤ C 0 ∧
      C 0 ≤ max (weightedRate p q L / (1 - survivalProduct q L)) (weightedRate p q L + 1) :=
  ⟨h.weightedRate_div_le hP, h.le_max_weightedRate hP⟩

/-- **The usable corollary.**  A bound on the raw accumulated rate bounds the
base value in terms of that rate and the deleted survival product alone, with
no dependence on the cycle length `L`. -/
theorem CyclicSolution.le_max_of_sum_le (h : CyclicSolution p q C L)
    (hP : survivalProduct q L < 1) {A : ℝ} (hA : ∑ k ∈ range L, p k ≤ A) :
    C 0 ≤ max (A / (1 - survivalProduct q L)) (A + 1) := by
  have hpos : (0 : ℝ) < 1 - survivalProduct q L := by linarith
  have hW : weightedRate p q L ≤ A :=
    le_trans (weightedRate_le_sum h.rate_nonneg h.survival_nonneg h.survival_le_one L) hA
  refine le_trans (h.le_max_weightedRate hP) (max_le_max ?_ (by linarith))
  exact div_le_div_of_nonneg_right hW hpos.le

/-- Uniqueness at the base point: the phase maps are `q k`-Lipschitz, so their
composite around the cycle is `P`-Lipschitz and `P < 1` pins the base value. -/
theorem CyclicSolution.unique_at_zero {C' : ℕ → ℝ} (h : CyclicSolution p q C L)
    (h' : CyclicSolution p q C' L) (hP : survivalProduct q L < 1) :
    C 0 = C' 0 := by
  have step : ∀ m ≤ L, |C 0 - C' 0| ≤ survivalProduct q m * |C m - C' m| := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        have hmL : m < L := by omega
        have hprev := ih (by omega)
        have hdiff : |C m - C' m| ≤ q m * |C (m + 1) - C' (m + 1)| := by
          have hrw : C m - C' m =
              max (q m * C (m + 1) + p m) (1 - p m) -
                max (q m * C' (m + 1) + p m) (1 - p m) := by
            rw [h.eq_max m hmL, h'.eq_max m hmL, max_comm (1 - p m), max_comm (1 - p m)]
          rw [hrw]
          refine le_trans (abs_max_sub_max_le_abs _ _ _) (le_of_eq ?_)
          rw [show q m * C (m + 1) + p m - (q m * C' (m + 1) + p m)
              = q m * (C (m + 1) - C' (m + 1)) by ring, abs_mul,
            abs_of_nonneg (h.survival_nonneg m)]
        have hs : 0 ≤ survivalProduct q m := survivalProduct_nonneg h.survival_nonneg m
        rw [survivalProduct_succ]
        nlinarith [mul_le_mul_of_nonneg_left hdiff hs]
  have hL := step L le_rfl
  rw [h.wrap, h'.wrap] at hL
  have hnn : 0 ≤ |C 0 - C' 0| := abs_nonneg _
  have hz : |C 0 - C' 0| = 0 := le_antisymm (by nlinarith) hnn
  linarith [abs_eq_zero.mp hz]

end MainEstimate

/-!
### Sharpness

Both bounds are attained, so neither can be improved, and the hypotheses are
not vacuous.
-/

section Sharpness

-- `L = 1`, `p = 0`, `q = 1/2`: the capped branch binds, `W = 0`, `P = 1/2`,
-- and `C 0 = 1` equals the upper bound `max (W / (1 - P)) (W + 1) = 1`.
example :
    CyclicSolution (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ) / 2) (fun _ => (1 : ℝ)) 1 ∧
      max (weightedRate (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ) / 2) 1 /
          (1 - survivalProduct (fun _ => (1 : ℝ) / 2) 1))
        (weightedRate (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ) / 2) 1 + 1) = 1 :=
  ⟨{ rate_nonneg := fun _ => le_refl 0
     survival_nonneg := fun _ => by norm_num
     survival_le_one := fun _ => by norm_num
     eq_max := fun _ _ => by norm_num
     wrap := rfl },
   by norm_num [weightedRate, survivalProduct]⟩

-- `L = 1`, `p = q = 9/10`: the affine branch binds, `W = P = 9/10`, and
-- `C 0 = 9` equals the lower bound `W / (1 - P) = 9`.
example :
    CyclicSolution (fun _ => (9 : ℝ) / 10) (fun _ => (9 : ℝ) / 10) (fun _ => (9 : ℝ)) 1 ∧
      weightedRate (fun _ => (9 : ℝ) / 10) (fun _ => (9 : ℝ) / 10) 1 /
        (1 - survivalProduct (fun _ => (9 : ℝ) / 10) 1) = 9 :=
  ⟨{ rate_nonneg := fun _ => by norm_num
     survival_nonneg := fun _ => by norm_num
     survival_le_one := fun _ => by norm_num
     eq_max := fun _ _ => by norm_num
     wrap := rfl },
   by norm_num [weightedRate, survivalProduct]⟩

end Sharpness

section FinPhrasing

-- The coercion `ℕ → Fin L` is not a global instance; it is what reads indices cyclically.
open Fin.NatCast

variable {L : ℕ} [NeZero L]

/-- Casting `ℕ` into `Fin L` intertwines successor with the cyclic successor. -/
theorem natCast_succ_fin (k : ℕ) :
    ((k + 1 : ℕ) : Fin L) = ((k : ℕ) : Fin L) + 1 := by
  apply Fin.val_injective
  simp [Fin.val_add, Fin.val_natCast, Nat.add_mod]

/-- The unrolled survival product of a `Fin L`-indexed cycle is the product of
all its survival factors. -/
theorem survivalProduct_natCast (q : Fin L → ℝ) :
    survivalProduct (fun i => q (i : Fin L)) L = ∏ k : Fin L, q k := by
  rw [survivalProduct, ← Fin.prod_univ_eq_prod_range (fun i : ℕ => q (i : Fin L)) L]
  simp

/-- The unrolled rate sum of a `Fin L`-indexed cycle is the sum of all its
rates. -/
theorem sum_natCast (p : Fin L → ℝ) :
    ∑ k ∈ range L, p ((k : ℕ) : Fin L) = ∑ k : Fin L, p k := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => p (i : Fin L)) L]
  simp

/-- A genuinely cyclic `Fin L`-indexed solution unrolls to a `CyclicSolution`. -/
theorem cyclicSolution_of_fin {p q C : Fin L → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hC : ∀ k, C k = max (1 - p k) (q k * C (k + 1) + p k)) :
    CyclicSolution (fun i => p (i : Fin L)) (fun i => q (i : Fin L))
      (fun i => C (i : Fin L)) L where
  rate_nonneg _ := hp _
  survival_nonneg _ := hq0 _
  survival_le_one _ := hq1 _
  eq_max k _ := by
    simp only [natCast_succ_fin]
    exact hC _
  wrap := by simp

/-- The survival-weighted accumulated rate of a `Fin L`-indexed cycle: each
rate `p k` is weighted by the product of the survival factors at the phases
strictly before `k`. -/
noncomputable def finWeightedRate (p q : Fin L → ℝ) : ℝ :=
  ∑ k : Fin L, (∏ i ∈ range (k : ℕ), q (i : Fin L)) * p k

theorem finWeightedRate_eq (p q : Fin L → ℝ) :
    finWeightedRate p q = weightedRate (fun i => p (i : Fin L)) (fun i => q (i : Fin L)) L := by
  rw [finWeightedRate, weightedRate,
    ← Fin.sum_univ_eq_sum_range
      (fun k : ℕ => survivalProduct (fun i => q (i : Fin L)) k * p ((k : ℕ) : Fin L)) L]
  exact Finset.sum_congr rfl fun k _ => by simp [survivalProduct]

/-- **The main estimate in cyclic `Fin L` form.** -/
theorem fin_weightedRate_bounds {p q C : Fin L → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hC : ∀ k, C k = max (1 - p k) (q k * C (k + 1) + p k))
    (hP : ∏ k : Fin L, q k < 1) :
    finWeightedRate p q / (1 - ∏ k : Fin L, q k) ≤ C 0 ∧
      C 0 ≤ max (finWeightedRate p q / (1 - ∏ k : Fin L, q k)) (finWeightedRate p q + 1) := by
  have hsol := cyclicSolution_of_fin hp hq0 hq1 hC
  have hprod : survivalProduct (fun i => q (i : Fin L)) L = ∏ k : Fin L, q k :=
    survivalProduct_natCast q
  have hbound := hsol.weightedRate_bounds (by rw [hprod]; exact hP)
  rw [hprod, ← finWeightedRate_eq] at hbound
  simpa using hbound

/-- **The corollary in cyclic `Fin L` form.**  For any solution of the cyclic
system on `Fin L` whose rates sum to at most `A`, the base value is bounded by
`max (A / (1 - P)) (A + 1)` with `P = ∏ k, q k` — independently of `L`. -/
theorem fin_le_max_of_sum_le {p q C : Fin L → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hC : ∀ k, C k = max (1 - p k) (q k * C (k + 1) + p k))
    (hP : ∏ k : Fin L, q k < 1) {A : ℝ} (hA : ∑ k : Fin L, p k ≤ A) :
    C 0 ≤ max (A / (1 - ∏ k : Fin L, q k)) (A + 1) := by
  have hsol := cyclicSolution_of_fin hp hq0 hq1 hC
  have hprod : survivalProduct (fun i => q (i : Fin L)) L = ∏ k : Fin L, q k :=
    survivalProduct_natCast q
  have hbound := hsol.le_max_of_sum_le (A := A) (by rw [hprod]; exact hP)
    (by rw [sum_natCast]; exact hA)
  rw [hprod] at hbound
  simpa using hbound

end FinPhrasing

end Math.CyclicMaxAffine
