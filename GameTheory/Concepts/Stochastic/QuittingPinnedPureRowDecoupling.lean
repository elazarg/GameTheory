/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclicWeightRowDichotomy

/-!
# The pinned-pure decoupling lemma

A certificate-search sweep found this structural fact empirically: at a row `x` with one
coordinate pinned pure (`x k = 1`), every other coordinate's continuation term vanishes,
so its `gainValue` becomes independent of the continuation ("next-phase") value entirely,
and the exact-complementarity conditions at the row collapse from a system coupling every
coordinate to `next` into a family of purely algebraic, per-coordinate conditions. This
file makes that fact a theorem in the real-hazard encoding of
`QuittingCyclicWeightRowDichotomy`: `sigmaValue`, `gammaValue`, `gainValue` over a general
finite index type `ι`, specialized where needed to the explicit rational weight
`cyclicWeight` on three cyclically ordered coordinates.

## Contents

* `continueMassExcl_eq_zero_of_pinned`, `gammaValue_eq_excludedValue_of_pinned`,
  `gainValue_eq_sigma_sub_excluded_of_pinned`, `gainValue_pinned_indep_next`: the
  decoupling, for a general finite `ι` and a general weight `r` (goal 1).
* `single_coordinate_condition_iff`: the univariate solvability characterization of the
  single-coordinate exact-complementarity condition against a fixed gain value -- its
  solution set is a point, an interval, or empty, according to the sign of the gain
  (goal 2's general half).
* `isExactRowComplementary_iff_of_pinned`: the whole-row exact-complementarity condition,
  at a pinned-pure row, reduces to the pinned coordinate's own condition together with the
  independent per-coordinate conditions at every other coordinate (goal 2's row-level
  reduction).
* `gainValue_cyclicWeight_pinned_of_pred`, `gainValue_cyclicWeight_pinned_of_succ`: the
  explicit affine formulas for `cyclicWeight`'s decoupled gain, with coefficients read off
  the weight table (goal 1's explicit half).
* `cyclicWeight_pinned_pred_condition_iff`, `cyclicWeight_pinned_succ_condition_iff`: the
  explicit solvability characterization for `cyclicWeight`'s two coordinate shapes
  (goal 2's explicit half).
* `gainValue_cyclicWeight_pinned_succ_eq_zero_iff`: the genericity corollary -- the
  boundary of the succ-pinned univariate condition sits at the single rational point
  `3 / 7`, an explicitly bounded denominator (goal 3).
* `cyclicPred_cyclicSucc`, `not_isExactRowComplementary_cyclicWeight_of_pinned`: for
  `cyclicWeight` specifically, chaining the two coordinate-shape formulas around the row
  shows the pinned coordinate's own condition is always violated, so no exactly
  complementary row of `cyclicWeight` has any coordinate pinned to `1` at all (a corollary
  of goals 1 and 2 together, independent of the next-phase value's sign).
-/

set_option autoImplicit false

namespace GameTheory

/-! ## Goal 1: decoupling, for a general finite index type and a general weight -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Decoupling, step one.** If coordinate `k` is pinned pure (`x k = 1`), then for every
other coordinate `i ≠ k`, the deleted continue mass `c_{-i}(x)` vanishes: `k` is one of the
coordinates other than `i`, and its survival factor `1 - x k` is one of the factors in the
product, so the whole product is `0`. -/
theorem continueMassExcl_eq_zero_of_pinned (x : ι → ℝ) (k i : ι) (hk : x k = 1) (hik : i ≠ k) :
    continueMassExcl x i = 0 := by
  unfold continueMassExcl
  have hmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
  have hval : (1 - x k) = 0 := by rw [hk]; ring
  exact Finset.prod_eq_zero hmem hval

/-- **Decoupling, step two.** With the deleted continue mass at `0`, `Γ_i` loses its
continuation term entirely: it equals the nonempty-coalition value `A_i`, regardless of
the continuation ("next-phase") value fed in. -/
theorem gammaValue_eq_excludedValue_of_pinned (r : Finset ι → ι → ℝ) (x : ι → ℝ) (k i : ι)
    (hk : x k = 1) (hik : i ≠ k) (next : ℝ) :
    gammaValue r x i next = excludedValue r x i := by
  unfold gammaValue
  rw [continueMassExcl_eq_zero_of_pinned x k i hk hik]
  ring

/-- **Decoupling, step three.** Consequently `g_i = Σ_i - Γ_i` reduces to `Σ_i - A_i`, an
expression built entirely from the row's other coordinates through the weight table `r`,
with no reference to the continuation value at all. -/
theorem gainValue_eq_sigma_sub_excluded_of_pinned (r : Finset ι → ι → ℝ) (x : ι → ℝ) (k i : ι)
    (hk : x k = 1) (hik : i ≠ k) (next : ℝ) :
    gainValue r x i next = sigmaValue r x i - excludedValue r x i := by
  unfold gainValue
  rw [gammaValue_eq_excludedValue_of_pinned r x k i hk hik]

/-- **Decoupling, restated as independence.** At a pinned-pure row, `gainValue` at any
other coordinate does not depend on which continuation value is supplied. -/
theorem gainValue_pinned_indep_next (r : Finset ι → ι → ℝ) (x : ι → ℝ) (k i : ι)
    (hk : x k = 1) (hik : i ≠ k) (next next' : ℝ) :
    gainValue r x i next = gainValue r x i next' := by
  rw [gainValue_eq_sigma_sub_excluded_of_pinned r x k i hk hik,
    gainValue_eq_sigma_sub_excluded_of_pinned r x k i hk hik]

/-! ## Goal 2: the exact-row reduction -/

/-- **The univariate solvability characterization.** Fix a coordinate value `x0 ∈ [0,1]`
and a gain `g`. The single-coordinate exact-complementarity condition
`(0 < x0 → 0 ≤ g) ∧ (x0 < 1 → g ≤ 0)` holds iff `g` is positive and `x0` is pinned to `1`,
or `g` is negative and `x0` is pinned to `0`, or `g` is exactly `0` (in which case `x0` is
unconstrained). Since the condition, for fixed `g`, is affine (indeed constant) in `x0`,
its solution set is always a single point (`{1}` or `{0}`) or the whole interval `[0,1]`
-- an interval, a point, or (when `g`'s sign is unattainable for the given bounds, though
that cannot happen here since `x0 ∈ [0,1]` is nonempty) empty. -/
theorem single_coordinate_condition_iff (x0 g : ℝ) (hx0 : 0 ≤ x0) (hx1 : x0 ≤ 1) :
    ((0 < x0 → 0 ≤ g) ∧ (x0 < 1 → g ≤ 0)) ↔
      (0 < g ∧ x0 = 1) ∨ (g < 0 ∧ x0 = 0) ∨ g = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy g 0 with hg | hg | hg
    · refine Or.inr (Or.inl ⟨hg, ?_⟩)
      by_contra hne
      exact absurd (h1 (lt_of_le_of_ne hx0 (Ne.symm hne))) (not_le.mpr hg)
    · exact Or.inr (Or.inr hg)
    · refine Or.inl ⟨hg, ?_⟩
      by_contra hne
      exact absurd (h2 (lt_of_le_of_ne hx1 hne)) (not_le.mpr hg)
  · rintro (⟨hg, hx⟩ | ⟨hg, hx⟩ | hg)
    · subst hx
      exact ⟨fun _ => le_of_lt hg, fun h => absurd h (lt_irrefl 1)⟩
    · subst hx
      exact ⟨fun h => absurd h (lt_irrefl 0), fun _ => le_of_lt hg⟩
    · subst hg
      exact ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The row-level reduction.** At a pinned-pure row (`x k = 1`), `IsExactRowComplementary`
reduces to: the pinned coordinate's own condition (only `0 ≤ g k` survives, since
`x k = 1` is never `< 1`), conjoined with the ordinary two-sided condition at every other
coordinate -- independent conditions, one per coordinate, since (by the decoupling above)
each `g i` for `i ≠ k` no longer references the continuation value. -/
theorem isExactRowComplementary_iff_of_pinned (x g : ι → ℝ) (k : ι) (hk : x k = 1) :
    IsExactRowComplementary x g ↔
      0 ≤ g k ∧ ∀ i, i ≠ k → (0 < x i → 0 ≤ g i) ∧ (x i < 1 → g i ≤ 0) := by
  unfold IsExactRowComplementary
  constructor
  · intro h
    exact ⟨(h k).1 (by rw [hk]; norm_num), fun i _ => h i⟩
  · rintro ⟨hgk, hrest⟩ i
    by_cases hik : i = k
    · subst hik
      exact ⟨fun _ => hgk, fun hlt => absurd hlt (by rw [hk]; norm_num)⟩
    · exact hrest i hik

/-! ## The explicit rational weight: affine coefficients from the table -/

/-- **Goal 1, explicit form: the pred-pinned coordinate.** If `i`'s predecessor is pinned
pure, `gainValue` at `i` collapses to the constant `-1`, independent of both the
continuation value and of `i`'s remaining free neighbor `x (cyclicSucc i)`: the weight
table's contribution from the successor's hazard is itself killed by the vanishing
`(1 - x (cyclicPred i))` factor in equation (15). -/
theorem gainValue_cyclicWeight_pinned_of_pred (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hk : x (cyclicPred i) = 1) (next : ℝ) :
    gainValue cyclicWeight x i next = -1 := by
  rw [gainValue_cyclicWeight, hk]; ring

/-- **Goal 1, explicit form: the succ-pinned coordinate.** If `i`'s successor is pinned
pure, `gainValue` at `i` collapses to the affine function `3/4 - (7/4) * x (cyclicPred i)`
of the single remaining free coordinate, with coefficients read directly off equation (15)
once `x (cyclicSucc i) = 1` is substituted. -/
theorem gainValue_cyclicWeight_pinned_of_succ (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hk : x (cyclicSucc i) = 1) (next : ℝ) :
    gainValue cyclicWeight x i next = 3 / 4 - 7 / 4 * x (cyclicPred i) := by
  rw [gainValue_cyclicWeight, hk]; ring

/-- **Goal 2, explicit form: the pred-pinned coordinate's condition.** Combining
`gainValue_cyclicWeight_pinned_of_pred` with `single_coordinate_condition_iff`: since the
collapsed gain is the negative constant `-1`, the single-coordinate condition at `i` holds
iff `x i = 0` -- unconditionally, for any value of the remaining free neighbor. -/
theorem cyclicWeight_pinned_pred_condition_iff (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hx0 : 0 ≤ x i) (hx1 : x i ≤ 1) (hk : x (cyclicPred i) = 1) (next : ℝ) :
    ((0 < x i → 0 ≤ gainValue cyclicWeight x i next) ∧
        (x i < 1 → gainValue cyclicWeight x i next ≤ 0)) ↔ x i = 0 := by
  rw [gainValue_cyclicWeight_pinned_of_pred x i hk next,
    single_coordinate_condition_iff (x i) (-1 : ℝ) hx0 hx1]
  constructor
  · rintro (⟨hg, _⟩ | ⟨_, hxe⟩ | hg)
    · linarith
    · exact hxe
    · linarith
  · intro hxe
    exact Or.inr (Or.inl ⟨by norm_num, hxe⟩)

/-- **Goal 2, explicit form: the succ-pinned coordinate's condition.** Combining
`gainValue_cyclicWeight_pinned_of_succ` with `single_coordinate_condition_iff`: the
single-coordinate condition at `i` holds iff the remaining free hazard
`x (cyclicPred i)` and `x i` satisfy exactly one of three mutually exclusive cases --
free hazard below `3/7` and `i` pinned active; free hazard above `3/7` and `i` pinned
inert; or free hazard exactly `3/7`, leaving `x i` unconstrained. The solution set for
`x (cyclicPred i)` under each target value of `x i` is correspondingly a half-open
interval or a single point: never anything more complicated, since the governing
condition is affine. -/
theorem cyclicWeight_pinned_succ_condition_iff (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hx0 : 0 ≤ x i) (hx1 : x i ≤ 1) (hk : x (cyclicSucc i) = 1) (next : ℝ) :
    ((0 < x i → 0 ≤ gainValue cyclicWeight x i next) ∧
        (x i < 1 → gainValue cyclicWeight x i next ≤ 0)) ↔
      (x (cyclicPred i) < 3 / 7 ∧ x i = 1) ∨
        (x (cyclicPred i) > 3 / 7 ∧ x i = 0) ∨ x (cyclicPred i) = 3 / 7 := by
  rw [gainValue_cyclicWeight_pinned_of_succ x i hk next,
    single_coordinate_condition_iff (x i) (3 / 4 - 7 / 4 * x (cyclicPred i)) hx0 hx1]
  constructor
  · rintro (⟨hg, hxe⟩ | ⟨hg, hxe⟩ | hg)
    · exact Or.inl ⟨by linarith, hxe⟩
    · exact Or.inr (Or.inl ⟨by linarith, hxe⟩)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (⟨hp, hxe⟩ | ⟨hp, hxe⟩ | hp)
    · exact Or.inl ⟨by linarith, hxe⟩
    · exact Or.inr (Or.inl ⟨by linarith, hxe⟩)
    · exact Or.inr (Or.inr (by linarith))

/-! ## Goal 3: the genericity corollary -/

/-- **Genericity corollary.** In the succ-pinned case, `gainValue` at `i` vanishes --
leaving `x i` unconstrained by the single-coordinate condition -- exactly when the
remaining free hazard `x (cyclicPred i)` hits the single rational point `3/7`. The
weight table's entries have denominators dividing `4`; combining the `3/4` and `1`
(from `-p`) coefficients of the affine map `p ↦ 3/4 - (7/4) p` through equation (15)
produces a boundary point of denominator `7`, not some larger denominator accumulated
from iterating the construction: whenever the succ-pinned univariate condition is
solvable at its boundary, it is solvable at this one explicit, bounded-denominator
point. -/
theorem gainValue_cyclicWeight_pinned_succ_eq_zero_iff (x : CyclicIndex → ℝ) (i : CyclicIndex)
    (hk : x (cyclicSucc i) = 1) (next : ℝ) :
    gainValue cyclicWeight x i next = 0 ↔ x (cyclicPred i) = 3 / 7 := by
  rw [gainValue_cyclicWeight_pinned_of_succ x i hk next]
  constructor <;> intro h <;> linarith

/-! ## A further corollary: no pinned-pure row of `cyclicWeight` is exactly complementary -/

/-- `π` is also a right inverse of `σ` on the three-cycle (the source file only records
`cyclicSucc_cyclicPred`, the left inverse). Used to identify "`i`'s predecessor is `k`"
from "`i` is `k`'s successor". -/
theorem cyclicPred_cyclicSucc (i : CyclicIndex) : cyclicPred (cyclicSucc i) = i := by
  fin_cases i <;> decide

/-- **A further corollary of goals 1 and 2, for `cyclicWeight` specifically.** Chain the
two coordinate-shape formulas around the pinned coordinate `k`: the successor of `k` is
forced inert (its own condition is the constant `-1`), which forces the predecessor of `k`
active (its condition becomes `3/4 - 0 = 3/4 > 0`) -- and then `k`'s own condition, which
is *not* decoupled from the continuation value, evaluates via `gainValue_cyclicWeight` to
`-1` from these two forced neighbor values, violating `0 ≤ g k`. So no exactly
complementary row of `cyclicWeight` has any coordinate pinned to `1`, for any next-phase
value `z` whatsoever (unlike `atMostOnePositive_of_isExactRowComplementary`, this needs no
`0 ≤ z j` hypothesis, precisely because the decoupled coordinates' conditions never see
`z`). This shows, in this one instance, that admissibility -- consistency with the
*other* coordinates' forced values and with the pinned coordinate's own, non-decoupled
condition -- rather than solvability of any single univariate condition in isolation, is
what rules the row out. -/
theorem not_isExactRowComplementary_cyclicWeight_of_pinned (x z : CyclicIndex → ℝ)
    (k : CyclicIndex) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hk : x k = 1) :
    ¬ IsExactRowComplementary x (fun i => gainValue cyclicWeight x i (z i - 1 / 2)) := by
  intro hcompl
  -- The successor of `k` has `k` as its predecessor, so its condition is `x i = 0`.
  have hpred1 : x (cyclicPred (cyclicSucc k)) = 1 := by rw [cyclicPred_cyclicSucc]; exact hk
  have hgain1 : gainValue cyclicWeight x (cyclicSucc k) (z (cyclicSucc k) - 1 / 2) = -1 :=
    gainValue_cyclicWeight_pinned_of_pred x (cyclicSucc k) hpred1 _
  have hx1_le : x (cyclicSucc k) ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have h := (hcompl (cyclicSucc k)).1 hlt
    dsimp only at h
    rw [hgain1] at h
    linarith
  have hx1 : x (cyclicSucc k) = 0 := le_antisymm hx1_le (hx (cyclicSucc k)).1
  -- The predecessor of `k` has `k` as its successor, so its condition forces `x i = 1`
  -- once the just-derived `x (cyclicSucc k) = 0` is substituted for its free neighbor.
  have hsucc2 : x (cyclicSucc (cyclicPred k)) = 1 := by rw [cyclicSucc_cyclicPred]; exact hk
  have hpred2 : cyclicPred (cyclicPred k) = cyclicSucc k := cyclicPred_cyclicPred_eq_cyclicSucc k
  have hgain2 : gainValue cyclicWeight x (cyclicPred k) (z (cyclicPred k) - 1 / 2) =
      3 / 4 - 7 / 4 * x (cyclicSucc k) := by
    rw [gainValue_cyclicWeight_pinned_of_succ x (cyclicPred k) hsucc2, hpred2]
  have hgain2' : gainValue cyclicWeight x (cyclicPred k) (z (cyclicPred k) - 1 / 2) = 3 / 4 := by
    rw [hgain2, hx1]; ring
  have hx2 : x (cyclicPred k) = 1 := by
    by_contra hlt
    have hle : x (cyclicPred k) < 1 := lt_of_le_of_ne (hx (cyclicPred k)).2 hlt
    have h := (hcompl (cyclicPred k)).2 hle
    dsimp only at h
    rw [hgain2'] at h
    linarith
  -- `k`'s own condition is not decoupled, and fails against the two forced values.
  have hgk : gainValue cyclicWeight x k (z k - 1 / 2) = -1 := by
    rw [gainValue_cyclicWeight, hx1, hx2]; ring
  have hkcond := (hcompl k).1 (by rw [hk]; norm_num)
  dsimp only at hkcond
  rw [hgk] at hkcond
  linarith

/-! ## Consequence for the periodic argument (docstring only, not a theorem)

The sweep's broader point is not formalized here as a theorem, since it concerns the
surrounding periodic argument built outside this file: whether an exactly complementary
period-one row can pass through a pinned-pure configuration `x k = 1` is governed
entirely by the univariate conditions above. Each remaining coordinate's condition,
once decoupled from the continuation value, is a single affine constraint (for
`cyclicWeight`, literally affine in one real variable) -- so its solvability is a
closed-form question with an explicit boundary, not a search problem. This is why, at
period one, **admissibility is the discriminating filter, not existence**: a univariate
condition being individually solvable (as the succ-pinned one always is, e.g. at the
boundary `x (cyclicPred i) = 3/7`, or by taking the free hazard below/above it) does not
by itself produce a valid row. The row also has to reconcile that per-coordinate solution
with every other coordinate's forced value and with the pinned coordinate's own,
non-decoupled condition -- and, one level up in the periodic construction that this file
does not build, with fitting into a consistent cycle across phases at all. For
`cyclicWeight` specifically that reconciliation always fails
(`not_isExactRowComplementary_cyclicWeight_of_pinned`), but the shape of the
argument -- decouple, solve each univariate condition in closed form, then check
consistency -- is the general pattern the sweep found, independent of which weight
table is in play.
-/

end GameTheory
