/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRootEndpointBackwardStability
import GameTheory.Concepts.Stochastic.QuittingRelaxedHazardRowBridge

/-!
# The lens identity, leg one: the backward condition number is the weighted-
# to-unweighted conversion factor

Three quantities in the exact-vs-relaxed-cycle program are conjectured to be
one phenomenon: the backward-stability condition number (S1,
`QuittingRootEndpointBackwardStability.lean`), the lock margin, and
the `ε`-bridge's weighted-gain weakness at extreme hazards
(`QuittingRelaxedHazardRowBridge.lean`'s
`exists_weighted_bound_not_isεRowComplementary`). This file proves the first
leg: the backward condition number and the weighted-to-unweighted conversion
factor are not merely analogous, they are *the same arithmetic step* applied
to *the same pair of inequalities*.

## The mechanism

A single `who`-clause of `IsεQuittingRootEndpointNash` is exactly the pair
`y * g ≤ ε` and `-ε ≤ x * g`, where `x = (root who true).toReal` is the Quit
probability, `y = (root who false).toReal` the Continue probability, and `g`
the raw (unweighted) endpoint gap `quittingRootEndpointDifference`. Reading
these as bounds on the *weighted* quantities `x * g`/`y * g`, recovering a
bound on the *raw* `g` itself costs dividing by `x` or `y` -- exactly the
same division that produces
`exists_exact_of_isεQuittingRootEndpointNash`'s shift bound
`|d i| * min x y ≤ ε`. `abs_le_div_min_of_weighted_bounds` isolates this
division as a standalone real-number fact, independent of any root/reward
machinery, with the resulting factor `1 / min x y`.

## Contents

* `abs_le_div_min_of_weighted_bounds`: the raw real-number conversion
  lemma -- weighted bounds at tolerance `ε` on a pair `(x, g)` with
  `x, y > 0` force `|g| ≤ ε / min x y`.
* `abs_quittingRootEndpointDifference_le_div_min_of_isεQuittingRootEndpointNash`:
  instantiated at a root Nash row, giving the same conversion factor
  `1 / min x y` for the raw endpoint gap.
* `exists_exact_ownShift_abs_eq_abs_quittingRootEndpointDifference`: **the
  headline.** At an interior coordinate, E64's own-set shift magnitude and
  the raw endpoint gap controlled by the conversion factor are *equal*, not
  merely bounded by the same formula -- so the backward condition number and
  the weighted-to-unweighted conversion factor coincide as literal real
  numbers, both `= ε / min x y`, at the *same* witness.
* `min_lt_inv_of_exists_weighted_bound_not_isεRowComplementary`: the
  conversion factor applied to `QuittingRelaxedHazardRowBridge.lean`'s
  reverse-bridge-failure witness. The witness's hazard is forced below
  `1 / εRow` -- the same `1/m` blowup that makes E64's condition number
  diverge at a near-pure row *is* the reason the reverse `ε`-bridge
  direction cannot be salvaged at any fixed row tolerance: it is not a
  coincidence of formulas, it is the conversion factor witnessing its own
  necessity.

## Scope

Period-one / fixed-tail only, matching `QuittingRootEndpointBackwardStability
.lean`'s scope. The other two legs of the three-lens identity -- the lock
margin and a general account of the `ε`-bridge's weighted-gain
weakness beyond this one witness family -- remain open; only S1's condition
number and the conversion factor are connected here.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The raw conversion lemma -/

/-- **The weighted-to-unweighted conversion factor is `1 / min x y`.** If a
pair `(x, g)` obeys the two weighted inequalities that make up a single
clause of `IsεQuittingRootEndpointNash` -- `y * g ≤ ε` and `-ε ≤ x * g` --
for `x, y > 0`, then the raw value `g` itself is controlled by `ε` divided
by `min x y`. This is exactly the division step inside
`exists_exact_of_isεQuittingRootEndpointNash`'s interior-coordinate
magnitude bound, extracted as a standalone real-number fact. -/
theorem abs_le_div_min_of_weighted_bounds
    (x y g ε : ℝ) (hx0 : 0 < x) (hy0 : 0 < y) (_hε : 0 ≤ ε)
    (hupper : y * g ≤ ε) (hlower : -ε ≤ x * g) :
    |g| ≤ ε / min x y := by
  have hm : 0 < min x y := lt_min hx0 hy0
  rw [le_div_iff₀ hm]
  rcases le_total 0 g with hg | hg
  · rw [abs_of_nonneg hg]
    calc
      g * min x y ≤ g * y := mul_le_mul_of_nonneg_left (min_le_right _ _) hg
      _ = y * g := by ring
      _ ≤ ε := hupper
  · rw [abs_of_nonpos hg]
    calc
      -g * min x y ≤ -g * x := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
      _ = -(x * g) := by ring
      _ ≤ ε := by linarith

/-! ## Instantiated at a root Nash row -/

/-- The conversion factor bounds the raw endpoint gap of any `ε`-complementary
root row at an interior coordinate, with the same `1 / min x y` that governs
E64's shift bound. -/
theorem abs_quittingRootEndpointDifference_le_div_min_of_isεQuittingRootEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) (hε : 0 ≤ ε)
    (hnash : IsεQuittingRootEndpointNash reward tail ε root)
    (who : ι) (hx0 : (root who true).toReal ≠ 0) (hy0 : (root who false).toReal ≠ 0) :
    |quittingRootEndpointDifference reward tail root who| ≤
      ε / min (root who true).toReal (root who false).toReal := by
  have hxpos : 0 < (root who true).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx0)
  have hypos : 0 < (root who false).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hy0)
  obtain ⟨hupper, hlower⟩ := hnash who
  exact abs_le_div_min_of_weighted_bounds _ _ _ ε hxpos hypos hε hupper hlower

/-! ## The headline: the shift magnitude and the conversion bound coincide -/

/-- **The lens identity, leg one.** At an interior coordinate, the own-set
shift magnitude `exists_exact_of_isεQuittingRootEndpointNash` produces and
the raw endpoint gap the conversion factor controls are the *same real
number* up to sign, hence bounded by the *same instantiated value* of
`ε / min x y` -- not merely by the same formula. The equality
`|d who| = |quittingRootEndpointDifference reward tail root who|` is derived
purely from the shift theorem's public interface (its exactness clause plus
`quittingRootEndpointDifference_ownShiftReward`), with no appeal to the
specific witness `d` the existential proof constructs. -/
theorem exists_exact_ownShift_abs_eq_abs_quittingRootEndpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (ε : ℝ) (root : ι → PMF Bool) (hε : 0 ≤ ε)
    (hnash : IsεQuittingRootEndpointNash reward tail ε root)
    (who : ι) (hx0 : (root who true).toReal ≠ 0) (hy0 : (root who false).toReal ≠ 0) :
    ∃ d : ι → ℝ,
      IsεQuittingRootEndpointNash (ownShiftReward reward d) tail 0 root ∧
        |d who| = |quittingRootEndpointDifference reward tail root who| ∧
        |d who| ≤ ε / min (root who true).toReal (root who false).toReal := by
  obtain ⟨d, hexact, hbound⟩ :=
    exists_exact_of_isεQuittingRootEndpointNash reward tail ε root hε hnash
  have hxpos : 0 < (root who true).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx0)
  have hypos : 0 < (root who false).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hy0)
  have hzero := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    (ownShiftReward reward d) tail root who hexact hypos hxpos
  have hshift := quittingRootEndpointDifference_ownShiftReward reward tail root d who
  have heq : quittingRootEndpointDifference reward tail root who + d who = 0 := by
    rw [← hshift]; exact hzero
  have hdwho : d who = -(quittingRootEndpointDifference reward tail root who) := by linarith
  refine ⟨d, hexact, by rw [hdwho, abs_neg], ?_⟩
  have hmul := (hbound who).2 hx0 hy0
  rwa [le_div_iff₀ (lt_min hxpos hypos)]

/-! ## The other side: the reverse-bridge witness is forced through the same
factor -/

/-- **The reverse `ε`-bridge failure is the same blowup as the backward
condition number.** `QuittingRelaxedHazardRowBridge.lean`'s
`exists_weighted_bound_not_isεRowComplementary` witnesses, for every row
tolerance `εRow`, a weighted-bound-respecting pair `(x, g)` with `g < -εRow`.
Feeding that witness through `abs_le_div_min_of_weighted_bounds` shows this
is not a free construction: the witnessing margin `min x (1 - x)` is forced
below `1 / εRow`, the exact reciprocal-condition-number threshold. So the
reverse direction's failure at every fixed tolerance and E64's condition
number blowup as the row approaches a pure endpoint are the same
phenomenon, read through the same inequality. -/
theorem min_lt_inv_of_exists_weighted_bound_not_isεRowComplementary
    (εRow : ℝ) (hεRow : 0 < εRow) :
    ∃ x g : ℝ, 0 < x ∧ x < 1 ∧ (1 - x) * g ≤ 1 ∧ -1 ≤ x * g ∧ g < -εRow ∧
      min x (1 - x) < 1 / εRow := by
  obtain ⟨x, g, hx0, hx1, hupper, hlower, hgneg⟩ :=
    exists_weighted_bound_not_isεRowComplementary εRow hεRow.le
  refine ⟨x, g, hx0, hx1, hupper, hlower, hgneg, ?_⟩
  have hy0 : (0 : ℝ) < 1 - x := by linarith
  have hm : 0 < min x (1 - x) := lt_min hx0 hy0
  have hbound : |g| ≤ 1 / min x (1 - x) :=
    abs_le_div_min_of_weighted_bounds x (1 - x) g 1 hx0 hy0 (by norm_num) hupper hlower
  have hgneg' : g < 0 := by linarith
  have hgabs : εRow < |g| := by
    rw [abs_of_neg hgneg']
    linarith
  have hlt : εRow < 1 / min x (1 - x) := hgabs.trans_le hbound
  rw [lt_div_iff₀ hm] at hlt
  rw [lt_div_iff₀ hεRow, mul_comm]
  exact hlt

end GameTheory
