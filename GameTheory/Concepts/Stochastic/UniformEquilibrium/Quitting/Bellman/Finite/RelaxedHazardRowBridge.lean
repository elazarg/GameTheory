/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge

/-!
# The relaxed (`ε > 0`) hazard/row bridge

`QuittingHazardRowBridge.lean` bridges the real-valued hazard encoding
(`QuittingCyclicWeightRowDichotomy.lean`) and the `PMF Bool` mixture encoding
exactly -- but only at `ε = 0`: `IsExactRowComplementary` at a translated row
is equivalent to `IsεQuittingRootEndpointNash reward tail 0 root`. The
exact-versus-relaxed programme lives at *positive* `ε`, where the objects of
interest -- relaxed cycles -- actually live, so this file extends the bridge
there.

## Contents

* `IsεRowComplementary`: the real-valued relaxed row condition, mirroring
  `IsExactRowComplementary` with slack `ε` on both clauses.
* `isεRowComplementary_zero_iff_isExactRowComplementary`: at `ε = 0` the new
  condition is definitionally the old one.
* `isεQuittingRootEndpointNash_of_isεRowComplementary_hazardOfRoot`: **the
  `ε`-bridge, forward direction**. `IsεRowComplementary ε` of the translated
  hazard row, with `ε` nonnegative, gives `IsεQuittingRootEndpointNash reward
  tail ε root` at the *same* `ε` -- no worse constant.
* `exists_weighted_bound_not_isεRowComplementary`: **the reverse direction
  fails outright**, for every candidate row tolerance. A worked real-number
  counterexample isolating exactly the mechanism: the endpoint condition only
  bounds `x * g`, so as the hazard `x → 0⁺` the same weighted bound stays
  satisfied while `g → -∞`.
* `cyclicWeight_pred_le_of_pos_relaxed`: the relaxed equation (16), verbatim
  from the lower clause of `IsεRowComplementary`: `-ε ≤ g i` gives
  `p ≤ (3/4) s (1-p) + ε`.
* `cyclicWeight_pred_le_succ_add_eps_of_pos`: its linear corollary,
  `p ≤ (3/4) s + ε`.
* `cyclicWeight_le_four_mul_eps_of_all_pos`: if all three coordinates are
  active, each is at most `4ε`.
* `atMostOneExceeds_four_mul_eps_of_isεRowComplementary_cyclicWeight`: **the
  relaxed row dichotomy**. A row of `cyclicWeight` satisfying the lower
  complementarity clause with slack `ε`, together with a nonnegative centered
  next-phase value, has at most one coordinate exceeding `4ε`.

## Scope

The `ε`-bridge is one-directional. Going from a relaxed real-valued row to a
relaxed Bool-side root Nash costs nothing (`ε' = ε`, given `0 ≤ ε`): this is
the direction that matters for showing a row built on the real side (where
the questions corpus lives, per `QuittingHazardRowBridge.lean`'s own
docstring) is a genuine equilibrium on the `PMF Bool` side. Going the other
way -- extracting real-row structure from an assumed Bool-side relaxed Nash
-- is not possible for any finite row tolerance: `exists_weighted_bound_not_
isεRowComplementary` proves this precisely, so no strengthened statement is
being left on the table. This is a second, sharper asymmetry than the
existing bridge's domain restriction (rows outside `[0,1]` do not transport);
here even a row inside `[0,1]` does not transport back once `ε > 0`.

Consequently `atMostOneExceeds_four_mul_eps_of_isεRowComplementary_cyclicWeight`
below is stated, and can only be stated, on the real-hazard side: it is what
lets a relaxed cycle -- built and analyzed as a row of reals, as the whole
programme does -- be compared against an exact row's "at most one active
coordinate" without first having to (impossibly) recover row structure from a
Bool-side Nash hypothesis.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-! ## The relaxed row condition -/

variable {ι : Type*}

/-- Relaxed complementarity of a single row `x` against gains `g`, mirroring
`IsExactRowComplementary` with slack `ε` on both clauses: `x i > 0 → g i ≥
-ε` and `x i < 1 → g i ≤ ε`, at every coordinate. -/
def IsεRowComplementary (ε : ℝ) (x g : ι → ℝ) : Prop :=
  ∀ i, (0 < x i → -ε ≤ g i) ∧ (x i < 1 → g i ≤ ε)

/-- At `ε = 0`, the relaxed row condition is definitionally the exact one. -/
theorem isεRowComplementary_zero_iff_isExactRowComplementary (x g : ι → ℝ) :
    IsεRowComplementary 0 x g ↔ IsExactRowComplementary x g := by
  simp [IsεRowComplementary, IsExactRowComplementary]

/-! ## The `ε`-bridge -/

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

/-- **The `ε`-bridge, forward direction.** `IsεRowComplementary ε` of the
translated hazard row against the translated gain vector, with `ε`
nonnegative, gives `IsεQuittingRootEndpointNash reward tail ε root` at the
*same* `ε`. This is deliverable (2)'s forward half: no worse constant, and no
extra hypothesis beyond `0 ≤ ε`. -/
theorem isεQuittingRootEndpointNash_of_isεRowComplementary_hazardOfRoot
    (reward : {S : Finset ι' // S.Nonempty} → Payoff ι') (tail : Payoff ι') (root : ι' → PMF Bool)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hrow : IsεRowComplementary ε (hazardOfRoot root)
        (fun i => gainValue (weightOfReward reward) (hazardOfRoot root) i (tail i))) :
    IsεQuittingRootEndpointNash reward tail ε root := by
  intro who
  set g := quittingRootEndpointDifference reward tail root who with hgdef
  have hgain : gainValue (weightOfReward reward) (hazardOfRoot root) who (tail who) = g :=
    (quittingRootEndpointDifference_eq_gainValue reward tail root who).symm
  obtain ⟨hb1, hb2⟩ := hrow who
  simp only [hgain] at hb1 hb2
  set x := hazardOfRoot root who with hxdef
  have hx0 : 0 ≤ x := hazardOfRoot_nonneg root who
  have hx1 : x ≤ 1 := hazardOfRoot_le_one root who
  have hxtrue : (root who true).toReal = x := rfl
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hyeq : (root who false).toReal = 1 - x := by rw [hxtrue] at hsum; linarith
  rw [hxtrue, hyeq]
  refine ⟨?_, ?_⟩
  · by_cases h1 : x < 1
    · nlinarith [hb2 h1, hx0, hx1, hε,
        mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (hb2 h1)), mul_nonneg hx0 hε]
    · have hxe : x = 1 := le_antisymm hx1 (not_lt.mp h1)
      have hz : (1 - x) * g = 0 := by rw [hxe]; ring
      linarith [hz, hε]
  · by_cases h0 : 0 < x
    · have hg1 : 0 ≤ g + ε := by linarith [hb1 h0]
      nlinarith [mul_nonneg hx0 hg1, mul_nonneg (sub_nonneg.mpr hx1) hε]
    · have hxe : x = 0 := le_antisymm (not_lt.mp h0) hx0
      have hz : x * g = 0 := by rw [hxe]; ring
      linarith [hz, hε]

/-- **The reverse `ε`-bridge direction fails, for every finite row
tolerance.** Fixing the endpoint tolerance at `1`, for every candidate row
tolerance `εRow` there is a hazard `x ∈ (0,1)` and gain `g` whose weighted
bounds `(1 - x) * g ≤ 1` and `-1 ≤ x * g` both hold -- exactly the shape of a
single `who`-clause of `IsεQuittingRootEndpointNash` -- while `g < -εRow`,
violating `IsεRowComplementary εRow`'s lower clause at that coordinate. This
is why no direction-reversing theorem is stated above: as `εRow → ∞` the
witnessing `x` is forced to `0⁺`, since the endpoint condition only controls
`x * g`, and shrinking `x` lets `g` diverge while the weighted product stays
bounded. -/
theorem exists_weighted_bound_not_isεRowComplementary (εRow : ℝ) (hεRow : 0 ≤ εRow) :
    ∃ x g : ℝ, 0 < x ∧ x < 1 ∧ (1 - x) * g ≤ 1 ∧ -1 ≤ x * g ∧ g < -εRow := by
  have hden : (0 : ℝ) < εRow + 2 := by linarith
  refine ⟨1 / (εRow + 2), -(εRow + 1), div_pos one_pos hden, ?_, ?_, ?_, by linarith⟩
  · rw [div_lt_one hden]; linarith
  · have h1x : (0 : ℝ) ≤ 1 - 1 / (εRow + 2) := by
      rw [sub_nonneg, div_le_one hden]; linarith
    have hgneg : -(εRow + 1) ≤ (0 : ℝ) := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h1x hgneg]
  · have hxg : (1 : ℝ) / (εRow + 2) * -(εRow + 1) = -(εRow + 1) / (εRow + 2) := by ring
    rw [hxg, le_div_iff₀ hden]
    linarith

/-! ## The relaxed row dichotomy -/

/-- **Equation (16), relaxed.** The lower clause of `IsεRowComplementary`
alone -- `-ε ≤ g i` -- relaxes equation (16) verbatim: dropping the
nonnegative `(1-p)(1-s)z` term from equation (15) now leaves a slack of `ε`
instead of forcing `p ≤ (3/4) s (1-p)` outright. -/
theorem cyclicWeight_pred_le_of_pos_relaxed (x z : CyclicIndex → ℝ) (ε : ℝ) (i : CyclicIndex)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : 0 ≤ z i)
    (hgain : -ε ≤ gainValue cyclicWeight x i (z i - 1 / 2)) :
    x (cyclicPred i) ≤ (3 / 4) * x (cyclicSucc i) * (1 - x (cyclicPred i)) + ε := by
  rw [gainValue_cyclicWeight] at hgain
  have hp := hx (cyclicPred i)
  have hs := hx (cyclicSucc i)
  have heq : z i - 1 / 2 + 1 / 2 = z i := by ring
  rw [heq] at hgain
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hs.2)) hz]

/-- The linear corollary of equation (16), relaxed: dropping the
predecessor's own survival factor `(1-p) ≤ 1` turns the quadratic bound into
a linear one, `p ≤ (3/4) s + ε`. -/
theorem cyclicWeight_pred_le_succ_add_eps_of_pos (x z : CyclicIndex → ℝ) (ε : ℝ) (i : CyclicIndex)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : 0 ≤ z i)
    (hgain : -ε ≤ gainValue cyclicWeight x i (z i - 1 / 2)) :
    x (cyclicPred i) ≤ (3 / 4) * x (cyclicSucc i) + ε := by
  have hbound := cyclicWeight_pred_le_of_pos_relaxed x z ε i hx hz hgain
  have hp := hx (cyclicPred i)
  have hs := hx (cyclicSucc i)
  nlinarith [mul_nonneg hs.1 hp.1]

/-- **If all three coordinates are active, each is at most `4ε`.** Chaining
the linear corollary around the cycle three times is a purely linear
elimination -- no multiplicative telescoping is needed here, unlike the exact
all-three-active case `cyclicWeight_false_of_all_pos`, because the survival
factors were already dropped by `cyclicWeight_pred_le_succ_add_eps_of_pos`. -/
theorem cyclicWeight_le_four_mul_eps_of_all_pos (x z : CyclicIndex → ℝ) (ε : ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : ∀ i, 0 < x i → -ε ≤ gainValue cyclicWeight x i (z i - 1 / 2))
    (h0 : 0 < x 0) (h1 : 0 < x 1) (h2 : 0 < x 2) :
    x 0 ≤ 4 * ε ∧ x 1 ≤ 4 * ε ∧ x 2 ≤ 4 * ε := by
  have b0 := cyclicWeight_pred_le_succ_add_eps_of_pos x z ε 0 hx (hz 0) (hcompl 0 h0)
  have b1 := cyclicWeight_pred_le_succ_add_eps_of_pos x z ε 1 hx (hz 1) (hcompl 1 h1)
  have b2 := cyclicWeight_pred_le_succ_add_eps_of_pos x z ε 2 hx (hz 2) (hcompl 2 h2)
  have e0s : cyclicSucc (0 : CyclicIndex) = 1 := by decide
  have e0p : cyclicPred (0 : CyclicIndex) = 2 := by decide
  have e1s : cyclicSucc (1 : CyclicIndex) = 2 := by decide
  have e1p : cyclicPred (1 : CyclicIndex) = 0 := by decide
  have e2s : cyclicSucc (2 : CyclicIndex) = 0 := by decide
  have e2p : cyclicPred (2 : CyclicIndex) = 1 := by decide
  rw [e0s, e0p] at b0
  rw [e1s, e1p] at b1
  rw [e2s, e2p] at b2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The two-large-coordinates case, relaxed.** If coordinate `k` is below
threshold (`x k ≤ 4ε`) while both its predecessor and successor exceed it,
the linear corollary applied at the predecessor derives a contradiction.
Generalizes `cyclicWeight_false_of_zero_between_two_pos`, replacing the exact
hypothesis `x k = 0` by the threshold bound `x k ≤ 4ε`. -/
theorem cyclicWeight_false_of_below_threshold_between_two_above (x z : CyclicIndex → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (k : CyclicIndex) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : ∀ i, 0 < x i → -ε ≤ gainValue cyclicWeight x i (z i - 1 / 2))
    (hk : x k ≤ 4 * ε) (hA : 4 * ε < x (cyclicPred k)) (hB : 4 * ε < x (cyclicSucc k)) :
    False := by
  have hApos : 0 < x (cyclicPred k) := by linarith
  have hbd := cyclicWeight_pred_le_succ_add_eps_of_pos x z ε (cyclicPred k) hx
    (hz (cyclicPred k)) (hcompl (cyclicPred k) hApos)
  rw [cyclicPred_cyclicPred_eq_cyclicSucc, cyclicSucc_cyclicPred] at hbd
  linarith

/-- Every unordered pair of coordinates fails to both exceed `4ε`: the
relaxed, quantitative analog of `cyclicWeight_pairwise_not_both_pos`. Each
pair splits on whether the third coordinate is itself below or above the
threshold. -/
theorem cyclicWeight_pairwise_not_both_exceed_four_mul_eps (x z : CyclicIndex → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : ∀ i, 0 < x i → -ε ≤ gainValue cyclicWeight x i (z i - 1 / 2)) :
    ¬ (4 * ε < x 0 ∧ 4 * ε < x 1) ∧ ¬ (4 * ε < x 1 ∧ 4 * ε < x 2) ∧
      ¬ (4 * ε < x 0 ∧ 4 * ε < x 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩
    by_cases hk : x 2 ≤ 4 * ε
    · have hA : 4 * ε < x (cyclicPred (2 : CyclicIndex)) := by
        have hp : cyclicPred (2 : CyclicIndex) = 1 := by decide
        rw [hp]; exact h1
      have hB : 4 * ε < x (cyclicSucc (2 : CyclicIndex)) := by
        have hs : cyclicSucc (2 : CyclicIndex) = 0 := by decide
        rw [hs]; exact h0
      exact cyclicWeight_false_of_below_threshold_between_two_above x z ε hε 2 hx hz hcompl hk hA hB
    · have h0' : 0 < x 0 := by linarith
      have h1' : 0 < x 1 := by linarith
      have h2' : 0 < x 2 := by linarith
      have hall := cyclicWeight_le_four_mul_eps_of_all_pos x z ε hx hz hcompl h0' h1' h2'
      linarith [hall.2.2]
  · rintro ⟨h1, h2⟩
    by_cases hk : x 0 ≤ 4 * ε
    · have hA : 4 * ε < x (cyclicPred (0 : CyclicIndex)) := by
        have hp : cyclicPred (0 : CyclicIndex) = 2 := by decide
        rw [hp]; exact h2
      have hB : 4 * ε < x (cyclicSucc (0 : CyclicIndex)) := by
        have hs : cyclicSucc (0 : CyclicIndex) = 1 := by decide
        rw [hs]; exact h1
      exact cyclicWeight_false_of_below_threshold_between_two_above x z ε hε 0 hx hz hcompl hk hA hB
    · have h0' : 0 < x 0 := by linarith
      have h1' : 0 < x 1 := by linarith
      have h2' : 0 < x 2 := by linarith
      have hall := cyclicWeight_le_four_mul_eps_of_all_pos x z ε hx hz hcompl h0' h1' h2'
      linarith [hall.1]
  · rintro ⟨h0, h2⟩
    by_cases hk : x 1 ≤ 4 * ε
    · have hA : 4 * ε < x (cyclicPred (1 : CyclicIndex)) := by
        have hp : cyclicPred (1 : CyclicIndex) = 0 := by decide
        rw [hp]; exact h0
      have hB : 4 * ε < x (cyclicSucc (1 : CyclicIndex)) := by
        have hs : cyclicSucc (1 : CyclicIndex) = 2 := by decide
        rw [hs]; exact h2
      exact cyclicWeight_false_of_below_threshold_between_two_above x z ε hε 1 hx hz hcompl hk hA hB
    · have h0' : 0 < x 0 := by linarith
      have h1' : 0 < x 1 := by linarith
      have h2' : 0 < x 2 := by linarith
      have hall := cyclicWeight_le_four_mul_eps_of_all_pos x z ε hx hz hcompl h0' h1' h2'
      linarith [hall.2.1]

/-- **The relaxed row dichotomy (deliverable 3).** A row of `cyclicWeight`
satisfying the lower complementarity clause of `IsεRowComplementary` with
slack `ε`, together with a nonnegative centered next-phase value, has at most
one coordinate exceeding `4ε`: any two coordinates both above that threshold
coincide. This is the quantitative, `ε`-explicit generalization of
`atMostOnePositive_of_isExactRowComplementary`, which is recovered exactly at
`ε = 0` (threshold `0`, hypothesis `0 < x i` in place of `4ε < x i`). It is
what lets a relaxed cycle be compared against an exact row: any coordinate a
relaxed row keeps above `4ε` is forced, by this dichotomy, to be alone. -/
theorem atMostOneExceeds_four_mul_eps_of_isεRowComplementary_cyclicWeight
    (x z : CyclicIndex → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hz : ∀ j, 0 ≤ z j)
    (hcompl : IsεRowComplementary ε x (fun i => gainValue cyclicWeight x i (z i - 1 / 2)))
    (i j : CyclicIndex) (hi : 4 * ε < x i) (hj : 4 * ε < x j) : i = j := by
  have hcompl' : ∀ k, 0 < x k → -ε ≤ gainValue cyclicWeight x k (z k - 1 / 2) :=
    fun k hk => (hcompl k).1 hk
  have H := cyclicWeight_pairwise_not_both_exceed_four_mul_eps x z ε hε hx hz hcompl'
  by_contra hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact H.1 ⟨hi, hj⟩
      | exact H.1 ⟨hj, hi⟩
      | exact H.2.1 ⟨hi, hj⟩
      | exact H.2.1 ⟨hj, hi⟩
      | exact H.2.2 ⟨hi, hj⟩
      | exact H.2.2 ⟨hj, hi⟩

end GameTheory
