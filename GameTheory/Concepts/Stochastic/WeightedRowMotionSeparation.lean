/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PerturbedCyclicWeightNoExactCycle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The weighted one-stage correspondence prices no motion

Two one-stage conditions are attached to a hazard row `x` at a continuation
vector `r`, both written through the stop-minus-continue difference
`D_i = gainValue r x i (r i)` of the real-hazard encoding:

* the **weighted** condition, `IsWeightedRow`: `(1 - x i) * D i ≤ ε` and
  `-(x i) * D i ≤ ε`.  This is exactly the statement that no mixture
  deviation `β ∈ [0,1]` of coordinate `i` gains more than `ε` against the
  affine one-stage payoff `β Σ_i + (1-β) Γ_i`
  (`isWeightedRow_iff_mixPayoff_le`);
* the **support-perfect** condition, `IsSupportPerfectRow`: `x i > 0 → D i ≥
  -ε` and `x i < 1 → D i ≤ ε`.

Support-perfect implies weighted (`isWeightedRow_of_isSupportPerfectRow`);
the converse needs division by `x i` and is false at small hazards.

The separation is exhibited on the **scaled cyclic weight** -- the
Flesch--Thuijsman--Vrieze three-coordinate table divided by `3`, which is
`normalizedPerturbedWeight 0` in the encoding of
`PerturbedCyclicWeightNoExactCycle.lean` -- at the continuation vector
`r* = (4/9, 4/9, 4/9)`, the average of the three solo rows, along the
symmetric hazard row `x(t) = (t,t,t)`:

* `D_i = -(1 + 4t - 2t^2)/9` at every coordinate;
* the row is weighted-`ρ` as soon as `t ≤ 3ρ`, while it is support-perfect
  only at tolerance `≥ 1/9`;
* the motion is second order: `f(r*, x(t)) - r* = -(2t^2(3-t)/9)(1,1,1)`,
  against a quit mass `q(x(t)) = 3t - 3t^2 + t^3` that is first order.

Hence `no_motion_price_scaledCyclicWeight`: **no positive constant `ρ`
satisfies `ρ q(x) ≤ ‖f(r*,x) - r*‖` for all weighted-`ρ` rows `x` at `r*`.**

## Contents

* `oneStageMixPayoff`, `oneStageNext`: the affine one-stage payoff of a
  mixture deviation, and the one-stage successor `f_i(r,x)` it produces at
  the undeviated mixture.
* `IsWeightedRow`, `IsSupportPerfectRow`, `isWeightedRow_iff_mixPayoff_le`,
  `isWeightedRow_of_isSupportPerfectRow`.
* `scaledCyclicWeight` and its seven rows.
* `gainValue_scaledCyclicWeight_symmetricRow`,
  `oneStageNext_scaledCyclicWeight_symmetricRow`,
  `quitMass_symmetricRow`, `isWeightedRow_symmetricRow`,
  `not_isSupportPerfectRow_symmetricRow`.
* `exists_weightedRow_motion_lt`, `no_motion_price_scaledCyclicWeight`.

## What is not claimed

Nothing here says the scaled cyclic weight has no stationary and no instant
approximate equilibria; those two premises are quoted from the literature by
the source argument and are not formalized in this file.  What is proved is
the failure of the motion price *as an inequality about the weighted
correspondence*, at one explicit continuation vector of one explicit weight.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The affine one-stage payoff -/

/-- The one-stage payoff of coordinate `i` when it deviates to the mixture
`β` and every other coordinate keeps its row hazard: `β Σ_i + (1-β) Γ_i`,
affine in `β` because `β` only splits the stop and continue branches. -/
def oneStageMixPayoff (r : Finset ι → ι → ℝ) (x : ι → ℝ) (rest : ι → ℝ) (i : ι) (β : ℝ) : ℝ :=
  β * sigmaValue r x i + (1 - β) * gammaValue r x i (rest i)

/-- The one-stage successor `f_i(r,x)`: the payoff at the undeviated
mixture `β = x i`. -/
def oneStageNext (r : Finset ι → ι → ℝ) (x : ι → ℝ) (rest : ι → ℝ) (i : ι) : ℝ :=
  oneStageMixPayoff r x rest i (x i)

/-- **The deviation gain is the hazard displacement times the
stop-minus-continue difference.**  Every one-stage inequality below is a
special case of this one identity. -/
theorem oneStageMixPayoff_sub_oneStageNext (r : Finset ι → ι → ℝ) (x : ι → ℝ)
    (rest : ι → ℝ) (i : ι) (β : ℝ) :
    oneStageMixPayoff r x rest i β - oneStageNext r x rest i =
      (β - x i) * gainValue r x i (rest i) := by
  unfold oneStageNext oneStageMixPayoff gainValue
  ring

/-! ## The two one-stage conditions -/

/-- **The weighted one-stage condition**, `x ∈ E_ε(r)`: at every coordinate
the two endpoint deviations, weighted by the mass that would be moved, gain
at most `ε`. -/
def IsWeightedRow (r : Finset ι → ι → ℝ) (x : ι → ℝ) (rest : ι → ℝ) (ε : ℝ) : Prop :=
  ∀ i, (1 - x i) * gainValue r x i (rest i) ≤ ε ∧ -(x i) * gainValue r x i (rest i) ≤ ε

/-- **The support-perfect condition**: the stop-minus-continue difference
itself is bounded, one-sidedly at each used endpoint. -/
def IsSupportPerfectRow (r : Finset ι → ι → ℝ) (x : ι → ℝ) (rest : ι → ℝ) (ε : ℝ) : Prop :=
  ∀ i, (0 < x i → -ε ≤ gainValue r x i (rest i)) ∧
    (x i < 1 → gainValue r x i (rest i) ≤ ε)

/-- **The weighted condition is exactly `ε`-optimality against every mixture
deviation.**  Both directions are the affine identity: the gain is linear in
`β`, so its maximum over `[0,1]` sits at an endpoint, and the two endpoints
are the two clauses of `IsWeightedRow`. -/
theorem isWeightedRow_iff_mixPayoff_le (r : Finset ι → ι → ℝ) (x : ι → ℝ)
    (rest : ι → ℝ) (ε : ℝ) :
    IsWeightedRow r x rest ε ↔
      ∀ i, ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
        oneStageMixPayoff r x rest i β ≤ oneStageNext r x rest i + ε := by
  constructor
  · intro hrow i β hβ0 hβ1
    obtain ⟨hstop, hgo⟩ := hrow i
    have hid := oneStageMixPayoff_sub_oneStageNext r x rest i β
    rcases le_total 0 (gainValue r x i (rest i)) with hsign | hsign
    · nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) hsign]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ0 hsign]
  · intro hmix i
    have h1 := hmix i 1 zero_le_one le_rfl
    have h0 := hmix i 0 le_rfl zero_le_one
    have e1 := oneStageMixPayoff_sub_oneStageNext r x rest i 1
    have e0 := oneStageMixPayoff_sub_oneStageNext r x rest i 0
    exact ⟨by linarith, by linarith⟩

/-- **Support-perfect implies weighted**, for rows in `[0,1]` and
nonnegative tolerance.  This is the only available conversion between the
two conditions at positive tolerance; the reverse implication would divide
the second clause by `x i`. -/
theorem isWeightedRow_of_isSupportPerfectRow (r : Finset ι → ι → ℝ) (x : ι → ℝ)
    (rest : ι → ℝ) (ε : ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) (hε : 0 ≤ ε)
    (h : IsSupportPerfectRow r x rest ε) : IsWeightedRow r x rest ε := by
  intro i
  obtain ⟨hlow, hhigh⟩ := h i
  constructor
  · rcases lt_or_eq_of_le (hx1 i) with hlt | heq
    · nlinarith [hhigh hlt, hx0 i]
    · rw [← heq]; simpa using hε
  · rcases lt_or_eq_of_le (hx0 i) with hlt | heq
    · nlinarith [hlow hlt, hx1 i]
    · rw [← heq]; simpa using hε

/-! ## The scaled cyclic weight -/

/-- **The scaled cyclic weight**: the Flesch--Thuijsman--Vrieze
three-coordinate table divided by `3`.  It is `normalizedPerturbedWeight`
at perturbation `0`; the seven rows are spelled out below. -/
def scaledCyclicWeight : Finset CyclicIndex → CyclicIndex → ℝ :=
  normalizedPerturbedWeight 0

/-- Row `{0}` of the table: `(1/3, 1, 0)`. -/
theorem scaledCyclicWeight_zero : scaledCyclicWeight {0} = ![1 / 3, 1, 0] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{1}` of the table: `(0, 1/3, 1)`. -/
theorem scaledCyclicWeight_one : scaledCyclicWeight {1} = ![0, 1 / 3, 1] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{2}` of the table: `(1, 0, 1/3)`. -/
theorem scaledCyclicWeight_two : scaledCyclicWeight {2} = ![1, 0, 1 / 3] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{0,1}` of the table: `(1/3, 0, 1/3)`. -/
theorem scaledCyclicWeight_zero_one : scaledCyclicWeight {0, 1} = ![1 / 3, 0, 1 / 3] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{1,2}` of the table: `(1/3, 1/3, 0)`. -/
theorem scaledCyclicWeight_one_two : scaledCyclicWeight {1, 2} = ![1 / 3, 1 / 3, 0] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{0,2}` of the table: `(0, 1/3, 1/3)`. -/
theorem scaledCyclicWeight_zero_two : scaledCyclicWeight {0, 2} = ![0, 1 / 3, 1 / 3] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Row `{0,1,2}` of the table: the zero vector. -/
theorem scaledCyclicWeight_all : scaledCyclicWeight {0, 1, 2} = ![0, 0, 0] := by
  funext i
  fin_cases i <;> simp +decide [scaledCyclicWeight, normalizedPerturbedWeight, perturbedWeight]

/-- Every entry of the table has absolute value at most `1`, so the bound
`M = 1` is available. -/
theorem abs_scaledCyclicWeight_le_one (S : Finset CyclicIndex) (i : CyclicIndex) :
    |scaledCyclicWeight S i| ≤ 1 :=
  abs_normalizedPerturbedWeight_le_one 0 le_rfl (by norm_num) S i

/-- The solo value of each coordinate is `d_i = 1/3`. -/
theorem scaledCyclicWeight_diagonal (i : CyclicIndex) : scaledCyclicWeight {i} i = 1 / 3 :=
  normalizedPerturbedWeight_diagonal 0 i

/-- `Σ_i` for the scaled weight: only the predecessor's survival matters,
because the successor's contributions cancel at perturbation `0`. -/
theorem sigmaValue_scaledCyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    sigmaValue scaledCyclicWeight x i = (1 - x (cyclicPred i)) / 3 := by
  have hfun : (fun S j => (1 / 3 : ℝ) * perturbedWeight 0 S j) = scaledCyclicWeight := by
    funext S j
    simp [scaledCyclicWeight, normalizedPerturbedWeight]
    ring
  rw [← hfun, sigmaValue_const_mul, sigmaValue_perturbedWeight]
  ring

/-- `A_i` for the scaled weight. -/
theorem excludedValue_scaledCyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) :
    excludedValue scaledCyclicWeight x i =
      x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) / 3 := by
  have hfun : (fun S j => (1 / 3 : ℝ) * perturbedWeight 0 S j) = scaledCyclicWeight := by
    funext S j
    simp [scaledCyclicWeight, normalizedPerturbedWeight]
    ring
  rw [← hfun, excludedValue_const_mul, excludedValue_perturbedWeight]
  ring

/-- `Γ_i` for the scaled weight. -/
theorem gammaValue_scaledCyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gammaValue scaledCyclicWeight x i next =
      x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) / 3 +
        (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * next := by
  unfold gammaValue
  rw [excludedValue_scaledCyclicWeight, continueMassExcl_cyclicIndex]
  ring

/-- `D_i` for the scaled weight, the stop-minus-continue difference against a
continuation value. -/
theorem gainValue_scaledCyclicWeight (x : CyclicIndex → ℝ) (i : CyclicIndex) (next : ℝ) :
    gainValue scaledCyclicWeight x i next =
      (1 - x (cyclicPred i)) / 3 - x (cyclicPred i) * (3 - 2 * x (cyclicSucc i)) / 3 -
        (1 - x (cyclicPred i)) * (1 - x (cyclicSucc i)) * next := by
  unfold gainValue
  rw [sigmaValue_scaledCyclicWeight, gammaValue_scaledCyclicWeight]
  ring

/-! ## The symmetric row at the averaged continuation vector -/

/-- The symmetric hazard row `x(t) = (t,t,t)`. -/
def symmetricRow (t : ℝ) : CyclicIndex → ℝ := fun _ => t

/-- The continuation vector `r* = (4/9, 4/9, 4/9)`. -/
def restPoint : CyclicIndex → ℝ := fun _ => 4 / 9

/-- `r*` is the average of the three solo rows, hence feasible: it is the
convex combination of `w({0})`, `w({1})`, `w({2})` with weights `1/3`. -/
theorem restPoint_eq_average_solo (i : CyclicIndex) :
    restPoint i =
      (1 / 3) * scaledCyclicWeight {0} i + (1 / 3) * scaledCyclicWeight {1} i +
        (1 / 3) * scaledCyclicWeight {2} i := by
  rw [scaledCyclicWeight_zero, scaledCyclicWeight_one, scaledCyclicWeight_two]
  fin_cases i <;> norm_num [restPoint]

/-- **The stop-minus-continue difference along the symmetric row**, equation
(15) of the source argument: `D_i = -(1 + 4t - 2t^2)/9` at every
coordinate. -/
theorem gainValue_scaledCyclicWeight_symmetricRow (t : ℝ) (i : CyclicIndex) :
    gainValue scaledCyclicWeight (symmetricRow t) i (restPoint i) =
      -(1 + 4 * t - 2 * t ^ 2) / 9 := by
  rw [gainValue_scaledCyclicWeight]
  simp only [symmetricRow, restPoint]
  ring

/-- The difference is strictly negative for `0 ≤ t ≤ 1`: stopping is worse
than continuing at every coordinate, by at least `1/9`. -/
theorem gainValue_scaledCyclicWeight_symmetricRow_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : CyclicIndex) :
    gainValue scaledCyclicWeight (symmetricRow t) i (restPoint i) ≤ -(1 / 9) := by
  rw [gainValue_scaledCyclicWeight_symmetricRow]
  nlinarith

/-- **The one-stage motion along the symmetric row**, equation (19):
`f(r*, x(t)) - r* = -(2 t^2 (3 - t)/9)(1,1,1)`, second order in `t`. -/
theorem oneStageNext_scaledCyclicWeight_symmetricRow (t : ℝ) (i : CyclicIndex) :
    oneStageNext scaledCyclicWeight (symmetricRow t) restPoint i - restPoint i =
      -(2 * t ^ 2 * (3 - t)) / 9 := by
  unfold oneStageNext oneStageMixPayoff
  rw [sigmaValue_scaledCyclicWeight, gammaValue_scaledCyclicWeight]
  simp only [symmetricRow, restPoint]
  ring

/-- **The quit mass of the symmetric row**, equation (18):
`q(x(t)) = 3t - 3t^2 + t^3`, first order in `t`. -/
theorem quitMass_symmetricRow (t : ℝ) :
    1 - continueMass (symmetricRow t) = 3 * t - 3 * t ^ 2 + t ^ 3 := by
  rw [continueMass, Fin.prod_univ_three]
  simp only [symmetricRow]
  ring

/-- The quit mass is positive for `0 < t ≤ 1`. -/
theorem quitMass_symmetricRow_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < 1 - continueMass (symmetricRow t) := by
  rw [quitMass_symmetricRow]
  nlinarith

/-- **Weighted membership**, equation (17): the symmetric row is a
weighted-`ρ` row at `r*` as soon as `t ≤ 3ρ`.  Only the continue-side
deviation binds, and its gain `-t D_i = t(1 + 4t - 2t^2)/9` is at most
`t/3`. -/
theorem isWeightedRow_symmetricRow (t ρ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht : t ≤ 3 * ρ) :
    IsWeightedRow scaledCyclicWeight (symmetricRow t) restPoint ρ := by
  have hρ : 0 ≤ ρ := by linarith
  intro i
  rw [gainValue_scaledCyclicWeight_symmetricRow]
  constructor
  · have hx : symmetricRow t i = t := rfl
    rw [hx]
    nlinarith
  · have hx : symmetricRow t i = t := rfl
    rw [hx]
    nlinarith [sq_nonneg (t - 1)]

/-- **The row is not support-perfect below tolerance `1/9`.**  The
stop action is worse by at least `1/9` at every coordinate, and every
coordinate uses it with positive probability, so the support-perfect lower
clause fails outright.  This is the separation between the two
correspondences. -/
theorem not_isSupportPerfectRow_symmetricRow (t ε : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hε : ε < 1 / 9) :
    ¬ IsSupportPerfectRow scaledCyclicWeight (symmetricRow t) restPoint ε := by
  intro h
  have hlow := (h 0).1 ht0
  have hgain := gainValue_scaledCyclicWeight_symmetricRow_le t ht0.le ht1 0
  linarith

/-! ## No constant prices motion -/

/-- **The motion is priced below any prescribed rate.**  For every `ρ > 0`
there is a hazard level `t` at which the symmetric row is a weighted-`ρ` row
at `r*` and yet the one-stage motion is strictly smaller than `ρ` times the
quit mass. -/
theorem exists_weightedRow_motion_lt (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      IsWeightedRow scaledCyclicWeight (symmetricRow t) restPoint ρ ∧
      ‖fun i => oneStageNext scaledCyclicWeight (symmetricRow t) restPoint i - restPoint i‖ <
        ρ * (1 - continueMass (symmetricRow t)) := by
  refine ⟨min ρ 1 / 2, by positivity, by
    have := min_le_right ρ 1
    linarith, ?_, ?_⟩
  · refine isWeightedRow_symmetricRow _ _ (by positivity) ?_ ?_
    · have := min_le_right ρ 1
      linarith
    · have := min_le_left ρ 1
      linarith
  · set t := min ρ 1 / 2 with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 2 := by
      have := min_le_right ρ 1
      simp only [ht]
      linarith
    have htρ : 2 * t ≤ ρ := by
      have := min_le_left ρ 1
      simp only [ht]
      linarith
    have hq : 0 < ρ * (1 - continueMass (symmetricRow t)) :=
      mul_pos hρ (quitMass_symmetricRow_pos t ht0 (by linarith))
    rw [pi_norm_lt_iff hq]
    intro i
    rw [Real.norm_eq_abs, oneStageNext_scaledCyclicWeight_symmetricRow,
      quitMass_symmetricRow, abs_lt]
    have hqpos : (0 : ℝ) < 3 * t - 3 * t ^ 2 + t ^ 3 := by nlinarith
    have hslack : (0 : ℝ) ≤ (ρ - 2 * t) * (3 * t - 3 * t ^ 2 + t ^ 3) :=
      mul_nonneg (by linarith) hqpos.le
    constructor
    · nlinarith
    · nlinarith

/-- **No constant prices motion on the weighted correspondence.**  There is
no `ρ > 0` for which every weighted-`ρ` hazard row `x` at the feasible
vector `r*` of the scaled cyclic weight moves the state by at least
`ρ q(x)`.

This is the failure of the granted motion constant, and with it of the lower
half of the motion sandwich, already at a single continuation vector and a
single one-parameter family of rows.  The defect is the substitution of the
weighted condition for the support-perfect one: by
`not_isSupportPerfectRow_symmetricRow` these rows are *not* support-perfect
at any tolerance below `1/9`. -/
theorem no_motion_price_scaledCyclicWeight :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : CyclicIndex → ℝ, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ 1) →
      IsWeightedRow scaledCyclicWeight x restPoint ρ →
        ρ * (1 - continueMass x) ≤
          ‖fun i => oneStageNext scaledCyclicWeight x restPoint i - restPoint i‖ := by
  rintro ⟨ρ, hρ, hprice⟩
  obtain ⟨t, ht0, ht1, hmem, hmotion⟩ := exists_weightedRow_motion_lt ρ hρ
  exact absurd (hprice _ (fun _ => ht0.le) (fun _ => ht1.le) hmem) (not_le.mpr hmotion)

end GameTheory
