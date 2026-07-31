/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.StrongDuality
import Mathlib.Topology.Order.Lattice

/-!
# One-dimensional finite affine minimax

For finitely many affine lines

`c ↦ intercept a + c * slope a`,

this file identifies the minimum, over `c ≥ 0`, of their pointwise maximum.
If at least one slope is nonnegative, the minimum is attained and equals

`max ∑ a, weight a * intercept a`,

where the maximum ranges over probability weights whose average slope is
nonnegative.  If every slope is negative, the affine maximum is unbounded
below.

The proof has two independent parts.  A direct one-dimensional cutoff
argument proves primal attainment, including a flat zero-slope plateau.
Finite LP strong duality then produces an optimal probability weight.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace Math
namespace LinearProgramming

variable {Action : Type*} [Fintype Action] [Nonempty Action]

/-- The pointwise maximum of a finite nonempty family of affine lines. -/
def finiteAffineMaximum
    (intercept slope : Action → ℝ) (c : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => intercept a + c * slope a)

theorem affine_le_finiteAffineMaximum
    (intercept slope : Action → ℝ) (c : ℝ) (a : Action) :
    intercept a + c * slope a ≤
      finiteAffineMaximum intercept slope c := by
  exact Finset.le_sup'
    (s := Finset.univ)
    (fun b => intercept b + c * slope b)
    (Finset.mem_univ a)

theorem finiteAffineMaximum_le_iff
    (intercept slope : Action → ℝ) (c value : ℝ) :
    finiteAffineMaximum intercept slope c ≤ value ↔
      ∀ a, intercept a + c * slope a ≤ value := by
  rw [finiteAffineMaximum, Finset.sup'_le_iff]
  simp

theorem continuous_finiteAffineMaximum
    (intercept slope : Action → ℝ) :
    Continuous (finiteAffineMaximum intercept slope) := by
  apply Continuous.finset_sup'_apply
    (f := fun a c => intercept a + c * slope a)
    Finset.univ_nonempty
  intro a _
  fun_prop

/-- `value` is the value of an affine majorant at a nonnegative scale. -/
def IsAffineMajorant
    (intercept slope : Action → ℝ) (c value : ℝ) : Prop :=
  0 ≤ c ∧ ∀ a, intercept a + c * slope a ≤ value

/-- `c` and `value` attain the least affine majorant over nonnegative scales. -/
def IsOptimalAffineMajorant
    (intercept slope : Action → ℝ) (c value : ℝ) : Prop :=
  IsAffineMajorant intercept slope c value ∧
    ∀ d candidate,
      IsAffineMajorant intercept slope d candidate → value ≤ candidate

theorem isAffineMajorant_finiteAffineMaximum
    (intercept slope : Action → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IsAffineMajorant intercept slope c
      (finiteAffineMaximum intercept slope c) := by
  exact ⟨hc, affine_le_finiteAffineMaximum intercept slope c⟩

private def affineCutoff
    (intercept slope : Action → ℝ) (anchor : Action) : ℝ :=
  ∑ a, if slope a < 0 then
    max 0 ((intercept a - intercept anchor) /
      (slope anchor - slope a))
  else 0

omit [Nonempty Action] in
private theorem affineCutoff_nonnegative
    (intercept slope : Action → ℝ) (anchor : Action) :
    0 ≤ affineCutoff intercept slope anchor := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [Nonempty Action] in
private theorem negative_line_le_anchor_of_cutoff_le
    (intercept slope : Action → ℝ) (anchor : Action)
    (hanchor : 0 ≤ slope anchor) {c : ℝ}
    (hcutoff : affineCutoff intercept slope anchor ≤ c)
    {a : Action} (ha : slope a < 0) :
    intercept a + c * slope a ≤
      intercept anchor + c * slope anchor := by
  have hdenom : 0 < slope anchor - slope a := by linarith
  have hterm_nonneg :
      ∀ b ∈ Finset.univ,
        0 ≤ if slope b < 0 then
          max 0 ((intercept b - intercept anchor) /
            (slope anchor - slope b))
        else 0 := by
    intro b _
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hsingle :
      max 0 ((intercept a - intercept anchor) /
        (slope anchor - slope a)) ≤
        affineCutoff intercept slope anchor := by
    rw [affineCutoff]
    have := Finset.single_le_sum hterm_nonneg (Finset.mem_univ a)
    simpa [ha] using this
  have hratio :
      (intercept a - intercept anchor) /
          (slope anchor - slope a) ≤ c := by
    exact (le_max_right _ _).trans (hsingle.trans hcutoff)
  have hdifference :
      intercept a - intercept anchor ≤
        c * (slope anchor - slope a) := by
    exact (div_le_iff₀ hdenom).mp hratio
  linarith

private theorem finiteAffineMaximum_cutoff_le
    (intercept slope : Action → ℝ) (anchor : Action)
    (hanchor : 0 ≤ slope anchor) {c : ℝ}
    (hcutoff : affineCutoff intercept slope anchor ≤ c) :
    finiteAffineMaximum intercept slope
        (affineCutoff intercept slope anchor) ≤
      finiteAffineMaximum intercept slope c := by
  rw [finiteAffineMaximum_le_iff]
  intro a
  by_cases ha : slope a < 0
  · calc
      intercept a +
          affineCutoff intercept slope anchor * slope a ≤
          intercept anchor +
            affineCutoff intercept slope anchor * slope anchor :=
        negative_line_le_anchor_of_cutoff_le
          intercept slope anchor hanchor le_rfl ha
      _ ≤ intercept anchor + c * slope anchor := by
        gcongr
      _ ≤ finiteAffineMaximum intercept slope c :=
        affine_le_finiteAffineMaximum intercept slope c anchor
  · have haslope : 0 ≤ slope a := le_of_not_gt ha
    calc
      intercept a +
          affineCutoff intercept slope anchor * slope a ≤
          intercept a + c * slope a := by
        gcongr
      _ ≤ finiteAffineMaximum intercept slope c :=
        affine_le_finiteAffineMaximum intercept slope c a

omit [Fintype Action] in
/-- If one line has nonnegative slope, the finite affine maximum attains its
minimum on the nonnegative half-line.  The result includes minima attained on
a zero-slope plateau. -/
theorem exists_optimalAffineMajorant
    [Finite Action]
    (intercept slope : Action → ℝ)
    (hbounded : ∃ anchor, 0 ≤ slope anchor) :
    ∃ c value, IsOptimalAffineMajorant intercept slope c value := by
  letI := Fintype.ofFinite Action
  obtain ⟨anchor, hanchor⟩ := hbounded
  let cutoff := affineCutoff intercept slope anchor
  have hcutoff : 0 ≤ cutoff :=
    affineCutoff_nonnegative intercept slope anchor
  have hcompact : IsCompact (Set.Icc (0 : ℝ) cutoff) :=
    isCompact_Icc
  obtain ⟨c, hc, hcmin⟩ :=
    hcompact.exists_isMinOn
      ⟨0, by exact ⟨le_rfl, hcutoff⟩⟩
      (continuous_finiteAffineMaximum intercept slope).continuousOn
  let value := finiteAffineMaximum intercept slope c
  refine ⟨c, value, ?_, ?_⟩
  · exact isAffineMajorant_finiteAffineMaximum
      intercept slope hc.1
  · intro d candidate hd
    have hmax_le_candidate :
        finiteAffineMaximum intercept slope d ≤ candidate :=
      (finiteAffineMaximum_le_iff intercept slope d candidate).mpr hd.2
    by_cases hdc : d ≤ cutoff
    · exact (hcmin ⟨hd.1, hdc⟩).trans hmax_le_candidate
    · have hcutoff_le_d : cutoff ≤ d := le_of_not_ge hdc
      calc
        value ≤ finiteAffineMaximum intercept slope cutoff :=
          hcmin ⟨hcutoff, le_rfl⟩
        _ ≤ finiteAffineMaximum intercept slope d :=
          finiteAffineMaximum_cutoff_le
            intercept slope anchor hanchor hcutoff_le_d
        _ ≤ candidate := hmax_le_candidate

/-- Probability weights with a nonnegative average slope. -/
def IsAdmissibleAffineWeight
    (slope : Action → ℝ) (weight : Action → ℝ) : Prop :=
  (∀ a, 0 ≤ weight a) ∧
    (∑ a, weight a) = 1 ∧
    0 ≤ ∑ a, weight a * slope a

omit [Nonempty Action] in
/-- Every admissible weight gives a lower bound on every affine majorant. -/
theorem affineWeight_le_majorant
    (intercept slope weight : Action → ℝ) {c value : ℝ}
    (hweight : IsAdmissibleAffineWeight slope weight)
    (hmajorant : IsAffineMajorant intercept slope c value) :
    (∑ a, weight a * intercept a) ≤ value := by
  have hweighted :
      (∑ a, weight a *
        (intercept a + c * slope a)) ≤
        ∑ a, weight a * value := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (hmajorant.2 a) (hweight.1 a)
  have hright :
      (∑ a, weight a * value) = value := by
    rw [← Finset.sum_mul, hweight.2.1]
    simp
  have hsum_expand :
      (∑ a, weight a *
        (intercept a + c * slope a)) =
        (∑ a, weight a * intercept a) +
          c * ∑ a, weight a * slope a := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsum_expand, hright] at hweighted
  have hcorrection :
      0 ≤ c * ∑ a, weight a * slope a :=
    mul_nonneg hmajorant.1 hweight.2.2
  linarith

omit [Nonempty Action] in
/-- At equal primal and dual values, the scale is complementary to the
average slope. -/
theorem scale_mul_averageSlope_eq_zero
    (intercept slope weight : Action → ℝ) {c value : ℝ}
    (hweight : IsAdmissibleAffineWeight slope weight)
    (hmajorant : IsAffineMajorant intercept slope c value)
    (hvalue : (∑ a, weight a * intercept a) = value) :
    c * ∑ a, weight a * slope a = 0 := by
  have hweighted :
      (∑ a, weight a *
        (intercept a + c * slope a)) ≤
        ∑ a, weight a * value := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (hmajorant.2 a) (hweight.1 a)
  have hleft :
      (∑ a, weight a *
        (intercept a + c * slope a)) =
        value + c * ∑ a, weight a * slope a := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hvalue, Finset.mul_sum]
    apply congrArg (value + ·)
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hright : (∑ a, weight a * value) = value := by
    rw [← Finset.sum_mul, hweight.2.1]
    simp
  rw [hleft, hright] at hweighted
  exact le_antisymm (by linarith) (mul_nonneg hmajorant.1 hweight.2.2)

omit [Nonempty Action] in
/-- Every action receiving positive optimal dual weight is active at the
primal affine maximum. -/
theorem affine_eq_majorant_of_positive_optimalWeight
    (intercept slope weight : Action → ℝ) {c value : ℝ}
    (hweight : IsAdmissibleAffineWeight slope weight)
    (hmajorant : IsAffineMajorant intercept slope c value)
    (hvalue : (∑ a, weight a * intercept a) = value)
    {a : Action} (ha : 0 < weight a) :
    intercept a + c * slope a = value := by
  let gap : Action → ℝ :=
    fun b => weight b *
      (value - (intercept b + c * slope b))
  have hgap_nonnegative : ∀ b, 0 ≤ gap b := by
    intro b
    exact mul_nonneg (hweight.1 b)
      (sub_nonneg.mpr (hmajorant.2 b))
  have hcomplementary :=
    scale_mul_averageSlope_eq_zero
      intercept slope weight hweight hmajorant hvalue
  have hgap_sum : (∑ b, gap b) = 0 := by
    calc
      (∑ b, gap b) =
          value * (∑ b, weight b) -
            ((∑ b, weight b * intercept b) +
              c * ∑ b, weight b * slope b) := by
        simp only [gap, mul_sub, Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro b _
          ring
        · simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
      _ = 0 := by rw [hweight.2.1, hvalue, hcomplementary]; ring
  have hgap_a : gap a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => hgap_nonnegative b)).mp hgap_sum
      a (Finset.mem_univ a)
  dsimp [gap] at hgap_a
  have hzero :
      value - (intercept a + c * slope a) = 0 := by
    exact (mul_eq_zero.mp hgap_a).resolve_left (ne_of_gt ha)
  linarith

private inductive AffinePrimalCoordinate
  | scale
  | upperPositive
  | upperNegative
  deriving DecidableEq, Fintype

private theorem sum_affinePrimalCoordinate
    (f : AffinePrimalCoordinate → ℝ) :
    (∑ j, f j) =
      f .scale + f .upperPositive + f .upperNegative := by
  classical
  rw [show (Finset.univ : Finset AffinePrimalCoordinate) =
      {.scale, .upperPositive, .upperNegative} by decide]
  simp
  ring

private def affinePrimalMatrix
    (slope : Action → ℝ) :
    Action → AffinePrimalCoordinate → ℝ
  | a, .scale => -slope a
  | _, .upperPositive => 1
  | _, .upperNegative => -1

private def affinePrimalObjective :
    AffinePrimalCoordinate → ℝ
  | .scale => 0
  | .upperPositive => 1
  | .upperNegative => -1

private def affinePrimalPoint
    (c value : ℝ) : AffinePrimalCoordinate → ℝ
  | .scale => c
  | .upperPositive => max value 0
  | .upperNegative => max (-value) 0

private theorem positivePart_sub_negativePart (value : ℝ) :
    max value 0 - max (-value) 0 = value := by
  rcases le_total 0 value with hvalue | hvalue
  · simp [max_eq_left hvalue, max_eq_right (neg_nonpos.mpr hvalue)]
  · have hneg : 0 ≤ -value := neg_nonneg.mpr hvalue
    simp [max_eq_right hvalue, max_eq_left hneg]

private theorem affinePrimalPoint_nonnegative
    {c value : ℝ} (hc : 0 ≤ c) :
    Nonnegative (affinePrimalPoint c value) := by
  intro j
  cases j with
  | scale => exact hc
  | upperPositive => exact le_max_right _ _
  | upperNegative => exact le_max_right _ _

private theorem affinePrimalPoint_value
    (c value : ℝ) :
    minPrimalValue affinePrimalObjective
      (affinePrimalPoint c value) = value := by
  rw [minPrimalValue, dot, sum_affinePrimalCoordinate]
  simp only [affinePrimalObjective, affinePrimalPoint]
  simpa [sub_eq_add_neg] using positivePart_sub_negativePart value

omit [Fintype Action] [Nonempty Action] in
private theorem affinePrimalPoint_feasible
    (intercept slope : Action → ℝ) {c value : ℝ}
    (hmajorant : IsAffineMajorant intercept slope c value) :
    MinPrimalFeasible (affinePrimalMatrix slope) intercept
      (affinePrimalPoint c value) := by
  constructor
  · exact affinePrimalPoint_nonnegative hmajorant.1
  · intro a
    have ha := hmajorant.2 a
    rw [rowEval, sum_affinePrimalCoordinate]
    simp only [affinePrimalMatrix, affinePrimalPoint]
    have hparts := positivePart_sub_negativePart value
    linarith

omit [Fintype Action] [Nonempty Action] in
private theorem affineMajorant_of_primalFeasible
    (intercept slope : Action → ℝ)
    {x : AffinePrimalCoordinate → ℝ}
    (hx : MinPrimalFeasible
      (affinePrimalMatrix slope) intercept x) :
    IsAffineMajorant intercept slope (x .scale)
      (x .upperPositive - x .upperNegative) := by
  constructor
  · exact hx.1 .scale
  · intro a
    have ha := hx.2 a
    rw [rowEval, sum_affinePrimalCoordinate] at ha
    simp only [affinePrimalMatrix] at ha
    linarith

private theorem affinePrimalValue_eq
    (x : AffinePrimalCoordinate → ℝ) :
    minPrimalValue affinePrimalObjective x =
      x .upperPositive - x .upperNegative := by
  rw [minPrimalValue, dot, sum_affinePrimalCoordinate]
  simp [affinePrimalObjective]
  ring

omit [Nonempty Action] in
/-- Strong duality for the one-dimensional affine maximum.  Any attained
primal optimum has a probability-weight dual optimizer with nonnegative
average slope and the same value. -/
theorem exists_optimalAffineWeight
    (intercept slope : Action → ℝ) {c value : ℝ}
    (hoptimal : IsOptimalAffineMajorant intercept slope c value) :
    ∃ weight,
      IsAdmissibleAffineWeight slope weight ∧
      (∑ a, weight a * intercept a) = value := by
  let x := affinePrimalPoint c value
  have hx :
      MinPrimalFeasible (affinePrimalMatrix slope) intercept x :=
    affinePrimalPoint_feasible intercept slope hoptimal.1
  have hopt :
      ∀ z,
        MinPrimalFeasible
          (affinePrimalMatrix slope) intercept z →
        minPrimalValue affinePrimalObjective x ≤
          minPrimalValue affinePrimalObjective z := by
    intro z hz
    rw [affinePrimalPoint_value, affinePrimalValue_eq]
    exact hoptimal.2 _ _ (affineMajorant_of_primalFeasible intercept slope hz)
  obtain ⟨weight, hweight, hvalue⟩ :=
    lp_strong_duality hx hopt
  have hxvalue :
      minPrimalValue affinePrimalObjective x = value := by
    exact affinePrimalPoint_value c value
  rw [hxvalue] at hvalue
  refine ⟨weight, ?_, ?_⟩
  · refine ⟨hweight.1, ?_, ?_⟩
    · have hupper := hweight.2 .upperPositive
      have hlower := hweight.2 .upperNegative
      simp [colEval, affinePrimalMatrix,
        affinePrimalObjective] at hupper hlower
      linarith
    · have hscale := hweight.2 .scale
      simp [colEval, affinePrimalMatrix,
        affinePrimalObjective] at hscale
      linarith
  · simpa [maxDualValue, dot, mul_comm] using hvalue

/-- Exact finite affine minimax duality in optimizer form. -/
theorem exists_affineMinimax_optimizers
    (intercept slope : Action → ℝ)
    (hbounded : ∃ a, 0 ≤ slope a) :
    ∃ c value weight,
      IsOptimalAffineMajorant intercept slope c value ∧
      IsAdmissibleAffineWeight slope weight ∧
      (∑ a, weight a * intercept a) = value ∧
      (∀ candidateWeight,
        IsAdmissibleAffineWeight slope candidateWeight →
        (∑ a, candidateWeight a * intercept a) ≤ value) := by
  obtain ⟨c, value, hoptimal⟩ :=
    exists_optimalAffineMajorant intercept slope hbounded
  obtain ⟨weight, hweight, hvalue⟩ :=
    exists_optimalAffineWeight intercept slope hoptimal
  refine ⟨c, value, weight, hoptimal, hweight, hvalue, ?_⟩
  intro candidateWeight hcandidate
  exact affineWeight_le_majorant
    intercept slope candidateWeight hcandidate hoptimal.1

omit [Nonempty Action] in
omit [Fintype Action] [Nonempty Action] in
/-- If every slope is negative, every prescribed upper value is eventually
an affine majorant: the primal value is unbounded below. -/
theorem exists_affineMajorant_of_all_slope_negative
    [Finite Action]
    (intercept slope : Action → ℝ)
    (hnegative : ∀ a, slope a < 0) (value : ℝ) :
    ∃ c, IsAffineMajorant intercept slope c value := by
  letI := Fintype.ofFinite Action
  let c : ℝ :=
    ∑ a, max 0 ((intercept a - value) / (-slope a))
  have hc : 0 ≤ c := by
    apply Finset.sum_nonneg
    intro a _
    exact le_max_left _ _
  refine ⟨c, hc, ?_⟩
  intro a
  have hdenom : 0 < -slope a := neg_pos.mpr (hnegative a)
  have hterm :
      max 0 ((intercept a - value) / (-slope a)) ≤ c := by
    change max 0 ((intercept a - value) / (-slope a)) ≤
      ∑ b, max 0 ((intercept b - value) / (-slope b))
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b =>
        max 0 ((intercept b - value) / (-slope b)))
      (fun b _ => le_max_left _ _)
      (Finset.mem_univ a)
  have hratio :
      (intercept a - value) / (-slope a) ≤ c :=
    (le_max_right _ _).trans hterm
  have hdifference :
      intercept a - value ≤ c * (-slope a) :=
    (div_le_iff₀ hdenom).mp hratio
  linarith

/-- Exhaustive pointwise alternative: either the affine minimax has primal
and dual optimizers, or all slopes are negative and the primal is unbounded
below.  A zero-slope active line belongs to the first branch and accounts for
the plateau case omitted by a pair-only classification. -/
theorem affineMinimax_alternative
    (intercept slope : Action → ℝ) :
    (∃ c value weight,
      IsOptimalAffineMajorant intercept slope c value ∧
      IsAdmissibleAffineWeight slope weight ∧
      (∑ a, weight a * intercept a) = value) ∨
    (∀ value, ∃ c, IsAffineMajorant intercept slope c value) := by
  by_cases hbounded : ∃ a, 0 ≤ slope a
  · left
    obtain ⟨c, value, weight, hopt, hweight, hvalue, -⟩ :=
      exists_affineMinimax_optimizers intercept slope hbounded
    exact ⟨c, value, weight, hopt, hweight, hvalue⟩
  · right
    have hnegative : ∀ a, slope a < 0 := by
      intro a
      exact lt_of_not_ge fun ha => hbounded ⟨a, ha⟩
    exact exists_affineMajorant_of_all_slope_negative
      intercept slope hnegative

end LinearProgramming
end Math
