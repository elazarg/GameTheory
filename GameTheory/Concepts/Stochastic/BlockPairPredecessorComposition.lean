/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairQuadraticRootSelection

/-!
# Validity and composition of block-pair predecessor charts

This file connects the explicit charts to the game-facing one-phase
predecessor correspondence.  It separates the algebraic core (inactive
hazards are zero, active players are indifferent, and the displayed value is
the terminal-table predecessor value) from the open chamber inequalities
checked by exact interval certificates.

The final section fixes composition orientation.  A word listed in temporal
order is folded from the right, so its last-phase chart acts first.  A fixed
point of that return therefore decodes to a cyclic chain of valid one-phase
predecessor links.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory.BlockPairCharts

open BlockPairK11

abbrev ContinuationValue := Player → ℝ

/-- The algebraic part of a one-phase support chart, before checking strict
hazard and inactive-deviation inequalities. -/
def IsCorePredecessorStep (support : QuitterMask)
    (hazard successor predecessor : ContinuationValue) : Prop :=
  predecessorValue hazard successor = predecessor ∧
    ∀ who : Player,
      if maskHasPlayer support who = true then
        difference hazard successor who = 0
      else
        hazard who = 0

/-- The full strategically valid one-phase predecessor condition (7). -/
def IsValidPredecessorStep (support : QuitterMask)
    (hazard successor predecessor : ContinuationValue) : Prop :=
  predecessorValue hazard successor = predecessor ∧
    ∀ who : Player,
      if maskHasPlayer support who = true then
        0 < hazard who ∧ hazard who < 1 ∧
          difference hazard successor who = 0
      else
        hazard who = 0 ∧ difference hazard successor who ≤ 0

theorem IsCorePredecessorStep.isValid
    {support : QuitterMask}
    {hazard successor predecessor : ContinuationValue}
    (hcore : IsCorePredecessorStep support hazard successor predecessor)
    (hactive : ∀ who, maskHasPlayer support who = true →
      0 < hazard who ∧ hazard who < 1)
    (hinactive : ∀ who, maskHasPlayer support who = false →
      difference hazard successor who ≤ 0) :
    IsValidPredecessorStep support hazard successor predecessor := by
  refine ⟨hcore.1, fun who ↦ ?_⟩
  by_cases hsupport : maskHasPlayer support who = true
  · have hcoreWho := hcore.2 who
    simp only [hsupport, if_true] at hcoreWho ⊢
    exact ⟨(hactive who hsupport).1, (hactive who hsupport).2,
      hcoreWho⟩
  · have hsupportFalse : maskHasPlayer support who = false := by
      cases hvalue : maskHasPlayer support who <;> simp_all
    have hcoreWho := hcore.2 who
    simp only [hsupport] at hcoreWho ⊢
    exact ⟨hcoreWho, hinactive who hsupportFalse⟩

theorem supportNine_core
    (successor : ContinuationValue)
    (hzero : successor 0 ≠ 0)
    (hthree : successor 3 + 4 ≠ 0) :
    IsCorePredecessorStep 9 (supportNineHazard successor) successor
      (supportNineValue successor) := by
  obtain ⟨hactiveZero, hactiveThree⟩ :=
    supportNine_active successor hzero hthree
  refine ⟨supportNine_predecessorValue successor hzero hthree, ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

theorem supportTen_core
    (successor : ContinuationValue)
    (hone : successor 1 + 4 ≠ 0)
    (hthree : successor 3 ≠ 0) :
    IsCorePredecessorStep 10 (supportTenHazard successor) successor
      (supportTenValue successor) := by
  obtain ⟨hactiveOne, hactiveThree⟩ :=
    supportTen_active successor hone hthree
  refine ⟨supportTen_predecessorValue successor hone hthree, ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

theorem supportSeven_core
    (successor : ContinuationValue)
    (htwo : successor 2 + 4 ≠ 0)
    (hmiddle : supportSevenMiddle successor ≠ 0)
    (hcoefficient : supportSevenCoefficient successor ≠ 0) :
    IsCorePredecessorStep 7 (supportSevenHazard successor) successor
      (supportSevenValue successor) := by
  obtain ⟨hactiveZero, hactiveOne, hactiveTwo⟩ :=
    supportSeven_active successor htwo hmiddle hcoefficient
  refine ⟨supportSeven_predecessorValue successor htwo hmiddle hcoefficient,
    ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

theorem supportFourteen_core
    (successor : ContinuationValue)
    (hone : successor 1 + 4 ≠ 0)
    (hmiddle : supportFourteenMiddle successor ≠ 0)
    (hcoefficient : supportFourteenCoefficient successor ≠ 0) :
    IsCorePredecessorStep 14 (supportFourteenHazard successor) successor
      (supportFourteenValue successor) := by
  obtain ⟨hactiveOne, hactiveTwo, hactiveThree⟩ :=
    supportFourteen_active successor hone hmiddle hcoefficient
  refine ⟨supportFourteen_predecessorValue successor hone hmiddle hcoefficient,
    ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

theorem supportThirteen_core
    (successor : ContinuationValue) (z : ℝ)
    (hzero : supportThirteenZeroDenominator successor z ≠ 0)
    (htwo : supportThirteenTwoDenominator successor z ≠ 0)
    (hpolynomial : supportThirteenPolynomial successor z = 0) :
    IsCorePredecessorStep 13 (supportThirteenHazard successor z) successor
      (supportThirteenValue successor z) := by
  obtain ⟨hactiveZero, hactiveTwo, hactiveThree⟩ :=
    supportThirteen_active successor z hzero htwo hpolynomial
  refine ⟨supportThirteen_predecessorValue successor z hzero htwo hpolynomial,
    ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

theorem supportEleven_core
    (successor : ContinuationValue) (z : ℝ)
    (hzero : supportElevenZeroDenominator successor z ≠ 0)
    (hone : supportElevenOneDenominator successor z ≠ 0)
    (hpolynomial : supportElevenPolynomial successor z = 0) :
    IsCorePredecessorStep 11 (supportElevenHazard successor z) successor
      (supportElevenValue successor z) := by
  obtain ⟨hactiveZero, hactiveOne, hactiveThree⟩ :=
    supportEleven_active successor z hzero hone hpolynomial
  refine ⟨supportEleven_predecessorValue successor z hzero hone hpolynomial,
    ?_⟩
  intro who
  fin_cases who <;> simp +decide <;> first | assumption | rfl

/-- A single-valued choice from the predecessor correspondence. -/
structure SelectedPredecessorChart where
  support : QuitterMask
  hazard : ContinuationValue → ContinuationValue
  predecessor : ContinuationValue → ContinuationValue

namespace SelectedPredecessorChart

def CoreAt (chart : SelectedPredecessorChart)
    (successor : ContinuationValue) : Prop :=
  IsCorePredecessorStep chart.support (chart.hazard successor) successor
    (chart.predecessor successor)

def ValidAt (chart : SelectedPredecessorChart)
    (successor : ContinuationValue) : Prop :=
  IsValidPredecessorStep chart.support (chart.hazard successor) successor
    (chart.predecessor successor)

theorem validAt_coreAt {chart : SelectedPredecessorChart}
    {successor : ContinuationValue} (hvalid : chart.ValidAt successor) :
    chart.CoreAt successor := by
  refine ⟨hvalid.1, fun who ↦ ?_⟩
  by_cases hsupport : maskHasPlayer chart.support who = true
  · have hvalidWho := hvalid.2 who
    simp only [hsupport, if_true] at hvalidWho ⊢
    exact hvalidWho.2.2
  · have hvalidWho := hvalid.2 who
    simp only [hsupport] at hvalidWho ⊢
    exact hvalidWho.1

end SelectedPredecessorChart

/-- The return associated to a temporal chart word.  It is a right fold:
for `[R₀, ..., R₁₀]`, `R₁₀` acts first. -/
def wordReturn : List SelectedPredecessorChart →
    ContinuationValue → ContinuationValue
  | [], value => value
  | chart :: charts, terminal =>
      chart.predecessor (wordReturn charts terminal)

/-- The exact validity hypotheses encountered while evaluating a chart word
from right to left. -/
def ValidAlong (validity : SelectedPredecessorChart →
    ContinuationValue → Prop) :
    List SelectedPredecessorChart → ContinuationValue → Prop
  | [], _ => True
  | chart :: charts, terminal =>
      ValidAlong validity charts terminal ∧
        validity chart (wordReturn charts terminal)

/-- A decoded predecessor path: the tail of the temporal word is decoded
first, and the head chart is then applied to its successor value. -/
inductive DecodedChartPath
    (validity : SelectedPredecessorChart → ContinuationValue → Prop) :
    List SelectedPredecessorChart → ContinuationValue →
      ContinuationValue → Prop
  | nil (value) : DecodedChartPath validity [] value value
  | cons {chart charts terminal successor}
      (htail : DecodedChartPath validity charts terminal successor)
      (hchart : validity chart successor) :
      DecodedChartPath validity (chart :: charts) terminal
        (chart.predecessor successor)

theorem wordReturn_decoded
    (validity : SelectedPredecessorChart → ContinuationValue → Prop)
    (charts : List SelectedPredecessorChart)
    (terminal : ContinuationValue)
    (hvalid : ValidAlong validity charts terminal) :
    DecodedChartPath validity charts terminal (wordReturn charts terminal) := by
  induction charts with
  | nil => exact .nil terminal
  | cons chart charts ih =>
      exact .cons (ih hvalid.1) hvalid.2

/-- A fixed point of a right-folded return decodes to a cyclic predecessor
path with exactly the listed temporal orientation. -/
theorem fixedPoint_decodedCycle
    (validity : SelectedPredecessorChart → ContinuationValue → Prop)
    (charts : List SelectedPredecessorChart)
    (value : ContinuationValue)
    (hvalid : ValidAlong validity charts value)
    (hfixed : wordReturn charts value = value) :
    DecodedChartPath validity charts value value := by
  simpa only [hfixed] using
    wordReturn_decoded validity charts value hvalid

end GameTheory.BlockPairCharts
