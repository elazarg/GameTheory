/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanDebtMonotonicity

/-!
# Debt-augmented quitting Nash--Bellman edges

Finite minimum-debt chains carry a fixed-dimensional backward costate.  At
an edge with current product root `x`, its coordinates satisfy

`bCurrent i = c_i(x) * bSuccessor i`,

where `c_i(x)` is the probability that every opponent of `i` continues.
This file defines the compact augmented state box and proves the exact
zero-loss support classification used by the calibrated plateau argument.

No occupation measure, invariant law, or Palm/marked-burst implication is
claimed here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One bounded Nash--Bellman point together with its playerwise nonnegative
terminal-debt costate. -/
abbrev QuittingDebtPoint (ι : Type) [Fintype ι] :=
  QuittingNashBellmanPoint ι × Payoff ι

/-- The positive singleton option which bounds one debt coordinate. -/
def quittingPositiveSingletonDebtCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) : ℝ :=
  max 0 (reward (quittingSingletonTerminal who) who)

/-- Compact box for augmented payoff/root/debt states. -/
def quittingDebtBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingDebtPoint ι) :=
  quittingNashBellmanBox (quittingRewardBound reward) ×ˢ
    Set.Icc (0 : Payoff ι) (quittingPositiveSingletonDebtCap reward)

omit [DecidableEq ι] in
/-- The augmented state box is compact. -/
theorem quittingDebtBox_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingDebtBox reward) := by
  exact (quittingNashBellmanBox_isCompact (ι := ι)
    (quittingRewardBound reward)).prod isCompact_Icc

/-- Opponent Continue mass written directly in the current root's simplex
coordinates. -/
def quittingDebtOpponentContinueMass
    (state : QuittingDebtPoint ι) (owner : ι) : ℝ :=
  ∏ other ∈ (Finset.univ.erase owner : Finset ι),
    state.1.2 other false

/-- The simplex costate factor is the operational fixed-opponents Continue
mass of the displayed product root. -/
theorem quittingDebtOpponentContinueMass_eq_stationary
    (state : QuittingDebtPoint ι) (owner : ι) :
    quittingDebtOpponentContinueMass state owner =
      quittingStationaryContinueMass
        (Function.update (quittingRootOfSimplex state.1.2) owner
          (PMF.pure false)) := by
  symm
  exact quittingFixedOpponentsContinueMass_quittingRootOfSimplex
    state.1.2 owner

/-- Every debt costate factor is nonnegative. -/
theorem quittingDebtOpponentContinueMass_nonneg
    (state : QuittingDebtPoint ι) (owner : ι) :
    0 ≤ quittingDebtOpponentContinueMass state owner := by
  unfold quittingDebtOpponentContinueMass
  exact Finset.prod_nonneg fun other _ ↦
    (state.1.2 other).property.1 false

/-- Every debt costate factor is at most one. -/
theorem quittingDebtOpponentContinueMass_le_one
    (state : QuittingDebtPoint ι) (owner : ι) :
    quittingDebtOpponentContinueMass state owner ≤ 1 := by
  unfold quittingDebtOpponentContinueMass
  apply Finset.prod_le_one
  · intro other _
    exact (state.1.2 other).property.1 false
  · intro other _
    rw [← quittingRootOfSimplex_apply_toReal]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (quittingRootOfSimplex state.1.2 other) false)

/-- Exact debt-augmented Nash--Bellman edge. -/
def IsQuittingDebtEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι) : Prop :=
  IsQuittingNashBellmanEdge reward current.1 successor.1 ∧
    ∀ who, current.2 who =
      quittingDebtOpponentContinueMass current who * successor.2 who

/-- Playerwise debt lost while moving from the current augmented state to
its successor. -/
def quittingDebtCoordinateLoss
    (current successor : QuittingDebtPoint ι) (who : ι) : ℝ :=
  successor.2 who - current.2 who

/-- Total one-edge costate loss. -/
def quittingDebtEdgeLoss
    (current successor : QuittingDebtPoint ι) : ℝ :=
  ∑ who, quittingDebtCoordinateLoss current successor who

/-- The coordinate loss is the successor debt times one minus the current
opponent Continue mass. -/
theorem quittingDebtCoordinateLoss_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDebtEdge reward current successor)
    (who : ι) :
    quittingDebtCoordinateLoss current successor who =
      (1 - quittingDebtOpponentContinueMass current who) *
        successor.2 who := by
  rw [quittingDebtCoordinateLoss, hedge.2 who]
  ring

/-- Coordinate loss is nonnegative on the augmented box. -/
theorem quittingDebtCoordinateLoss_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (_hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (who : ι) :
    0 ≤ quittingDebtCoordinateLoss current successor who := by
  rw [quittingDebtCoordinateLoss_eq reward current successor hedge who]
  exact mul_nonneg
    (sub_nonneg.mpr (quittingDebtOpponentContinueMass_le_one current who))
    (hsuccessor.2.1 who)

/-- Total edge loss is nonnegative on the augmented box. -/
theorem quittingDebtEdgeLoss_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor) :
    0 ≤ quittingDebtEdgeLoss current successor := by
  unfold quittingDebtEdgeLoss
  exact Finset.sum_nonneg fun who _ ↦
    quittingDebtCoordinateLoss_nonneg reward current successor
      hcurrent hsuccessor hedge who

/-- Zero total loss forces every coordinate loss to vanish. -/
theorem quittingDebtCoordinateLoss_eq_zero_of_edgeLoss_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (hloss : quittingDebtEdgeLoss current successor = 0)
    (who : ι) :
    quittingDebtCoordinateLoss current successor who = 0 := by
  apply (Finset.sum_eq_zero_iff_of_nonneg
    (fun player _ ↦ quittingDebtCoordinateLoss_nonneg reward
      current successor hcurrent hsuccessor hedge player)).1
  · exact hloss
  · exact Finset.mem_univ who

/-- **Zero-loss support implication.**  A positive successor debt coordinate
forces the corresponding opponent Continue mass to equal one. -/
theorem quittingDebtOpponentContinueMass_eq_one_of_edgeLoss_eq_zero_of_debt_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (hloss : quittingDebtEdgeLoss current successor = 0)
    (owner : ι) (hdebt : 0 < successor.2 owner) :
    quittingDebtOpponentContinueMass current owner = 1 := by
  have hcoordinate :=
    quittingDebtCoordinateLoss_eq_zero_of_edgeLoss_eq_zero reward
      current successor hcurrent hsuccessor hedge hloss owner
  rw [quittingDebtCoordinateLoss_eq reward current successor hedge owner]
    at hcoordinate
  rcases mul_eq_zero.mp hcoordinate with hmass | hdebtZero
  · linarith
  · exact (ne_of_gt hdebt hdebtZero).elim

/-- A positive debt owner on a zero-loss edge is the only player who may
quit at the current root. -/
theorem quittingRootOfSimplex_eq_pure_false_of_zeroDebtLoss_of_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (hloss : quittingDebtEdgeLoss current successor = 0)
    (owner : ι) (hdebt : 0 < successor.2 owner)
    (other : ι) (hne : other ≠ owner) :
    quittingRootOfSimplex current.1.2 other = PMF.pure false := by
  have hmass :=
    quittingDebtOpponentContinueMass_eq_one_of_edgeLoss_eq_zero_of_debt_pos
      reward current successor hcurrent hsuccessor hedge hloss owner hdebt
  rw [quittingDebtOpponentContinueMass_eq_stationary] at hmass
  have hzero :=
    quittingProbability_eq_zero_of_fixedOpponentsContinueMass_eq_one
      (quittingRootOfSimplex current.1.2) owner other hne hmass
  exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ hzero

/-- Positive total successor debt selects a player whose opponents all
Continue at a zero-loss root. -/
theorem exists_soloOwner_of_zeroDebtLoss_of_sum_debt_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (hloss : quittingDebtEdgeLoss current successor = 0)
    (hdebt : 0 < ∑ who, successor.2 who) :
    ∃ owner, 0 < successor.2 owner ∧
      ∀ other, other ≠ owner →
        quittingRootOfSimplex current.1.2 other = PMF.pure false := by
  obtain ⟨owner, _howner, hownerDebt⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun who _ ↦ hsuccessor.2.1 who)).1 hdebt
  exact ⟨owner, hownerDebt, fun other hne ↦
    quittingRootOfSimplex_eq_pure_false_of_zeroDebtLoss_of_other
      reward current successor hcurrent hsuccessor hedge hloss
        owner hownerDebt other hne⟩

/-- Two positive successor debt coordinates force the current root to be
all-Continue on a zero-loss edge. -/
theorem quittingRootOfSimplex_eq_allContinue_of_zeroDebtLoss_of_two_debts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hcurrent : current ∈ quittingDebtBox reward)
    (hsuccessor : successor ∈ quittingDebtBox reward)
    (hedge : IsQuittingDebtEdge reward current successor)
    (hloss : quittingDebtEdgeLoss current successor = 0)
    (first second : ι) (hne : first ≠ second)
    (hfirst : 0 < successor.2 first) (hsecond : 0 < successor.2 second) :
    quittingRootOfSimplex current.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  funext player
  by_cases hp : player = first
  · subst player
    exact quittingRootOfSimplex_eq_pure_false_of_zeroDebtLoss_of_other
      reward current successor hcurrent hsuccessor hedge hloss
        second hsecond first hne
  · exact quittingRootOfSimplex_eq_pure_false_of_zeroDebtLoss_of_other
      reward current successor hcurrent hsuccessor hedge hloss
        first hfirst player hp

end GameTheory
