/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CycleIsolatedCoordinate
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation

/-!
# Periodic holonomy of exact dynamic debt

Exact dynamic-debt transport identifies a player's debt ratio across a finite
window with the product of the opponents' Continue masses.  This module records
the rigidity consequence for a returning positive debt coordinate.

For a coordinate `who`, the returning condition used here consists of exactly
three hypotheses:

* its debt is positive at the start of the window;
* its own prescribed Continue probability is positive at every phase; and
* its debt coordinate, not necessarily the whole debt point, returns at the
  end of the window.

The debt-ratio identity then makes opponent survival equal to one.  Since each
factor lies in `[0, 1]`, every opponent continues surely at every phase.  Two
distinct returning coordinates therefore force every phase root to be the
all-Continue root, so their common finite period cannot absorb.  Equivalently,
an absorbing period has at most one returning positive debt coordinate.

These are finite-window consequences for an already supplied chronological
exact-debt tail.  In particular, the endpoint debt equality is an explicit
hypothesis.  Nothing here turns a counterexample tail, a recurrent annotation,
or a limiting debt value into a periodic exact-debt word.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A coordinate of an exact dynamic-debt tail returns positively across a
finite window: its entry debt is positive, its own Continue action has positive
probability at every traversed phase, and its endpoint debt equals its entry
debt.

This predicate does not assert periodicity of the full debt point or root. -/
def IsQuittingReturningDynamicDebtCoordinate
    (tail : ℕ → QuittingDebtPoint ι) (who : ι)
    (start period : ℕ) : Prop :=
  0 < (tail start).2 who ∧
    (∀ offset, offset < period →
      0 < (quittingDynamicDebtTailRoots tail (start + offset) who false).toReal) ∧
    (tail (start + period)).2 who = (tail start).2 who

/-- **Positive-debt cycle holonomy.**  A returning positive debt coordinate
whose own Continue probability stays positive has opponent-survival product
exactly one over the finite window. -/
theorem quittingOpponentSurvivalWeight_eq_one_of_returningDynamicDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start period : ℕ)
    (hreturning :
      IsQuittingReturningDynamicDebtCoordinate tail who start period) :
    quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots tail) who start period = 1 := by
  rcases hreturning with ⟨hdebt, hcontinue, hreturn⟩
  have hendDebt : 0 < (tail (start + period)).2 who := by
    rw [hreturn]
    exact hdebt
  calc
    quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots tail) who start period =
        (tail start).2 who / (tail (start + period)).2 who :=
      quittingOpponentSurvivalWeight_eq_debt_div
        (reward := reward) tail hbox hedge who start period hcontinue hendDebt
    _ = (tail start).2 who / (tail start).2 who := by rw [hreturn]
    _ = 1 := div_self hdebt.ne'

/-- Every opponent-Continue factor in a returning positive-debt window is
one.  This is the phasewise form of positive-debt cycle holonomy. -/
theorem quittingFixedOpponentsContinueMass_eq_one_of_returningDynamicDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start period : ℕ)
    (hreturning :
      IsQuittingReturningDynamicDebtCoordinate tail who start period)
    (offset : ℕ) (hoffset : offset < period) :
    quittingFixedOpponentsContinueMass
        (quittingDynamicDebtTailRoots tail) who (start + offset) = 1 := by
  have hproduct :=
    quittingOpponentSurvivalWeight_eq_one_of_returningDynamicDebt
      (reward := reward) tail hbox hedge who start period hreturning
  unfold quittingOpponentSurvivalWeight at hproduct
  exact eq_one_of_prod_eq_one_of_mem
    (f := fun phase ↦ quittingFixedOpponentsContinueMass
      (quittingDynamicDebtTailRoots tail) who (start + phase))
    (fun phase _ ↦ quittingRootDeletedContinueMass_nonneg
      (quittingDynamicDebtTailRoots tail (start + phase)) who)
    (fun phase _ ↦ quittingRootDeletedContinueMass_le_one
      (quittingDynamicDebtTailRoots tail (start + phase)) who)
    hproduct (Finset.mem_range.mpr hoffset)

/-- A returning positive debt coordinate is isolated throughout its finite
window: every opponent continues surely at every traversed phase. -/
theorem isQuittingIsolatedRoot_of_returningDynamicDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) (start period : ℕ)
    (hreturning :
      IsQuittingReturningDynamicDebtCoordinate tail who start period)
    (offset : ℕ) (hoffset : offset < period) :
    IsQuittingIsolatedRoot
      (quittingDynamicDebtTailRoots tail (start + offset)) who := by
  apply isQuittingIsolatedRoot_of_deletedContinueMass_eq_one
  rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
  exact quittingFixedOpponentsContinueMass_eq_one_of_returningDynamicDebt
    (reward := reward) tail hbox hedge who start period hreturning offset hoffset

/-- Two distinct returning positive debt coordinates force every traversed
phase to be the all-Continue root. -/
theorem quittingDynamicDebtTailRoots_eq_allContinue_of_two_returningDynamicDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    {first second : ι} (hne : first ≠ second) (start period : ℕ)
    (hfirst :
      IsQuittingReturningDynamicDebtCoordinate tail first start period)
    (hsecond :
      IsQuittingReturningDynamicDebtCoordinate tail second start period)
    (offset : ℕ) (hoffset : offset < period) :
    quittingDynamicDebtTailRoots tail (start + offset) =
      quittingAllContinueRoot := by
  have hfirstIsolated := isQuittingIsolatedRoot_of_returningDynamicDebt
    (reward := reward) tail hbox hedge first start period hfirst offset hoffset
  have hsecondIsolated := isQuittingIsolatedRoot_of_returningDynamicDebt
    (reward := reward) tail hbox hedge second start period hsecond offset hoffset
  funext player
  change quittingDynamicDebtTailRoots tail (start + offset) player = PMF.pure false
  by_cases hplayer : player = first
  · subst player
    exact hsecondIsolated first hne
  · exact hfirstIsolated player hplayer

/-- Two distinct returning positive debt coordinates make the whole finite
period nonabsorbing: its joint all-Continue survival is one. -/
theorem quittingJointSurvivalWeight_eq_one_of_two_returningDynamicDebt
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    {first second : ι} (hne : first ≠ second) (start period : ℕ)
    (hfirst :
      IsQuittingReturningDynamicDebtCoordinate tail first start period)
    (hsecond :
      IsQuittingReturningDynamicDebtCoordinate tail second start period) :
    quittingJointSurvivalWeight
        (quittingDynamicDebtTailRoots tail) start period = 1 := by
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_eq_one
  intro offset hoffset
  rw [quittingDynamicDebtTailRoots_eq_allContinue_of_two_returningDynamicDebt
    (reward := reward) tail hbox hedge hne start period hfirst hsecond offset
      (Finset.mem_range.mp hoffset)]
  simp [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingAllContinueRoot]

/-- **At most one returning positive debt coordinate on an absorbing
period.**  If the joint survival over the window is strictly below one, any
two coordinates satisfying positive debt, positive own Continue at every
phase, and endpoint debt return must coincide. -/
theorem eq_of_two_returningDynamicDebt_of_jointSurvival_lt_one
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (start period : ℕ)
    (habsorbing : quittingJointSurvivalWeight
      (quittingDynamicDebtTailRoots tail) start period < 1)
    {first second : ι}
    (hfirst :
      IsQuittingReturningDynamicDebtCoordinate tail first start period)
    (hsecond :
      IsQuittingReturningDynamicDebtCoordinate tail second start period) :
    first = second := by
  by_contra hne
  have hnonabsorbing :=
    quittingJointSurvivalWeight_eq_one_of_two_returningDynamicDebt
      (reward := reward) tail hbox hedge hne start period hfirst hsecond
  rw [hnonabsorbing] at habsorbing
  exact (lt_irrefl 1) habsorbing

/-- Phasewise absorbing form of the at-most-one theorem.  If some traversed
root has positive absorption mass, two returning positive debt coordinates
must coincide. -/
theorem eq_of_two_returningDynamicDebt_of_exists_absorbingPhase
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (start period : ℕ)
    (habsorbing : ∃ offset, offset < period ∧
      0 < quittingRootAbsorptionMass
        (quittingDynamicDebtTailRoots tail (start + offset)))
    {first second : ι}
    (hfirst :
      IsQuittingReturningDynamicDebtCoordinate tail first start period)
    (hsecond :
      IsQuittingReturningDynamicDebtCoordinate tail second start period) :
    first = second := by
  obtain ⟨offset, hoffset, habsorb⟩ := habsorbing
  by_contra hne
  have hroot :=
    quittingDynamicDebtTailRoots_eq_allContinue_of_two_returningDynamicDebt
      (reward := reward) tail hbox hedge hne start period hfirst hsecond
        offset hoffset
  have hmass : quittingStationaryContinueMass
      (quittingDynamicDebtTailRoots tail (start + offset)) = 1 := by
    rw [hroot]
    simp [quittingStationaryContinueMass_eq_prod_continueProbability,
      quittingAllContinueRoot]
  rw [quittingRootAbsorptionMass, hmass] at habsorb
  linarith

end GameTheory
