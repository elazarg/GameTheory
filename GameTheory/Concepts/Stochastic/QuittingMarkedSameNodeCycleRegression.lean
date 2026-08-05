/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BigMatch
import GameTheory.Concepts.Stochastic.QuittingMarkedFenceIteration
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate

/-!
# A same-node marked-transfer cycle need not give an invariant edge law

This file records a two-player, two-edge exact quitting-game calculation.  At
the first root both players mix one half, its current value is `(-2,-2)`, and
its declared successor is `(-1,-1)`.  At the second root both players quit
surely, with successor zero.  Both roots are exact Nash roots and both
successor equations hold.

At the first root either player can mark the other player using a bad
owner-deleted singleton atom.  Consequently a procedure which merely changes
the marked player, but does not advance the suffix time, can alternate the two
marks forever while selecting the *same* Bellman edge.  Repeated marks then do
not imply matching current and successor marginals: the selected edge still
has distinct endpoints `(-2,-2)` and `(-1,-1)`.

This is only a regression for that recurrence inference.  It is not a
counterexample to equilibrium existence: the displayed two-edge chain itself
ends at a surely absorbing exact Nash root.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingMarkedSameNodeCycleRegression

/-- The symmetric terminal table: a joint quit pays `-1`, while a singleton
quit pays `-3`, to both players. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun _ => if quitters.1.card = 2 then -1 else -3

/-- The first root, at which both players quit with probability one half. -/
def halfRoot : Bool → PMF Bool := fun _ => PMF.uniformOfFintype Bool

/-- The terminal root, at which both players quit surely. -/
def sureRoot : Bool → PMF Bool := fun _ => PMF.pure true

/-- Current value at the half root. -/
def firstValue : Payoff Bool := fun _ => -2

/-- Successor value of the half root and current value of the sure root. -/
def secondValue : Payoff Bool := fun _ => -1

/-- Terminal continuation beyond the surely absorbing root. -/
def terminalValue : Payoff Bool := fun _ => 0

@[simp] theorem expect_uniform_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

/-- Fubini expansion of a two-player Boolean product law. -/
theorem expect_pmfPi_bool (root : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi root) f =
      expect (root false) (fun first ↦
        expect (root true) (fun second ↦
          f (fun who ↦ if who then second else first))) :=
  StochasticGame.BigMatch.expect_pmfPi_bool root f

/-- Explicit quitter set for a two-coordinate Boolean action.  Keeping this
small normal form available makes the endpoint calculations below robust to
the representation of `Finset.univ` chosen by simplification. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool ↦ if who then second else first) =
      (if first = true then {false} else ∅) ∪
        (if second = true then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

@[simp] theorem halfRoot_true_toReal (who : Bool) :
    (halfRoot who true).toReal = 1 / 2 := by
  norm_num [halfRoot, PMF.uniformOfFintype_apply]

@[simp] theorem halfRoot_false_toReal (who : Bool) :
    (halfRoot who false).toReal = 1 / 2 := by
  norm_num [halfRoot, PMF.uniformOfFintype_apply]

@[simp] theorem sureRoot_true_toReal (who : Bool) :
    (sureRoot who true).toReal = 1 := by
  simp [sureRoot]

@[simp] theorem sureRoot_false_toReal (who : Bool) :
    (sureRoot who false).toReal = 0 := by
  simp [sureRoot]

/-- At the half root, pure Quit pays `-2`: the opponent's singleton and
joint-quit outcomes have equal weight. -/
@[simp] theorem halfRoot_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward secondValue halfRoot who = -2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [halfRoot, secondValue, quittingRootPayoff,
      reward, expect_uniform_bool] <;>
    norm_num

/-- At the half root, pure Continue also pays `-2`: the opponent's singleton
outcome and the all-continue successor have equal weight. -/
@[simp] theorem halfRoot_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward secondValue halfRoot who = -2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [halfRoot, secondValue, quittingRootPayoff,
      reward, expect_uniform_bool] <;>
    norm_num

/-- The half root has current value exactly `(-2,-2)`. -/
@[simp] theorem halfRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward secondValue halfRoot who =
      firstValue who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [firstValue]
  norm_num

/-- The half root is an exact Nash root. -/
theorem halfRoot_isExactNash :
    IsεQuittingRootNash reward secondValue 0 halfRoot := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  simp [quittingRootEndpointDifference]

/-- Against the surely quitting opponent, pure Quit pays the joint-quit
reward `-1`. -/
@[simp] theorem sureRoot_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward terminalValue sureRoot who = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [sureRoot, terminalValue, quittingRootPayoff,
      reward]

/-- Against the surely quitting opponent, pure Continue pays the opponent's
singleton reward `-3`. -/
@[simp] theorem sureRoot_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward terminalValue sureRoot who = -3 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [sureRoot, terminalValue, quittingRootPayoff,
      reward]

/-- The sure root has current value exactly `(-1,-1)`. -/
@[simp] theorem sureRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward terminalValue sureRoot who =
      secondValue who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [secondValue]

/-- The sure root is an exact Nash root: the prescribed pure-Quit action
strictly dominates pure Continue. -/
theorem sureRoot_isExactNash :
    IsεQuittingRootNash reward terminalValue 0 sureRoot := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  simp [quittingRootEndpointDifference]

/-- Every owner-deleted singleton atom at the half root pays the other player
`-3`, while that player's current marked value is at most `-1`. -/
theorem ownerDeletedSingleton_isBad
    (owner next : Bool) (hne : next ≠ owner) :
    next ≠ owner ∧
      reward (quittingSingletonTerminal next) next = -3 ∧
        firstValue next ≤ -1 := by
  exact ⟨hne, by simp [reward, quittingSingletonTerminal], by simp [firstValue]⟩

/-- Both directed mark changes exist at the same half-root edge. -/
theorem alternating_sameNode_marks :
    (false ≠ true) ∧ (true ≠ false) := by simp

/-- The selected half-root Bellman edge is not a self-loop.  Therefore
repeating this edge after cycling only the mark cannot produce equal current
and successor Dirac marginals. -/
theorem selectedEdge_source_ne_successor : firstValue ≠ secondValue := by
  intro h
  have := congrFun h false
  norm_num [firstValue, secondValue] at this

/-- The source and successor Dirac laws of the repeatedly selected edge are
different. -/
theorem selectedEdge_diracMarginals_ne :
    PMF.pure firstValue ≠ PMF.pure secondValue := by
  intro h
  have hmass :
      (PMF.pure firstValue : PMF (Payoff Bool)) firstValue =
        (PMF.pure secondValue : PMF (Payoff Bool)) firstValue := by
    rw [h]
  rw [PMF.pure_apply_self,
    PMF.pure_apply_of_ne secondValue firstValue
      selectedEdge_source_ne_successor] at hmass
  exact one_ne_zero hmass

/-! ## Arbitrarily long chains with a bounded-depth marked packet -/

/-- Pure Quit at an all-Continue prefix receives the singleton reward. -/
@[simp] theorem allContinue_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward firstValue quittingAllContinueRoot who =
      -3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [quittingAllContinueRoot, firstValue, quittingRootPayoff, reward]

/-- Pure Continue at an all-Continue prefix preserves the fixed value. -/
@[simp] theorem allContinue_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward firstValue quittingAllContinueRoot who =
      -2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_bool]
  cases who <;>
    simp [quittingAllContinueRoot, firstValue, quittingRootPayoff, reward]

/-- An all-Continue root fixes `firstValue`.  These roots provide arbitrary
exact prefixes without changing the terminal marked packet. -/
@[simp] theorem allContinue_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward firstValue quittingAllContinueRoot who =
      firstValue who := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [quittingAllContinueRoot, firstValue]

/-- At the prefix root, Quit gives `-3` while Continue preserves `-2`, so
all-Continue is an exact Nash root. -/
theorem allContinue_isExactNash :
    IsεQuittingRootNash reward firstValue 0 quittingAllContinueRoot := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  have hdiff : quittingRootEndpointDifference reward firstValue
      quittingAllContinueRoot who = -1 := by
    cases who <;>
      norm_num [quittingRootEndpointDifference, quittingSingletonTerminal,
        reward, firstValue]
  simp [quittingAllContinueRoot, hdiff]

/-- Cutoff of the chain with `bulk` fixed all-Continue prefixes, followed by
the half root and the surely quitting root. -/
def liftedCutoff (bulk : ℕ) : ℕ := bulk + 2

/-- Root sequence of the arbitrarily long exact lift. -/
def liftedRoots (bulk time : ℕ) : Bool → PMF Bool :=
  if time < bulk then quittingAllContinueRoot
  else if time = bulk then halfRoot else sureRoot

/-- Value sequence of the arbitrarily long exact lift. -/
def liftedValue (bulk time : ℕ) : Payoff Bool :=
  if time ≤ bulk then firstValue
  else if time = bulk + 1 then secondValue else terminalValue

@[simp] theorem liftedValue_at_cutoff (bulk : ℕ) :
    liftedValue bulk (liftedCutoff bulk) = 0 := by
  funext who
  simp [liftedValue, liftedCutoff, terminalValue]

/-- Every edge in the lifted chain satisfies its exact Bellman equation. -/
theorem liftedValue_eq_successor (bulk time : ℕ)
    (htime : time < liftedCutoff bulk) :
    liftedValue bulk time =
      quittingRootSuccessorPayoff reward (liftedValue bulk (time + 1))
        (liftedRoots bulk time) := by
  by_cases hbulk : time < bulk
  · have hnext : time + 1 ≤ bulk := by omega
    funext who
    simp [liftedValue, liftedRoots, hbulk, hbulk.le, hnext]
  · have hge : bulk ≤ time := Nat.le_of_not_gt hbulk
    have hcases : time = bulk ∨ time = bulk + 1 := by
      unfold liftedCutoff at htime
      omega
    rcases hcases with rfl | rfl
    · funext who
      simp [liftedValue, liftedRoots]
    · funext who
      simp [liftedValue, liftedRoots]

/-- Every root in the lifted chain is an exact Nash root. -/
theorem liftedRoots_isExactNash (bulk time : ℕ)
    (htime : time < liftedCutoff bulk) :
    IsεQuittingRootNash reward (liftedValue bulk (time + 1)) 0
      (liftedRoots bulk time) := by
  by_cases hbulk : time < bulk
  · have hnext : time + 1 ≤ bulk := by omega
    simpa [liftedValue, liftedRoots, hbulk, hnext] using
      allContinue_isExactNash
  · have hge : bulk ≤ time := Nat.le_of_not_gt hbulk
    have hcases : time = bulk ∨ time = bulk + 1 := by
      unfold liftedCutoff at htime
      omega
    rcases hcases with rfl | rfl
    · simpa [liftedValue, liftedRoots] using halfRoot_isExactNash
    · simpa [liftedValue, liftedRoots, terminalValue] using
        sureRoot_isExactNash

/-- The lifted chain packages the exact zero-boundary interface consumed by
the marked-fence iteration. -/
theorem liftedChain_exact (bulk : ℕ) :
    liftedValue bulk (liftedCutoff bulk) = 0 ∧
      (∀ time, time < liftedCutoff bulk →
        liftedValue bulk time =
          quittingRootSuccessorPayoff reward (liftedValue bulk (time + 1))
            (liftedRoots bulk time)) ∧
      ∀ time, time < liftedCutoff bulk →
        IsεQuittingRootNash reward (liftedValue bulk (time + 1)) 0
          (liftedRoots bulk time) := by
  exact ⟨liftedValue_at_cutoff bulk, liftedValue_eq_successor bulk,
    liftedRoots_isExactNash bulk⟩

/-- A negative player flag at the half root of the lifted chain. -/
def liftedFlag (bulk : ℕ) (owner : Bool) :
    QuittingNegativeFlagState (liftedValue bulk) (liftedCutoff bulk) 1 where
  owner := owner
  time := bulk
  time_le_cutoff := by simp [liftedCutoff]
  negative := by simp [liftedValue, firstValue]

/-- The owner-deleted singleton action used by a same-date transfer. -/
def singletonAction (who : Bool) : Bool → Bool :=
  fun player ↦ if player = who then true else false

@[simp] theorem singletonAction_self (who : Bool) :
    singletonAction who who = true := by simp [singletonAction]

@[simp] theorem singletonAction_other {owner who : Bool} (hne : owner ≠ who) :
    singletonAction who owner = false := by simp [singletonAction, hne]

/-- `singletonAction` has exactly its named quitter. -/
@[simp] theorem quittingQuitters_singletonAction (who : Bool) :
    quittingQuitters (singletonAction who) = {who} := by
  ext player
  cases who <;> cases player <;> simp [quittingQuitters, singletonAction]

/-- Every singleton terminal reward in this symmetric regression is `-3`. -/
@[simp] theorem reward_singleton (quitter who : Bool) :
    reward (quittingSingletonTerminal quitter) who = -3 := by
  simp [reward, quittingSingletonTerminal]

/-- The root payoff displayed by a singleton action is independent of the
unused all-Continue tail. -/
@[simp] theorem rootPayoff_singletonAction
    (tail : Payoff Bool) (quitter who : Bool) :
    quittingRootPayoff reward tail (singletonAction quitter) who = -3 := by
  simp only [quittingRootPayoff, quittingQuitters_singletonAction,
    Finset.singleton_nonempty, dite_true]
  change reward (quittingSingletonTerminal quitter) who = -3
  exact reward_singleton quitter who

/-- Changing to the other player at the half root is a genuine supported
marked-fence transfer at the same actual suffix date. -/
theorem liftedFlag_isActualTransfer (bulk : ℕ) (owner target : Bool)
    (hne : owner ≠ target) :
    (liftedFlag bulk owner).IsActualTransfer reward (liftedRoots bulk)
      (liftedValue bulk) (liftedCutoff bulk) 1 (liftedFlag bulk target) := by
  let offset : Fin (liftedCutoff bulk - bulk) := ⟨0, by
    simp [liftedCutoff]⟩
  let mark : QuittingFirstOpponentMark Bool
      (liftedCutoff bulk - (liftedFlag bulk owner).time) :=
    ⟨offset, singletonAction target⟩
  refine ⟨mark, ?_, ?_, ?_, ?_⟩
  · simp [mark, offset, liftedFlag]
  · cases owner <;> cases target <;> simp_all [mark, offset,
      quittingFirstOpponentRawWeight, quittingOpponentSurvivalWeight,
      quittingOpponentQuitFlag, quittingSomeOpponentQuits, singletonAction,
      liftedFlag, liftedRoots, halfRoot, pmfPi_apply]
  · refine ⟨?_, ?_, ?_⟩
    · change 2 * quittingRootPayoff reward (0 : Payoff Bool)
          (singletonAction target) owner ≤ -1
      simp
      norm_num
    · change target ∈ (quittingQuitters (singletonAction target)).erase owner
      simp [hne.symm]
    · change liftedValue bulk (bulk + (offset : ℕ)) target ≤ -1
      simp [offset, liftedValue, firstValue]
  · simp [liftedFlag, liftedRoots]

/-- The two actual marked transfers alternate forever without advancing the
fixed chain's calendar. -/
theorem liftedFlag_sameTime_twoCycle (bulk : ℕ) :
    (liftedFlag bulk false).IsActualTransfer reward (liftedRoots bulk)
        (liftedValue bulk) (liftedCutoff bulk) 1 (liftedFlag bulk true) ∧
      (liftedFlag bulk true).IsActualTransfer reward (liftedRoots bulk)
        (liftedValue bulk) (liftedCutoff bulk) 1 (liftedFlag bulk false) := by
  exact ⟨liftedFlag_isActualTransfer bulk false true (by decide),
    liftedFlag_isActualTransfer bulk true false (by decide)⟩

/-- Although the cutoffs diverge with the prefix length, every selected
marked packet in this family has the same finite residual depth `2`. -/
theorem liftedFlag_residualDepth_eq_two (bulk : ℕ) :
    liftedCutoff bulk - (liftedFlag bulk false).time = 2 ∧
      liftedCutoff bulk - (liftedFlag bulk true).time = 2 := by
  simp [liftedCutoff, liftedFlag]

/-- The family has unbounded entry cutoffs. -/
theorem liftedCutoff_tendsto_atTop :
    Filter.Tendsto liftedCutoff Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro lower
  exact ⟨lower, fun bulk hbulk ↦ by simp [liftedCutoff]; omega⟩

/-- Entry depth does not imply residual-horizon escape: the selected packet
depth is constantly `2`. -/
theorem liftedFlag_residualDepth_not_tendsto_atTop :
    ¬ Filter.Tendsto
        (fun bulk ↦ liftedCutoff bulk - (liftedFlag bulk false).time)
        Filter.atTop Filter.atTop := by
  simp [liftedCutoff, liftedFlag, Filter.not_tendsto_const_atTop]

end QuittingMarkedSameNodeCycleRegression

end GameTheory
