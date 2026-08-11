/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalFundingFarkasDecoder

/-!
# Collision signs forced by a zero-target funding lift

The sparse one-owner terminal-funding root fails at every owner with positive
singleton debt.  Enlarging the support is not merely a formal response to
that Farkas certificate.  Any interior-support root which really mixes such
an owner at zero Bellman target must place positive conditional mass on a
simultaneous-quitting action at which that owner's terminal reward is
strictly negative.

Indeed exact mixing makes the owner's pure-Quit endpoint equal the zero
Bellman target.  The solo-Quit action has positive conditional probability
and strictly positive payoff.  Therefore another positive-probability action
in the same conditional product row must carry a negative payoff.  This is a
finite game-facing necessary condition on every support enlargement capable
of replacing the failed one-owner funding ray.

The theorem does not construct the enlarged root or turn the negative
collision into a punishment cycle.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [Fintype ι] [DecidableEq ι] in
/-- Every marginal of an interior-support root assigns positive probability
to Continue.  Off the declared support it assigns Continue probability one. -/
theorem rootContinueProbability_pos_of_interiorOnSupport
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (who : ι) :
    0 < (root who false).toReal := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  by_cases hwho : who ∈ support
  · have hlt := (hsupport.1 who hwho).2
    change (root who true).toReal < 1 at hlt
    linarith
  · have hzero := hsupport.2 who hwho
    change (root who true).toReal = 0 at hzero
    linarith

/-- The solo-Quit action has positive probability after an interior-support
root is conditioned on the displayed owner quitting. -/
theorem forcedQuit_singletonAction_ne_zero_of_interiorOnSupport
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (owner : ι) :
    pmfPi (Function.update root owner (PMF.pure true))
        (quittingSetAction {owner}) ≠ 0 := by
  rw [pmfPi_apply]
  apply Finset.prod_ne_zero_iff.mpr
  intro who _
  by_cases hwho : who = owner
  · subst who
    simp [quittingSetAction]
  · rw [Function.update_of_ne hwho]
    have haction : quittingSetAction {owner} who = false := by
      simp [quittingSetAction, hwho]
    rw [haction]
    have hpos := rootContinueProbability_pos_of_interiorOnSupport
      root support hsupport who
    intro hzero
    rw [hzero] at hpos
    simp at hpos

/-- At zero Bellman target, every declared active owner has pure-Quit
endpoint zero. -/
theorem quittingRootQuitPayoff_eq_zero_of_zeroTargetLift
    (floor : Payoff ι) (upper : ℝ)
    (root : ι → PMF Bool) (support : Finset ι)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0 floor upper
      root support continuation)
    (owner : ι) (howner : owner ∈ support) :
    quittingRootQuitPayoff reward continuation root owner = 0 := by
  have hderivative := hlift.2.1 owner howner
  rw [← quittingRootEndpointDifference_eq_mobiusCoordinateDerivative]
    at hderivative
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward continuation root owner
  have htarget := congrFun hlift.1 owner
  have hsum := quittingRoot_continueProbability_add_quitProbability root owner
  unfold quittingRootEndpointDifference at hderivative
  simp only [Pi.zero_apply] at htarget
  have hendpoints : quittingRootQuitPayoff reward continuation root owner =
      quittingRootContinuePayoff reward continuation root owner :=
    sub_eq_zero.mp hderivative
  calc
    quittingRootQuitPayoff reward continuation root owner =
        ((root owner false).toReal + (root owner true).toReal) *
          quittingRootQuitPayoff reward continuation root owner := by
      rw [hsum, one_mul]
    _ = quittingRootSuccessorPayoff reward continuation root owner := by
      rw [hmix, ← hendpoints]
      ring
    _ = 0 := htarget.symm

/-- **Negative-collision necessity for terminal funding.**  Suppose an
interior-support frozen root gives a physical continuation lift at zero
Bellman target.  If an active owner has positive singleton payoff, then,
conditional on that owner quitting, some positive-probability action also
contains an opponent quitter and pays the owner strictly negatively. -/
theorem exists_negativeCollision_of_positiveSingleton_zeroTargetLift
    (floor : Payoff ι) (upper : ℝ)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0 floor upper
      root support continuation)
    (owner : ι) (howner : owner ∈ support)
    (hpositive : 0 < reward (quittingSingletonTerminal owner) owner) :
    ∃ action : ι → Bool,
      pmfPi (Function.update root owner (PMF.pure true)) action ≠ 0 ∧
      action owner = true ∧
      quittingSomeOpponentQuits owner action ∧
      quittingSetReward reward (quittingQuitters action) owner < 0 := by
  let distribution := pmfPi (Function.update root owner (PMF.pure true))
  let supportedPayoff : (ι → Bool) → ℝ := fun action =>
    if distribution action = 0 then 0 else
      quittingSetReward reward (quittingQuitters action) owner
  by_contra hno
  push Not at hno
  have hnonneg : ∀ action, 0 ≤ supportedPayoff action := by
    intro action
    by_cases hmass : distribution action = 0
    · simp [supportedPayoff, hmass]
    · have hsupportAction : action ∈ distribution.support := by
        simpa [PMF.mem_support_iff] using hmass
      have hself : action owner = true :=
        action_eq_true_of_mem_support_pmfPi_update_pure_true
          root owner action hsupportAction
      have hquitters : (quittingQuitters action).Nonempty :=
        (quittingQuitters_nonempty_iff action).2 ⟨owner, hself⟩
      by_cases hopponent : quittingSomeOpponentQuits owner action
      · have hreward := hno action hmass hself hopponent
        simp only [supportedPayoff, hmass, if_false]
        exact hreward
      · have hsingleton : quittingQuitters action = {owner} :=
          quittingQuitters_eq_singleton_of_noOpponent_of_self
            owner action hopponent hself
        simp only [supportedPayoff, hmass, if_false, hsingleton]
        rw [quittingSetReward_of_nonempty reward
          (Finset.singleton_nonempty owner)]
        simpa [quittingSingletonTerminal] using hpositive.le
  let singletonAction := quittingSetAction ({owner} : Finset ι)
  have hsingletonMass : distribution singletonAction ≠ 0 := by
    exact forcedQuit_singletonAction_ne_zero_of_interiorOnSupport
      root support hsupport owner
  have hsingletonPayoff : 0 < supportedPayoff singletonAction := by
    have hquitters : quittingQuitters singletonAction = {owner} := by
      exact quittingQuitters_setAction {owner}
    simp only [supportedPayoff, hsingletonMass, if_false, hquitters]
    rw [quittingSetReward_of_nonempty reward
      (Finset.singleton_nonempty owner)]
    simpa [quittingSingletonTerminal] using hpositive
  have hexpectPos : 0 < expect distribution supportedPayoff := by
    have hlt := expect_lt_of_le_of_exists_lt distribution
      (fun _ => (0 : ℝ)) supportedPayoff hnonneg
      ⟨singletonAction, hsingletonMass, hsingletonPayoff⟩
    simpa using hlt
  have hexpectEq : expect distribution supportedPayoff =
      quittingRootQuitPayoff reward continuation root owner := by
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    apply expect_congr_on_support
    intro action haction
    have hmass : distribution action ≠ 0 := by
      simpa [PMF.mem_support_iff] using haction
    simp only [supportedPayoff, hmass, if_false]
    have hself := action_eq_true_of_mem_support_pmfPi_update_pure_true
      root owner action haction
    have hquitters : (quittingQuitters action).Nonempty :=
      (quittingQuitters_nonempty_iff action).2 ⟨owner, hself⟩
    rw [quittingSetReward_of_nonempty reward hquitters]
    simp [quittingRootPayoff, hquitters]
  rw [hexpectEq,
    quittingRootQuitPayoff_eq_zero_of_zeroTargetLift
      (reward := reward) floor upper root support continuation hlift owner howner]
      at hexpectPos
  exact lt_irrefl 0 hexpectPos

end GameTheory
