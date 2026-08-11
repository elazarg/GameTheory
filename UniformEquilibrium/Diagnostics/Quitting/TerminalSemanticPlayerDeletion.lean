/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCoalitionToggleDeletion
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomicBlockerCompletion
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge
import UniformEquilibrium.Quitting.Cycles.ConditionedProperFaceDeficientClock
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Exact deletion of a universal Never player

Fix a player `owner` and restrict the quitting table to the subtype of the
other players.  This file supplies the naturality which is absent from the
equivalence-only player-reindexing API: a root sequence of the reduced game
lifts to the original game by making `owner` Continue surely.

The construction is kept at the live-root level.  This loses no behavioral
generality in a quitting game: terminal payoffs and arbitrary unilateral
behavioral deviations depend only on the unique all-Continue public history.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The subtype of players remaining after deleting `owner`. -/
abbrev QuittingDeletedPlayer (owner : ι) := {who : ι // who ≠ owner}

/-- Embed a nonempty coalition of undeleted players in the original player
type. -/
def quittingExtendDeletedCoalition (owner : ι)
    (terminal : {S : Finset (QuittingDeletedPlayer owner) // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  ⟨terminal.1.map
      (Function.Embedding.subtype (p := fun who : ι => who ≠ owner)),
    Finset.map_nonempty.mpr terminal.2⟩

/-- Restriction of a quitting reward table to the players other than
`owner`. -/
def quittingDeletePlayerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    {S : Finset (QuittingDeletedPlayer owner) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer owner) :=
  fun terminal who => reward (quittingExtendDeletedCoalition owner terminal) who.1

/-- Extend an action of the reduced game by making `owner` Continue. -/
def quittingExtendDeletedAction (owner : ι)
    (action : QuittingDeletedPlayer owner → Bool) : ι → Bool :=
  fun who => if h : who = owner then false else action ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedAction_owner (owner : ι)
    (action : QuittingDeletedPlayer owner → Bool) :
    quittingExtendDeletedAction owner action owner = false := by
  simp [quittingExtendDeletedAction]

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedAction_apply (owner : ι)
    (action : QuittingDeletedPlayer owner → Bool)
    (who : QuittingDeletedPlayer owner) :
    quittingExtendDeletedAction owner action who.1 = action who := by
  simp [quittingExtendDeletedAction, who.2]

omit [Fintype ι] in
theorem quittingExtendDeletedAction_injective (owner : ι) :
    Function.Injective (quittingExtendDeletedAction owner) := by
  intro first second heq
  funext who
  have h := congrFun heq who.1
  simpa using h

/-- Extend a reduced product root by making `owner` Continue surely. -/
def quittingExtendDeletedRoot (owner : ι)
    (root : QuittingDeletedPlayer owner → PMF Bool) : ι → PMF Bool :=
  fun who => if h : who = owner then PMF.pure false else root ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedRoot_owner (owner : ι)
    (root : QuittingDeletedPlayer owner → PMF Bool) :
    quittingExtendDeletedRoot owner root owner = PMF.pure false := by
  simp [quittingExtendDeletedRoot]

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedRoot_apply (owner : ι)
    (root : QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) :
    quittingExtendDeletedRoot owner root who.1 = root who := by
  simp [quittingExtendDeletedRoot, who.2]

/-- The full product law with a sure-Continue deleted coordinate is the push
forward of the reduced product law under action extension. -/
theorem pmfPi_quittingExtendDeletedRoot
    (owner : ι) (root : QuittingDeletedPlayer owner → PMF Bool) :
    pmfPi (quittingExtendDeletedRoot owner root) =
      PMF.map (quittingExtendDeletedAction owner) (pmfPi root) := by
  classical
  ext action
  rw [pmfPi_apply, PMF.map_apply, tsum_fintype]
  by_cases howner : action owner = false
  · let reduced : QuittingDeletedPlayer owner → Bool := fun who => action who.1
    have hext : quittingExtendDeletedAction owner reduced = action := by
      funext who
      by_cases h : who = owner
      · subst who
        simp [howner]
      · simp [quittingExtendDeletedAction, reduced, h]
    have hprod :
        (∏ who : ι, quittingExtendDeletedRoot owner root who (action who)) =
          ∏ who : QuittingDeletedPlayer owner, root who (reduced who) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne
        (fun who => quittingExtendDeletedRoot owner root who (action who)) owner]
      simp [howner, reduced]
    rw [hprod]
    change (pmfPi root) reduced = _
    symm
    have hsum :
        (∑ b ∈ Finset.univ,
          if action = quittingExtendDeletedAction owner b then
            (pmfPi root) b else 0) =
          (if action = quittingExtendDeletedAction owner reduced then
            (pmfPi root) reduced else 0) := by
      apply Finset.sum_eq_single reduced
      · intro other _ hne
        have hneq : action ≠ quittingExtendDeletedAction owner other := by
          intro heq
          apply hne
          apply quittingExtendDeletedAction_injective owner
          exact heq.symm.trans hext.symm
        simp [hneq]
      · simp
    rw [if_pos hext.symm] at hsum
    convert hsum using 1
    congr 1
    funext other
    by_cases h : action = quittingExtendDeletedAction owner other <;> simp [h]
  · have htrue : action owner = true := by
      cases h : action owner <;> simp_all
    have hprod :
        (∏ who : ι, quittingExtendDeletedRoot owner root who (action who)) = 0 := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne
        (fun who => quittingExtendDeletedRoot owner root who (action who)) owner]
      simp [htrue]
    rw [hprod]
    symm
    have hsum :
        (∑ reduced ∈ Finset.univ,
          if action = quittingExtendDeletedAction owner reduced then
            (pmfPi root) reduced else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro reduced _
      simp [show action ≠ quittingExtendDeletedAction owner reduced by
        intro heq
        have := congrFun heq owner
        simp [htrue] at this]
    convert hsum using 1
    congr 1
    funext reduced
    by_cases h : action = quittingExtendDeletedAction owner reduced <;> simp [h]

/-- Extend a reduced payoff vector by an irrelevant zero coordinate at the
deleted player. -/
def quittingExtendDeletedPayoff (owner : ι)
    (payoff : Payoff (QuittingDeletedPlayer owner)) : Payoff ι :=
  fun who => if h : who = owner then 0 else payoff ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedPayoff_apply (owner : ι)
    (payoff : Payoff (QuittingDeletedPlayer owner))
    (who : QuittingDeletedPlayer owner) :
    quittingExtendDeletedPayoff owner payoff who.1 = payoff who := by
  simp [quittingExtendDeletedPayoff, who.2]

/-- Extending a reduced action maps its quitter set to the corresponding
coalition in the original player type. -/
theorem quittingQuitters_extendDeletedAction (owner : ι)
    (action : QuittingDeletedPlayer owner → Bool) :
    quittingQuitters (quittingExtendDeletedAction owner action) =
      (quittingQuitters action).map
        (Function.Embedding.subtype (p := fun who : ι => who ≠ owner)) := by
  classical
  ext who
  by_cases h : who = owner
  · subst who
    simp [quittingQuitters]
  · simp [quittingQuitters, quittingExtendDeletedAction, h]

/-- One-stage root payoffs commute with deletion for every surviving
coordinate. -/
theorem quittingRootPayoff_extendDeletedAction_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (fullContinuation : Payoff ι)
    (continuation : Payoff (QuittingDeletedPlayer owner))
    (action : QuittingDeletedPlayer owner → Bool)
    (who : QuittingDeletedPlayer owner)
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootPayoff reward fullContinuation
        (quittingExtendDeletedAction owner action) who.1 =
      quittingRootPayoff (quittingDeletePlayerReward reward owner)
        continuation action who := by
  classical
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hextQuit :
        (quittingQuitters (quittingExtendDeletedAction owner action)).Nonempty := by
      rw [quittingQuitters_extendDeletedAction]
      exact Finset.map_nonempty.mpr hquit
    rw [quittingRootPayoff, dif_pos hextQuit,
      quittingRootPayoff, dif_pos hquit]
    unfold quittingDeletePlayerReward quittingExtendDeletedCoalition
    congr 2
    exact quittingQuitters_extendDeletedAction owner action
  · have hextQuit :
        ¬(quittingQuitters (quittingExtendDeletedAction owner action)).Nonempty := by
      rw [quittingQuitters_extendDeletedAction]
      exact fun h => hquit (Finset.map_nonempty.mp h)
    rw [quittingRootPayoff, dif_neg hextQuit,
      quittingRootPayoff, dif_neg hquit]
    exact hcontinuation

/-- The extension form of one-stage payoff naturality. -/
theorem quittingRootPayoff_extendDeletedAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (continuation : Payoff (QuittingDeletedPlayer owner))
    (action : QuittingDeletedPlayer owner → Bool)
    (who : QuittingDeletedPlayer owner) :
    quittingRootPayoff reward (quittingExtendDeletedPayoff owner continuation)
        (quittingExtendDeletedAction owner action) who.1 =
      quittingRootPayoff (quittingDeletePlayerReward reward owner)
        continuation action who :=
  quittingRootPayoff_extendDeletedAction_of_apply_eq
    reward owner (quittingExtendDeletedPayoff owner continuation)
      continuation action who
      (quittingExtendDeletedPayoff_apply owner continuation who)

/-- Expected one-stage payoffs commute with deletion for every surviving
coordinate. -/
theorem quittingRootExpectedPayoff_extendDeletedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (continuation : Payoff (QuittingDeletedPlayer owner))
    (root : QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) :
    quittingRootExpectedPayoff reward
        (quittingExtendDeletedPayoff owner continuation)
        (quittingExtendDeletedRoot owner root) who.1 =
      quittingRootExpectedPayoff (quittingDeletePlayerReward reward owner)
        continuation root who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_quittingExtendDeletedRoot, expect_map]
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_extendDeletedAction
    reward owner continuation action who

/-- Root-payoff naturality only needs agreement of the two continuation
vectors at the displayed surviving player. -/
theorem quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (fullContinuation : Payoff ι)
    (continuation : Payoff (QuittingDeletedPlayer owner))
    (root : QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner)
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootExpectedPayoff reward fullContinuation
        (quittingExtendDeletedRoot owner root) who.1 =
      quittingRootExpectedPayoff (quittingDeletePlayerReward reward owner)
        continuation root who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_quittingExtendDeletedRoot, expect_map]
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_extendDeletedAction_of_apply_eq
    reward owner fullContinuation continuation action who hcontinuation

omit [Fintype ι] in
/-- Extending roots commutes with updating a surviving coordinate. -/
theorem Function.update_quittingExtendDeletedRoot
    (owner : ι) (root : QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) (hazard : PMF Bool) :
    Function.update (quittingExtendDeletedRoot owner root) who.1 hazard =
      quittingExtendDeletedRoot owner (Function.update root who hazard) := by
  funext player
  by_cases hp : player = who.1
  · subst player
    rw [Function.update_self]
    simp
  · by_cases ho : player = owner
    · subst player
      rw [Function.update_of_ne hp]
      simp
    · rw [Function.update_of_ne hp]
      unfold quittingExtendDeletedRoot
      rw [dif_neg ho]
      have hsub : (⟨player, ho⟩ : QuittingDeletedPlayer owner) ≠ who := by
        intro heq
        apply hp
        exact congrArg Subtype.val heq
      rw [dif_neg ho]
      simp [Function.update_of_ne hsub]

/-- Extend every row of a reduced root chronology by making `owner`
Continue. -/
def quittingExtendDeletedRoots (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool) :
    ℕ → ι → PMF Bool :=
  fun time => quittingExtendDeletedRoot owner (roots time)

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedRoots_owner (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool) (time : ℕ) :
    quittingExtendDeletedRoots owner roots time owner = PMF.pure false := by
  simp [quittingExtendDeletedRoots]

omit [Fintype ι] in
@[simp] theorem quittingExtendDeletedRoots_apply (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool) (time : ℕ)
    (who : QuittingDeletedPlayer owner) :
    quittingExtendDeletedRoots owner roots time who.1 = roots time who := by
  simp [quittingExtendDeletedRoots]

/-- Every finite zero-boundary unilateral payoff is preserved under the
Never lift, for arbitrary hazards of a surviving player. -/
theorem quittingFiniteRootPayoff_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteRootPayoff reward (quittingExtendDeletedRoots owner roots)
          who.1 hazard start fuel =
        quittingFiniteRootPayoff (quittingDeletePlayerReward reward owner)
          roots who hazard start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff, quittingFiniteRootPayoff,
        show quittingExtendDeletedRoots owner roots start =
          quittingExtendDeletedRoot owner (roots start) by rfl,
        Function.update_quittingExtendDeletedRoot]
      exact quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq
        reward owner
          (fun _ => quittingFiniteRootPayoff reward
            (quittingExtendDeletedRoots owner roots) who.1 hazard
              (start + 1) fuel)
          (fun _ => quittingFiniteRootPayoff
            (quittingDeletePlayerReward reward owner) roots who hazard
              (start + 1) fuel)
          (Function.update (roots start) who (hazard start)) who (ih (start + 1))

/-- Infinite terminal values of arbitrary surviving-player hazard deviations
are preserved by the Never lift. -/
theorem quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) (hazard : ℕ → PMF Bool)
    (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingExtendDeletedRoots owner roots) who.1 hazard start =
      quittingRootSequenceHazardTerminalValue
        (quittingDeletePlayerReward reward owner) roots who hazard start := by
  have hfull := tendsto_quittingFiniteRootPayoff_terminal reward
    (quittingExtendDeletedRoots owner roots) who.1 hazard start
  have hreduced := tendsto_quittingFiniteRootPayoff_terminal
    (quittingDeletePlayerReward reward owner) roots who hazard start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel =>
    (quittingFiniteRootPayoff_extendDeletedRoots
      reward owner roots who hazard start fuel).symm

/-- The prescribed terminal value of a reduced chronology is preserved by
the Never lift. -/
theorem quittingRootSequenceTerminalValue_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (roots : ℕ → QuittingDeletedPlayer owner → PMF Bool)
    (who : QuittingDeletedPlayer owner) (start : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingExtendDeletedRoots owner roots) who.1 start =
      quittingRootSequenceTerminalValue
        (quittingDeletePlayerReward reward owner) roots who start := by
  have hfull := tendsto_quittingFiniteRootPayoff_self_terminalValue reward
    (quittingExtendDeletedRoots owner roots) who.1 start
  have hreduced := tendsto_quittingFiniteRootPayoff_self_terminalValue
    (quittingDeletePlayerReward reward owner) roots who start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel => by
    simpa using (quittingFiniteRootPayoff_extendDeletedRoots reward owner roots
      who (fun time => roots time who) start fuel).symm

/-- Lift an arbitrary reduced behavioral profile through its canonical live
root sequence, making the deleted owner Continue surely. -/
def quittingLiftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingInfinitePathProfile reward
    (quittingExtendDeletedRoots owner
      (quittingProfileLiveRoot (quittingDeletePlayerReward reward owner)
        profile))

@[simp] theorem quittingProfileLiveRoot_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingLiftDeletedProfile reward owner profile) =
      quittingExtendDeletedRoots owner
        (quittingProfileLiveRoot (quittingDeletePlayerReward reward owner)
          profile) := by
  unfold quittingLiftDeletedProfile
  exact quittingProfileLiveRoot_infinitePathProfile _ _

/-- Every surviving player's on-path terminal payoff is exactly preserved by
the profile lift. -/
theorem quittingTerminalPayoff_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (who : QuittingDeletedPlayer owner) :
    quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward owner profile) who.1 =
      quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
        profile who := by
  unfold quittingLiftDeletedProfile
  rw [quittingTerminalPayoff_infinitePathProfile,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  exact quittingRootSequenceTerminalValue_extendDeletedRoots reward owner
    (quittingProfileLiveRoot (quittingDeletePlayerReward reward owner) profile)
      who 0

/-- Pure quit-time deviations of surviving players have exactly the same
payoff before and after the lift. -/
theorem quittingTerminalPayoff_update_pureTime_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (who : QuittingDeletedPlayer owner) (quitTime : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update (quittingLiftDeletedProfile reward owner profile)
          who.1 (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 =
      quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy
            (quittingDeletePlayerReward reward owner) who quitTime)) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  unfold quittingLiftDeletedProfile
  rw [quittingProfileLiveRoot_infinitePathProfile]
  exact quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    reward owner
      (quittingProfileLiveRoot (quittingDeletePlayerReward reward owner) profile)
      who (quittingPureTimeHazard quitTime) 0

/-- The full behavioral best-response value of every surviving player is
exactly preserved by the Never lift. -/
theorem quittingBestReplyValue_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (who : QuittingDeletedPlayer owner) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward owner profile) who.1 =
      quittingBestReplyValue (quittingDeletePlayerReward reward owner)
        profile who := by
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward (quittingLiftDeletedProfile reward owner profile) who.1
          deviation hε
    calc
      quittingTerminalPayoff reward
          (Function.update (quittingLiftDeletedProfile reward owner profile)
            who.1 deviation) who.1 ≤
        quittingTerminalPayoff reward
            (Function.update (quittingLiftDeletedProfile reward owner profile)
              who.1
              (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 +
          ε := htime
      _ = quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy
                (quittingDeletePlayerReward reward owner) who quitTime)) who +
          ε := by rw [quittingTerminalPayoff_update_pureTime_liftDeletedProfile]
      _ ≤ quittingBestReplyValue (quittingDeletePlayerReward reward owner)
            profile who + ε := by
        have hle := le_quittingBestReplyValue
          (quittingDeletePlayerReward reward owner) profile who
          (quittingPureTimeBehaviorStrategy
            (quittingDeletePlayerReward reward owner) who quitTime)
        linarith
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        (quittingDeletePlayerReward reward owner) profile who deviation hε
    calc
      quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy
                (quittingDeletePlayerReward reward owner) who quitTime)) who +
          ε := htime
      _ = quittingTerminalPayoff reward
            (Function.update (quittingLiftDeletedProfile reward owner profile)
              who.1
              (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 +
          ε := by rw [quittingTerminalPayoff_update_pureTime_liftDeletedProfile]
      _ ≤ quittingBestReplyValue reward
            (quittingLiftDeletedProfile reward owner profile) who.1 + ε :=
        by
          have hle := le_quittingBestReplyValue reward
            (quittingLiftDeletedProfile reward owner profile) who.1
            (quittingPureTimeBehaviorStrategy reward who.1 quitTime)
          linarith

/-- Read the live-path hazard of an original-game deviation as a behavioral
strategy of the reduced game.  Off the unique live history its history
argument is irrelevant. -/
def quittingDeletePlayerDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (who : QuittingDeletedPlayer owner)
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorStrategy who :=
  fun time _ => quittingBehaviorLiveHazard reward deviation time

/-- An arbitrary behavioral deviation by a surviving player has exactly the
same payoff after deletion.  This is stronger than equality of suprema and
preserves a witnessed exploitability gap without epsilon loss. -/
theorem quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (who : QuittingDeletedPlayer owner)
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    quittingTerminalPayoff reward
        (Function.update (quittingLiftDeletedProfile reward owner profile)
          who.1 deviation) who.1 =
      quittingTerminalPayoff (quittingDeletePlayerReward reward owner)
        (Function.update profile who
          (quittingDeletePlayerDeviation reward owner who deviation)) who := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_liftDeletedProfile]
  unfold quittingDeletePlayerDeviation quittingBehaviorLiveHazard
  exact quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    reward owner
      (quittingProfileLiveRoot (quittingDeletePlayerReward reward owner) profile)
      who (fun time => deviation time (quittingLiveHist reward time)) 0

/-- The lifted profile already has the deleted owner playing literal Never
on every history. -/
theorem Function.update_liftDeletedProfile_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile) :
    Function.update (quittingLiftDeletedProfile reward owner profile) owner
        (quittingPureTimeBehaviorStrategy reward owner none) =
      quittingLiftDeletedProfile reward owner profile := by
  funext player time history
  by_cases hp : player = owner
  · subst player
    simp [quittingPureTimeBehaviorStrategy, quittingLiftDeletedProfile,
      quittingInfinitePathProfile,
      quittingRootSequenceProfile, quittingExtendDeletedRoots]
  · simp [Function.update_of_ne hp]

/-- In the antitone branch, the deleted owner has exactly zero debt on every
lifted reduced profile. -/
theorem quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward owner profile) owner =
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward owner profile) owner := by
  rw [quittingBestReplyValue_eq_never_of_ownerJoinAntitone
    reward (quittingLiftDeletedProfile reward owner profile) owner
      hjoin hsolo hchi]
  rw [Function.update_liftDeletedProfile_never]

/-- **Exact exploitability-floor descent.**  If the owner-side coalition
increments are all nonpositive at the negative singleton gate, deleting the
universal-Never owner preserves a witnessed positive terminal
exploitability gap exactly.  The proof also covers an empty complement: in
that case its conclusion is impossible, so the hypotheses themselves rule
out the original positive floor. -/
theorem hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    HasTerminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) gap := by
  intro profile
  obtain ⟨player, deviation, hdeviation⟩ :=
    hexploit (quittingLiftDeletedProfile reward owner profile)
  by_cases hp : player = owner
  · subst player
    have hbest := quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff
      reward owner profile hjoin hsolo hchi
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward owner profile) owner deviation
    linarith
  · let who : QuittingDeletedPlayer owner := ⟨player, hp⟩
    refine ⟨who, quittingDeletePlayerDeviation reward owner who deviation, ?_⟩
    have hon := quittingTerminalPayoff_liftDeletedProfile
      reward owner profile who
    have hdev :=
      quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
        reward owner profile who deviation
    dsimp only [who] at hon hdev
    linarith

/-- A positive gap in the deletion branch forces the complement of the owner
to be inhabited.  Thus the one-player edge case is discharged before any
cardinality induction is invoked. -/
theorem nonempty_deletedPlayer_of_ownerJoinAntitone_and_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    Nonempty (QuittingDeletedPlayer owner) := by
  have hdeleted :=
    hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
      reward owner hgap hexploit hjoin hsolo hchi
  obtain ⟨who, _deviation, _⟩ :=
    hdeleted (quittingAlwaysContinueProfile
      (quittingDeletePlayerReward reward owner))
  exact ⟨who⟩

/-- The deleted subtype has strictly smaller cardinality. -/
theorem card_quittingDeletedPlayer_lt (owner : ι) :
    Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι := by
  exact Fintype.card_subtype_lt (p := fun who : ι => who ≠ owner)
    (x := owner) (by simp)

/-- **Toggle-or-cardinality-descent dispatcher.**  At the negative singleton
gate with a positive terminal exploitability floor, either a strict
owner-side coalition toggle exists, or the exact same floor descends to the
nonempty, strictly smaller player subtype. -/
theorem exists_strict_owner_toggle_or_exact_playerDeletion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) gap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  rcases exists_strict_owner_toggle_or_ownerJoinAntitone reward owner with
    htoggle | hjoin
  · exact Or.inl htoggle
  · exact Or.inr
      ⟨nonempty_deletedPlayer_of_ownerJoinAntitone_and_gap
          reward owner hgap hexploit hjoin hsolo hchi,
        hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
          reward owner hgap hexploit hjoin hsolo hchi,
        card_quittingDeletedPlayer_lt owner⟩

/-! ## The strict-toggle branch enters the atomic blocker geometry -/

/-- At the pure row in which `owner` joins a nonempty opponent coalition,
the atomic blocker balance is exactly the corresponding insertion gain. -/
theorem quittingAtomicBlockerBalance_pure_ownerToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (howner : owner ∉ quitters) :
    quittingAtomicBlockerBalance reward
        (QuittingSureSetOwnerRepair.quittingPureSetRoot
          (insert owner quitters)) owner =
      reward
          ⟨insert owner quitters,
            Finset.insert_nonempty owner quitters⟩ owner -
        reward ⟨quitters, hquitters⟩ owner := by
  have herase : (insert owner quitters).erase owner = quitters := by
    simp [howner]
  have heraseNonempty : ((insert owner quitters).erase owner).Nonempty := by
    simpa [herase] using hquitters
  unfold quittingAtomicBlockerBalance quittingForcedOwnerObeyValue
    quittingForcedOwnerRefusalCap
    quittingForcedOwnerAllOutsidersContinueMass
  rw [QuittingSureSetOwnerRepair.quittingRootAbsorbingContribution_pureSetRoot,
    quittingStationaryFixedOpponentsContinueReward_pureSetRoot,
    quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_nonempty
      heraseNonempty]
  simp [QuittingSureSetOwnerRepair.quittingSetReward, herase, hquitters]

/-- A strict owner-side insertion toggle cannot itself be a stable atomic
row in a game with a positive terminal exploitability floor.  Some outsider
has a strict one-stage deviation at the pure joined-coalition row.  This is
the exact handoff from deletion failure to the atomic blocker branch. -/
theorem exists_outsider_atomicDeviation_of_strict_ownerToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (owner : ι) (quitters : Finset ι) (hquitters : quitters.Nonempty)
    (howner : owner ∉ quitters)
    (htoggle : reward ⟨quitters, hquitters⟩ owner <
      reward
        ⟨insert owner quitters,
          Finset.insert_nonempty owner quitters⟩ owner) :
    ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0
          (Function.update
            (QuittingSureSetOwnerRepair.quittingPureSetRoot
              (insert owner quitters)) who deviation) who >
        quittingRootExpectedPayoff reward 0
          (QuittingSureSetOwnerRepair.quittingPureSetRoot
            (insert owner quitters)) who := by
  let root := QuittingSureSetOwnerRepair.quittingPureSetRoot
    (insert owner quitters)
  have hrootOwner : root owner = PMF.pure true := by
    simp [root, QuittingSureSetOwnerRepair.quittingPureSetRoot,
      QuittingSureSetOwnerRepair.quittingSetAction]
  have hbalance : 0 < quittingAtomicBlockerBalance reward root owner := by
    rw [show quittingAtomicBlockerBalance reward root owner =
      quittingAtomicBlockerBalance reward
        (QuittingSureSetOwnerRepair.quittingPureSetRoot
          (insert owner quitters)) owner by rfl,
      quittingAtomicBlockerBalance_pure_ownerToggle reward owner quitters
        hquitters howner]
    linarith
  have hnot : ¬ IsQuittingForcedOwnerNashRow reward owner root := by
    intro hrow
    have hbarrier :=
      quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap
        hrow hgap hexploit
    linarith
  have houtsider : ¬ ∀ who, who ≠ owner → ∀ deviation : PMF Bool,
      quittingRootExpectedPayoff reward 0
          (Function.update root who deviation) who ≤
        quittingRootExpectedPayoff reward 0 root who := by
    intro hstable
    exact hnot ⟨hrootOwner, hstable⟩
  push Not at houtsider
  simpa [root] using houtsider

/-- Strengthen the toggle side of the deletion dispatcher with its forced
atomic-row instability witness. -/
theorem strictToggle_or_playerDeletion_to_atomicHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) (owner : ι)
    (hdispatch :
      (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
          owner ∉ quitters ∧
            reward ⟨quitters, hquitters⟩ owner <
              reward
                ⟨insert owner quitters,
                  Finset.insert_nonempty owner quitters⟩ owner) ∨
        (Nonempty (QuittingDeletedPlayer owner) ∧
          HasTerminalExploitabilityGap
            (quittingDeletePlayerReward reward owner) gap ∧
          Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι)) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner ∧
          ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
            quittingRootExpectedPayoff reward 0
                (Function.update
                  (QuittingSureSetOwnerRepair.quittingPureSetRoot
                    (insert owner quitters)) who deviation) who >
              quittingRootExpectedPayoff reward 0
                (QuittingSureSetOwnerRepair.quittingPureSetRoot
                  (insert owner quitters)) who) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) gap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  rcases hdispatch with htoggle | hdelete
  · left
    obtain ⟨quitters, hquitters, howner, hstrict⟩ := htoggle
    exact ⟨quitters, hquitters, howner, hstrict,
      exists_outsider_atomicDeviation_of_strict_ownerToggle reward hgap
        hexploit owner quitters hquitters howner hstrict⟩
  · exact Or.inr hdelete

/-- **Deficient-clock closure in a counterexample regime.**  A summable
conditioned deleted clock has no residual analytic branch.  If the limiting
solo payoff clears the owner's punishment floor, the existing solo compiler
contradicts the regime.  Otherwise, at a nonpositive punishment floor, the
reward table itself exposes either a strict coalition toggle or an exact
smaller-player exploitability-floor instance. -/
theorem
    QuittingCounterexampleRegime.strictToggle_or_playerDeletion_of_summableConditionedDeletedClock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (owner : ι) (start : ℕ)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (htight : ∀ who,
      boundary who = quittingSoloBaseline reward who)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsmall : ∀ time, start ≤ time → Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner))
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) regime.terminalGap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  by_cases hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner
  · have huniform :=
      isUniformEquilibriumPayoff_soloReward_of_summableConditionedDeletedClock
        reward roots value boundary owner start hpolicy hnash hpositive
        heventualZero hconditionedBound htight hmesh hsmall hsummable
        hpunishment
    exact False.elim (regime.not_exists_uniformEquilibriumPayoff
      ⟨quittingSoloReward reward owner, huniform⟩)
  · have hsolo : reward (quittingSingletonTerminal owner) owner <
        quittingPunishmentValue reward owner := by
      change quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner
      exact lt_of_not_ge hpunishment
    exact exists_strict_owner_toggle_or_exact_playerDeletion reward owner
      regime.terminalGap_pos regime.terminalExploitability hsolo hchi

end GameTheory
