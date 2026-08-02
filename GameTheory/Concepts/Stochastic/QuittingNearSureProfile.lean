/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingNearSureRoot

/-!
# Full-profile near-sure-to-sure perturbation in quitting games

`QuittingNearSureRoot` controls one-stage continuation games.  This file
proves the profile-level estimate used in the near-sure `First` extraction:
if one root coordinate is within `d` of quitting surely, force it to quit and
keep the same continuation profile after all-continue.

The key equality decomposes an arbitrary behavior deviation into its root
marginal and its continuation after the unique all-continue action.  For a
player other than the forced quitter, both the prescribed and deviating
terminal payoffs move by at most `2 * M * d`.  For the forced quitter, the
deviating profile is unchanged and only the prescribed payoff moves.  Thus a
terminal epsilon-equilibrium becomes a terminal
`(epsilon + 4 * M * d)`-equilibrium.

The last theorem first applies the arbitrary-profile adapter and therefore
works for any supplied behavior profile with an actually near-sure first
stage.  No assertion is made that a terminal atom in a weak path limit
produces such a stage; that mass-time extraction remains a separate lemma.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The continuation-payoff vector relevant to one arbitrary full behavior
deviation from a root/continuation splice. -/
def quittingRootDeviationContinuationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    Payoff ι :=
  Function.update
    (fun player => quittingTerminalPayoff reward continuation player)
    who
    (quittingTerminalPayoff reward
      (Function.update continuation who
        (quittingShiftBehaviorStrategy reward deviation
          quittingAllContinueAction)) who)

/-- Exact root equation for an arbitrary unilateral behavior deviation from a
root/continuation splice.  Only the deviation shifted after all-continue can
affect a continuation payoff. -/
theorem quittingTerminalPayoff_update_rootThenContinuation_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation)
          who deviation) who =
      quittingRootExpectedPayoff reward
        (quittingRootDeviationContinuationPayoff
          reward continuation who deviation)
        (Function.update root who
          (deviation 0 ((quittingGame reward).emptyHist none))) who := by
  rw [quittingTerminalPayoff_eq_expect_rootContinuation,
    stageActionDist_update_quittingRootThenContinuationProfile]
  unfold quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi (Function.update root who
    (deviation 0 ((quittingGame reward).emptyHist none)))))
  funext action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootContinuationPayoff, quittingRootPayoff, hquit]
  · have haction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
        action hquit
    subst action
    rw [quittingRootContinuationPayoff_of_allContinue _ _ _ _ hquit]
    rw [shiftProfile_update_quittingRootThenContinuationProfile]
    simp [quittingRootPayoff, quittingRootDeviationContinuationPayoff]

/-- Bounded terminal rewards bound the deviation-specific continuation vector. -/
theorem abs_quittingRootDeviationContinuationPayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    (player : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S i, |reward S i| ≤ M) :
    |quittingRootDeviationContinuationPayoff
      reward continuation who deviation player| ≤ M := by
  by_cases hp : player = who
  · subst player
    simp only [quittingRootDeviationContinuationPayoff,
      Function.update_self]
    exact abs_quittingTerminalPayoff_le reward _ who hM hreward
  · simp only [quittingRootDeviationContinuationPayoff,
      Function.update_of_ne hp]
    exact abs_quittingTerminalPayoff_le reward continuation player hM hreward

/-- Forcing one root coordinate to quit changes every prescribed terminal
payoff of a root/continuation splice by at most `2 M` times that coordinate's
former continue probability. -/
theorem abs_quittingTerminalPayoff_rootThenContinuation_forceQuit_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (changed who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward
            (Function.update root changed (PMF.pure true))
            continuation) who| ≤
      2 * M * (root changed false).toReal := by
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_rootThenContinuation_eq]
  exact abs_quittingRootExpectedPayoff_forceQuit_sub_le
    reward (fun player =>
      quittingTerminalPayoff reward continuation player)
    root changed who hreward
    (fun player => abs_quittingTerminalPayoff_le
      reward continuation player hM hreward)

/-- For a player other than the forced quitter, the payoff of every fixed full
behavior deviation moves by at most `2 M d`. -/
theorem abs_quittingTerminalPayoff_update_rootThenContinuation_forceQuit_other_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (changed who : ι) (hother : changed ≠ who)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who deviation) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward
              (Function.update root changed (PMF.pure true))
              continuation)
            who deviation) who| ≤
      2 * M * (root changed false).toReal := by
  rw [quittingTerminalPayoff_update_rootThenContinuation_eq,
    quittingTerminalPayoff_update_rootThenContinuation_eq,
    Function.update_comm (f := root) (a := changed) (b := who)
      hother (PMF.pure true)
      (deviation 0 ((quittingGame reward).emptyHist none))]
  simpa [Function.update_of_ne hother] using
    (abs_quittingRootExpectedPayoff_forceQuit_sub_le
      reward
      (quittingRootDeviationContinuationPayoff
        reward continuation who deviation)
      (Function.update root who
        (deviation 0 ((quittingGame reward).emptyHist none)))
      changed who hreward
      (fun player => abs_quittingRootDeviationContinuationPayoff_le
        reward continuation who deviation player hM hreward))

/-- For the forced quitter itself, updating by any fixed full behavior
deviation erases the root perturbation exactly. -/
theorem quittingTerminalPayoff_update_rootThenContinuation_forceQuit_self_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (changed : ι)
    (deviation : (quittingGame reward).BehaviorStrategy changed) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation)
          changed deviation) changed =
      quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward
            (Function.update root changed (PMF.pure true)) continuation)
          changed deviation) changed := by
  rw [quittingTerminalPayoff_update_rootThenContinuation_eq,
    quittingTerminalPayoff_update_rootThenContinuation_eq]
  simp only [Function.update_idem]

/-- Uniform deviation-payoff perturbation bound, including the forced quitter. -/
theorem abs_quittingTerminalPayoff_update_rootThenContinuation_forceQuit_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (changed who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who deviation) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward
              (Function.update root changed (PMF.pure true))
              continuation)
            who deviation) who| ≤
      2 * M * (root changed false).toReal := by
  by_cases hself : changed = who
  · subst who
    rw [quittingTerminalPayoff_update_rootThenContinuation_forceQuit_self_eq]
    simp only [sub_self, abs_zero]
    positivity
  · exact
      abs_quittingTerminalPayoff_update_rootThenContinuation_forceQuit_other_sub_le
        reward root continuation changed who hself deviation hM hreward

/-- **Full-profile near-sure-to-sure transfer.**  Forcing one root coordinate
to quit surely increases terminal equilibrium error by at most four times the
payoff bound times that coordinate's former continue probability. -/
theorem isεAsymptoticNash_rootThenContinuation_update_pure_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (changed : ι) {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (ε + 4 * M * (root changed false).toReal)
      (quittingRootThenContinuationProfile reward
        (Function.update root changed (PMF.pure true)) continuation) := by
  intro who deviation
  have hold := hnash who deviation
  have hprescribed :=
    abs_quittingTerminalPayoff_rootThenContinuation_forceQuit_sub_le
      reward root continuation changed who hM hreward
  have hdeviation :=
    abs_quittingTerminalPayoff_update_rootThenContinuation_forceQuit_sub_le
      reward root continuation changed who deviation hM hreward
  rw [abs_le] at hprescribed hdeviation
  linarith

/-- A supplied root/continuation profile with an actually near-sure root can
be replaced by a surely absorbing `First` profile with quantified error. -/
theorem exists_sureFirstProfile_of_allContinue_mass_le_pow
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {ε M d : ℝ} (hd : 0 < d) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnear : ((pmfPi root) quittingAllContinueAction).toReal ≤
      d ^ Fintype.card ι)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation)) :
    ∃ sureRoot : ι → PMF Bool,
      QuittingRootHasSureQuitter sureRoot ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 4 * M * d)
        (quittingRootThenContinuationProfile
          reward sureRoot continuation) := by
  obtain ⟨changed, hcontinue⟩ :=
    exists_continueProbability_le_of_allContinue_mass_le_pow root hd hnear
  let sureRoot := Function.update root changed (PMF.pure true)
  refine ⟨sureRoot,
    quittingRootHasSureQuitter_update_pure_true root changed, ?_⟩
  dsimp [sureRoot]
  have hforced :=
    isεAsymptoticNash_rootThenContinuation_update_pure_true
      reward root continuation changed hM hreward hnash
  intro who deviation
  have hbound := hforced who deviation
  have hfour : 0 ≤ 4 * M := mul_nonneg (by norm_num) hM
  have hscale := mul_le_mul_of_nonneg_left hcontinue hfour
  linarith

/-- Arbitrary-profile form of the conditional near-sure extraction.  The
canonical adapter supplies the root and the all-continue continuation before
the one-coordinate perturbation is applied. -/
theorem exists_sureFirstProfile_of_profile_allContinue_mass_le_pow
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε M d : ℝ} (hd : 0 < d) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnear : (((quittingGame reward).stageActionDist profile
      ((quittingGame reward).emptyHist none))
      quittingAllContinueAction).toReal ≤ d ^ Fintype.card ι)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    ∃ sureRoot : ι → PMF Bool,
      QuittingRootHasSureQuitter sureRoot ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 4 * M * d)
        (quittingRootThenContinuationProfile reward sureRoot
          (quittingProfileAllContinueContinuation reward profile)) := by
  apply exists_sureFirstProfile_of_allContinue_mass_le_pow
    reward (quittingProfileRoot reward profile)
      (quittingProfileAllContinueContinuation reward profile)
      hd hM hreward
  · change ((pmfPi (quittingProfileRoot reward profile))
      quittingAllContinueAction).toReal ≤ d ^ Fintype.card ι at hnear
    exact hnear
  · exact (isεAsymptoticNash_firstStageAdapter_iff
      reward profile ε).mpr hnash

end GameTheory
