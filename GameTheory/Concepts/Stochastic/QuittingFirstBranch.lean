/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRootPerturbation

/-!
# The sure-first-stage branch of a quitting game

This module records the continuation datum needed by the `First` branch.  A
surely absorbing root action cannot use residual payoff zero as its
all-continue payoff: a unilateral attempt to continue starts the prescribed
continuation profile, whose playerwise best-response supremum is the relevant
root-game continuation vector.

Only this profile-level closure is developed here.  No absorption-path
equivalence is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A root product action has a sure quitter when one marginal is the point
mass at `true`. -/
def QuittingRootHasSureQuitter (root : ι → PMF Bool) : Prop :=
  ∃ player, root player = PMF.pure true

/-- A Boolean marginal assigns zero mass to `false` exactly when it is sure
`true`. -/
theorem pmf_eq_pure_true_iff_apply_false_eq_zero (marginal : PMF Bool) :
    marginal = PMF.pure true ↔ marginal false = 0 := by
  constructor
  · rintro rfl
    simp
  · intro hfalse
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype marginal
    rw [Fintype.sum_bool, hfalse, add_zero] at hsum
    ext action
    cases action <;> simp [PMF.pure_apply, hfalse, hsum]

omit [DecidableEq ι] in
/-- For an independent finite root law, absorption at the first stage has
probability one exactly when some player is a sure quitter. -/
theorem quittingRootHasSureQuitter_iff_allContinue_mass_zero
    (root : ι → PMF Bool) :
    QuittingRootHasSureQuitter root ↔
      pmfPi root (fun _ : ι => false) = 0 := by
  constructor
  · rintro ⟨sure, hsure⟩
    rw [pmfPi_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ sure)
    rw [hsure]
    simp
  · intro hzero
    rw [pmfPi_apply, Finset.prod_eq_zero_iff] at hzero
    obtain ⟨sure, -, hsure⟩ := hzero
    exact ⟨sure,
      (pmf_eq_pure_true_iff_apply_false_eq_zero (root sure)).mpr hsure⟩

omit [DecidableEq ι] in
/-- A uniform terminal-reward bound also bounds every terminal payoff of an
arbitrary quitting-game behavior profile. -/
theorem abs_quittingTerminalPayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalPayoff reward profile who| ≤ M := by
  have hstage : ∀ t : ℕ,
      |(quittingGame reward).expectedStagePayoff profile none t who| ≤ M := by
    intro t
    apply (quittingGame reward).abs_expectedStagePayoff_le
    intro state action
    cases state with
    | none => simpa [quittingGame] using hM
    | some S => simpa [quittingGame] using hreward S who
  exact le_of_tendsto'
    (tendsto_expectedStagePayoff_quittingGame reward profile who).abs hstage

/-- Player `who`'s continuation best-response value against the prescribed
opponents, defined as the supremum over all behavior deviations. -/
def quittingContinuationBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) : ℝ :=
  sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward
      (Function.update continuation who deviation) who)

/-- The vector of playerwise continuation best-response suprema. -/
def quittingContinuationBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile) : Payoff ι :=
  fun who => quittingContinuationBestResponseValue reward continuation who

/-- Every continuation deviation is bounded by its best-response supremum. -/
theorem quittingTerminalPayoff_update_le_continuationBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingTerminalPayoff reward
        (Function.update continuation who deviation) who ≤
      quittingContinuationBestResponseValue reward continuation who := by
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro payoff ⟨candidate, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update continuation who candidate) who hM hreward)
  · exact ⟨deviation, rfl⟩

/-- The continuation best-response supremum can be approached from below by
an actual behavior deviation. -/
theorem exists_quittingContinuation_deviation_ge_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingContinuationBestResponseValue reward continuation who - δ ≤
        quittingTerminalPayoff reward
          (Function.update continuation who deviation) who := by
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward
      (Function.update continuation who deviation) who
  have hvalues : values.Nonempty := by
    let candidate : (quittingGame reward).BehaviorStrategy who :=
      fun _ _ => PMF.pure false
    exact ⟨quittingTerminalPayoff reward
      (Function.update continuation who candidate) who,
      ⟨candidate, rfl⟩⟩
  have hbounded : BddAbove values := by
    refine ⟨M, ?_⟩
    rintro payoff ⟨candidate, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update continuation who candidate) who hM hreward)
  have hlt :
      quittingContinuationBestResponseValue reward continuation who - δ <
        quittingContinuationBestResponseValue reward continuation who :=
    sub_lt_self _ hδ
  change sSup values - δ < sSup values at hlt
  obtain ⟨payoff, ⟨deviation, rfl⟩, hpayoff⟩ :=
    (lt_csSup_iff hbounded hvalues).mp hlt
  exact ⟨deviation, hpayoff.le⟩

omit [DecidableEq ι] in
/-- Every joint action in the support of a root law with a sure quitter has a
nonempty quitter set. -/
theorem quittingQuitters_nonempty_of_mem_support_pmfPi_of_hasSureQuitter
    (root : ι → PMF Bool) (hsure : QuittingRootHasSureQuitter root)
    (action : ι → Bool) (haction : action ∈ (pmfPi root).support) :
    (quittingQuitters action).Nonempty := by
  obtain ⟨sure, hsure⟩ := hsure
  have hcoord : action sure ∈
      (Math.ProbabilityMassFunction.pushforward (pmfPi root)
        (fun joint => joint sure)).support := by
    rw [Math.ProbabilityMassFunction.pushforward,
      PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord root sure, hsure] at hcoord
  have htrue : action sure = true :=
    (PMF.mem_support_pure_iff _ _).mp hcoord
  exact (quittingQuitters_nonempty_iff action).mpr ⟨sure, htrue⟩

omit [DecidableEq ι] in
/-- Under a surely absorbing root product action, the prescribed root payoff
does not depend on the hypothetical all-continue continuation vector. -/
theorem quittingRootExpectedPayoff_eq_of_hasSureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (hsure : QuittingRootHasSureQuitter root)
    (first second : Payoff ι) (who : ι) :
    quittingRootExpectedPayoff reward first root who =
      quittingRootExpectedPayoff reward second root who := by
  unfold quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro action haction
  have hquit :=
    quittingQuitters_nonempty_of_mem_support_pmfPi_of_hasSureQuitter
      root hsure action haction
  simp [quittingRootPayoff, hquit]

/-- A root product action is an `ε`-Nash action in the finite continuation
game when no player gains more than `ε` by changing its root marginal. -/
def IsεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuationValue : Payoff ι) (ε : ℝ)
    (root : ι → PMF Bool) : Prop :=
  ∀ who (deviation : PMF Bool),
    quittingRootExpectedPayoff reward continuationValue
        (Function.update root who deviation) who ≤
      quittingRootExpectedPayoff reward continuationValue root who + ε

omit [DecidableEq ι] in
/-- Root expected payoff for `who` depends only on `who`'s coordinate of the
continuation vector. -/
theorem quittingRootExpectedPayoff_continuation_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (h : first who = second who) :
    quittingRootExpectedPayoff reward first root who =
      quittingRootExpectedPayoff reward second root who := by
  unfold quittingRootExpectedPayoff
  apply congrArg (expect (pmfPi root))
  funext action
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootPayoff, hquit]
  · simp [quittingRootPayoff, hquit, h]

omit [DecidableEq ι] in
/-- Raising `who`'s continuation value by at most `δ` raises its expected root
payoff by at most `δ`. -/
theorem quittingRootExpectedPayoff_continuation_le_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : first who ≤ second who + δ) :
    quittingRootExpectedPayoff reward first root who ≤
      quittingRootExpectedPayoff reward second root who + δ := by
  unfold quittingRootExpectedPayoff
  calc
    expect (pmfPi root)
        (fun action => quittingRootPayoff reward first action who) ≤
      expect (pmfPi root)
        (fun action => quittingRootPayoff reward second action who + δ) := by
          apply expect_mono
          intro action
          by_cases hquit : (quittingQuitters action).Nonempty
          · simp [quittingRootPayoff, hquit, hδ]
          · simpa [quittingRootPayoff, hquit] using h
    _ = expect (pmfPi root)
          (fun action => quittingRootPayoff reward second action who) + δ := by
      rw [expect_add, expect_const]

/-- A behavior deviation assembled from a root marginal and a continuation
behavior deviation. -/
def quittingRootAndContinuationDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who : ι} (rootDeviation : PMF Bool)
    (continuationDeviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).BehaviorStrategy who :=
  fun
    | 0, _ => rootDeviation
    | t + 1, history =>
        continuationDeviation t (Fin.tail history.1, history.2)

/-- Updating a root/continuation splice by the assembled deviation is exactly
the splice of the updated root and updated continuation. -/
theorem update_quittingRootThenContinuationProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (rootDeviation : PMF Bool)
    (continuationDeviation : (quittingGame reward).BehaviorStrategy who) :
    Function.update
        (quittingRootThenContinuationProfile reward root continuation)
        who
        (quittingRootAndContinuationDeviation reward rootDeviation
          continuationDeviation) =
      quittingRootThenContinuationProfile reward
        (Function.update root who rootDeviation)
        (Function.update continuation who continuationDeviation) := by
  funext player t history
  cases t with
  | zero =>
      by_cases hp : player = who
      · subst player
        simp [quittingRootThenContinuationProfile,
          quittingRootAndContinuationDeviation]
      · simp [Function.update_of_ne hp,
          quittingRootThenContinuationProfile]
  | succ t =>
      by_cases hp : player = who
      · subst player
        simp [quittingRootThenContinuationProfile,
          quittingRootAndContinuationDeviation]
      · simp [Function.update_of_ne hp,
          quittingRootThenContinuationProfile]

/-- Exact payoff of an assembled root-and-continuation deviation. -/
theorem quittingTerminalPayoff_update_rootAndContinuationDeviation_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (rootDeviation : PMF Bool)
    (continuationDeviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation)
          who
          (quittingRootAndContinuationDeviation reward rootDeviation
            continuationDeviation)) who =
      quittingRootExpectedPayoff reward
        (Function.update
          (fun player => quittingTerminalPayoff reward continuation player)
          who
          (quittingTerminalPayoff reward
            (Function.update continuation who continuationDeviation) who))
        (Function.update root who rootDeviation) who := by
  rw [update_quittingRootThenContinuationProfile_eq,
    quittingTerminalPayoff_rootThenContinuation_eq]
  apply quittingRootExpectedPayoff_continuation_congr
  simp

/-- **First-branch sufficiency.**  If a root law has a sure quitter and is an
`ε`-Nash action of the root game whose all-continue payoff is the continuation
best-response vector, then the root/continuation splice is a terminal
`ε`-equilibrium. -/
theorem isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsure : QuittingRootHasSureQuitter root)
    (hroot : IsεQuittingRootNash reward
      (quittingContinuationBestResponse reward continuation) ε root) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation) := by
  intro who deviation
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let best : Payoff ι :=
    quittingContinuationBestResponse reward continuation
  have hbound : ∀ candidate : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update continuation who candidate) who ≤ best who := by
    intro candidate
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward continuation who candidate hM hreward
  have hdeviation := quittingTerminalPayoff_update_rootThenContinuation_le
    reward root continuation who (best who) hbound deviation
  have hdevContinuation :
      Function.update base who (best who) who = best who := by simp
  have hdevEq := quittingRootExpectedPayoff_continuation_congr
    reward (Function.update base who (best who)) best
    (Function.update root who
      (deviation 0 ((quittingGame reward).emptyHist none))) who
    hdevContinuation
  have hrootBound := hroot who
    (deviation 0 ((quittingGame reward).emptyHist none))
  have hprescribed :=
    quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  have hprescribedEq := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    reward root hsure base best who
  dsimp [base, best] at hdeviation hdevEq hrootBound hprescribed hprescribedEq ⊢
  linarith

/-- **First-branch necessity.**  A terminal `ε`-equilibrium root/continuation
splice with a sure quitter is an `ε`-Nash action of the finite root game with
the continuation best-response vector.  The supremum need not be attained;
an approximating continuation deviation is enough. -/
theorem isεQuittingRootNash_of_isεAsymptoticNash_quittingRootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsure : QuittingRootHasSureQuitter root)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation)) :
    IsεQuittingRootNash reward
      (quittingContinuationBestResponse reward continuation) ε root := by
  intro who rootDeviation
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let best : Payoff ι :=
    quittingContinuationBestResponse reward continuation
  by_contra hnot
  have hgain :
      quittingRootExpectedPayoff reward best
          (Function.update root who rootDeviation) who >
        quittingRootExpectedPayoff reward best root who + ε :=
    lt_of_not_ge hnot
  let gap : ℝ :=
    quittingRootExpectedPayoff reward best
        (Function.update root who rootDeviation) who -
      (quittingRootExpectedPayoff reward best root who + ε)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let δ : ℝ := gap / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨continuationDeviation, happ⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward continuation who hδ hM hreward
  let continuationPayoff := quittingTerminalPayoff reward
    (Function.update continuation who continuationDeviation) who
  let assembled := quittingRootAndContinuationDeviation reward
    rootDeviation continuationDeviation
  have hnashDeviation := hnash who assembled
  have hfullEq :=
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq
      reward root continuation who rootDeviation continuationDeviation
  have hprescribed :=
    quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  have hprescribedEq := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    reward root hsure base best who
  have hbestLe : best who ≤ continuationPayoff + δ := by
    dsimp [best, continuationPayoff, quittingContinuationBestResponse]
    linarith
  have hrootApprox := quittingRootExpectedPayoff_continuation_le_add
    reward best (Function.update base who continuationPayoff)
    (Function.update root who rootDeviation) who hδ.le (by simpa using hbestLe)
  have hfullBound :
      quittingRootExpectedPayoff reward
          (Function.update base who continuationPayoff)
          (Function.update root who rootDeviation) who ≤
        quittingRootExpectedPayoff reward best root who + ε := by
    calc
      _ = quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who assembled) who := by
              symm
              simpa [assembled, base, continuationPayoff] using hfullEq
      _ ≤ quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who + ε :=
        hnashDeviation
      _ = quittingRootExpectedPayoff reward base root who + ε := by
        rw [hprescribed]
      _ = quittingRootExpectedPayoff reward best root who + ε := by
        rw [hprescribedEq]
  dsimp [gap, δ] at hrootApprox
  linarith

/-- Exact profile-level closure criterion for the surely absorbing `First`
branch. -/
theorem isεAsymptoticNash_quittingRootThenContinuation_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsure : QuittingRootHasSureQuitter root) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingRootThenContinuationProfile reward root continuation) ↔
      IsεQuittingRootNash reward
        (quittingContinuationBestResponse reward continuation) ε root := by
  constructor
  · exact isεQuittingRootNash_of_isεAsymptoticNash_quittingRootThenContinuation
      reward root continuation hM hreward hsure
  · exact isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
      reward root continuation hM hreward hsure

end GameTheory
