/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.FirstBranch
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Approximate root/continuation splicing

This module gives the semantic handoff from a one-stage quitting root to an
arbitrary continuation profile.  The root is tested against a declared target
vector, while the continuation may deliver a nearby terminal payoff rather
than that target exactly.

The estimate is deliberately profile-level and does not assume sure
absorption.  A unilateral continuation deviation contributes its terminal
continuation error once.  Replacing the declared target by the prescribed
continuation payoff costs at most `δ` at the deviating root and at most `δ` at
the prescribed root, giving the sharp uniform bound `η + ε + 2 * δ` exposed
below.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An approximate target match and a terminal approximate Nash continuation
can be prepended to an approximate root Nash action.  No sure-quit or reward
bound is needed: the continuation Nash hypothesis itself supplies the only
bound required by the root deviation decomposition. -/
theorem isεAsymptoticNash_quittingRootThenContinuation_of_target_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (target : Payoff ι)
    {η ε δ : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hroot : IsεQuittingRootNash reward target η root)
    (hcontinuation : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε continuation)
    (hclose : ∀ who,
      |quittingTerminalPayoff reward continuation who - target who| ≤ δ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (η + ε + 2 * δ)
      (quittingRootThenContinuationProfile reward root continuation) := by
  intro who deviation
  let prescribed : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let rootDeviation : PMF Bool :=
    deviation 0 ((quittingGame reward).emptyHist none)
  have hcontinuationBound : ∀ candidate :
      (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update continuation who candidate) who ≤
        prescribed who + ε := by
    intro candidate
    have h := hcontinuation who candidate
    exact h
  have hdeviation := quittingTerminalPayoff_update_rootThenContinuation_le
    reward root continuation who (prescribed who + ε)
    (by intro candidate; exact hcontinuationBound candidate) deviation
  have hdeviationTarget :
      prescribed who + ε ≤ target who + δ + ε := by
    have h := hclose who
    have hright := (abs_le.mp h).2
    dsimp [prescribed]
    linarith
  have hrootTarget := hroot who rootDeviation
  have hrootClose :
      quittingRootExpectedPayoff reward target root who ≤
        quittingRootExpectedPayoff reward prescribed root who + δ := by
    apply quittingRootExpectedPayoff_continuation_le_add
      reward target prescribed root who hδ
    have hleft := (abs_le.mp (hclose who)).1
    dsimp [prescribed]
    linarith
  have hdeviationRoot :
      quittingRootExpectedPayoff reward
          (Function.update prescribed who (prescribed who + ε))
          (Function.update root who rootDeviation) who ≤
        quittingRootExpectedPayoff reward target
          (Function.update root who rootDeviation) who + δ + ε := by
    have htmp := quittingRootExpectedPayoff_continuation_le_add
      reward
      (Function.update prescribed who (prescribed who + ε))
      target (Function.update root who rootDeviation) who
      (δ := δ + ε) (by linarith)
      (by
        have hu :
            Function.update prescribed who (prescribed who + ε) who =
              prescribed who + ε := by simp
        rw [hu]
        linarith [hdeviationTarget])
    linarith
  have hrootTarget' :
      quittingRootExpectedPayoff reward target
          (Function.update root who rootDeviation) who ≤
        quittingRootExpectedPayoff reward target root who + η := by
    simpa [rootDeviation] using hrootTarget
  have hdeviationFinal :
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who deviation) who ≤
        quittingRootExpectedPayoff reward
          (Function.update prescribed who (prescribed who + ε))
          (Function.update root who rootDeviation) who := by
    exact hdeviation
  have hprescribed :
      quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who =
        quittingRootExpectedPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who := by
    exact quittingTerminalPayoff_rootThenContinuation_eq reward root continuation who
  have hdeviationFinal' :
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who deviation) who ≤
        quittingRootExpectedPayoff reward
          (Function.update
            (fun player => quittingTerminalPayoff reward continuation player)
            who (quittingTerminalPayoff reward continuation who + ε))
          (Function.update root who rootDeviation) who := by
    simpa [prescribed] using hdeviationFinal
  have hdeviationRoot' :
      quittingRootExpectedPayoff reward
          (Function.update
            (fun player => quittingTerminalPayoff reward continuation player)
            who (quittingTerminalPayoff reward continuation who + ε))
          (Function.update root who rootDeviation) who ≤
        quittingRootExpectedPayoff reward target
          (Function.update root who rootDeviation) who + δ + ε := by
    simpa [prescribed] using hdeviationRoot
  have hrootClose' :
      quittingRootExpectedPayoff reward target root who ≤
        quittingRootExpectedPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who + δ := by
    exact (by simpa [prescribed] using hrootClose)
  have hfinal :
      quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who +
          (η + ε + 2 * δ) ≥
        quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who deviation) who := by
    linarith [hdeviationFinal', hdeviationRoot', hrootTarget', hrootClose',
      hprescribed]
  exact hfinal

/-- Endpoint-form wrapper for
`isεAsymptoticNash_quittingRootThenContinuation_of_target_close`. -/
theorem isεAsymptoticNash_quittingRootThenContinuation_of_endpointNash_target_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (target : Payoff ι)
    {η ε δ : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hroot : IsεQuittingRootEndpointNash reward target η root)
    (hcontinuation : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε continuation)
    (hclose : ∀ who,
      |quittingTerminalPayoff reward continuation who - target who| ≤ δ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (η + ε + 2 * δ)
      (quittingRootThenContinuationProfile reward root continuation) := by
  apply isεAsymptoticNash_quittingRootThenContinuation_of_target_close
    reward root continuation target hδ hε
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward target η root).mp hroot)
    hcontinuation hclose

end GameTheory
