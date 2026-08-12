/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSpliceMarkedLaw

/-!
# Nashification interface for finite stopping-law splices

Finite capping controls both the prescribed terminal payoff and the full
behavioral best-response envelope.  Consequently it also transports a
terminal approximate-Nash certificate directly: the Nash error increases by
at most twice the common payoff/envelope perturbation.

For an outer stopping-law mixture of weight `lambda`, the exact interface
loss is

`lambda * (4 * M * quittingFiniteSpliceError ...)`.

This bypasses metric reprojection when the uncapped literal profile already
has a quantitative all-behavior Nash certificate.  It does not produce that
certificate from debt-height minimality, a marked event, or a common suffix;
those data alone remain insufficient for Bellman return.  In particular, the
diagonal consumer below transports vanishing terminal Nash exploitability; it
does not produce exploitability decay or rowwise Nash--Bellman roots.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite capping of one complete live-path stopping law preserves terminal
approximate Nash, with one splice-error copy for the best-response envelope
and one for the prescribed payoff. -/
theorem isεAsymptoticNash_finiteCap
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (Function.update profile mover strategy)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (ε + 4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff)
      (Function.update profile mover
        (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
          cutoff)) := by
  let sourceProfile := Function.update profile mover strategy
  let cappedProfile := Function.update profile mover
    (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy cutoff)
  let error := 2 * M * quittingFiniteSpliceError
    (quittingProfileLiveRoot reward profile) mover
      (quittingBehaviorLiveHazard reward strategy) cutoff
  have hsourceBest : ∀ observer,
      quittingContinuationBestResponseValue reward sourceProfile observer ≤
        quittingTerminalPayoff reward sourceProfile observer + ε := by
    intro observer
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨sourceProfile observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnash observer deviation
  have hbest : ∀ observer,
      |quittingContinuationBestResponseValue reward sourceProfile observer -
        quittingContinuationBestResponseValue reward cappedProfile observer| ≤
          error := by
    intro observer
    dsimp only [sourceProfile, cappedProfile, error]
    exact abs_quittingContinuationBestResponseValue_finiteCap_sub_le
      reward profile mover observer strategy cutoff hM hreward
  have hpayoff : ∀ observer,
      |quittingTerminalPayoff reward sourceProfile observer -
        quittingTerminalPayoff reward cappedProfile observer| ≤ error := by
    intro observer
    dsimp only [sourceProfile, cappedProfile, error]
    exact abs_quittingTerminalPayoff_finiteCap_sub_le
      reward profile mover observer strategy cutoff hM hreward
  have hdouble : error + error =
      4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
    dsimp only [error]
    ring
  intro observer deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward cappedProfile observer deviation hM hreward
  have hbestUpper :
      quittingContinuationBestResponseValue reward cappedProfile observer ≤
        quittingContinuationBestResponseValue reward sourceProfile observer +
          error := by
    linarith [neg_le_abs
      (quittingContinuationBestResponseValue reward sourceProfile observer -
        quittingContinuationBestResponseValue reward cappedProfile observer),
      hbest observer]
  have hpayoffUpper :
      quittingTerminalPayoff reward sourceProfile observer ≤
        quittingTerminalPayoff reward cappedProfile observer + error := by
    linarith [le_abs_self
      (quittingTerminalPayoff reward sourceProfile observer -
        quittingTerminalPayoff reward cappedProfile observer),
      hpayoff observer]
  change quittingTerminalPayoff reward cappedProfile observer +
      (ε + 4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward strategy) cutoff) ≥
    quittingTerminalPayoff reward
      (Function.update cappedProfile observer deviation) observer
  linarith [hsourceBest observer, hdouble]

/-- The outer stopping-law mixture retains its exact `lambda` scaling when a
finite cap is transported through a terminal approximate-Nash certificate. -/
theorem isεAsymptoticNash_mixtureFiniteCap
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (cutoff : ℕ) {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
          lambda hlambda0 hlambda1))) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (ε + lambda * (4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff))
      (Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source
          (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target
            cutoff) lambda hlambda0 hlambda1)) := by
  let sourceProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      lambda hlambda0 hlambda1)
  let cappedProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source
      (quittingStoppingLawFiniteCapBehaviorStrategy reward mover target cutoff)
      lambda hlambda0 hlambda1)
  let error := lambda * (2 * M * quittingFiniteSpliceError
    (quittingProfileLiveRoot reward profile) mover
      (quittingBehaviorLiveHazard reward target) cutoff)
  have hsourceBest : ∀ observer,
      quittingContinuationBestResponseValue reward sourceProfile observer ≤
        quittingTerminalPayoff reward sourceProfile observer + ε := by
    intro observer
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨sourceProfile observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnash observer deviation
  have hbest : ∀ observer,
      |quittingContinuationBestResponseValue reward sourceProfile observer -
        quittingContinuationBestResponseValue reward cappedProfile observer| ≤
          error := by
    intro observer
    dsimp only [sourceProfile, cappedProfile, error]
    exact abs_quittingContinuationBestResponseValue_mixtureFiniteCap_sub_le
      reward profile mover observer source target lambda hlambda0 hlambda1
        cutoff hM hreward
  have hpayoff : ∀ observer,
      |quittingTerminalPayoff reward sourceProfile observer -
        quittingTerminalPayoff reward cappedProfile observer| ≤ error := by
    intro observer
    dsimp only [sourceProfile, cappedProfile, error]
    exact abs_quittingTerminalPayoff_mixtureFiniteCap_sub_le
      reward profile mover observer source target lambda hlambda0 hlambda1
        cutoff hM hreward
  have hdouble : error + error =
      lambda * (4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff) := by
    dsimp only [error]
    ring
  intro observer deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward cappedProfile observer deviation hM hreward
  have hbestUpper :
      quittingContinuationBestResponseValue reward cappedProfile observer ≤
        quittingContinuationBestResponseValue reward sourceProfile observer +
          error := by
    linarith [neg_le_abs
      (quittingContinuationBestResponseValue reward sourceProfile observer -
        quittingContinuationBestResponseValue reward cappedProfile observer),
      hbest observer]
  have hpayoffUpper :
      quittingTerminalPayoff reward sourceProfile observer ≤
        quittingTerminalPayoff reward cappedProfile observer + error := by
    linarith [le_abs_self
      (quittingTerminalPayoff reward sourceProfile observer -
        quittingTerminalPayoff reward cappedProfile observer),
      hpayoff observer]
  change quittingTerminalPayoff reward cappedProfile observer +
      (ε + lambda * (4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward profile) mover
          (quittingBehaviorLiveHazard reward target) cutoff)) ≥
    quittingTerminalPayoff reward
      (Function.update cappedProfile observer deviation) observer
  linarith [hsourceBest observer, hdouble]

/-! ## Cap-tight diagonal consumer -/

/-- Along a cap-tight reset sequence, the same finite cutoffs simultaneously
retain a marked terminal-law event and transport an all-behavior
approximate-Nash certificate.  If the uncapped Nash errors tend to zero, so
do the capped errors.

The additional hypothesis is exactly the missing strategic datum: the
uncapped literal reset mixtures must already have vanishing terminal Nash
exploitability.  Cap tightness and marked-law retention do not imply it, and
the conclusion supplies no rowwise Nash--Bellman roots. -/
theorem exists_finiteSpliceCutoffs_mixtureNash_markedEvent_of_capTight
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : ℕ → (quittingGame reward).BehaviorStrategy mover)
    (lambda epsilon : ℕ → ℝ)
    (hlambda0 : ∀ n, 0 ≤ lambda n) (hlambda1 : ∀ n, lambda n ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : ∀ n,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (epsilon n)
        (Function.update (profile n) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source n) (target n) (lambda n)
              (hlambda0 n) (hlambda1 n))))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (event : Finset (QuittingTerminalOutcome ι)) (rho : ℝ)
    (hretained : ∀ n,
      rho ≤ quittingTerminalOutcomeEventMass reward
        (Function.update (profile n) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source n) (target n) (lambda n)
              (hlambda0 n) (hlambda1 n))) event)
    (hcap : Tendsto (fun n =>
      quittingHazardNeverMass
          (quittingBehaviorLiveHazard reward (target n)) *
        quittingMaxPairDeletedSurvivalLimit
          (quittingProfileLiveRoot reward (profile n)) mover 0)
      atTop (nhds 0)) :
    ∃ cutoffs : ℕ → ℕ,
      Tendsto cutoffs atTop atTop ∧
      Tendsto (fun n =>
        quittingFiniteSpliceError
          (quittingProfileLiveRoot reward (profile n)) mover
          (quittingBehaviorLiveHazard reward (target n)) (cutoffs n))
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        epsilon n + lambda n *
          (4 * M * quittingFiniteSpliceError
            (quittingProfileLiveRoot reward (profile n)) mover
            (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)))
        atTop (nhds 0) ∧
      (∀ n,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward)
          (epsilon n + lambda n *
            (4 * M * quittingFiniteSpliceError
              (quittingProfileLiveRoot reward (profile n)) mover
              (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)))
          (Function.update (profile n) mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              (source n)
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
                (target n) (cutoffs n))
              (lambda n) (hlambda0 n) (hlambda1 n)))) ∧
      ∀ n,
        rho - lambda n *
            (2 * quittingFiniteSpliceError
              (quittingProfileLiveRoot reward (profile n)) mover
              (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)) ≤
          quittingTerminalOutcomeEventMass reward
            (Function.update (profile n) mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (source n)
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
                  (target n) (cutoffs n))
                (lambda n) (hlambda0 n) (hlambda1 n))) event := by
  obtain ⟨cutoffs, hcutoffs, herror, hmarked⟩ :=
    exists_finiteSpliceCutoffs_markedEvent_retained_of_capTight
      reward profile mover source target lambda hlambda0 hlambda1 event rho
        hretained hcap
  have hscaled : Tendsto (fun n =>
      4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward (profile n)) mover
        (quittingBehaviorLiveHazard reward (target n)) (cutoffs n))
      atTop (nhds 0) := by
    simpa using herror.const_mul (4 * M)
  have hextra : Tendsto (fun n =>
      lambda n * (4 * M * quittingFiniteSpliceError
        (quittingProfileLiveRoot reward (profile n)) mover
        (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (hlambda0 n)
        (mul_nonneg (mul_nonneg (by norm_num) hM)
          (quittingFiniteSpliceError_nonneg
            (quittingProfileLiveRoot reward (profile n)) mover
            (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)))
    · intro n
      have hscale : 0 ≤ 4 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward (profile n)) mover
          (quittingBehaviorLiveHazard reward (target n)) (cutoffs n) :=
        mul_nonneg (mul_nonneg (by norm_num) hM)
          (quittingFiniteSpliceError_nonneg
            (quittingProfileLiveRoot reward (profile n)) mover
            (quittingBehaviorLiveHazard reward (target n)) (cutoffs n))
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (hlambda1 n) hscale)
    · exact hscaled
  have htotal : Tendsto (fun n =>
      epsilon n + lambda n *
        (4 * M * quittingFiniteSpliceError
          (quittingProfileLiveRoot reward (profile n)) mover
          (quittingBehaviorLiveHazard reward (target n)) (cutoffs n)))
      atTop (nhds 0) := by
    simpa using hepsilon.add hextra
  refine ⟨cutoffs, hcutoffs, herror, htotal, ?_, hmarked⟩
  intro n
  exact isεAsymptoticNash_mixtureFiniteCap
    reward (profile n) mover (source n) (target n) (lambda n)
      (hlambda0 n) (hlambda1 n) (cutoffs n) hM hreward (hnash n)

end GameTheory
