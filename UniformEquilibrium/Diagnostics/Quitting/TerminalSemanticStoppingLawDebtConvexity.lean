/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMixture

/-!
# Full debt convexity under a complete stopping-law mixture

Mixing one player's complete stopping laws is affine on the entire terminal
outcome law, not only on that player's payoff.  The other players' behavioral
best-response envelopes are consequently convex.  Thus every semantic-debt
coordinate of the mixed profile lies below the corresponding chord between
the two endpoint profiles; the moved coordinate is exactly affine.

This is one-sided seam control.  It prevents a stopping-law reset from
creating debt above the endpoint chord, but it does not solve arbitrary exact
entry/exit anchor equations.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every absorbing-coalition mass is affine under a complete stopping-law
mixture of one player's strategies. -/
theorem quittingAbsorbedMassLimit_stoppingLawMixture_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) terminal =
      (1 - lambda) * quittingAbsorbedMassLimit reward
          (Function.update profile mover source) terminal +
        lambda * quittingAbsorbedMassLimit reward
          (Function.update profile mover target) terminal := by
  let mixedProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      lambda hlambda0 hlambda1)
  let sourceProfile := Function.update profile mover source
  let targetProfile := Function.update profile mover target
  have hmixed := hasSum_quittingStageCoalitionMass reward mixedProfile terminal
  have hsource := hasSum_quittingStageCoalitionMass reward sourceProfile terminal
  have htarget := hasSum_quittingStageCoalitionMass reward targetProfile terminal
  have hchord := (hsource.mul_left (1 - lambda)).add
    (htarget.mul_left lambda)
  have hfunctions :
      (fun time => quittingStageCoalitionMass reward mixedProfile time terminal) =
        (fun time =>
          (1 - lambda) *
              quittingStageCoalitionMass reward sourceProfile time terminal +
            lambda *
              quittingStageCoalitionMass reward targetProfile time terminal) := by
    funext time
    dsimp only [mixedProfile, sourceProfile, targetProfile]
    exact quittingStageCoalitionMass_stoppingLawMixture_eq
      reward profile mover source target lambda hlambda0 hlambda1 time terminal
  rw [hfunctions] at hmixed
  exact hmixed.unique hchord

/-- The complete terminal outcome law, including `Never`, is affine under a
complete stopping-law mixture. -/
theorem quittingTerminalOutcomeMass_stoppingLawMixture_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) outcome =
      (1 - lambda) * quittingTerminalOutcomeMass reward
          (Function.update profile mover source) outcome +
        lambda * quittingTerminalOutcomeMass reward
          (Function.update profile mover target) outcome := by
  let mixedProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      lambda hlambda0 hlambda1)
  let sourceProfile := Function.update profile mover source
  let targetProfile := Function.update profile mover target
  cases outcome with
  | some terminal =>
      simpa [quittingTerminalOutcomeMass, mixedProfile, sourceProfile,
        targetProfile] using
        quittingAbsorbedMassLimit_stoppingLawMixture_eq
          reward profile mover source target lambda hlambda0 hlambda1 terminal
  | none =>
      have hmixed :=
        (quittingTerminalOutcomeMass_mem_stdSimplex reward mixedProfile).2
      have hsource :=
        (quittingTerminalOutcomeMass_mem_stdSimplex reward sourceProfile).2
      have htarget :=
        (quittingTerminalOutcomeMass_mem_stdSimplex reward targetProfile).2
      rw [Fintype.sum_option] at hmixed hsource htarget
      have hcoalitions :
          (∑ terminal,
              quittingTerminalOutcomeMass reward mixedProfile (some terminal)) =
            (1 - lambda) *
                (∑ terminal,
                  quittingTerminalOutcomeMass reward sourceProfile
                    (some terminal)) +
              lambda *
                (∑ terminal,
                  quittingTerminalOutcomeMass reward targetProfile
                    (some terminal)) := by
        simp_rw [show ∀ terminal,
            quittingTerminalOutcomeMass reward mixedProfile (some terminal) =
              (1 - lambda) *
                  quittingTerminalOutcomeMass reward sourceProfile
                    (some terminal) +
                lambda *
                  quittingTerminalOutcomeMass reward targetProfile
                    (some terminal) by
          intro terminal
          simpa [quittingTerminalOutcomeMass, mixedProfile, sourceProfile,
            targetProfile] using
            quittingAbsorbedMassLimit_stoppingLawMixture_eq
              reward profile mover source target lambda hlambda0 hlambda1
                terminal]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      dsimp [mixedProfile, sourceProfile, targetProfile] at hmixed hsource htarget hcoalitions ⊢
      nlinarith

/-- Every player's terminal payoff is affine under another player's complete
stopping-law mixture. -/
theorem quittingTerminalPayoff_stoppingLawMixture_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer =
      (1 - lambda) * quittingTerminalPayoff reward
          (Function.update profile mover source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update profile mover target) observer := by
  rw [← quittingTerminalRewardMoment_outcomeMass reward
      (Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
          lambda hlambda0 hlambda1)),
    ← quittingTerminalRewardMoment_outcomeMass reward
      (Function.update profile mover source),
    ← quittingTerminalRewardMoment_outcomeMass reward
      (Function.update profile mover target)]
  simp only [quittingTerminalRewardMoment]
  simp_rw [quittingTerminalOutcomeMass_stoppingLawMixture_eq
    reward profile mover source target lambda hlambda0 hlambda1]
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Every player's behavioral best-response envelope is convex under a
complete stopping-law mixture of one player's prescribed strategy. -/
theorem quittingContinuationBestResponseValue_stoppingLawMixture_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer ≤
      (1 - lambda) * quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer +
        lambda * quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer := by
  by_cases hsame : observer = mover
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self]
    nlinarith
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    rintro payoff ⟨deviation, rfl⟩
    have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update profile observer deviation) mover observer
        source target lambda hlambda0 hlambda1
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (Function.update profile mover source) observer deviation
          hM hreward
    have htargetBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (Function.update profile mover target) observer deviation
          hM hreward
    have hcommuteSource :
        Function.update (Function.update profile observer deviation) mover source =
          Function.update (Function.update profile mover source) observer deviation :=
      Function.update_comm hsame deviation source profile
    have hcommuteTarget :
        Function.update (Function.update profile observer deviation) mover target =
          Function.update (Function.update profile mover target) observer deviation :=
      Function.update_comm hsame deviation target profile
    have hcommuteMixed :
        Function.update (Function.update profile observer deviation) mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1) =
          Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1)) observer deviation :=
      Function.update_comm hsame deviation
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
          lambda hlambda0 hlambda1) profile
    rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at haffine
    change quittingTerminalPayoff reward
        (Function.update
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer deviation) observer ≤ _
    rw [haffine]
    have hweightSource : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
    exact add_le_add
      (mul_le_mul_of_nonneg_left hsourceBound hweightSource)
      (mul_le_mul_of_nonneg_left htargetBound hlambda0)

/-- Full coordinatewise debt convexity.  A complete stopping-law mixture
cannot create any player's semantic debt above the chord between the two
endpoint profiles. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer +
        lambda * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer := by
  have henvelope :=
    quittingContinuationBestResponseValue_stoppingLawMixture_le
      reward profile mover observer source target lambda hlambda0 hlambda1
        hM hreward
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0 hlambda1
  dsimp only [quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] at henvelope hpayoff ⊢
  linarith

/-- The moved player's debt coordinate is exactly affine, because its
best-response envelope depends only on its fixed opponents. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) mover =
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) mover +
        lambda * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) mover := by
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover mover source target lambda hlambda0 hlambda1
  dsimp only [quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair]
  rw [show quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) mover =
      quittingContinuationBestResponseValue reward profile mover by
        exact quittingContinuationBestResponseValue_update_self _ _ _ _,
    show quittingContinuationBestResponseValue reward
        (Function.update profile mover source) mover =
      quittingContinuationBestResponseValue reward profile mover by
        exact quittingContinuationBestResponseValue_update_self _ _ _ _,
    show quittingContinuationBestResponseValue reward
        (Function.update profile mover target) mover =
      quittingContinuationBestResponseValue reward profile mover by
        exact quittingContinuationBestResponseValue_update_self _ _ _ _]
  linarith

end GameTheory
