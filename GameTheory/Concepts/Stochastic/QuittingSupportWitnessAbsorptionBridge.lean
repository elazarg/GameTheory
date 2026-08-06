/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessIndividualRational
import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge

/-!
# Complete absorption supplies the support-survival switch

The support-witness compiler uses the first date at which one player's own
prescribed survival drops below a fixed threshold.  Simon's source hypothesis
is instead complete absorption, or equivalently vanishing joint survival.
For finitely many players these formulations are linked by the exact product
identity

`joint survival = product over players of own survival`.

Consequently, if joint survival tends to zero, every positive threshold is
crossed by at least one player's own survival at some finite date.  Combining
this observation with the support-witness clock collapse and the
individual-rational target-tail construction gives a direct terminal-Nash and
uniform-payoff compiler for completely absorbing witness-carrying paths.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Joint survival through a finite prefix is exactly the product of the
players' own prescribed survival probabilities through that prefix. -/
theorem quittingSurvivalPrefix_eq_prod_ownSurvival
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingSurvivalPrefix roots cutoff =
      ∏ who,
        quittingHazardSurvival
          (quittingRootSequenceOwnHazard roots who) cutoff := by
  classical
  unfold quittingSurvivalPrefix quittingHazardSurvival
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [Finset.prod_comm]
  simp only [quittingRootSequenceOwnHazard]

omit [DecidableEq ι] in
/-- If joint survival is strictly below `threshold ^ |ι|`, then some player's
own survival is at most `threshold`.  The strict inequality on the joint
product lets us use the ordinary monotone product bound; no cancellative
multiplicative structure on `ℝ` is needed. -/
theorem exists_ownSurvival_le_of_survivalPrefix_lt_pow
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hjoint : quittingSurvivalPrefix roots cutoff <
      threshold ^ Fintype.card ι) :
    ∃ who,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) cutoff ≤ threshold := by
  classical
  by_contra hnone
  push Not at hnone
  have hproduct :
      threshold ^ Fintype.card ι ≤
        ∏ who,
          quittingHazardSurvival
            (quittingRootSequenceOwnHazard roots who) cutoff := by
    have hlower :
        (∏ _who : ι, threshold) ≤
          ∏ who,
            quittingHazardSurvival
              (quittingRootSequenceOwnHazard roots who) cutoff := by
      apply Finset.prod_le_prod
      · intro who _
        exact hthreshold.le
      · intro who _
        exact (hnone who).le
    simpa using hlower
  rw [← quittingSurvivalPrefix_eq_prod_ownSurvival roots cutoff] at hproduct
  exact (not_lt_of_ge hproduct) hjoint

omit [DecidableEq ι] in
/-- Complete absorption forces a finite own-survival crossing at every
positive threshold. -/
theorem exists_ownSurvival_crossing_of_completelyAbsorbing
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (habsorbing : IsCompletelyAbsorbing roots) :
    ∃ cutoff, ∃ who,
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) cutoff ≤ threshold := by
  have hpow : 0 < threshold ^ Fintype.card ι :=
    pow_pos hthreshold _
  have heventually : ∀ᶠ cutoff : ℕ in atTop,
      quittingSurvivalPrefix roots cutoff <
        threshold ^ Fintype.card ι :=
    (tendsto_order.1 habsorbing).2 _ hpow
  obtain ⟨cutoff, hcutoff⟩ := heventually.exists
  obtain ⟨who, hwho⟩ :=
    exists_ownSurvival_le_of_survivalPrefix_lt_pow
      roots cutoff hthreshold hcutoff
  exact ⟨cutoff, who, hwho⟩

/-- Support-local one-stage witnesses, complete absorption, and individual
rationality at the induced global support-survival switch.  Unlike
`HasQuittingSupportWitnessIndividualRationalPackage`, no finite crossing is
supplied as separate input: complete absorption produces it. -/
def HasQuittingCompletelyAbsorbingSupportWitnessPackage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (plan : ℕ → ι → PMF Bool)
      (δ ledgerCap threshold continuationSlack : ℝ),
    0 ≤ δ ∧
    0 < ledgerCap ∧
    0 < threshold ∧
    0 < continuationSlack ∧
    δ ≤ ledgerCap * threshold ∧
    IsQuittingRootSequenceSupportApproxNash reward plan δ ∧
    IsCompletelyAbsorbing plan ∧
    (∀ target : ι,
      quittingPunishmentValue reward target ≤
        quittingRootSequenceTerminalValue reward plan target
          (quittingSupportSurvivalSwitchIndex plan threshold)) ∧
    ledgerCap + 2 * δ + continuationSlack +
        threshold * (7 * quittingRewardBound reward) ≤ ε

/-- Complete absorption discharges the explicit crossing field of the
individual-rational support-witness package. -/
theorem
    hasQuittingSupportWitnessIndividualRationalPackage_of_completelyAbsorbing
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingCompletelyAbsorbingSupportWitnessPackage reward ε) :
    HasQuittingSupportWitnessIndividualRationalPackage reward ε := by
  obtain ⟨plan, δ, ledgerCap, threshold, continuationSlack,
    hδ, hledgerCap, hthreshold, hcontinuationSlack, hscale,
    hsupport, habsorbing, hir, herror⟩ := hpackage
  refine ⟨plan, δ, ledgerCap, threshold, continuationSlack,
    hδ, hledgerCap, hthreshold, hcontinuationSlack, hscale,
    hsupport, ?_, hir, herror⟩
  exact exists_ownSurvival_crossing_of_completelyAbsorbing
    plan hthreshold habsorbing

/-- A completely absorbing support-witness package produces a terminal
approximate Nash profile against every behavioral unilateral deviation. -/
theorem
    exists_isεAsymptoticNash_of_hasQuittingCompletelyAbsorbingSupportWitnessPackage
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {ε : ℝ}
    (hpackage : HasQuittingCompletelyAbsorbingSupportWitnessPackage reward ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  exists_isεAsymptoticNash_of_hasQuittingSupportWitnessIndividualRationalPackage
    reward
      (hasQuittingSupportWitnessIndividualRationalPackage_of_completelyAbsorbing
        reward hpackage)

/-- Completely absorbing support-witness packages at every positive accuracy
imply a uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_completelyAbsorbingSupportWitnessPackage
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpackage : ∀ ε : ℝ, 0 < ε →
      HasQuittingCompletelyAbsorbingSupportWitnessPackage reward ε) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_supportWitnessIndividualRationalPackage
    reward fun ε hε =>
      hasQuittingSupportWitnessIndividualRationalPackage_of_completelyAbsorbing
        reward (hpackage ε hε)

end GameTheory
