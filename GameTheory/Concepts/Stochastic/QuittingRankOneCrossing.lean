/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge
import GameTheory.Concepts.Stochastic.QuittingLedgerPunishClock
import Math.Probability.DecisionVariationMaximalInequality

/-!
# Rank-one crossing bounds for quitting plans

This file isolates the exact two-step estimate used in Case 1 of Simon's
quitting-game construction.

First, a finite adaptive decision process whose live histories force a score
crossing inherits the weak-L² maximal bound.  The statement is deliberately
agnostic about how the process is constructed; the intended game-specific
instance has the punished player's one-stage decision discrepancy as its
score and rank-one decision variation at most twice the payoff diameter.

Second, a bound on the probability that the prescribed profile reaches the
ledger trigger is converted into the deleted survival bound needed against a
player who deviates by never quitting.  The conversion is exact:

`joint survival = opponent survival * own prescribed survival`.

Thus a joint reach bound `(ε / M)^2`, together with the Case-1 fact that every
player's own prescribed survival is still at least `ε / M`, gives the required
deleted reach bound `ε / M`.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A live-event probability is bounded by the adaptive weak-L² estimate as
soon as every live history has already produced the corresponding score
crossing.  This is the exact abstract interface needed by the rank-one
quitting decision process. -/
theorem quittingSurvivalPrefix_le_of_crossingMaximalInequality
    {Ω : Type*} [Finite Ω]
    (roots : ℕ → ι → PMF Bool)
    (horizon : ℕ)
    (step : ∀ n, (Fin n → Ω) → PMF Ω)
    (score : ∀ n, (Fin n → Ω) → Ω → ℝ)
    (live : (Fin horizon → Ω) → Prop) [DecidablePred live]
    {δ ε B : ℝ}
    (hcenter : ∀ n history,
      expect (step n history) (score n history) = 0)
    (hδ : 0 ≤ δ)
    (hbalanced : ∀ n history observation,
      |score n history observation| ≤ δ)
    (hε : 0 < ε)
    (hbudget : ∀ T, expectedDecisionVariation step score T ≤ B)
    (hliveProbability :
      quittingSurvivalPrefix roots horizon =
        expect (adaptiveHistoryLaw step horizon)
          (fun history => if live history then 1 else 0))
    (hliveCrosses : ∀ history,
      live history → ε ≤ scoreRunningMaxAbs score horizon history) :
    quittingSurvivalPrefix roots horizon ≤ δ * B / ε ^ 2 := by
  rw [hliveProbability]
  calc
    expect (adaptiveHistoryLaw step horizon)
        (fun history => if live history then 1 else 0) ≤
      expect (adaptiveHistoryLaw step horizon)
        (fun history =>
          if ε ≤ scoreRunningMaxAbs score horizon history then 1 else 0) := by
      apply expect_mono
      intro history
      by_cases hlive : live history
      · rw [if_pos hlive, if_pos (hliveCrosses history hlive)]
      · rw [if_neg hlive]
        split_ifs <;> norm_num
    _ ≤ δ * B / ε ^ 2 :=
      expect_indicator_le_div_of_expectedDecisionVariation_le
        step score hcenter hδ hbalanced hε hbudget horizon

/-- Divide a joint-survival estimate by a positive lower bound on one
player's own prescribed survival. -/
theorem quittingOpponentSurvivalWeight_le_of_survivalPrefix_le_mul
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {lower upper : ℝ}
    (hlower : 0 < lower)
    (hown : lower ≤
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) cutoff)
    (hjoint : quittingSurvivalPrefix roots cutoff ≤ lower * upper) :
    quittingOpponentSurvivalWeight roots who 0 cutoff ≤ upper := by
  have hownProduct : lower ≤
      ∏ time ∈ Finset.range cutoff, (roots time who false).toReal := by
    simpa only [quittingHazardSurvival_quittingRootSequenceOwnHazard]
      using hown
  have hopponentNonneg :
      0 ≤ quittingOpponentSurvivalWeight roots who 0 cutoff :=
    quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff
  have hscaled :
      lower * quittingOpponentSurvivalWeight roots who 0 cutoff ≤
        (∏ time ∈ Finset.range cutoff,
          (roots time who false).toReal) *
            quittingOpponentSurvivalWeight roots who 0 cutoff :=
    mul_le_mul_of_nonneg_right hownProduct hopponentNonneg
  have htoJoint :
      lower * quittingOpponentSurvivalWeight roots who 0 cutoff ≤
        quittingSurvivalPrefix roots cutoff := by
    calc
      lower * quittingOpponentSurvivalWeight roots who 0 cutoff ≤
          (∏ time ∈ Finset.range cutoff,
            (roots time who false).toReal) *
              quittingOpponentSurvivalWeight roots who 0 cutoff := hscaled
      _ = quittingSurvivalPrefix roots cutoff := by
        rw [quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own]
        ring
  have htotal :
      lower * quittingOpponentSurvivalWeight roots who 0 cutoff ≤
        lower * upper := htoJoint.trans hjoint
  exact (mul_le_mul_left hlower).mp htotal

/-- Simon's Case-1 scale.  A prescribed reach probability at most
`ε² / M²`, while `who`'s own prescribed survival remains at least `ε / M`,
forces the deleted reach probability under `who`'s never-quit deviation to be
at most `ε / M`. -/
theorem quittingOpponentSurvivalWeight_le_caseOne
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hjoint : quittingSurvivalPrefix roots cutoff ≤ ε ^ 2 / M ^ 2)
    (hown : ε / M ≤
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots who) cutoff) :
    quittingOpponentSurvivalWeight roots who 0 cutoff ≤ ε / M := by
  have hscalePos : 0 < ε / M := div_pos hε hM
  apply quittingOpponentSurvivalWeight_le_of_survivalPrefix_le_mul
    roots who cutoff hscalePos hown
  calc
    quittingSurvivalPrefix roots cutoff ≤ ε ^ 2 / M ^ 2 := hjoint
    _ = (ε / M) * (ε / M) := by ring

end GameTheory
