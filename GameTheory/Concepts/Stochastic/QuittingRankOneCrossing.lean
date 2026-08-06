/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge
import GameTheory.Concepts.Stochastic.QuittingLedgerPunishClock
import Math.Probability.DecisionVariationMaximalInequality

/-!
# Abstract rank-one crossing alternative for quitting plans

This module records the stochastic route corresponding to Simon's Case 1
when the one-stage support witness has been forgotten.

It is intentionally abstract.  The main theorem assumes both pieces that a
game-specific rank-one decision process would have to provide:

* every live history at the proposed ledger trigger has already produced a
  score crossing; and
* the adaptive decision process has a uniform expected-variation budget.

Under those assumptions the weak-L² maximal inequality bounds the prescribed
joint probability of reaching the trigger.  A separate exact survival identity
then converts that joint bound into the deleted opponent-survival bound needed
against a never-quit deviation:

`joint survival = opponent survival * own prescribed survival`.

Thus a joint reach bound `(ε / M)^2`, together with own prescribed survival at
least `ε / M`, gives deleted reach at most `ε / M`.

No theorem in the support-witness compiler depends on this module.  Retaining
the actual support witness gives the stronger deterministic clock-collapse
argument in `QuittingSupportWitnessClockCollapse`.  Conversely, this file does
not construct Simon's rank-one decision-discrepancy process, prove its crossing
implication, or establish its variation budget; it is an abstract consumer
theorem for an alternative route where those data are available.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A live-event probability is bounded by the adaptive weak-L² estimate as
soon as every live history has already produced the corresponding score
crossing.  This is the abstract consumer interface for a possible rank-one
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
  have hlowerNe : lower ≠ 0 := ne_of_gt hlower
  calc
    quittingOpponentSurvivalWeight roots who 0 cutoff =
        lower⁻¹ *
          (lower * quittingOpponentSurvivalWeight roots who 0 cutoff) := by
            field_simp
    _ ≤ lower⁻¹ * (lower * upper) :=
      mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr hlower.le)
    _ = upper := by field_simp

/-- At Simon's Case-1 scale, joint reach at most `ε² / M²` and own survival
at least `ε / M` force deleted reach at most `ε / M`. -/
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
