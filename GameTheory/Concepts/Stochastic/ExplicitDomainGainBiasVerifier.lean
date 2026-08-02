/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ArbitraryStartUnilateralCap

/-!
# Explicit-domain gain--bias verifier

This module is a thin consumer of the arbitrary-start prescribed and
unilateral telescopes.  A prescribed bias is checked only on the declared
prescribed-closed domain, while each player's deviation bias is checked only
on that player's declared unilateral arena.  The verifier exposes both exact
endpoint formulas and one shared `O(1/T)` constant.

At a prescribed entry, the existing implication from prescribed relevance to
every owner arena makes the two halves sufficient for the public-response
enforcement ledger.  Nothing here asserts delivery on the union of owner
arenas, recurrent coverage, a converse, necessity, or obstruction extraction.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section ExplicitDomainVerifier

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- **Explicit-domain gain--bias sufficiency verifier.**

The returned constant is shared by every player, every prescribed entry,
every entry in the selected player's unilateral arena, every horizon, and
every unilateral behavior deviation.  The first two clauses retain the exact
endpoint terms; the last two clauses give their common uniform `O(1/T)`
consequence. -/
theorem exists_explicitDomainGainBiasVerifier
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (prescribedBias unilateralBias : ι → A.Config → ℝ)
    (hprescribedBias : ∀ (who : ι) (z : A.Config), R.prescribed z →
      u z who + prescribedBias who z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) (prescribedBias who))
    (hunilateralBias : ∀ (who : ι) (z : A.Config),
      R.unilateral who z → ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act))
              (unilateralBias who) ≤
          u z who + unilateralBias who z) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ (who : ι) (z : A.Config), R.prescribed z → ∀ T : ℕ,
        (∑ t ∈ Finset.range T,
            G.expectedStagePayoff (A.rebase z).phaseProfile.behaviorProfile
              (A.publicState z) t who) =
          (T : ℝ) * u z who + prescribedBias who z -
            G.expectedHistoryValue (A.rebase z).phaseProfile.behaviorProfile
              (A.publicState z)
              (fun t h => prescribedBias who
                ((A.rebase z).configAt t h)) T) ∧
      (∀ (who : ι) (z : A.Config), R.unilateral who z →
        ∀ (dev : G.BehaviorStrategy who) (T : ℕ),
          (∑ t ∈ Finset.range T,
              G.expectedStagePayoff
                (Function.update (A.rebase z).phaseProfile.behaviorProfile
                  who dev)
                (A.publicState z) t who) ≤
            (T : ℝ) * u z who + unilateralBias who z -
              G.expectedHistoryValue
                (Function.update (A.rebase z).phaseProfile.behaviorProfile
                  who dev)
                (A.publicState z)
                (fun t h => unilateralBias who
                  ((A.rebase z).configAt t h)) T) ∧
      (∀ (who : ι) (z : A.Config), R.prescribed z →
        ∀ {T : ℕ}, 0 < T →
          |G.finiteAveragePayoff (A.publicState z) T
              (A.rebase z).phaseProfile.behaviorProfile who - u z who| ≤
            M / T) ∧
      (∀ (who : ι) (z : A.Config), R.unilateral who z →
        ∀ (dev : G.BehaviorStrategy who) {T : ℕ}, 0 < T →
          G.finiteAveragePayoff (A.publicState z) T
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              who ≤ u z who + M / T) := by
  classical
  let M : ℝ := ∑ who : ι,
    (2 * A.configBound (prescribedBias who) +
      2 * A.configBound (unilateralBias who))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun who _ => by
      have hp := A.configBound_nonneg (prescribedBias who)
      have hu := A.configBound_nonneg (unilateralBias who)
      linarith
  have hprescribedLe : ∀ who : ι,
      2 * A.configBound (prescribedBias who) ≤ M := by
    intro who
    have hpick :
        2 * A.configBound (prescribedBias who) +
            2 * A.configBound (unilateralBias who) ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (f := fun player =>
          2 * A.configBound (prescribedBias player) +
            2 * A.configBound (unilateralBias player))
        (fun player _ => by
          have hp := A.configBound_nonneg (prescribedBias player)
          have hu := A.configBound_nonneg (unilateralBias player)
          linarith)
        (Finset.mem_univ who)
    have hu := A.configBound_nonneg (unilateralBias who)
    linarith
  have hunilateralLe : ∀ who : ι,
      2 * A.configBound (unilateralBias who) ≤ M := by
    intro who
    have hpick :
        2 * A.configBound (prescribedBias who) +
            2 * A.configBound (unilateralBias who) ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (f := fun player =>
          2 * A.configBound (prescribedBias player) +
            2 * A.configBound (unilateralBias player))
        (fun player _ => by
          have hp := A.configBound_nonneg (prescribedBias player)
          have hu := A.configBound_nonneg (unilateralBias player)
          linarith)
        (Finset.mem_univ who)
    have hp := A.configBound_nonneg (prescribedBias who)
    linarith
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  · intro who z hz T
    exact A.expectedCumulativePayoff_prescribed_from_eq_on
      hT0 who (prescribedBias who) (hprescribedBias who) z hz T
  · intro who z hz dev T
    exact A.expectedCumulativePayoff_update_from_le_on
      hTi who (unilateralBias who) (hunilateralBias who) z hz dev T
  · intro who z hz T hT
    have hlocal := A.abs_finiteAveragePayoff_prescribed_from_sub_le_on
      hT0 who (prescribedBias who) (hprescribedBias who) z hz hT
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hdiv := (div_le_div_iff_of_pos_right hTreal).2
      (hprescribedLe who)
    exact le_trans hlocal hdiv
  · intro who z hz dev T hT
    have hlocal := A.finiteAveragePayoff_update_from_le_on
      hTi who (unilateralBias who) (hunilateralBias who) z hz dev hT
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hdiv := (div_le_div_iff_of_pos_right hTreal).2
      (hunilateralLe who)
    linarith

end ExplicitDomainVerifier

section LedgerAdapter

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- At any prescribed entry, the explicit-domain gain--bias verifier supplies
the existing public-response enforcement ledger.  This adapter is intentionally
restricted to `R.prescribed`: only there does the region API place the entry in
every owner's unilateral arena as well. -/
theorem nonempty_publicResponseEnforcementLedgerAt_from_of_gainBiasOn
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (prescribedBias unilateralBias : ι → A.Config → ℝ)
    (hprescribedBias : ∀ (who : ι) (z : A.Config), R.prescribed z →
      u z who + prescribedBias who z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) (prescribedBias who))
    (hunilateralBias : ∀ (who : ι) (z : A.Config),
      R.unilateral who z → ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act))
              (unilateralBias who) ≤
          u z who + unilateralBias who z)
    (z : A.Config) (hz : R.prescribed z)
    {err : ℝ} (herr : 0 < err) :
    Nonempty (G.PublicResponseEnforcementLedgerAt (A.rebase z).phaseProfile
      (A.publicState z) (u z) err) := by
  classical
  obtain ⟨M, hM, -, -, hprescribed, hunilateral⟩ :=
    A.exists_explicitDomainGainBiasVerifier hT0 hTi
      prescribedBias unilateralBias hprescribedBias hunilateralBias
  have hstep : ∀ total : ℕ, max 2 ⌈M / err⌉₊ ≤ total →
      0 < total ∧ M / (total : ℝ) ≤ err := by
    intro total htotal
    have htwo : 2 ≤ total := le_trans (le_max_left _ _) htotal
    have htotalPos : 0 < total := by omega
    have htotalReal : (0 : ℝ) < total := by exact_mod_cast htotalPos
    have hceil : (⌈M / err⌉₊ : ℝ) ≤ (total : ℝ) := by
      exact_mod_cast le_trans (le_max_right 2 _) htotal
    have hMdiv : M / err ≤ (total : ℝ) :=
      le_trans (Nat.le_ceil _) hceil
    refine ⟨htotalPos, ?_⟩
    rw [div_le_iff₀ htotalReal]
    have hmul := (div_le_iff₀ herr).1 hMdiv
    linarith
  refine ⟨{
    horizon := max 2 ⌈M / err⌉₊
    lowerLoss := fun who _ h =>
      u z who - G.stageEUAt (A.rebase z).phaseProfile.behaviorProfile h who
    upperLoss := fun who _ h =>
      G.stageEUAt (A.rebase z).phaseProfile.behaviorProfile h who - u z who
    monitoringResidual := fun _ _ _ _ => 0
    continuationResidual := fun who dev _ h =>
      G.stageEUAt
        (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
        h who - u z who
    monitoringError := 0
    continuationError := err
    error_nonneg := herr.le
    horizon_ge_two := le_max_left _ _
    lower_stage := by intro i t h; linarith
    upper_stage := by intro i t h; linarith
    deviation_stage := by intro i dev t h; linarith
    lowerLoss_cesaro := ?_
    upperLoss_cesaro := ?_
    monitoringResidual_cesaro := by
      intro who dev total htotal
      simp [expectedHistoryValue]
    continuationResidual_cesaro := ?_
    deviation_budget := by linarith }⟩
  · intro who total htotal
    obtain ⟨htotalPos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_sub_stageEUAt
      (A.rebase z).phaseProfile.behaviorProfile (A.publicState z)
      who (u z who) htotalPos]
    have habs := hprescribed who z hz htotalPos
    rw [abs_le] at habs
    linarith
  · intro who total htotal
    obtain ⟨htotalPos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_stageEUAt_sub
      (A.rebase z).phaseProfile.behaviorProfile (A.publicState z)
      who (u z who) htotalPos]
    have habs := hprescribed who z hz htotalPos
    rw [abs_le] at habs
    linarith
  · intro who dev total htotal
    obtain ⟨htotalPos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_stageEUAt_sub
      (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
      (A.publicState z) who (u z who) htotalPos]
    have hdev := hunilateral who z
      (R.prescribed_unilateral who z hz) dev htotalPos
    linarith

end LedgerAdapter

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
