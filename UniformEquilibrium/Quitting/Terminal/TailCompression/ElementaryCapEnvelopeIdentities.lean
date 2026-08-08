/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Strategic identities for elementary quitting-tail caps

The sure-solo and Never caps differ only in the owner's own coordinate.
Consequently they present exactly the same opponents to that owner, and hence
have identical literal behavioral best-response envelopes.  This elementary
identity is the strategic reduction used in the unique-positive-deleted-clock
branch of terminal-tail compression.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Updating the sure-solo cap in its owner's coordinate produces the same
root word as updating the Never cap by the same hazard. -/
theorem quittingRootSequenceUpdate_elementarySureSolo_eq_never
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (owner : ι)
    (hazard : ℕ → PMF Bool) :
    quittingRootSequenceUpdate
        (quittingElementaryTailRoots roots cutoff (.sureSolo owner))
        owner hazard =
      quittingRootSequenceUpdate
        (quittingElementaryTailRoots roots cutoff (.never)) owner hazard := by
  funext time player
  unfold quittingRootSequenceUpdate
  by_cases hp : player = owner
  · subst player
    simp
  · by_cases htime : time < cutoff
    · rw [quittingElementaryTailRoots_of_lt roots (.sureSolo owner) htime,
        quittingElementaryTailRoots_of_lt roots (.never) htime]
    · have hcutoff : cutoff ≤ time := Nat.le_of_not_gt htime
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hcutoff
      rw [quittingElementaryTailRoots_add,
        quittingElementaryTailRoots_add]
      cases offset with
      | zero =>
          rw [Function.update_of_ne hp, Function.update_of_ne hp]
          exact quittingSureSoloRoot_of_ne hp
      | succ offset =>
          rw [Function.update_of_ne hp, Function.update_of_ne hp]
          rfl

/-- The owner sees exactly the same all-behavior deviation problem under a
sure-solo cap as under the Never cap. -/
theorem quittingRootSequenceBestResponseValue_elementarySureSolo_owner_eq_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) (owner : ι) :
    quittingRootSequenceBestResponseValue reward
        (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) owner =
      quittingRootSequenceBestResponseValue reward
        (quittingElementaryTailRoots roots cutoff (.never)) owner := by
  unfold quittingRootSequenceBestResponseValue
    quittingContinuationBestResponseValue
  have hpay : (fun deviation : (quittingGame reward).BehaviorStrategy owner =>
      quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) 0)
          owner deviation) owner) =
      (fun deviation : (quittingGame reward).BehaviorStrategy owner =>
      quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward
          (quittingElementaryTailRoots roots cutoff (.never)) 0)
          owner deviation) owner) := by
    funext deviation
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero,
        quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    unfold quittingRootSequenceHazardTerminalValue
    rw [quittingRootSequenceUpdate_elementarySureSolo_eq_never]
  rw [hpay]

/-! ## Sure-solo prefix estimates away from the owner -/

/-- Prescribed values of a sure-solo capped prefix have the ordinary joint
survival error bound. -/
theorem abs_quittingRootSequenceTerminalValue_sub_elementarySureSolo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who 0| ≤
      2 * M * quittingJointSurvivalWeight roots 0 cutoff := by
  simpa using
    (abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq
      reward roots
        (quittingElementaryTailRoots roots cutoff (.sureSolo owner))
      who cutoff hM hreward fun time htime =>
        (quittingElementaryTailRoots_of_lt roots (.sureSolo owner) htime).symm)

/-- Every non-owner envelope has the standard deleted-clock prefix bound.
For the owner, the exact identity above is the sharper route. -/
theorem abs_quittingRootSequenceBestResponseValue_sub_elementarySureSolo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingElementaryTailRoots roots cutoff (.sureSolo owner)) who| ≤
      2 * M * quittingOpponentSurvivalWeight roots who 0 cutoff := by
  simpa using
    (abs_quittingRootSequenceBestResponseValue_sub_le_of_prefix_eq
      reward roots
        (quittingElementaryTailRoots roots cutoff (.sureSolo owner))
      who cutoff hM hreward fun time htime =>
        (quittingElementaryTailRoots_of_lt roots (.sureSolo owner) htime).symm)

end GameTheory
