/-
# Groves mechanisms beyond auctions

This public-choice fixture has no bid or winner semantics.  It exercises the
general Groves API on an efficient binary decision, proves truthful reporting
both directly and through the canonical DSIC bridge, and rejects a reversed
allocation rule that is not efficient.
-/

import GameTheory.Mechanism.Groves

noncomputable section

namespace GameTheory.Tests.Groves

open GameTheory Mechanism

/-- Player `false` has twice the public-choice value of player `true`. -/
def playerWeight (who : Bool) : ℝ :=
  if who then 1 else 2

/-- A player values exactly the public decision matching their report. -/
def reportedValue (who report outcome : Bool) : ℝ :=
  if outcome = report then playerWeight who else 0

/-- The efficient public decision follows the higher-weight player's report.
The offset may depend on the other player's report, but not on one's own. -/
def publicChoice : GrovesSetup Bool where
  Θ _ := Bool
  Outcome := Bool
  val := reportedValue
  alloc reports := reports false
  h who reports := if who then (if reports false then 1 else 0)
    else (if reports true then 1 else 0)

theorem publicChoice_isEfficient : publicChoice.IsEfficient := by
  intro reports outcome
  cases hfalse : reports false <;>
    cases htrue : reports true <;>
      cases outcome
  all_goals
    simp only [Fintype.sum_bool]
    dsimp only [publicChoice, reportedValue, playerWeight]
    norm_num [hfalse, htrue]

theorem publicChoice_offset_independent :
    ∀ (who : Bool) (reports : publicChoice.ReportProfile)
      (replacement : publicChoice.Θ who),
      publicChoice.h who (Profile.update reports who replacement) =
        publicChoice.h who reports := by
  intro who reports replacement
  cases who <;> simp [publicChoice, Profile.update_of_ne]

/-- The general theorem yields ex-post Nash truthfulness without auction data. -/
theorem publicChoice_truthful_isExPostNash :
    ∀ trueTypes : publicChoice.ReportProfile,
      IsNash (publicChoice.toUtilityGame trueTypes).form
        (euPreference (publicChoice.toUtilityGame trueTypes).utility) trueTypes :=
  publicChoice.truthfulStrategy_isExPostNash publicChoice_isEfficient
    publicChoice_offset_independent

/-- The same public-choice mechanism consumes the canonical DSIC interface. -/
theorem publicChoice_isDSIC :
    publicChoice.toQuasiLinearMechanism.IsDSIC :=
  publicChoice.toQuasiLinearMechanism_isDSIC publicChoice_isEfficient
    publicChoice_offset_independent

/-- Truth is strictly better for the high-weight player in a conflicting
profile, so this is not merely a constant-allocation truthfulness witness. -/
theorem truthful_strictly_better_for_high_weight_player :
    publicChoice.trueUtility false true
        (Profile.update (fun _ => false) false false) <
      publicChoice.trueUtility false true
        (Profile.update (fun _ => false) false true) := by
  simp only [GrovesSetup.trueUtility, GrovesSetup.grovesPayment]
  dsimp only [publicChoice, reportedValue, playerWeight]
  norm_num [Profile.update_same, Profile.update_of_ne]

/-- Reversing the public decision fails the exact efficiency premise used by
the Groves truthfulness theorem. -/
def reversedPublicChoice : GrovesSetup Bool where
  Θ _ := Bool
  Outcome := Bool
  val := reportedValue
  alloc reports := !(reports false)
  h := publicChoice.h

theorem reversedPublicChoice_not_efficient :
    ¬ reversedPublicChoice.IsEfficient := by
  intro efficient
  have impossible := efficient (fun _ => false) false
  simp only [Fintype.sum_bool] at impossible
  dsimp only [reversedPublicChoice, reportedValue, playerWeight] at impossible
  norm_num at impossible

end GameTheory.Tests.Groves
