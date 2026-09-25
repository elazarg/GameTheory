/-
# Utility-invariance hostile fixture

A one-player binary choice separates the positivity theorem from the false
claim that arbitrary affine rescaling preserves incentives.
-/

import GameTheory.Core.UtilityInvariance

noncomputable section

namespace GameTheory.Tests.UtilityInvariance

open GameTheory GameTheory.Math.Probability

/-- The sole player chooses the observed Boolean outcome. -/
@[reducible]
def binaryChoice : GameForm Unit where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Bool }
  play profile := PMF.pure (profile ())

@[simp]
theorem binaryChoice_play (profile : Profile binaryChoice.sig) :
    binaryChoice.play profile = PMF.pure (profile ()) :=
  rfl

/-- Choosing `true` yields one; choosing `false` yields zero. -/
def binaryChoiceUtility (outcome : Bool) (_ : Unit) : ℝ :=
  if outcome then 1 else 0

def chooses (choice : Bool) : Profile binaryChoice.sig :=
  fun _ => choice

@[simp]
theorem chooses_apply (choice : Bool) (who : Unit) : chooses choice who = choice :=
  rfl

/-- The high-payoff action is Nash before rescaling. -/
theorem chooses_true_isNash :
    IsNash binaryChoice (euPreference binaryChoiceUtility) (chooses true) := by
  rw [isNash_iff]
  intro who replacement
  rcases who with ⟨⟩
  cases replacement
  · simpa only [binaryChoice, chooses_apply, Profile.update_same,
      euPreference_pure_iff] using
      (show binaryChoiceUtility false () ≤ binaryChoiceUtility true () by
        simp [binaryChoiceUtility])
  · simpa only [binaryChoice, chooses_apply, Profile.update_same,
      euPreference_pure_iff] using
      (show binaryChoiceUtility true () ≤ binaryChoiceUtility true () by rfl)

/-- The high-payoff action is also dominant. -/
theorem true_isDominant :
    IsDominant binaryChoice (euPreference binaryChoiceUtility) () true := by
  intro alternative profile
  cases alternative
  · simpa only [binaryChoice, Profile.update_same, euPreference_pure_iff] using
      (show binaryChoiceUtility false () ≤ binaryChoiceUtility true () by
        simp [binaryChoiceUtility])
  · simpa only [binaryChoice, Profile.update_same, euPreference_pure_iff] using
      (show binaryChoiceUtility true () ≤ binaryChoiceUtility true () by rfl)

/-- A genuinely nontrivial positive affine change preserves the Nash witness. -/
theorem chooses_true_isNash_positiveAffine :
    IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => 3) (fun _ => 7)))
      (chooses true) :=
  (isNash_affine (F := binaryChoice) binaryChoiceUtility (fun _ => 3) (fun _ => 7)
    (fun _ => by norm_num) (chooses true)).1 chooses_true_isNash

/-- The same affine change preserves the dominant-strategy witness. -/
theorem true_isDominant_positiveAffine :
  IsDominant binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => 3) (fun _ => 7)))
      () true :=
  (isDominant_affine (F := binaryChoice) binaryChoiceUtility (fun _ => 3) (fun _ => 7)
    (fun _ => by norm_num) () true).1 true_isDominant

/-- Positivity is essential: multiplying by `-1` destroys the original Nash
profile. -/
theorem chooses_true_not_isNash_negativeScale :
    ¬ IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)))
      (chooses true) := by
  intro hnash
  have h := (isNash_iff (chooses true)).1 hnash () false
  have h' : affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
      false () ≤ affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
        true () := by
    have hpref : euPreference (affineUtility binaryChoiceUtility (fun _ => -1)
        (fun _ => 0)) () (PMF.pure true) (PMF.pure false) := by
      simpa only [binaryChoice, chooses_apply, Profile.update_same] using h
    exact (euPreference_pure_iff _ _ _ _).1 hpref
  norm_num [binaryChoiceUtility, affineUtility] at h'

/-- Under the negative scale the low original payoff becomes the Nash action,
so the hostile case exhibits an actual incentive reversal. -/
theorem chooses_false_isNash_negativeScale :
    IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)))
      (chooses false) := by
  rw [isNash_iff]
  intro who replacement
  rcases who with ⟨⟩
  cases replacement
  · simpa only [binaryChoice, chooses_apply, Profile.update_same,
      euPreference_pure_iff] using
      (show affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
          false () ≤ affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
          false () by rfl)
  · simpa only [binaryChoice, chooses_apply, Profile.update_same,
      euPreference_pure_iff] using
      (show affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
          true () ≤ affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)
          false () by norm_num [binaryChoiceUtility, affineUtility])

end GameTheory.Tests.UtilityInvariance
