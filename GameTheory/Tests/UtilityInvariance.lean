/-
# Utility-invariance hostile fixture

A one-player binary choice separates the positivity theorem from the false
claim that arbitrary affine rescaling preserves incentives.
-/

import GameTheory.Core.UtilityInvariance

noncomputable section

namespace GameTheory.Tests.UtilityInvariance

open GameTheory Probability

/-- The sole player chooses the observed Boolean outcome. -/
@[reducible]
def binaryChoice : GameForm Unit where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Bool }
  play profile := FinDist.pure (profile ())

@[simp]
theorem binaryChoice_play (profile : Profile binaryChoice.sig) :
    binaryChoice.play profile = FinDist.pure (profile ()) :=
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
  cases replacement <;>
    simp [binaryChoice, binaryChoiceUtility, chooses, expectedUtility]

/-- The high-payoff action is also dominant. -/
theorem true_isDominant :
    IsDominant binaryChoice (euPreference binaryChoiceUtility) () true := by
  intro alternative profile
  cases alternative <;>
    norm_num [euPreference_apply, binaryChoiceUtility]

/-- A genuinely nontrivial positive affine change preserves the Nash witness. -/
theorem chooses_true_isNash_positiveAffine :
    IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => 3) (fun _ => 7)))
      (chooses true) :=
  (isNash_affine binaryChoiceUtility (fun _ => 3) (fun _ => 7)
    (fun _ => by norm_num) (chooses true)).1 chooses_true_isNash

/-- The same affine change preserves the dominant-strategy witness. -/
theorem true_isDominant_positiveAffine :
    IsDominant binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => 3) (fun _ => 7)))
      () true :=
  (isDominant_affine binaryChoiceUtility (fun _ => 3) (fun _ => 7)
    (F := binaryChoice) (fun _ => by norm_num) () true).1 true_isDominant

/-- Positivity is essential: multiplying by `-1` destroys the original Nash
profile. -/
theorem chooses_true_not_isNash_negativeScale :
    ¬ IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)))
      (chooses true) := by
  intro hnash
  have h := (isNash_iff (chooses true)).1 hnash () false
  simp [euPreference_apply] at h
  norm_num [binaryChoiceUtility, affineUtility] at h

/-- Under the negative scale the low original payoff becomes the Nash action,
so the hostile case exhibits an actual incentive reversal. -/
theorem chooses_false_isNash_negativeScale :
    IsNash binaryChoice
      (euPreference (affineUtility binaryChoiceUtility (fun _ => -1) (fun _ => 0)))
      (chooses false) := by
  rw [isNash_iff]
  intro who replacement
  rcases who with ⟨⟩
  cases replacement <;>
    norm_num [euPreference_apply, binaryChoiceUtility, affineUtility]

end GameTheory.Tests.UtilityInvariance
