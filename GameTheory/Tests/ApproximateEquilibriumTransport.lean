/-
# Approximate-equilibrium transport control

A coordinate-swapping profile equivalence preserves every player's payoff
after conjugating the target utility. It does not preserve same-player
unilateral deviations, and consequently does not preserve even zero-slack
approximate Nash equilibrium.
-/

import GameTheory.Core.Approximate

noncomputable section

namespace GameTheory.Tests.ApproximateEquilibriumTransport

open GameTheory.Math.Probability

@[reducible]
def binarySignature : GameSignature Bool where
  Strategy _ := Bool
  Outcome := Bool → Bool

def swapProfile (profile : Profile binarySignature) : Profile binarySignature :=
  fun who => profile (!who)

/-- Swapping the two player coordinates is an ordinary profile equivalence. -/
def profileEquiv : Profile binarySignature ≃ Profile binarySignature where
  toFun := swapProfile
  invFun := swapProfile
  left_inv profile := by
    funext who
    cases who <;> rfl
  right_inv profile := by
    funext who
    cases who <;> rfl

@[reducible]
def sourceForm : GameForm Bool :=
  GameForm.deterministic binarySignature fun profile => profile

@[reducible]
def targetForm : GameForm Bool := sourceForm

/-- Only player `false` values its own source coordinate. -/
def sourceUtility (outcome : binarySignature.Outcome) (who : Bool) : ℝ :=
  if who then 0 else if outcome false then 1 else 0

/-- Target payoffs are the exact conjugates of source payoffs. -/
def targetUtility (outcome : binarySignature.Outcome) (who : Bool) : ℝ :=
  sourceUtility (swapProfile outcome) who

def baseProfile : Profile binarySignature := fun _ => false

/-- Payoff conjugacy holds at every profile, not only the hostile base point. -/
theorem expectedUtility_eq (targetProfile : Profile targetForm.sig) (who : Bool) :
    expectedUtility targetUtility who (targetForm.play targetProfile) =
      expectedUtility sourceUtility who
        (sourceForm.play (profileEquiv.symm targetProfile)) := by
  simp [sourceUtility, targetUtility, profileEquiv]

/-- The conjugated target profile is zero-slack Nash. -/
theorem target_isεNash_zero :
    IsεNash targetForm targetUtility 0 (profileEquiv baseProfile) := by
  rw [isεNash_iff]
  intro who replacement
  cases who <;> cases replacement <;>
    simp [sourceUtility, targetUtility, sourceForm, targetForm, profileEquiv,
      swapProfile, baseProfile]

/-- The source base profile is not zero-slack Nash: player `false` profits by
switching its own coordinate to `true`. -/
theorem source_not_isεNash_zero :
    ¬ IsεNash sourceForm sourceUtility 0 baseProfile := by
  intro hNash
  have hdeviation :=
    (isεNash_iff sourceForm sourceUtility).1 hNash false true
  norm_num [sourceUtility, sourceForm, baseProfile] at hdeviation

/-- The exact same-player forward update-reflection witness already fails for
player `false` switching to `true`. -/
theorem no_forward_reflection_false_true :
    ¬ ∃ targetReplacement : targetForm.sig.Strategy false,
        profileEquiv (Profile.update baseProfile false true) =
          Profile.update (profileEquiv baseProfile) false targetReplacement := by
  rintro ⟨targetReplacement, hupdate⟩
  have htrue := congrFun hupdate true
  simp [profileEquiv, swapProfile, baseProfile] at htrue
  rw [Bool.not_true, Profile.update_same] at htrue
  exact Bool.noConfusion htrue

/-- Hence the universal forward-reflection premise of the transport theorem
is false for this payoff-preserving profile equivalence. -/
theorem forward_update_reflection_fails :
    ¬ (∀ (sourceProfile : Profile sourceForm.sig) (who : Bool)
        (replacement : sourceForm.sig.Strategy who),
        ∃ targetReplacement : targetForm.sig.Strategy who,
          profileEquiv (Profile.update sourceProfile who replacement) =
            Profile.update (profileEquiv sourceProfile) who targetReplacement) := by
  intro hforward
  exact no_forward_reflection_false_true (hforward baseProfile false true)

/-- Profile bijection plus exact payoff equality is insufficient without
same-player update reflection. -/
theorem payoff_conjugacy_alone_does_not_preserve_zero_nash :
    IsεNash targetForm targetUtility 0 (profileEquiv baseProfile) ∧
      ¬ IsεNash sourceForm sourceUtility 0 baseProfile :=
  ⟨target_isεNash_zero, source_not_isεNash_zero⟩

end GameTheory.Tests.ApproximateEquilibriumTransport
