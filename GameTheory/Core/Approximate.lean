/-
# Approximate expected-utility equilibrium

`IsεNash` is not a second equilibrium engine: it is ordinary `IsNash` for
the expected-utility preference relaxed by an additive slack.  Keeping that
relationship transparent lets every generic Nash theorem continue to apply.
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo usSource uoSource usTarget uoTarget

variable {ι : Type uι}

variable [DecidableEq ι] (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)

/-- An `ε`-Nash equilibrium is ordinary Nash for the expected-utility
preference relaxed by `ε`. -/
def IsεNash (ε : ℝ) (profile : Profile F.sig) : Prop :=
  IsNash F (euPreferenceWithin ε utility) profile

/-- An `ε`-best response is an ordinary best response for the same relaxed
expected-utility preference. -/
def IsεBestResponse (ε : ℝ) (who : ι) (opponents : Profile F.sig)
    (candidate : F.sig.Strategy who) : Prop :=
  IsBestResponse F (euPreferenceWithin ε utility) who opponents candidate

theorem isεNash_iff {ε : ℝ} {profile : Profile F.sig} :
    IsεNash F utility ε profile ↔
      ∀ who replacement,
        expectedUtility utility who (F.play (Profile.update profile who replacement)) ≤
          expectedUtility utility who (F.play profile) + ε := by
  rw [IsεNash, isNash_iff]
  rfl

/-- Approximate Nash is invariant under a profile equivalence that reflects
unilateral updates in both directions and preserves every player's expected
utility. -/
theorem isεNash_iff_of_profileEquiv_of_expectedUtility_eq
    (source : GameForm.{uι, usSource, uoSource} ι)
    (target : GameForm.{uι, usTarget, uoTarget} ι)
    (sourceUtility : source.sig.Outcome → ι → ℝ)
    (targetUtility : target.sig.Outcome → ι → ℝ)
    (profileEquiv : Profile source.sig ≃ Profile target.sig)
    (hforward :
      ∀ (sourceProfile : Profile source.sig) (who : ι)
        (replacement : source.sig.Strategy who),
        ∃ targetReplacement : target.sig.Strategy who,
          profileEquiv (Profile.update sourceProfile who replacement) =
            Profile.update (profileEquiv sourceProfile) who targetReplacement)
    (hbackward :
      ∀ (sourceProfile : Profile source.sig) (who : ι)
        (targetReplacement : target.sig.Strategy who),
        ∃ replacement : source.sig.Strategy who,
          profileEquiv (Profile.update sourceProfile who replacement) =
            Profile.update (profileEquiv sourceProfile) who targetReplacement)
    (expectedUtility_eq :
      ∀ (targetProfile : Profile target.sig) (who : ι),
        expectedUtility targetUtility who (target.play targetProfile) =
          expectedUtility sourceUtility who
            (source.play (profileEquiv.symm targetProfile)))
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (profileEquiv profile) ↔
      IsεNash source sourceUtility ε profile := by
  have expectedUtility_apply
      (sourceProfile : Profile source.sig) (who : ι) :
      expectedUtility targetUtility who
          (target.play (profileEquiv sourceProfile)) =
        expectedUtility sourceUtility who (source.play sourceProfile) := by
    simpa using expectedUtility_eq (profileEquiv sourceProfile) who
  rw [isεNash_iff, isεNash_iff]
  constructor
  · intro htarget who replacement
    obtain ⟨targetReplacement, hupdate⟩ :=
      hforward profile who replacement
    calc
      expectedUtility sourceUtility who
          (source.play (Profile.update profile who replacement)) =
          expectedUtility targetUtility who
            (target.play
              (profileEquiv (Profile.update profile who replacement))) :=
        (expectedUtility_apply (Profile.update profile who replacement) who).symm
      _ = expectedUtility targetUtility who
          (target.play
            (Profile.update (profileEquiv profile) who targetReplacement)) := by
        rw [hupdate]
      _ ≤ expectedUtility targetUtility who
          (target.play (profileEquiv profile)) + ε :=
        htarget who targetReplacement
      _ = expectedUtility sourceUtility who (source.play profile) + ε := by
        rw [expectedUtility_apply profile who]
  · intro hsource who targetReplacement
    obtain ⟨replacement, hupdate⟩ :=
      hbackward profile who targetReplacement
    calc
      expectedUtility targetUtility who
          (target.play
            (Profile.update (profileEquiv profile) who targetReplacement)) =
          expectedUtility targetUtility who
            (target.play
              (profileEquiv (Profile.update profile who replacement))) := by
        rw [hupdate]
      _ = expectedUtility sourceUtility who
          (source.play (Profile.update profile who replacement)) :=
        expectedUtility_apply (Profile.update profile who replacement) who
      _ ≤ expectedUtility sourceUtility who (source.play profile) + ε :=
        hsource who replacement
      _ = expectedUtility targetUtility who
          (target.play (profileEquiv profile)) + ε := by
        rw [expectedUtility_apply profile who]

/-- Every Nash equilibrium is an `ε`-Nash equilibrium when `ε` is nonnegative. -/
theorem IsεNash.of_isNash {profile : Profile F.sig}
    (hN : IsNash F (euPreference utility) profile) {ε : ℝ} (hε : 0 ≤ ε) :
    IsεNash F utility ε profile := by
  rw [isεNash_iff]
  intro who replacement
  have h := (isNash_iff profile).1 hN who replacement
  rw [euPreference_apply] at h
  linarith

/-- Zero slack recovers exactly ordinary expected-utility Nash. -/
theorem isNash_iff_isεNash_zero {profile : Profile F.sig} :
    IsNash F (euPreference utility) profile ↔ IsεNash F utility 0 profile := by
  constructor
  · exact fun h => IsεNash.of_isNash F utility h le_rfl
  · intro h
    rw [isNash_iff]
    intro who replacement
    have h' := (isεNash_iff F utility).1 h who replacement
    simpa [euPreference_apply] using h'

/-- Relaxing the error bound preserves approximate Nash. -/
theorem IsεNash.mono {profile : Profile F.sig} {ε₁ ε₂ : ℝ}
    (h : IsεNash F utility ε₁ profile) (hle : ε₁ ≤ ε₂) :
    IsεNash F utility ε₂ profile := by
  rw [isεNash_iff] at h ⊢
  intro who replacement
  linarith [h who replacement]

/-- Approximate Nash is mutual approximate best response. -/
theorem isεNash_iff_εBestResponse {ε : ℝ} {profile : Profile F.sig} :
    IsεNash F utility ε profile ↔
      ∀ who, IsεBestResponse F utility ε who profile (profile who) := by
  exact isNash_iff_isBestResponse (F := F) (weaklyPrefers := euPreferenceWithin ε utility) profile

/-- Strict expected-utility Nash is `ε`-Nash for every nonnegative `ε`. -/
theorem IsStrictNash.isεNash {profile : Profile F.sig} (h : IsStrictNash F utility profile)
    {ε : ℝ} (hε : 0 ≤ ε) : IsεNash F utility ε profile := by
  rw [isεNash_iff]
  intro who replacement
  by_cases hsame : replacement = profile who
  · subst replacement
    simp [Profile.update_eq_self, hε]
  · have hlt := h who replacement hsame
    linarith

end GameTheory
