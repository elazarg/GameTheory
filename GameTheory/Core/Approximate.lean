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
        UtilityHasExpectation utility who (F.play profile) ∧
          UtilityHasExpectation utility who
            (F.play (Profile.update profile who replacement)) ∧
            extendedExpectedUtility utility who
                (F.play (Profile.update profile who replacement)) ≤
              extendedExpectedUtility utility who (F.play profile) + ε := by
  rw [IsεNash, isNash_iff]
  rfl

/-- Approximate Nash is invariant under a profile equivalence that reflects
unilateral updates in both directions and preserves every player's extended
expected utility. -/
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
    (hasExpectation_iff :
      ∀ (targetProfile : Profile target.sig) (who : ι),
        UtilityHasExpectation targetUtility who (target.play targetProfile) ↔
          UtilityHasExpectation sourceUtility who
            (source.play (profileEquiv.symm targetProfile)))
    (extendedExpectedUtility_eq :
      ∀ (targetProfile : Profile target.sig) (who : ι),
        extendedExpectedUtility targetUtility who (target.play targetProfile) =
          extendedExpectedUtility sourceUtility who
            (source.play (profileEquiv.symm targetProfile)))
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (profileEquiv profile) ↔
      IsεNash source sourceUtility ε profile := by
  have hexpectation : ∀ sourceProfile who,
      UtilityHasExpectation targetUtility who (target.play (profileEquiv sourceProfile)) ↔
        UtilityHasExpectation sourceUtility who (source.play sourceProfile) := by
    intro sourceProfile who
    simpa using hasExpectation_iff (profileEquiv sourceProfile) who
  have hvalue : ∀ sourceProfile who,
      extendedExpectedUtility targetUtility who (target.play (profileEquiv sourceProfile)) =
        extendedExpectedUtility sourceUtility who (source.play sourceProfile) := by
    intro sourceProfile who
    simpa using extendedExpectedUtility_eq (profileEquiv sourceProfile) who
  rw [isεNash_iff, isεNash_iff]
  constructor
  · intro htarget who replacement
    obtain ⟨targetReplacement, hupdate⟩ := hforward profile who replacement
    obtain ⟨hbase, halternative, hle⟩ := htarget who targetReplacement
    rw [← hupdate] at halternative hle
    rw [hvalue, hvalue] at hle
    exact ⟨(hexpectation _ _).1 hbase, (hexpectation _ _).1 halternative, hle⟩
  · intro hsource who targetReplacement
    obtain ⟨replacement, hupdate⟩ := hbackward profile who targetReplacement
    obtain ⟨hbase, halternative, hle⟩ := hsource who replacement
    rw [← hupdate, hvalue, hvalue]
    exact ⟨(hexpectation _ _).2 hbase, (hexpectation _ _).2 halternative, hle⟩

/-- Every Nash equilibrium is an `ε`-Nash equilibrium when `ε` is nonnegative. -/
theorem IsεNash.of_isNash {profile : Profile F.sig}
    (hN : IsNash F (euPreference utility) profile) {ε : ℝ} (hε : 0 ≤ ε) :
    IsεNash F utility ε profile := by
  rw [isεNash_iff]
  intro who replacement
  rcases (isNash_iff profile).1 hN who replacement with
    ⟨hpreferred, halternative, hle⟩
  exact ⟨hpreferred, halternative,
    hle.trans (le_add_of_nonneg_right (EReal.coe_nonneg.2 hε))⟩

/-- Zero slack recovers exactly ordinary expected-utility Nash. -/
theorem isNash_iff_isεNash_zero {profile : Profile F.sig} :
    IsNash F (euPreference utility) profile ↔ IsεNash F utility 0 profile := by
  rw [isεNash_iff, isNash_iff]
  simp only [EReal.coe_zero, add_zero]
  rfl

/-- Relaxing the error bound preserves approximate Nash. -/
theorem IsεNash.mono {profile : Profile F.sig} {ε₁ ε₂ : ℝ}
    (h : IsεNash F utility ε₁ profile) (hle : ε₁ ≤ ε₂) :
    IsεNash F utility ε₂ profile := by
  rw [isεNash_iff] at h ⊢
  intro who replacement
  rcases h who replacement with ⟨hpreferred, halternative, hvalue⟩
  exact ⟨hpreferred, halternative,
    hvalue.trans (add_le_add_right (EReal.coe_le_coe_iff.2 hle) _)⟩

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
  have hslack : extendedExpectedUtility utility who (F.play profile) ≤
      extendedExpectedUtility utility who (F.play profile) + ε :=
    le_add_of_nonneg_right (EReal.coe_nonneg.2 hε)
  obtain ⟨hbase, hstrict⟩ := h who
  by_cases hsame : replacement = profile who
  · subst replacement
    rw [Profile.update_eq_self]
    exact ⟨hbase, hbase, hslack⟩
  · obtain ⟨hdev, hlt⟩ := hstrict replacement hsame
    exact ⟨hbase, hdev, hlt.le.trans hslack⟩

end GameTheory
