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
        ∃ hpreferred : UtilityIntegrable utility who (F.play profile),
          ∃ halternative : UtilityIntegrable utility who
            (F.play (Profile.update profile who replacement)),
            expectedUtility utility who
                (F.play (Profile.update profile who replacement)) halternative ≤
              expectedUtility utility who (F.play profile) hpreferred + ε := by
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
    (integrable_iff :
      ∀ (targetProfile : Profile target.sig) (who : ι),
        UtilityIntegrable targetUtility who (target.play targetProfile) ↔
          UtilityIntegrable sourceUtility who
            (source.play (profileEquiv.symm targetProfile)))
    (expectedUtility_eq :
      ∀ (targetProfile : Profile target.sig) (who : ι)
        (htarget : UtilityIntegrable targetUtility who (target.play targetProfile))
        (hsource : UtilityIntegrable sourceUtility who
          (source.play (profileEquiv.symm targetProfile))),
        expectedUtility targetUtility who (target.play targetProfile) htarget =
          expectedUtility sourceUtility who
            (source.play (profileEquiv.symm targetProfile)) hsource)
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (profileEquiv profile) ↔
      IsεNash source sourceUtility ε profile := by
  rw [isεNash_iff, isεNash_iff]
  constructor
  · intro htarget who replacement
    obtain ⟨targetReplacement, hupdate⟩ :=
      hforward profile who replacement
    obtain ⟨htBase, htAlternative, hle⟩ :=
      htarget who targetReplacement
    have htMapped : UtilityIntegrable targetUtility who
        (target.play (profileEquiv (Profile.update profile who replacement))) := by
      simpa [hupdate] using htAlternative
    have hsBase : UtilityIntegrable sourceUtility who (source.play profile) := by
      simpa using (integrable_iff (profileEquiv profile) who).mp htBase
    have hsAlternative : UtilityIntegrable sourceUtility who
        (source.play (Profile.update profile who replacement)) := by
      simpa using (integrable_iff
        (profileEquiv (Profile.update profile who replacement)) who).mp htMapped
    have hsBaseAt : UtilityIntegrable sourceUtility who
        (source.play (profileEquiv.symm (profileEquiv profile))) := by
      simpa using hsBase
    have hsAlternativeAt : UtilityIntegrable sourceUtility who
        (source.play (profileEquiv.symm
          (profileEquiv (Profile.update profile who replacement)))) := by
      simpa using hsAlternative
    have hLaw : target.play (profileEquiv (Profile.update profile who replacement)) =
        target.play (Profile.update (profileEquiv profile) who targetReplacement) :=
      congrArg target.play hupdate
    refine ⟨hsBase, hsAlternative, ?_⟩
    calc
      expectedUtility sourceUtility who (source.play
          (Profile.update profile who replacement)) hsAlternative =
          expectedUtility targetUtility who (target.play
            (profileEquiv (Profile.update profile who replacement))) htMapped := by
        symm
        have hv := expectedUtility_eq
          (profileEquiv (Profile.update profile who replacement)) who
          htMapped hsAlternativeAt
        simpa using hv
      _ = expectedUtility targetUtility who
          (target.play (Profile.update (profileEquiv profile) who targetReplacement))
          htAlternative := by
        exact expectedUtility_congr_law targetUtility who hLaw htMapped htAlternative
      _ ≤ expectedUtility targetUtility who (target.play (profileEquiv profile))
          htBase + ε := hle
      _ = expectedUtility sourceUtility who (source.play profile) hsBase + ε := by
        have hv := expectedUtility_eq
          (profileEquiv profile) who htBase hsBaseAt
        simpa using hv
  · intro hsource who targetReplacement
    obtain ⟨replacement, hupdate⟩ :=
      hbackward profile who targetReplacement
    obtain ⟨hsBase, hsAlternative, hle⟩ := hsource who replacement
    have hsBaseAt : UtilityIntegrable sourceUtility who
        (source.play (profileEquiv.symm (profileEquiv profile))) := by
      simpa using hsBase
    have htBase : UtilityIntegrable targetUtility who
        (target.play (profileEquiv profile)) := by
      exact (integrable_iff (profileEquiv profile) who).mpr hsBaseAt
    have hsMapped : UtilityIntegrable sourceUtility who
        (source.play (profileEquiv.symm
          (Profile.update (profileEquiv profile) who targetReplacement))) := by
      have hinv : profileEquiv.symm
          (Profile.update (profileEquiv profile) who targetReplacement) =
            Profile.update profile who replacement := by
        apply profileEquiv.injective
        simpa using hupdate.symm
      simpa [hinv] using hsAlternative
    have htAlternative : UtilityIntegrable targetUtility who
        (target.play (Profile.update (profileEquiv profile) who targetReplacement)) := by
      exact (integrable_iff
        (Profile.update (profileEquiv profile) who targetReplacement) who).mpr hsMapped
    have hinv : profileEquiv.symm
        (Profile.update (profileEquiv profile) who targetReplacement) =
          Profile.update profile who replacement := by
      apply profileEquiv.injective
      simpa using hupdate.symm
    refine ⟨htBase, htAlternative, ?_⟩
    calc
      expectedUtility targetUtility who
          (target.play
            (Profile.update (profileEquiv profile) who targetReplacement))
            htAlternative = expectedUtility sourceUtility who
              (source.play (Profile.update profile who replacement)) hsAlternative := by
        have hv := expectedUtility_eq
          (Profile.update (profileEquiv profile) who targetReplacement) who
          htAlternative hsMapped
        have hLaw := congrArg source.play hinv
        have htransport := expectedUtility_congr_law sourceUtility who hLaw
          hsMapped hsAlternative
        exact hv.trans htransport
      _ ≤ expectedUtility sourceUtility who
          (source.play profile) hsBase + ε := by
        exact hle
      _ = expectedUtility targetUtility who
          (target.play (profileEquiv profile)) htBase + ε := by
        have hsBaseAt : UtilityIntegrable sourceUtility who
            (source.play (profileEquiv.symm (profileEquiv profile))) := by
          simpa using hsBase
        have hv := expectedUtility_eq
          (profileEquiv profile) who htBase hsBaseAt
        simpa using hv.symm

/-- Every Nash equilibrium is an `ε`-Nash equilibrium when `ε` is nonnegative. -/
theorem IsεNash.of_isNash {profile : Profile F.sig}
    (hN : IsNash F (euPreference utility) profile) {ε : ℝ} (hε : 0 ≤ ε) :
    IsεNash F utility ε profile := by
  rw [isεNash_iff]
  intro who replacement
  rcases (isNash_iff profile).1 hN who replacement with
    ⟨hpreferred, halternative, hle⟩
  exact ⟨hpreferred, halternative, by linarith⟩

/-- Zero slack recovers exactly ordinary expected-utility Nash. -/
theorem isNash_iff_isεNash_zero {profile : Profile F.sig} :
    IsNash F (euPreference utility) profile ↔ IsεNash F utility 0 profile := by
  constructor
  · exact fun h => IsεNash.of_isNash F utility h le_rfl
  · intro h
    rw [isNash_iff]
    intro who replacement
    rcases (isεNash_iff F utility).1 h who replacement with
      ⟨hpreferred, halternative, hle⟩
    exact ⟨hpreferred, halternative, by simpa using hle⟩

/-- Relaxing the error bound preserves approximate Nash. -/
theorem IsεNash.mono {profile : Profile F.sig} {ε₁ ε₂ : ℝ}
    (h : IsεNash F utility ε₁ profile) (hle : ε₁ ≤ ε₂) :
    IsεNash F utility ε₂ profile := by
  rw [isεNash_iff] at h ⊢
  intro who replacement
  rcases h who replacement with ⟨hpreferred, halternative, hle⟩
  exact ⟨hpreferred, halternative, by linarith⟩

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
    obtain ⟨hbase, hstrict⟩ := h who
    have heq : F.play (Profile.update profile who (profile who)) =
        F.play profile := by simp
    have hsame : UtilityIntegrable utility who
        (F.play (Profile.update profile who (profile who))) := by
      simpa [heq] using hbase
    refine ⟨hbase, hsame, ?_⟩
    have hv := expectedUtility_congr_law utility who heq hsame hbase
    rw [hv]
    linarith
  · obtain ⟨hbase, hstrict⟩ := h who
    obtain ⟨hdev, hlt⟩ := hstrict replacement hsame
    refine ⟨hbase, hdev, ?_⟩
    calc
      expectedUtility utility who
          (F.play (Profile.update profile who replacement)) hdev ≤
          expectedUtility utility who (F.play profile) hbase := le_of_lt hlt
      _ ≤ expectedUtility utility who (F.play profile) hbase + ε := by linarith

end GameTheory
