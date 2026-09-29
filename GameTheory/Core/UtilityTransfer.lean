/- Copyright (c) 2026 GameTheory contributors. All rights reserved. -/

import GameTheory.Core.CoalitionEquilibrium

/-! # Strategic transfer from profile-local utility bounds

The hypotheses concern only honest and considered deviation laws. Uniform
certificates are an explicit additional import, `GameTheory.Core.UtilitySimulation`.
-/

noncomputable section

namespace GameTheory.GameForm

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

/-- Profile-local utility coverage transfers approximate Nash. Each target
unilateral deviation needs an expectation only when its source comparison has
one. -/
theorem isεNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who
      (_ : UtilityHasExpectation sourceUtility who (source.play profile)),
      UtilityHasExpectation targetUtility who (target.play targetProfile) ∧
        extendedExpectedUtility targetUtility who (target.play targetProfile) =
          extendedExpectedUtility sourceUtility who (source.play profile))
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        UtilityHasExpectation sourceUtility who
            (source.play (Profile.update profile who alternative)) →
          UtilityHasExpectation targetUtility who
              (target.play (Profile.update targetProfile who replacement)) ∧
            extendedExpectedUtility targetUtility who
                (target.play (Profile.update targetProfile who replacement)) ≤
              extendedExpectedUtility sourceUtility who
                (source.play (Profile.update profile who alternative)))
    (ε : ℝ) (h : IsεNash source sourceUtility ε profile) :
    IsεNash target targetUtility ε targetProfile := by
  rw [isεNash_iff] at h ⊢
  intro who replacement
  obtain ⟨alternative, hbound⟩ := deviationBound who replacement
  obtain ⟨hsbase, hsdev, hsource⟩ := h who alternative
  obtain ⟨htbase, hhonest⟩ := honestUtility who hsbase
  obtain ⟨htdev, htarget⟩ := hbound hsdev
  refine ⟨htbase, htdev, ?_⟩
  calc
    _ ≤ extendedExpectedUtility sourceUtility who
        (source.play (Profile.update profile who alternative)) := htarget
    _ ≤ extendedExpectedUtility sourceUtility who (source.play profile) + ε := hsource
    _ = extendedExpectedUtility targetUtility who (target.play targetProfile) + ε := by
      rw [hhonest]

/-- Exact Nash is the zero-slack instance of profile-local utility coverage. -/
theorem isNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who
      (_ : UtilityHasExpectation sourceUtility who (source.play profile)),
      UtilityHasExpectation targetUtility who (target.play targetProfile) ∧
        extendedExpectedUtility targetUtility who (target.play targetProfile) =
          extendedExpectedUtility sourceUtility who (source.play profile))
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        UtilityHasExpectation sourceUtility who
            (source.play (Profile.update profile who alternative)) →
          UtilityHasExpectation targetUtility who
              (target.play (Profile.update targetProfile who replacement)) ∧
            extendedExpectedUtility targetUtility who
                (target.play (Profile.update targetProfile who replacement)) ≤
              extendedExpectedUtility sourceUtility who
                (source.play (Profile.update profile who alternative)))
    (h : IsNash source (euPreference sourceUtility) profile) :
    IsNash target (euPreference targetUtility) targetProfile := by
  rw [isNash_iff_isεNash_zero] at h ⊢
  exact isεNash_of_deviation_bounds profile targetProfile honestUtility deviationBound 0 h

/-- Honest expectations and value agreement reflect selected-coalition
approximate equilibrium from a compiled profile. -/
theorem isεGroupNash_of_compileProfile
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestExpectation : ∀ profile who,
      UtilityHasExpectation targetUtility who
          (target.play (Profile.map compileStrategy profile)) ↔
        UtilityHasExpectation sourceUtility who (source.play profile))
    (honestUtility : ∀ profile who
      (_ : UtilityHasExpectation targetUtility who
        (target.play (Profile.map compileStrategy profile)))
      (_ : UtilityHasExpectation sourceUtility who (source.play profile)),
      extendedExpectedUtility targetUtility who
          (target.play (Profile.map compileStrategy profile)) =
        extendedExpectedUtility sourceUtility who (source.play profile))
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile source.sig)
    (h : IsεGroupNash target targetUtility groups ε
      (Profile.map compileStrategy profile)) :
    IsεGroupNash source sourceUtility groups ε profile := by
  rw [isεGroupNash_iff] at h ⊢
  intro members hmembers hne replacement
  obtain ⟨member, hmember, htbase, htdev, hbound⟩ :=
    h members hmembers hne (fun i => compileStrategy i.1 (replacement i))
  have hmap := Profile.map_override compileStrategy members replacement profile
  have htdev' : UtilityHasExpectation targetUtility member
      (target.play (Profile.map compileStrategy
        (Profile.override members replacement profile))) := by
    simpa only [hmap] using htdev
  have hsbase := (honestExpectation profile member).mp htbase
  have hsdev := (honestExpectation
    (Profile.override members replacement profile) member).mp htdev'
  refine ⟨member, hmember, hsbase, hsdev, ?_⟩
  have hvalue := honestUtility (Profile.override members replacement profile)
    member htdev' hsdev
  have hbase := honestUtility profile member htbase hsbase
  calc
    extendedExpectedUtility sourceUtility member
        (source.play (Profile.override members replacement profile)) =
      extendedExpectedUtility targetUtility member
        (target.play (Profile.map compileStrategy
          (Profile.override members replacement profile))) := hvalue.symm
    _ = extendedExpectedUtility targetUtility member
        (target.play (Profile.override members
          (fun i => compileStrategy i.1 (replacement i))
          (Profile.map compileStrategy profile))) := by
      apply extendedExpectedUtility_congr_law
      exact congrArg target.play hmap
    _ ≤ extendedExpectedUtility targetUtility member
        (target.play (Profile.map compileStrategy profile)) + ε :=
      hbound
    _ = extendedExpectedUtility sourceUtility member (source.play profile) + ε := by
      rw [hbase]

/-- Honest value equality and one source replacement per target coalition
give the same additive error on both sides. -/
theorem isεGroupNash_compileProfile_iff_of_utility_bounds
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestExpectation : ∀ profile who,
      UtilityHasExpectation targetUtility who
          (target.play (Profile.map compileStrategy profile)) ↔
        UtilityHasExpectation sourceUtility who (source.play profile))
    (honestUtility : ∀ profile who
      (_ : UtilityHasExpectation targetUtility who
        (target.play (Profile.map compileStrategy profile)))
      (_ : UtilityHasExpectation sourceUtility who (source.play profile)),
      extendedExpectedUtility targetUtility who
          (target.play (Profile.map compileStrategy profile)) =
        extendedExpectedUtility sourceUtility who (source.play profile))
    (groups : Set (Finset Player)) (profile : Profile source.sig)
    (deviationBound : ∀ members ∈ groups,
      ∀ replacement : Subprofile target.sig members,
      ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
        UtilityHasExpectation sourceUtility member
            (source.play (Profile.override members alternative profile)) →
          UtilityHasExpectation targetUtility member
              (target.play (Profile.override members replacement
                (Profile.map compileStrategy profile))) ∧
            extendedExpectedUtility targetUtility member
                (target.play (Profile.override members replacement
                  (Profile.map compileStrategy profile))) ≤
              extendedExpectedUtility sourceUtility member
                (source.play (Profile.override members alternative profile)))
    (ε : ℝ) :
    IsεGroupNash target targetUtility groups ε
        (Profile.map compileStrategy profile) ↔
      IsεGroupNash source sourceUtility groups ε profile := by
  constructor
  · exact isεGroupNash_of_compileProfile compileStrategy honestExpectation
      honestUtility groups ε profile
  · rw [isεGroupNash_iff, isεGroupNash_iff]
    intro h members hmembers hne replacement
    obtain ⟨alternative, hbound⟩ := deviationBound members hmembers replacement
    obtain ⟨member, hmember, hsbase, hsdev, hsource⟩ :=
      h members hmembers hne alternative
    obtain ⟨htdev, htarget⟩ := hbound member hmember hsdev
    have htbase := (honestExpectation profile member).mpr hsbase
    refine ⟨member, hmember, htbase, htdev, ?_⟩
    calc
      _ ≤ extendedExpectedUtility sourceUtility member
          (source.play (Profile.override members alternative profile)) := htarget
      _ ≤ extendedExpectedUtility sourceUtility member (source.play profile) + ε := hsource
      _ = extendedExpectedUtility targetUtility member
          (target.play (Profile.map compileStrategy profile)) + ε := by
        rw [honestUtility profile member htbase hsbase]

end GameTheory.GameForm
