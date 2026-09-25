/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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
unilateral deviation needs only the integration used by its source comparison. -/
theorem isεNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who
      (hsource : UtilityIntegrable sourceUtility who (source.play profile)),
      ∃ htarget : UtilityIntegrable targetUtility who (target.play targetProfile),
        expectedUtility targetUtility who (target.play targetProfile) htarget =
          expectedUtility sourceUtility who (source.play profile) hsource)
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        ∀ hsource : UtilityIntegrable sourceUtility who
            (source.play (Profile.update profile who alternative)),
          ∃ htarget : UtilityIntegrable targetUtility who
              (target.play (Profile.update targetProfile who replacement)),
            expectedUtility targetUtility who
                (target.play (Profile.update targetProfile who replacement)) htarget ≤
              expectedUtility sourceUtility who
                (source.play (Profile.update profile who alternative)) hsource)
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
    _ ≤ expectedUtility sourceUtility who
        (source.play (Profile.update profile who alternative)) hsdev := htarget
    _ ≤ expectedUtility sourceUtility who (source.play profile) hsbase + ε := hsource
    _ = expectedUtility targetUtility who (target.play targetProfile) htbase + ε := by
      rw [hhonest]

/-- Exact Nash is the zero-slack instance of profile-local utility coverage. -/
theorem isNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who
      (hsource : UtilityIntegrable sourceUtility who (source.play profile)),
      ∃ htarget : UtilityIntegrable targetUtility who (target.play targetProfile),
        expectedUtility targetUtility who (target.play targetProfile) htarget =
          expectedUtility sourceUtility who (source.play profile) hsource)
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        ∀ hsource : UtilityIntegrable sourceUtility who
            (source.play (Profile.update profile who alternative)),
          ∃ htarget : UtilityIntegrable targetUtility who
              (target.play (Profile.update targetProfile who replacement)),
            expectedUtility targetUtility who
                (target.play (Profile.update targetProfile who replacement)) htarget ≤
              expectedUtility sourceUtility who
                (source.play (Profile.update profile who alternative)) hsource)
    (h : IsNash source (euPreference sourceUtility) profile) :
    IsNash target (euPreference targetUtility) targetProfile := by
  rw [isNash_iff_isεNash_zero] at h ⊢
  exact isεNash_of_deviation_bounds profile targetProfile honestUtility deviationBound 0 h

/-- Honest integrability and value agreement reflect selected-coalition
approximate equilibrium from a compiled profile. -/
theorem isεGroupNash_of_compileProfile
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestIntegrable : ∀ profile who,
      UtilityIntegrable targetUtility who
          (target.play (Profile.map compileStrategy profile)) ↔
        UtilityIntegrable sourceUtility who (source.play profile))
    (honestUtility : ∀ profile who
      (htarget : UtilityIntegrable targetUtility who
        (target.play (Profile.map compileStrategy profile)))
      (hsource : UtilityIntegrable sourceUtility who (source.play profile)),
      expectedUtility targetUtility who
          (target.play (Profile.map compileStrategy profile)) htarget =
        expectedUtility sourceUtility who (source.play profile) hsource)
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile source.sig)
    (h : IsεGroupNash target targetUtility groups ε
      (Profile.map compileStrategy profile)) :
    IsεGroupNash source sourceUtility groups ε profile := by
  rw [isεGroupNash_iff] at h ⊢
  intro members hmembers hne replacement
  obtain ⟨member, hmember, htbase, htdev, hbound⟩ :=
    h members hmembers hne (fun i => compileStrategy i.1 (replacement i))
  have hmap := Profile.map_override compileStrategy members replacement profile
  have htdev' : UtilityIntegrable targetUtility member
      (target.play (Profile.map compileStrategy
        (Profile.override members replacement profile))) := by
    simpa only [hmap] using htdev
  have hsbase := (honestIntegrable profile member).mp htbase
  have hsdev := (honestIntegrable
    (Profile.override members replacement profile) member).mp htdev'
  refine ⟨member, hmember, hsbase, hsdev, ?_⟩
  have hvalue := honestUtility (Profile.override members replacement profile)
    member htdev' hsdev
  have hbase := honestUtility profile member htbase hsbase
  calc
    expectedUtility sourceUtility member
        (source.play (Profile.override members replacement profile)) hsdev =
      expectedUtility targetUtility member
        (target.play (Profile.map compileStrategy
          (Profile.override members replacement profile))) htdev' := hvalue.symm
    _ = expectedUtility targetUtility member
        (target.play (Profile.override members
          (fun i => compileStrategy i.1 (replacement i))
          (Profile.map compileStrategy profile))) htdev := by
      apply expectedUtility_congr_law
      exact congrArg target.play hmap
    _ ≤ expectedUtility targetUtility member
        (target.play (Profile.map compileStrategy profile)) htbase + ε :=
      hbound
    _ = expectedUtility sourceUtility member (source.play profile) hsbase + ε := by
      rw [hbase]

/-- Guarded honest equality and one source replacement per target coalition
give the same additive error on both sides. -/
theorem isεGroupNash_compileProfile_iff_of_utility_bounds
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestIntegrable : ∀ profile who,
      UtilityIntegrable targetUtility who
          (target.play (Profile.map compileStrategy profile)) ↔
        UtilityIntegrable sourceUtility who (source.play profile))
    (honestUtility : ∀ profile who
      (htarget : UtilityIntegrable targetUtility who
        (target.play (Profile.map compileStrategy profile)))
      (hsource : UtilityIntegrable sourceUtility who (source.play profile)),
      expectedUtility targetUtility who
          (target.play (Profile.map compileStrategy profile)) htarget =
        expectedUtility sourceUtility who (source.play profile) hsource)
    (groups : Set (Finset Player)) (profile : Profile source.sig)
    (deviationBound : ∀ members ∈ groups,
      ∀ replacement : Subprofile target.sig members,
      ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
        ∀ hsource : UtilityIntegrable sourceUtility member
            (source.play (Profile.override members alternative profile)),
          ∃ htarget : UtilityIntegrable targetUtility member
              (target.play (Profile.override members replacement
                (Profile.map compileStrategy profile))),
            expectedUtility targetUtility member
                (target.play (Profile.override members replacement
                  (Profile.map compileStrategy profile))) htarget ≤
              expectedUtility sourceUtility member
                (source.play (Profile.override members alternative profile)) hsource)
    (ε : ℝ) :
    IsεGroupNash target targetUtility groups ε
        (Profile.map compileStrategy profile) ↔
      IsεGroupNash source sourceUtility groups ε profile := by
  constructor
  · exact isεGroupNash_of_compileProfile compileStrategy honestIntegrable
      honestUtility groups ε profile
  · rw [isεGroupNash_iff, isεGroupNash_iff]
    intro h members hmembers hne replacement
    obtain ⟨alternative, hbound⟩ := deviationBound members hmembers replacement
    obtain ⟨member, hmember, hsbase, hsdev, hsource⟩ :=
      h members hmembers hne alternative
    obtain ⟨htdev, htarget⟩ := hbound member hmember hsdev
    have htbase := (honestIntegrable profile member).mpr hsbase
    refine ⟨member, hmember, htbase, htdev, ?_⟩
    calc
      _ ≤ expectedUtility sourceUtility member
          (source.play (Profile.override members alternative profile)) hsdev := htarget
      _ ≤ expectedUtility sourceUtility member (source.play profile) hsbase + ε := hsource
      _ = expectedUtility targetUtility member
          (target.play (Profile.map compileStrategy profile)) htbase + ε := by
        rw [honestUtility profile member htbase hsbase]

end GameTheory.GameForm
