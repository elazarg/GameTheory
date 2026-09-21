/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.CoalitionEquilibrium

/-! # Strategic transfer from profile-local utility bounds

Direct transfer and reflection theorems over the canonical equilibrium
predicates. Uniform reusable certificates are an explicit additional import,
`GameTheory.Core.UtilitySimulation`.
-/

noncomputable section

namespace GameTheory.GameForm

universe uPlayer uSource uTarget uSourceOutcome uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

/-- Profile-local utility coverage transfers approximate Nash. Only the honest
utilities at these two profiles must agree; each target deviation has a source
replacement bounding the deviating player's utility. No uniform certificate or
strategy translation is required. -/
theorem isεNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who,
      expectedUtility targetUtility who (target.play targetProfile) =
        expectedUtility sourceUtility who (source.play profile))
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        expectedUtility targetUtility who
            (target.play (Profile.update targetProfile who replacement)) ≤
          expectedUtility sourceUtility who
            (source.play (Profile.update profile who alternative)))
    (ε : ℝ) (h : IsεNash source sourceUtility ε profile) :
    IsεNash target targetUtility ε targetProfile := by
  rw [isεNash_iff] at h ⊢
  intro who replacement
  obtain ⟨alternative, hbound⟩ := deviationBound who replacement
  rw [honestUtility]
  exact hbound.trans (h who alternative)

/-- Exact Nash is the zero-slack instance of profile-local utility coverage. -/
theorem isNash_of_deviation_bounds
    (profile : Profile source.sig) (targetProfile : Profile target.sig)
    (honestUtility : ∀ who,
      expectedUtility targetUtility who (target.play targetProfile) =
        expectedUtility sourceUtility who (source.play profile))
    (deviationBound : ∀ who replacement,
      ∃ alternative : source.sig.Strategy who,
        expectedUtility targetUtility who
            (target.play (Profile.update targetProfile who replacement)) ≤
          expectedUtility sourceUtility who
            (source.play (Profile.update profile who alternative)))
    (h : IsNash source (euPreference sourceUtility) profile) :
    IsNash target (euPreference targetUtility) targetProfile := by
  rw [isNash_iff_isεNash_zero] at h ⊢
  exact isεNash_of_deviation_bounds profile targetProfile honestUtility deviationBound 0 h

/-- Honest expected-utility equality alone reflects the coalition predicate
from a compiled profile. No simulation of target deviations is needed. -/
theorem isεGroupNash_of_compileProfile
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile source.sig)
    (h : IsεGroupNash target targetUtility groups ε
      (fun player => compileStrategy player (profile player))) :
    IsεGroupNash source sourceUtility groups ε profile := by
  rw [isεGroupNash_iff] at h ⊢
  intro members hmembers hne replacement
  obtain ⟨member, hmember, hbound⟩ :=
    h members hmembers hne (fun i => compileStrategy i.1 (replacement i))
  refine ⟨member, hmember, ?_⟩
  have hmap := Profile.map_override compileStrategy members replacement profile
  unfold Profile.map at hmap
  rw [← hmap] at hbound
  simp only [expectedUtility] at hbound ⊢
  rwa [honestUtility, honestUtility] at hbound

/-- Utility equality at compiled profiles and coalition deviation bounds give
the same additive error on both sides. -/
theorem isεGroupNash_compileProfile_iff_of_utility_bounds
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (groups : Set (Finset Player)) (profile : Profile source.sig)
    (deviationBound : ∀ members ∈ groups,
      ∀ replacement : Subprofile target.sig members,
      ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
        (target.play (Profile.override members replacement
            (fun player => compileStrategy player (profile player)))).expect
            (fun outcome => targetUtility outcome member) ≤
          (source.play (Profile.override members alternative profile)).expect
            (fun outcome => sourceUtility outcome member))
    (ε : ℝ) :
    IsεGroupNash target targetUtility groups ε
        (fun player => compileStrategy player (profile player)) ↔
      IsεGroupNash source sourceUtility groups ε profile := by
  constructor
  · exact isεGroupNash_of_compileProfile compileStrategy honestUtility groups ε profile
  · rw [isεGroupNash_iff, isεGroupNash_iff]
    intro h members hmembers hne replacement
    obtain ⟨alternative, hbound⟩ := deviationBound members hmembers replacement
    obtain ⟨member, hmember, hsource⟩ := h members hmembers hne alternative
    refine ⟨member, hmember, ?_⟩
    simp only [expectedUtility] at hsource ⊢
    refine (hbound member hmember).trans (hsource.trans ?_)
    rw [honestUtility]

end GameTheory.GameForm
