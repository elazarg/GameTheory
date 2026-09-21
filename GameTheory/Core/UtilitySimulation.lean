/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.UtilityTransfer

/-! # Strategic transfer by utility bounds

Some target deviations admit a source deviation with at least as much utility,
although their outcome laws differ. The certificate is indexed by the coalitions
whose joint deviations it bounds. Honest utility equality alone reflects
equilibrium at a compiled profile; preservation needs the bound at the same
coalitions, where one source witness has to serve every member of a coalition
at once.

Singleton coalitions give approximate Nash and all nonempty coalitions give
strong Nash. These are genuinely different certificates. A target that adds a
communication channel to the source satisfies the singleton bound and refutes
the coalition bound, because one member can route private information to
another; `GameTheory.Tests.CoalitionSimulation` is that witness.

The utilities are parameters of a certificate. It transports no guarantee for
other utilities, and none for players outside the deviating coalition.
This stable opt-in leaf serves reused uniform bounds and composition. Isolated
transfers can import `Core.UtilityTransfer` without constructing a certificate.
-/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uMiddle uSourceOutcome uTargetOutcome uMiddleOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

/-- A strategy translation preserving honest expected utilities and bounding
every joint deviation of an allowed coalition by one legal source deviation.
The witness may depend on the fixed opponents and on the utilities, but a
single witness must serve every member of the coalition. -/
structure UtilitySimulation
    (source : GameForm.{uPlayer, uSource, uSourceOutcome} Player)
    (target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player)
    (sourceUtility : source.sig.Outcome → Player → ℝ)
    (targetUtility : target.sig.Outcome → Player → ℝ)
    (groups : Set (Finset Player)) where
  /-- Translate each player's source strategy into a target strategy. -/
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_utility : ∀ profile who,
    (target.play (fun player => compileStrategy player (profile player))).expect
        (fun outcome => targetUtility outcome who) =
      (source.play profile).expect (fun outcome => sourceUtility outcome who)
  deviation_bound : ∀ members ∈ groups, ∀ (profile : Profile source.sig)
      (replacement : Subprofile target.sig members),
    ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
      (target.play (Profile.override members replacement
          (fun player => compileStrategy player (profile player)))).expect
          (fun outcome => targetUtility outcome member) ≤
        (source.play (Profile.override members alternative profile)).expect
          (fun outcome => sourceUtility outcome member)

variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

namespace UtilitySimulation

variable {groups : Set (Finset Player)}

/-- Translate a complete source profile player by player. -/
def compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) : Profile target.sig :=
  Profile.map simulation.compileStrategy profile

theorem compileProfile_update
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) (who : Player) (alternative : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who alternative) =
      simulation.compileProfile (Profile.update profile who alternative) :=
  (Profile.map_update simulation.compileStrategy profile who alternative).symm

/-- The same additive error is preserved and reflected at every compiled
profile, for the coalitions the certificate covers. -/
theorem isεGroupNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (ε : ℝ) (profile : Profile source.sig) :
    IsεGroupNash target targetUtility groups ε (simulation.compileProfile profile) ↔
      IsεGroupNash source sourceUtility groups ε profile :=
  isεGroupNash_compileProfile_iff_of_utility_bounds simulation.compileStrategy
    simulation.honest_utility groups profile
    (fun members hmembers replacement =>
      simulation.deviation_bound members hmembers profile replacement) ε

/-- A certificate for the one-player coalitions transfers approximate Nash. -/
theorem isεNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (singletonGroups Player))
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (simulation.compileProfile profile) ↔
      IsεNash source sourceUtility ε profile := by
  rw [← isεGroupNash_singletonGroups_iff, ← isεGroupNash_singletonGroups_iff]
  exact simulation.isεGroupNash_compileProfile_iff ε profile

theorem isNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (singletonGroups Player))
    (profile : Profile source.sig) :
    IsNash target (euPreference targetUtility) (simulation.compileProfile profile) ↔
      IsNash source (euPreference sourceUtility) profile := by
  simpa only [isNash_iff_isεNash_zero] using simulation.isεNash_compileProfile_iff 0 profile

/-- A certificate for every nonempty coalition transfers strong Nash. -/
theorem isStrongNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (nonemptyGroups Player))
    (ε : ℝ) (profile : Profile source.sig) :
    IsStrongNash target (euPreferenceWithin ε targetUtility)
        (simulation.compileProfile profile) ↔
      IsStrongNash source (euPreferenceWithin ε sourceUtility) profile := by
  rw [← isεGroupNash_nonemptyGroups_iff, ← isεGroupNash_nonemptyGroups_iff]
  exact simulation.isεGroupNash_compileProfile_iff ε profile

/-- Strong Nash is reflected from a compiled profile by honest utilities alone,
with no coalition bound. Preservation is the direction that needs one. -/
theorem isStrongNash_of_compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (ε : ℝ) (profile : Profile source.sig)
    (h : IsStrongNash target (euPreferenceWithin ε targetUtility)
      (simulation.compileProfile profile)) :
    IsStrongNash source (euPreferenceWithin ε sourceUtility) profile := by
  rw [← isεGroupNash_nonemptyGroups_iff] at h ⊢
  exact isεGroupNash_of_compileProfile simulation.compileStrategy simulation.honest_utility
    (nonemptyGroups Player) ε profile h

/-- The one-player case of the coalition bound, in unilateral form. -/
theorem unilateral_bound
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (profile : Profile source.sig) (who : Player)
    (replacement : target.sig.Strategy who) :
    ∃ alternative : source.sig.Strategy who,
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
          (fun outcome => targetUtility outcome who) ≤
        (source.play (Profile.update profile who alternative)).expect
          (fun outcome => sourceUtility outcome who) := by
  obtain ⟨alternative, hbound⟩ := simulation.deviation_bound {who} (hsingle ⟨who, rfl⟩)
    profile (Subprofile.single who replacement)
  refine ⟨alternative ⟨who, Finset.mem_singleton_self who⟩, ?_⟩
  have hstep := hbound who (Finset.mem_singleton_self who)
  rwa [Profile.override_single, Profile.override_singleton] at hstep

/-- Compiling opponents ignores the deviator's own coordinate, which the
best-response comparison overwrites on both sides. -/
private theorem update_compileProfile_update
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) (who : Player)
    (strategy : source.sig.Strategy who) (replacement : target.sig.Strategy who) :
    Profile.update (simulation.compileProfile (Profile.update profile who strategy))
        who replacement =
      Profile.update (simulation.compileProfile profile) who replacement := by
  funext player
  by_cases h : player = who
  · subst player; simp
  · simp [compileProfile, Profile.update_of_ne, h]

/-- A source best response compiles to a best response against the compiled
opponents, now against arbitrary target deviations. Unlike the Nash transfer
this fixes one player, so the opponents need not be best responding. Target
profiles outside the compiler image are not covered. -/
theorem isBestResponse_compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (profile : Profile source.sig) (who : Player)
    (best : IsBestResponse source (euPreference sourceUtility) who profile (profile who)) :
    IsBestResponse target (euPreference targetUtility) who
      (simulation.compileProfile profile)
      (simulation.compileStrategy who (profile who)) := by
  intro replacement
  obtain ⟨alternative, hbound⟩ := simulation.unilateral_bound hsingle profile who replacement
  have hbest := best alternative
  rw [euPreference_apply, Profile.update_eq_self] at hbest
  rw [euPreference_apply, simulation.compileProfile_update profile who (profile who),
    Profile.update_eq_self]
  exact hbound.trans (hbest.trans (simulation.honest_utility profile who).symm.le)

/-- A dominant source strategy compiles to a best response against every
compiled opponent profile. Arbitrary target deviations are admitted, whereas
opponents outside the compiler image are not: this is dominance relative to the
source-expressible environments, not target dominance. -/
theorem isBestResponse_compileStrategy_of_isDominant
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (who : Player) (strategy : source.sig.Strategy who)
    (dominant : IsDominant source (euPreference sourceUtility) who strategy)
    (opponents : Profile source.sig) :
    IsBestResponse target (euPreference targetUtility) who
      (simulation.compileProfile opponents) (simulation.compileStrategy who strategy) := by
  have hown : (Profile.update opponents who strategy) who = strategy :=
    Profile.update_same opponents who strategy
  have best : IsBestResponse source (euPreference sourceUtility) who
      (Profile.update opponents who strategy)
      ((Profile.update opponents who strategy) who) := by
    intro alternative
    rw [hown]
    exact dominant alternative (Profile.update opponents who strategy)
  have transferred := simulation.isBestResponse_compileProfile hsingle
    (Profile.update opponents who strategy) who best
  rw [hown] at transferred
  intro replacement
  have hstep := transferred replacement
  simp only [simulation.update_compileProfile_update] at hstep
  exact hstep

/-- Overriding every coordinate discards the profile that was there. -/
private theorem override_univ [Fintype Player] {sig : GameSignature Player}
    (replacement profile : Profile sig) :
    Profile.override Finset.univ (fun i => replacement i.1) profile = replacement := by
  funext player
  simp [Profile.override]

/-- A coalition value that no source deviation matches for one member refutes
every certificate covering that coalition, whatever the strategy translation.
The hypothesis quantifies over the nonmembers' target strategies, which the
certificate is free to choose. -/
theorem isEmpty_of_unmatchedValue {groups : Set (Finset Player)}
    (members : Finset Player) (hmembers : members ∈ groups)
    (member : Player) (hmember : member ∈ members)
    (profile : Profile source.sig) (replacement : Subprofile target.sig members)
    (hgain : ∀ (opponents : Profile target.sig) (alternative : Subprofile source.sig members),
      (source.play (Profile.override members alternative profile)).expect
          (fun outcome => sourceUtility outcome member) <
        (target.play (Profile.override members replacement opponents)).expect
          (fun outcome => targetUtility outcome member)) :
    IsEmpty (UtilitySimulation source target sourceUtility targetUtility groups) := by
  constructor
  intro simulation
  obtain ⟨alternative, hbound⟩ :=
    simulation.deviation_bound members hmembers profile replacement
  exact absurd (hbound member hmember) (not_le.mpr
    (hgain (fun player => simulation.compileStrategy player (profile player)) alternative))

/-- A target profile worth more to one player than every source profile refutes
every certificate covering the grand coalition. No property of the strategy
translation is used, because the grand coalition overwrites all of it. -/
theorem isEmpty_of_grandCoalitionValue [Fintype Player] {groups : Set (Finset Player)}
    (hgroups : Finset.univ ∈ groups) (profile : Profile source.sig) (member : Player)
    (targetProfile : Profile target.sig) (bound : ℝ)
    (hsource : ∀ alternative : Profile source.sig,
      (source.play alternative).expect (fun outcome => sourceUtility outcome member) ≤ bound)
    (htarget : bound < (target.play targetProfile).expect
      (fun outcome => targetUtility outcome member)) :
    IsEmpty (UtilitySimulation source target sourceUtility targetUtility groups) := by
  refine isEmpty_of_unmatchedValue Finset.univ hgroups member (Finset.mem_univ member)
    profile (fun i => targetProfile i.1) ?_
  intro opponents alternative
  rw [override_univ]
  exact lt_of_le_of_lt (hsource _) htarget

/-- Build the one-player certificate from a bound stated per deviating
player. -/
def ofUnilateral
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (deviationBound : ∀ profile who replacement,
      ∃ alternative : source.sig.Strategy who,
        (target.play (Profile.update
          (fun player => compileStrategy player (profile player)) who replacement)).expect
            (fun outcome => targetUtility outcome who) ≤
          (source.play (Profile.update profile who alternative)).expect
            (fun outcome => sourceUtility outcome who)) :
    UtilitySimulation source target sourceUtility targetUtility (singletonGroups Player) where
  compileStrategy := compileStrategy
  honest_utility := honestUtility
  deviation_bound := by
    rintro members ⟨who, rfl⟩ profile replacement
    obtain ⟨alternative, hbound⟩ :=
      deviationBound profile who (replacement ⟨who, Finset.mem_singleton_self who⟩)
    refine ⟨Subprofile.single who alternative, ?_⟩
    intro member hmember
    obtain rfl := Finset.mem_singleton.mp hmember
    rw [Profile.override_single, Profile.override_singleton]
    exact hbound

/-- A simulation is unchanged by utility interpretations with the same
expectation at every game profile. Values at unreachable outcomes can differ;
the strategy translation is retained exactly. -/
def congrUtilities
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (sourceValue : source.sig.Outcome → Player → ℝ)
    (targetValue : target.sig.Outcome → Player → ℝ)
    (hsource : ∀ profile who,
      (source.play profile).expect (fun outcome => sourceUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceValue outcome who))
    (htarget : ∀ profile who,
      (target.play profile).expect (fun outcome => targetUtility outcome who) =
        (target.play profile).expect (fun outcome => targetValue outcome who)) :
    UtilitySimulation source target sourceValue targetValue groups where
  compileStrategy := simulation.compileStrategy
  honest_utility profile who :=
    (htarget _ who).symm.trans ((simulation.honest_utility profile who).trans (hsource profile who))
  deviation_bound members hmembers profile replacement := by
    obtain ⟨alternative, hbound⟩ := simulation.deviation_bound members hmembers profile replacement
    exact ⟨alternative, fun member hmember =>
      (htarget _ member).symm.le.trans ((hbound member hmember).trans (hsource _ member).le)⟩

/-- Utility comparisons compose through independently verified target layers. -/
def trans {middle : GameForm.{uPlayer, uMiddle, uMiddleOutcome} Player}
    {middleUtility : middle.sig.Outcome → Player → ℝ}
    (left : UtilitySimulation source middle sourceUtility middleUtility groups)
    (right : UtilitySimulation middle target middleUtility targetUtility groups) :
    UtilitySimulation source target sourceUtility targetUtility groups where
  compileStrategy who strategy := right.compileStrategy who (left.compileStrategy who strategy)
  honest_utility profile who :=
    (right.honest_utility (left.compileProfile profile) who).trans
      (left.honest_utility profile who)
  deviation_bound members hmembers profile replacement := by
    obtain ⟨middleAlternative, hright⟩ :=
      right.deviation_bound members hmembers (left.compileProfile profile) replacement
    obtain ⟨sourceAlternative, hleft⟩ :=
      left.deviation_bound members hmembers profile middleAlternative
    exact ⟨sourceAlternative, fun member hmember =>
      (hright member hmember).trans (hleft member hmember)⟩

end UtilitySimulation

end GameTheory.GameForm
