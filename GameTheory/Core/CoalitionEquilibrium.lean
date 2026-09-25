/-
# Equilibrium against selected coalitions

Selected coalitions restrict the canonical constant-coalition deviation scheme.
Empty coalitions are ignored, just as in strong Nash. Approximation changes only
the expected-utility preference, not the equilibrium predicate.
-/

import GameTheory.Core.Approximate

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uPlayer uStrategy uOutcome

/-- The one-player coalitions. -/
def singletonGroups (Player : Type uPlayer) : Set (Finset Player) :=
  {members | ∃ who, members = {who}}

/-- Every coalition with at least one member. -/
def nonemptyGroups (Player : Type uPlayer) : Set (Finset Player) :=
  {members | members.Nonempty}

variable {Player : Type uPlayer} [DecidableEq Player]

omit [DecidableEq Player] in
theorem singletonGroups_subset_nonemptyGroups :
    singletonGroups Player ⊆ nonemptyGroups Player := by
  rintro members ⟨who, rfl⟩
  exact Finset.singleton_nonempty who

/-- Approximate equilibrium against the selected nonempty coalitions, using
the same equilibrium predicate and coalition preference as strong Nash. -/
def IsεGroupNash (F : GameForm.{uPlayer, uStrategy, uOutcome} Player)
    (utility : F.sig.Outcome → Player → ℝ)
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile F.sig) : Prop :=
  IsEquilibrium F
    (fun (coalition : { members : Finset Player // members.Nonempty ∧ members ∈ groups }) =>
      Preference.coalition (euPreferenceWithin ε utility) ⟨coalition.1, coalition.2.1⟩)
    (PMF.pure profile)
    ((DeviationScheme.coalitionConstant F.sig).comap
      (fun (coalition : { members : Finset Player // members.Nonempty ∧ members ∈ groups }) =>
        ⟨coalition.1, coalition.2.1⟩))

variable {F : GameForm.{uPlayer, uStrategy, uOutcome} Player}

theorem isεGroupNash_iff (utility : F.sig.Outcome → Player → ℝ)
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile F.sig) :
    IsεGroupNash F utility groups ε profile ↔
      ∀ members ∈ groups, members.Nonempty →
        ∀ replacement : Subprofile F.sig members,
          ∃ member ∈ members,
            ∃ hbase : UtilityIntegrable utility member (F.play profile),
              ∃ hdev : UtilityIntegrable utility member
                (F.play (Profile.override members replacement profile)),
                expectedUtility utility member
                    (F.play (Profile.override members replacement profile)) hdev ≤
                  expectedUtility utility member (F.play profile) hbase + ε := by
  constructor
  · intro h members hmembers hne replacement
    simpa [IsεGroupNash, DeviationScheme.comap, DeviationScheme.apply,
      DeviationScheme.coalitionConstant, GameForm.outcomeLaw, euPreferenceWithin,
      PMF.pure_bind] using
      h ⟨members, hne, hmembers⟩ replacement
  · intro h coalition replacement
    dsimp only [DeviationScheme.comap, DeviationScheme.coalitionConstant] at replacement
    simpa [DeviationScheme.comap, DeviationScheme.apply,
      DeviationScheme.coalitionConstant, GameForm.outcomeLaw, euPreferenceWithin,
      PMF.pure_bind] using
      h coalition.1 coalition.2.2 coalition.2.1 replacement

/-- One-player coalitions recover ordinary approximate Nash. -/
theorem isεGroupNash_singletonGroups_iff (utility : F.sig.Outcome → Player → ℝ)
    (ε : ℝ) (profile : Profile F.sig) :
    IsεGroupNash F utility (singletonGroups Player) ε profile ↔
      IsεNash F utility ε profile := by
  rw [isεGroupNash_iff, isεNash_iff]
  constructor
  · intro h who replacement
    obtain ⟨member, hmember, hbound⟩ := h {who} ⟨who, rfl⟩
      (Finset.singleton_nonempty who) (Subprofile.single who replacement)
    obtain rfl := Finset.mem_singleton.mp hmember
    rwa [Profile.override_single] at hbound
  · rintro h members ⟨who, rfl⟩ _ replacement
    refine ⟨who, Finset.mem_singleton_self who, ?_⟩
    rw [Profile.override_singleton]
    exact h who _

/-- All nonempty coalitions recover strong Nash for the relaxed preference. -/
theorem isεGroupNash_nonemptyGroups_iff (utility : F.sig.Outcome → Player → ℝ)
    (ε : ℝ) (profile : Profile F.sig) :
    IsεGroupNash F utility (nonemptyGroups Player) ε profile ↔
      IsStrongNash F (euPreferenceWithin ε utility) profile := by
  rw [isεGroupNash_iff, isStrongNash_iff]
  exact ⟨fun h coalition hne replacement => h coalition hne hne replacement,
    fun h members _ hne replacement => h members hne replacement⟩

end GameTheory
