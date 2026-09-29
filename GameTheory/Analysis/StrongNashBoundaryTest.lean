/-
# Strong Nash is not a comparison family

A coalition deviation is blocked when *some* member weakly prefers the status
quo, a disjunction over members. Its supporting utilities need not be closed
under addition: here each of two utilities is blocked by a different member,
while their sum makes both members gain from the joint deviation. So no family
of incentive comparisons has strong Nash as its concept, and its preservation is
not decided by a cone criterion.
-/

import GameTheory.Analysis.IncentiveHierarchy

noncomputable section

namespace GameTheory.Tests.StrongNashBoundary

open GameTheory GameTheory.Math.Probability

@[reducible]
def form : GameForm Bool where
  sig := { Strategy := fun _ => Bool, Outcome := Bool × Bool }
  play profile := PMF.pure (profile false, profile true)

def statusQuo : Profile form.sig := fun _ => false

/-- The first utility: only the second player gains from the joint deviation. -/
def first : Bool × Bool → Bool → ℝ
  | (true, true), true => 1
  | (true, false), _ => -1
  | (false, true), _ => -1
  | _, _ => 0

/-- The second utility: only the first player gains from the joint deviation. -/
def second : Bool × Bool → Bool → ℝ
  | (true, true), false => 1
  | (true, false), _ => -1
  | (false, true), _ => -1
  | _, _ => 0

def IsStrong (utility : Bool × Bool → Bool → ℝ) : Prop :=
  IsStrongNash form (euPreference fun outcome who => utility outcome who) statusQuo

private theorem play_override (coalition : Finset Bool)
    (replacement : Subprofile form.sig coalition) :
    form.play (Profile.override coalition replacement statusQuo) =
      PMF.pure (Profile.override coalition replacement statusQuo false,
        Profile.override coalition replacement statusQuo true) := rfl

private theorem true_mem_of_not_false_mem {coalition : Finset Bool}
    (hne : coalition.Nonempty) (hfalse : false ∉ coalition) : true ∈ coalition := by
  obtain ⟨member, hmember⟩ := hne
  cases member
  · exact absurd hmember hfalse
  · exact hmember

theorem first_isStrong : IsStrong first := by
  rw [IsStrong, isStrongNash_iff]
  intro coalition hne replacement
  rw [play_override]
  by_cases hfalse : false ∈ coalition
  · refine ⟨false, hfalse, ?_⟩
    rw [euPreference_pure_iff]
    rcases Profile.override coalition replacement statusQuo false with _ | _ <;>
      rcases Profile.override coalition replacement statusQuo true with _ | _ <;>
        simp [first, statusQuo]
  · refine ⟨true, true_mem_of_not_false_mem hne hfalse, ?_⟩
    rw [euPreference_pure_iff, Profile.override_of_not_mem _ _ _ hfalse]
    rcases Profile.override coalition replacement statusQuo true with _ | _ <;>
      simp [first, statusQuo]

theorem second_isStrong : IsStrong second := by
  rw [IsStrong, isStrongNash_iff]
  intro coalition hne replacement
  rw [play_override]
  by_cases htrue : true ∈ coalition
  · refine ⟨true, htrue, ?_⟩
    rw [euPreference_pure_iff]
    rcases Profile.override coalition replacement statusQuo false with _ | _ <;>
      rcases Profile.override coalition replacement statusQuo true with _ | _ <;>
        simp [second, statusQuo]
  · have hfalse : false ∈ coalition := by
      obtain ⟨member, hmember⟩ := hne
      cases member
      · exact hmember
      · exact absurd hmember htrue
    refine ⟨false, hfalse, ?_⟩
    rw [euPreference_pure_iff, Profile.override_of_not_mem _ _ _ htrue]
    rcases Profile.override coalition replacement statusQuo false with _ | _ <;>
      simp [second, statusQuo]

/-- Under the summed utility both players gain from deviating together. -/
theorem sum_not_isStrong : ¬ IsStrong (first + second) := by
  rw [IsStrong, isStrongNash_iff]
  intro hstrong
  obtain ⟨member, -, hmember⟩ := hstrong Finset.univ Finset.univ_nonempty fun _ => true
  rw [play_override, euPreference_pure_iff] at hmember
  have hall : Profile.override (Finset.univ : Finset Bool) (fun _ => true) statusQuo =
      fun _ => true := by
    funext player
    simp [Profile.override]
  rw [hall] at hmember
  cases member <;> norm_num [first, second, statusQuo] at hmember

/-- **Strong Nash is the concept of no comparison family.** -/
theorem strongNash_not_family :
    ¬ ∃ (Index : Bool → Type) (family : (who : Bool) → Index who →
        IncentiveComparison (Bool × Bool)),
      ∀ utility, (∀ who deviation, (family who deviation).Holds (utility · who)) ↔
        IsStrong utility :=
  IncentiveComparison.not_exists_family_of_not_add IsStrong first_isStrong second_isStrong
    sum_not_isStrong

end GameTheory.Tests.StrongNashBoundary
