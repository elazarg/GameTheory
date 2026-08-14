/-
# Rosenthal-potential fixture

Two players select one of two resources with delay equal to load. Splitting
across resources raises both the deviator's utility and Rosenthal's potential
by one. A constant candidate therefore fails the exact-potential identity.
-/

import GameTheory.Congestion

noncomputable section

namespace GameTheory.Tests.Congestion

open GameTheory

@[reducible]
def fixture : CongestionGame (Fin 2) where
  Resource := Bool
  Strategy _ := Bool
  resources _ choice := {choice}
  delay _ load := load

def crowded : fixture.Profile := fun _ => false

def split : fixture.Profile :=
  Profile.update (sig := fixture.toGameForm.sig) crowded 1 true

theorem crowded_usedResources : fixture.usedResources crowded = {false} := by
  classical
  ext resource
  cases resource <;>
    simp [CongestionGame.usedResources, fixture, crowded]

theorem split_usedResources : fixture.usedResources split = {false, true} := by
  classical
  ext resource
  cases resource <;>
    simp [CongestionGame.usedResources, fixture, split, crowded, Profile.update]

theorem crowded_congestion_false : fixture.congestion crowded false = 2 := by
  classical
  norm_num [CongestionGame.congestion, fixture, crowded]

theorem split_congestion_false : fixture.congestion split false = 1 := by
  classical
  norm_num [CongestionGame.congestion, fixture, split, crowded, Profile.update]
  decide

theorem split_congestion_true : fixture.congestion split true = 1 := by
  classical
  norm_num [CongestionGame.congestion, fixture, split, crowded, Profile.update]
  decide

theorem crowded_player_one_cost : fixture.playerCost crowded 1 = 2 := by
  rw [CongestionGame.playerCost]
  show ∑ resource ∈ ({false} : Finset Bool),
      fixture.delay resource (fixture.congestion crowded resource) = 2
  rw [Finset.sum_singleton, crowded_congestion_false]
  rfl

theorem split_player_one_cost : fixture.playerCost split 1 = 1 := by
  rw [CongestionGame.playerCost]
  show ∑ resource ∈ ({true} : Finset Bool),
      fixture.delay resource (fixture.congestion split resource) = 1
  rw [Finset.sum_singleton, split_congestion_true]
  norm_num [fixture]

theorem crowded_potential : fixture.potential crowded = -3 := by
  rw [CongestionGame.potential, crowded_usedResources]
  rw [Finset.sum_singleton, crowded_congestion_false]
  norm_num [fixture, Finset.sum_range_succ]

theorem split_potential : fixture.potential split = -2 := by
  rw [CongestionGame.potential, split_usedResources]
  simp [split_congestion_false, split_congestion_true, fixture]
  norm_num

/-- The canonical Rosenthal theorem applies to a deviation with a nonzero
utility and potential change. -/
theorem rosenthal_identity_nonzero :
    expectedUtility fixture.utility 1 (fixture.toGameForm.play split) -
        expectedUtility fixture.utility 1 (fixture.toGameForm.play crowded) =
      fixture.potential split - fixture.potential crowded := by
  have h := fixture.isExactPotential 1 crowded true
  simpa [split] using h

/-- A constant function is not an exact potential for this congestion game. -/
theorem constant_not_exactPotential :
    ¬ IsExactPotential fixture.toGameForm fixture.utility (fun _ => 0) := by
  intro hconstant
  have h := hconstant 1 crowded true
  have hupdate :
      Profile.update (sig := fixture.toGameForm.sig) crowded 1 true = split := rfl
  rw [hupdate] at h
  simp only [expectedUtility_pure] at h
  unfold CongestionGame.utility at h
  have hcost :
      -fixture.playerCost split 1 - -fixture.playerCost crowded 1 =
        (0 : ℝ) - 0 := h
  rw [split_player_one_cost, crowded_player_one_cost] at hcost
  norm_num at hcost

/-- Rosenthal's theorem feeds the canonical potential existence theorem. -/
theorem congestion_nash_exists :
    ∃ profile : fixture.Profile,
      IsNash fixture.toGameForm (euPreference fixture.utility) profile :=
  fixture.nash_exists

end GameTheory.Tests.Congestion
