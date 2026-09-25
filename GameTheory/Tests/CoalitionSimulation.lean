/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.UtilitySimulation
import GameTheory.Math.Probability.Uniform

/-! # A channel that only a coalition can use

The base game draws a fair coin and pays both players when the second player
guesses it. The target adds a message channel from player zero to player one.
Constant messages preserve all unilateral utility bounds, but a coalition can
transmit the coin and earn one rather than one half.
-/

noncomputable section

namespace GameTheory.GameForm.CoalitionWitness

open GameTheory.Math.Probability

def fairCoin : PMF Bool := PMF.uniformOfFintype Bool

abbrev baseGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Bool × Bool }
  play profile := fairCoin.map fun coin => (coin, profile 1)

abbrev channelGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool → Bool, Outcome := Bool × Bool }
  play profile := fairCoin.map fun coin => (coin, profile 1 (profile 0 coin))

def matchUtility (outcome : Bool × Bool) (_player : Fin 2) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

def compileConstant : (who : Fin 2) → baseGame.sig.Strategy who →
    channelGame.sig.Strategy who := fun _ strategy _ => strategy

private theorem matchBound (who : Fin 2) (outcome : Bool × Bool) :
    |matchUtility outcome who| ≤ 1 := by
  simp [matchUtility]
  split_ifs <;> norm_num

private theorem matchGuard (law : PMF (Bool × Bool)) (who : Fin 2) :
    UtilityIntegrable matchUtility who law :=
  payoffIntegrable_of_bounded law _ (matchBound who)

/-- Any fixed guess succeeds on half of the fair draw. -/
theorem expect_constantGuess (guess : Bool) (who : Fin 2)
    (h : UtilityIntegrable matchUtility who
      (fairCoin.map fun coin => ((coin, guess) : Bool × Bool))) :
    expectedUtility matchUtility who
      (fairCoin.map fun coin => ((coin, guess) : Bool × Bool)) h = 1 / 2 := by
  rw [expectedUtility_map]
  unfold expectedUtility
  simp only [fairCoin]
  rw [expect_proof_irrel (PMF.uniformOfFintype Bool) _ _
    (payoffIntegrable_of_finite _ _), expect_uniformOfFintype]
  cases guess <;> norm_num [matchUtility]

/-- Copying the fair draw succeeds surely. -/
theorem expect_copyCoin (who : Fin 2)
    (h : UtilityIntegrable matchUtility who
      (fairCoin.map fun coin => ((coin, coin) : Bool × Bool))) :
    expectedUtility matchUtility who
      (fairCoin.map fun coin => ((coin, coin) : Bool × Bool)) h = 1 := by
  rw [expectedUtility_map]
  unfold expectedUtility
  simp only [fairCoin]
  rw [expect_proof_irrel (PMF.uniformOfFintype Bool) _ _
    (payoffIntegrable_of_finite _ _), expect_uniformOfFintype]
  norm_num [matchUtility]

theorem base_expect (profile : Profile baseGame.sig) (who : Fin 2)
    (h : UtilityIntegrable matchUtility who (baseGame.play profile)) :
    expectedUtility matchUtility who (baseGame.play profile) h = 1 / 2 :=
  expect_constantGuess (profile 1) who h

theorem update_compileConstant_play (profile : Profile baseGame.sig) (who : Fin 2)
    (replacement : channelGame.sig.Strategy who) :
    ∃ guess : Bool,
      channelGame.play (Profile.update
          (Profile.map compileConstant profile) who replacement) =
        fairCoin.map fun coin => ((coin, guess) : Bool × Bool) := by
  fin_cases who
  · exact ⟨profile 1, by simp [compileConstant, Profile.update_of_ne]⟩
  · exact ⟨replacement (profile 0), by simp [compileConstant, Profile.update_of_ne]⟩

/-- The embedding carries an exact one-player certificate. -/
def unilateralSimulation :
    UtilitySimulation baseGame channelGame matchUtility matchUtility
      (singletonGroups (Fin 2)) :=
  UtilitySimulation.ofUnilateral compileConstant
    (fun _ _ => ⟨fun _ => matchGuard _ _, fun _ => matchGuard _ _⟩)
    (fun profile who htarget hsource => by
      obtain ⟨guess, hplay⟩ := update_compileConstant_play profile who
        (compileConstant who (profile who))
      have hself : Profile.update (Profile.map compileConstant profile) who
          (compileConstant who (profile who)) = Profile.map compileConstant profile := by
        simpa only [Profile.map_apply] using
          Profile.update_eq_self (Profile.map compileConstant profile) who
      rw [hself] at hplay
      calc
        _ = expectedUtility matchUtility who
              (fairCoin.map fun coin => ((coin, guess) : Bool × Bool))
              (matchGuard _ _) :=
          expectedUtility_congr_law matchUtility who hplay htarget (matchGuard _ _)
        _ = 1 / 2 := expect_constantGuess guess who _
        _ = _ := (base_expect profile who hsource).symm)
    (fun profile who replacement => by
      refine ⟨profile who, ?_⟩
      intro hsource
      obtain ⟨guess, hplay⟩ := update_compileConstant_play profile who replacement
      have htarget : UtilityIntegrable matchUtility who
          (channelGame.play (Profile.update
            (Profile.map compileConstant profile) who replacement)) :=
        matchGuard _ _
      refine ⟨htarget, le_of_eq ?_⟩
      have hsource' : UtilityIntegrable matchUtility who (baseGame.play profile) :=
        matchGuard _ _
      calc
        _ = expectedUtility matchUtility who
              (fairCoin.map fun coin => ((coin, guess) : Bool × Bool))
              (matchGuard _ _) :=
          expectedUtility_congr_law matchUtility who hplay htarget (matchGuard _ _)
        _ = 1 / 2 := expect_constantGuess guess who _
        _ = expectedUtility matchUtility who (baseGame.play profile) hsource' :=
          (base_expect profile who hsource').symm
        _ = _ := by
          have hlaw : baseGame.play profile =
              baseGame.play (Profile.update profile who (profile who)) := by
            rw [Profile.update_eq_self]
          exact expectedUtility_congr_law matchUtility who hlaw hsource' hsource)

def copyProfile : Profile channelGame.sig := fun _ => id

theorem copyProfile_expect (who : Fin 2)
    (h : UtilityIntegrable matchUtility who (channelGame.play copyProfile)) :
    expectedUtility matchUtility who (channelGame.play copyProfile) h = 1 :=
  expect_copyCoin who h

theorem override_copyProfile (profile : Profile channelGame.sig) :
    Profile.override Finset.univ (fun i => copyProfile i.1) profile = copyProfile := by
  funext player
  simp [Profile.override]

/-- The grand coalition reaches a payoff no source profile can match. -/
theorem isEmpty_coalitionSimulation :
    IsEmpty (UtilitySimulation baseGame channelGame matchUtility matchUtility
      (nonemptyGroups (Fin 2))) :=
  UtilitySimulation.isEmpty_of_grandCoalitionValue Finset.univ_nonempty
    (fun _ => false) 0 copyProfile (1 / 2)
    (fun alternative =>
      ⟨matchGuard _ _, le_of_eq (base_expect alternative 0 (matchGuard _ _))⟩)
    (fun ht => by rw [copyProfile_expect 0 ht]; norm_num)

/-- Every base profile is strong Nash: no coalition can beat one half. -/
theorem base_isStrongNash (profile : Profile baseGame.sig) :
    IsStrongNash baseGame (euPreference matchUtility) profile := by
  rw [isStrongNash_iff]
  intro coalition hne replacement
  obtain ⟨member, hmember⟩ := hne
  refine ⟨member, hmember, matchGuard _ _, matchGuard _ _, ?_⟩
  rw [base_expect profile member, base_expect _ member]

/-- The channel lets the grand coalition improve from one half to one. -/
theorem compiled_not_isStrongNash (profile : Profile baseGame.sig) :
    ¬ IsStrongNash channelGame (euPreference matchUtility)
      (Profile.map compileConstant profile) := by
  rw [isStrongNash_iff]
  intro h
  obtain ⟨member, _, hbase, hdev, hprefer⟩ :=
    h Finset.univ Finset.univ_nonempty (fun i => copyProfile i.1)
  have hdevlaw : channelGame.play
      (Profile.override Finset.univ (fun i => copyProfile i.1)
        (Profile.map compileConstant profile)) = channelGame.play copyProfile := by
    rw [override_copyProfile]
  have hdevvalue : expectedUtility matchUtility member _ hdev = 1 := by
    calc
      _ = expectedUtility matchUtility member (channelGame.play copyProfile)
          (matchGuard _ _) :=
        expectedUtility_congr_law matchUtility member hdevlaw hdev (matchGuard _ _)
      _ = 1 := copyProfile_expect member _
  rw [hdevvalue] at hprefer
  obtain ⟨guess, hplay⟩ := update_compileConstant_play profile member
    (compileConstant member (profile member))
  have hself : Profile.update (Profile.map compileConstant profile) member
      (compileConstant member (profile member)) = Profile.map compileConstant profile := by
    simpa only [Profile.map_apply] using
      Profile.update_eq_self (Profile.map compileConstant profile) member
  rw [hself] at hplay
  have hhalf : expectedUtility matchUtility member
      (channelGame.play (Profile.map compileConstant profile)) hbase = 1 / 2 := by
    calc
      _ = expectedUtility matchUtility member
          (fairCoin.map fun coin => ((coin, guess) : Bool × Bool))
          (matchGuard _ _) :=
        expectedUtility_congr_law matchUtility member hplay hbase (matchGuard _ _)
      _ = 1 / 2 := expect_constantGuess guess member _
  rw [hhalf] at hprefer
  norm_num at hprefer

/-- Coordination succeeds only when both players choose true. -/
abbrev coordinationGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Bool }
  play profile := PMF.pure (profile 0 && profile 1)

def coordinationUtility (outcome : Bool) (_player : Fin 2) : ℝ :=
  if outcome then 1 else 0

abbrev redundantGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool × Bool, Outcome := Bool }
  play profile := PMF.pure ((profile 0).1 && (profile 1).1)

/-- One source replacement matches all members of a deviating coalition. -/
def coalitionSimulation :
    UtilitySimulation coordinationGame redundantGame
      coordinationUtility coordinationUtility (nonemptyGroups (Fin 2)) where
  compileStrategy _ strategy := (strategy, false)
  honest_integrable profile who := by
    exact ⟨fun _ => payoffIntegrable_pure _ _, fun _ => payoffIntegrable_pure _ _⟩
  honest_utility profile who _ _ := by
    simp [coordinationGame, redundantGame, expectedUtility_pure, Profile.map_apply]
  deviation_bound members _ profile replacement := by
    refine ⟨fun i => (replacement i).1, ?_⟩
    intro member _ hsource
    have hlaw :
        redundantGame.play (Profile.override members replacement
          (Profile.map (fun _ strategy => (strategy, false)) profile)) =
        coordinationGame.play
          (Profile.override members (fun i => (replacement i).1) profile) := by
      by_cases hzero : (0 : Fin 2) ∈ members <;>
        by_cases hone : (1 : Fin 2) ∈ members <;>
        simp [redundantGame, coordinationGame, Profile.override,
          Profile.map_apply, hzero, hone]
    have htarget : UtilityIntegrable coordinationUtility member
        (redundantGame.play (Profile.override members replacement
          (Profile.map (fun _ strategy => (strategy, false)) profile))) :=
      payoffIntegrable_pure _ _
    refine ⟨htarget, le_of_eq ?_⟩
    exact expectedUtility_congr_law coordinationUtility member hlaw htarget hsource

theorem coordination_isStrongNash :
    IsStrongNash coordinationGame (euPreference coordinationUtility)
      (fun _ => true) := by
  rw [isStrongNash_iff]
  intro members hne replacement
  obtain ⟨member, hmember⟩ := hne
  refine ⟨member, hmember, ?_⟩
  rw [euPreference_pure_iff]
  simp [coordinationGame, coordinationUtility]
  split_ifs <;> norm_num

theorem coordination_false_isNash :
    IsNash coordinationGame (euPreference coordinationUtility)
      (fun _ => false) := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_pure_iff]
  fin_cases who <;> cases replacement <;>
    simp [coordinationGame, coordinationUtility, Profile.update_of_ne]

/-- Both players jointly gain even though neither can repair coordination. -/
theorem coordination_false_not_isStrongNash :
    ¬ IsStrongNash coordinationGame (euPreference coordinationUtility)
      (fun _ => false) := by
  rw [isStrongNash_iff]
  intro h
  obtain ⟨member, _, hbound⟩ :=
    h Finset.univ Finset.univ_nonempty (fun _ => true)
  rw [euPreference_pure_iff] at hbound
  norm_num [coordinationGame, coordinationUtility, Profile.override] at hbound

/-- The redundant-strategy extension preserves strong Nash. -/
theorem redundant_isStrongNash :
    IsStrongNash redundantGame (euPreference coordinationUtility)
      (coalitionSimulation.compileProfile (fun _ => true)) := by
  have hpreference : euPreferenceWithin 0 coordinationUtility =
      euPreference coordinationUtility := by
    funext player preferred alternative
    simp [euPreferenceWithin, euPreference]
  have hsource : IsStrongNash coordinationGame
      (euPreferenceWithin 0 coordinationUtility) (fun _ => true) := by
    rw [hpreference]
    exact coordination_isStrongNash
  have htarget :=
    (coalitionSimulation.isStrongNash_compileProfile_iff 0 (fun _ => true)).mpr hsource
  rwa [hpreference] at htarget

/-- A group family containing only the empty coalition is vacuous. -/
theorem empty_group_vacuous (ε : ℝ) (profile : Profile channelGame.sig) :
    IsεGroupNash channelGame matchUtility ({∅} : Set (Finset (Fin 2))) ε profile := by
  rw [isεGroupNash_iff]
  intro members hmembers hne
  have hempty : members = ∅ := hmembers
  subst members
  simp at hne

end GameTheory.GameForm.CoalitionWitness
