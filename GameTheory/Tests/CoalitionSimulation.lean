/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Core.UtilitySimulation

/-! # A channel that only a coalition can use

The base game draws a fair coin, one player has nothing to do, and the other is
paid for guessing the coin. No strategy sees the draw, so every profile is worth
one half to both players, and every profile is strong Nash.

The target game is the same draw with a channel: the first player's strategy is
a message chosen as a function of the coin, and the second player's strategy is
a guess chosen as a function of the received message. Compiling a base strategy
sends a constant message and ignores the received one.

A lone deviator gains nothing: against a constant message the guess is constant,
and a message nobody listens to changes no outcome. So the compiled embedding
carries an exact one-player certificate. The two-player coalition that sends the
coin and copies it is worth one, so no coalition certificate exists at all, for
any strategy translation, and strong Nash is not preserved.

This is why `UtilitySimulation` is indexed by the coalitions it covers: the
one-player certificate does not supply the coalition one, and exactness at one
player does not help.
-/

noncomputable section

namespace GameTheory.GameForm.CoalitionWitness

open GameTheory.Math.Probability

/-- The fair draw both games share. -/
def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

/-- The base game: player `1` guesses the coin without observing anything. -/
abbrev baseGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Bool × Bool }
  play profile := fairCoin.map fun coin => (coin, profile 1)

/-- The same draw with a channel: player `0` sends a message chosen from the
coin, and player `1` guesses from the message. -/
abbrev channelGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool → Bool, Outcome := Bool × Bool }
  play profile := fairCoin.map fun coin => (coin, profile 1 (profile 0 coin))

/-- Both players are paid exactly when the guess matches the coin. -/
def matchUtility (outcome : Bool × Bool) (_player : Fin 2) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

/-- Compiling ignores the channel: a constant message, and a guess that does not
read the message it receives. -/
def compileConstant : (who : Fin 2) → baseGame.sig.Strategy who → channelGame.sig.Strategy who :=
  fun _ strategy _ => strategy

/-- A guess that does not depend on the coin is right half the time. -/
theorem expect_constantGuess (guess : Bool) (who : Fin 2) :
    (fairCoin.map fun coin => ((coin, guess) : Bool × Bool)).expect
        (fun outcome => matchUtility outcome who) = 1 / 2 := by
  cases guess <;>
    norm_num [fairCoin, matchUtility, FinDist.expect_map, FinDist.expect_mix]

/-- A guess that copies the coin is always right. -/
theorem expect_copyCoin (who : Fin 2) :
    (fairCoin.map fun coin => ((coin, coin) : Bool × Bool)).expect
        (fun outcome => matchUtility outcome who) = 1 := by
  norm_num [fairCoin, matchUtility, FinDist.expect_map, FinDist.expect_mix]

/-- Every base profile is worth one half to both players. -/
theorem base_expect (profile : Profile baseGame.sig) (who : Fin 2) :
    (baseGame.play profile).expect (fun outcome => matchUtility outcome who) = 1 / 2 :=
  expect_constantGuess (profile 1) who

/-- Against compiled opponents a single deviation still produces a guess that
does not depend on the coin. -/
theorem update_compileConstant_play (profile : Profile baseGame.sig) (who : Fin 2)
    (replacement : channelGame.sig.Strategy who) :
    ∃ guess : Bool,
      channelGame.play (Profile.update
          (fun player => compileConstant player (profile player)) who replacement) =
        fairCoin.map fun coin => ((coin, guess) : Bool × Bool) := by
  fin_cases who
  · exact ⟨profile 1, by simp [compileConstant, Profile.update_of_ne]⟩
  · exact ⟨replacement (profile 0), by simp [compileConstant, Profile.update_of_ne]⟩

/-- The embedding carries an exact one-player certificate. -/
def unilateralSimulation :
    UtilitySimulation baseGame channelGame matchUtility matchUtility
      (singletonGroups (Fin 2)) :=
  UtilitySimulation.ofUnilateral compileConstant
    (fun profile who => by
      obtain ⟨guess, hplay⟩ := update_compileConstant_play profile who (compileConstant who
        (profile who))
      rw [Profile.update_eq_self] at hplay
      rw [hplay, expect_constantGuess, base_expect])
    (fun profile who replacement => by
      refine ⟨profile who, ?_⟩
      obtain ⟨guess, hplay⟩ := update_compileConstant_play profile who replacement
      rw [hplay, expect_constantGuess, Profile.update_eq_self, base_expect])

/-- Send the coin, then copy the message received. -/
def copyProfile : Profile channelGame.sig := fun _ => id

/-- The coalition that sends the coin and copies it is always right. -/
theorem copyProfile_expect (who : Fin 2) :
    (channelGame.play copyProfile).expect (fun outcome => matchUtility outcome who) = 1 :=
  expect_copyCoin who

/-- Overriding both coordinates is that coalition, whatever was there. -/
theorem override_copyProfile (profile : Profile channelGame.sig) :
    Profile.override Finset.univ (fun i => copyProfile i.1) profile = copyProfile := by
  funext player
  simp [Profile.override]

/-- No coalition certificate exists, for any strategy translation. The grand
coalition reaches one in the target, while every base profile is worth one
half, so the bound would assert `1 ≤ 1 / 2`. -/
theorem isEmpty_coalitionSimulation :
    IsEmpty (UtilitySimulation baseGame channelGame matchUtility matchUtility
      (nonemptyGroups (Fin 2))) :=
  UtilitySimulation.isEmpty_of_grandCoalitionValue Finset.univ_nonempty
    (fun _ => false) 0 copyProfile (1 / 2)
    (fun alternative => le_of_eq (base_expect alternative 0))
    (by rw [copyProfile_expect]; norm_num)

/-- Every base profile is strong Nash: no coalition can beat one half. -/
theorem base_isStrongNash (profile : Profile baseGame.sig) :
    IsStrongNash baseGame (euPreference matchUtility) profile := by
  rw [isStrongNash_iff]
  intro coalition hne replacement
  obtain ⟨member, hmember⟩ := hne
  refine ⟨member, hmember, ?_⟩
  simp only [euPreference_apply, expectedUtility]
  rw [expect_constantGuess, expect_constantGuess]

/-- Its compilation is not: the coalition that uses the channel gains. -/
theorem compiled_not_isStrongNash (profile : Profile baseGame.sig) :
    ¬ IsStrongNash channelGame (euPreference matchUtility)
      (fun player => compileConstant player (profile player)) := by
  rw [isStrongNash_iff]
  intro h
  obtain ⟨member, _, hprefer⟩ :=
    h Finset.univ Finset.univ_nonempty (fun i => copyProfile i.1)
  rw [euPreference_apply, expectedUtility, expectedUtility, override_copyProfile,
    copyProfile_expect] at hprefer
  have hhonest : (channelGame.play
      (fun player => compileConstant player (profile player))).expect
        (fun outcome => matchUtility outcome member) = 1 / 2 := by
    obtain ⟨guess, hplay⟩ := update_compileConstant_play profile member
      (compileConstant member (profile member))
    rw [Profile.update_eq_self] at hplay
    rw [hplay, expect_constantGuess]
  rw [hhonest] at hprefer
  norm_num at hprefer

/-- Coordination succeeds only when both players choose true. -/
abbrev coordinationGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Bool }
  play profile := FinDist.pure (profile 0 && profile 1)

def coordinationUtility (outcome : Bool) (_player : Fin 2) : ℝ :=
  if outcome then 1 else 0

/-- Extra private strategy coordinates that play ignores cannot create a
coalitional communication channel. -/
abbrev redundantGame : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool × Bool, Outcome := Bool }
  play profile := FinDist.pure ((profile 0).1 && (profile 1).1)

/-- One projected source replacement simultaneously matches the utilities of
every coalition member, including the genuine two-player coalition. -/
def coalitionSimulation :
    UtilitySimulation coordinationGame redundantGame coordinationUtility coordinationUtility
      (nonemptyGroups (Fin 2)) where
  compileStrategy _ strategy := (strategy, false)
  honest_utility _ _ := rfl
  deviation_bound members _ profile replacement := by
    refine ⟨fun i => (replacement i).1, ?_⟩
    intro member _
    have hlaw :
        redundantGame.play (Profile.override members replacement
          (fun player => (profile player, false))) =
        coordinationGame.play
          (Profile.override members (fun i => (replacement i).1) profile) := by
      by_cases hzero : (0 : Fin 2) ∈ members <;>
        by_cases hone : (1 : Fin 2) ∈ members <;>
        simp [redundantGame, Profile.override, hzero, hone]
    rw [hlaw]

theorem coordination_isStrongNash :
    IsStrongNash coordinationGame (euPreference coordinationUtility) (fun _ => true) := by
  rw [isStrongNash_iff]
  intro members hne replacement
  obtain ⟨member, hmember⟩ := hne
  refine ⟨member, hmember, ?_⟩
  simp only [euPreference, expectedUtility, coordinationGame, FinDist.expect_pure,
    coordinationUtility, Bool.and_self, ite_true]
  split_ifs <;> norm_num

theorem coordination_false_isNash :
    IsNash coordinationGame (euPreference coordinationUtility) (fun _ => false) := by
  rw [isNash_iff]
  intro who replacement
  fin_cases who <;> cases replacement <;>
    norm_num [euPreference, expectedUtility, coordinationGame, coordinationUtility,
      Profile.update_of_ne]

/-- The positive fixture has a genuine coalition gain: neither player can
repair failed coordination alone, but their joint true replacement improves
both. It is therefore not merely a constant-utility certificate. -/
theorem coordination_false_not_isStrongNash :
    ¬ IsStrongNash coordinationGame (euPreference coordinationUtility) (fun _ => false) := by
  rw [isStrongNash_iff]
  intro h
  obtain ⟨member, _, hbound⟩ := h Finset.univ Finset.univ_nonempty (fun _ => true)
  norm_num [euPreference, expectedUtility, coordinationGame, coordinationUtility,
    Profile.override] at hbound

/-- Unlike the channel extension, the redundant-strategy extension preserves
strong Nash using one certificate for every nonempty coalition. -/
theorem redundant_isStrongNash :
    IsStrongNash redundantGame (euPreference coordinationUtility)
      (coalitionSimulation.compileProfile (fun _ => true)) := by
  have hpreference : euPreferenceWithin 0 coordinationUtility =
      euPreference coordinationUtility := by
    funext player preferred alternative
    simp [euPreferenceWithin, euPreference]
  have hsource : IsStrongNash coordinationGame (euPreferenceWithin 0 coordinationUtility)
      (fun _ => true) := by
    rw [hpreference]
    exact coordination_isStrongNash
  have htarget :=
    (coalitionSimulation.isStrongNash_compileProfile_iff 0 (fun _ => true)).mpr hsource
  rwa [hpreference] at htarget

/-- Empty coalitions cannot supply an improving member. A group family
containing only the empty coalition therefore imposes no equilibrium test. -/
theorem empty_group_vacuous (ε : ℝ) (profile : Profile channelGame.sig) :
    IsεGroupNash channelGame matchUtility ({∅} : Set (Finset (Fin 2))) ε profile := by
  rw [isεGroupNash_iff]
  intro members hmembers hne
  have hempty : members = ∅ := hmembers
  subst members
  simp at hne

end GameTheory.GameForm.CoalitionWitness
