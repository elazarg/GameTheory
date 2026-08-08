/-
Hostile finite consumer for empirical potential recurrences.

A one-player process starts at the inferior action and then plays the unique
best action forever.  Its first played gain is one, so the first empirical
potential step is genuinely nonzero rather than a constant-path tautology.
-/

import GameTheory.Core.FictitiousPlayPotential

noncomputable section

namespace GameTheory.Tests.FictitiousPlayPotential

open Probability

@[reducible]
def signature : GameSignature (Fin 1) where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def form : GameForm (Fin 1) where
  sig := signature
  play profile := FinDist.pure (profile 0)

def reward (outcome : Bool) : ℝ := if outcome then 1 else 0

@[reducible]
def game : UtilityGame (Fin 1) where
  form := form
  utility := fun outcome _ => reward outcome

def potential (profile : Profile signature) : ℝ := reward (profile 0)

def allFalse : Profile signature := fun _ => false

def history : ℕ → Profile signature
  | 0 => allFalse
  | _ + 1 => fun _ => true

theorem exactPotential :
    IsExactPotential game.form game.utility potential := by
  show IsExactPotential form (fun outcome _ => reward outcome)
    (fun profile => reward (profile 0))
  simpa [form] using
    (isExactPotential_of_identicalInterests (F := form) reward)

theorem firstBelief :
    game.empiricalBelief history 1 = game.form.purify allFalse := by
  funext who
  show (FinDist.uniformFin 1).map
      (fun round : Fin 1 => history round.val who) = FinDist.pure false
  have hconstant : (fun round : Fin 1 => history round.val who) =
      fun _ => false := by
    funext round
    have hround : round = 0 := Subsingleton.elim _ _
    subst round
    rfl
  rw [hconstant, FinDist.map_const]

theorem expectedUtility_update
    (mixedProfile : Profile game.form.sig.mixed)
    (replacement : FinDist Bool) :
    expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update mixedProfile 0 replacement)) =
      replacement.expect reward := by
  rw [GameForm.mixed_play_update, expectedUtility_bind]
  apply FinDist.expect_congr
  intro action _
  have hpure :
      Profile.update mixedProfile 0 (FinDist.pure action) =
        game.form.purify (fun _ => action) := by
    funext who
    have hwho : who = 0 := Subsingleton.elim _ _
    subst who
    simp [GameForm.purify]
  rw [hpure, GameForm.mixed_play_purify, expectedUtility_pure]

/-- The inferior initial observation followed by `true` is genuine fictitious
play; no later action can improve on reward one. -/
theorem isFictitiousPlay : game.IsFictitiousPlay history := by
  intro t who replacement
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  rw [euPreference_apply, expectedUtility_update, expectedUtility_update]
  have hplayed : history (t + 1) 0 = true := by simp [history]
  rw [hplayed, FinDist.expect_pure]
  exact expect_le_of_forall replacement reward 1 fun action _ => by
    cases action <;> norm_num [reward]

/-- The first action chosen against the inferior empirical belief gains one. -/
theorem firstPlayedGain : game.playedGain history 0 0 = 1 := by
  have hplayed : history 1 0 = true := rfl
  rw [UtilityGame.playedGain, firstBelief]
  unfold UtilityGame.mixedGain
  rw [purify_update, GameForm.mixed_play_purify,
    GameForm.mixed_play_purify, expectedUtility_pure, expectedUtility_pure]
  norm_num [game, form, potential, reward, allFalse, hplayed]

/-- The first empirical-potential increment is the nonzero half-step predicted
by the general recurrence. -/
theorem firstPotentialStep :
    game.mixedPotential potential
        (Profile.update (game.empiricalBelief history 1) 0
          (game.empiricalMarginal history 0 2)) -
      game.mixedPotential potential (game.empiricalBelief history 1) = 1 / 2 := by
  calc
    _ = (1 / (0 + 2 : ℝ)) * game.playedGain history 0 0 :=
      by simpa using
        (UtilityGame.IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub
          (G := game) exactPotential history 0 0)
    _ = 1 / 2 := by rw [firstPlayedGain]; norm_num

/-- The generic aggregate-improvement bound specializes to a process with a
strictly positive first played gain. -/
theorem firstImprovementBound :
    game.mixedImprovement (game.empiricalBelief history 1) ≤
      game.weightedPlayedGain history 0 :=
  UtilityGame.IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
    (G := game) isFictitiousPlay 0

theorem potential_abs_bound (profile : Profile signature) :
    |potential profile| ≤ 1 := by
  simp only [potential, reward]
  split <;> norm_num

/-- The quantitative one-coordinate estimate applies to the same nonzero first
step; it is not proved only for constant trajectories. -/
theorem firstPotentialStep_abs_bound :
    |game.mixedPotential potential
          (Profile.update (game.empiricalBelief history 1) 0
            (game.empiricalMarginal history 0 2)) -
        game.mixedPotential potential (game.empiricalBelief history 1)| ≤
      (1 / (0 + 2 : ℝ)) * (2 * 1) := by
  simpa using
    (game.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential potential_abs_bound history
      (game.empiricalBelief history 1) 0 0 rfl)

/-- The uniform `4C/(t+2)` gain-stability estimate includes the changed
player's own coordinate. -/
theorem firstGainStep_abs_bound :
    |game.mixedPotentialGain potential
          (Profile.update (game.empiricalBelief history 1) 0
            (game.empiricalMarginal history 0 2)) 0 true -
        game.mixedPotentialGain potential
          (game.empiricalBelief history 1) 0 true| ≤
      (1 / (0 + 2 : ℝ)) * (4 * 1) := by
  simpa using
    (game.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
      potential potential_abs_bound history
      (game.empiricalBelief history 1) true 0 rfl)

theorem firstAggregatePlayedGain : game.aggregatePlayedGain history 0 = 1 := by
  rw [UtilityGame.aggregatePlayedGain]
  simpa using firstPlayedGain

/-- The all-player sweep is concrete even in the minimal hostile fixture: its
single update produces the next empirical belief. -/
theorem firstAdvanceAll :
    game.advanceMarginals history 0 Finset.univ.toList
        (game.empiricalBelief history 1) =
      game.empiricalBelief history 2 := by
  simpa using game.advanceMarginals_univ_eq_empiricalBelief_succ history 0

/-- The Lyapunov lower bound is exercised on the same path whose first-order
played-gain term is nonzero. -/
theorem firstLyapunovBound :
    (1 / (0 + 2 : ℝ)) * game.aggregatePlayedGain history 0 -
        ((Fintype.card (Fin 1) : ℝ) * (Fintype.card (Fin 1) : ℝ)) *
          ((1 / (0 + 2 : ℝ)) ^ 2 * (4 * 1)) ≤
      game.mixedPotential potential (game.empiricalBelief history 2) -
        game.mixedPotential potential (game.empiricalBelief history 1) := by
  simpa using
    (UtilityGame.IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge
      (G := game) exactPotential potential_abs_bound history 0)

end GameTheory.Tests.FictitiousPlayPotential
