/-
Hostile finite consumer for empirical potential recurrences.

A one-player process starts at the inferior action and then plays the unique
best action forever.  Its first played gain is one, so the first empirical
potential step is genuinely nonzero rather than a constant-path tautology.
-/

import GameTheory.Core.FictitiousPlayPotential

noncomputable section

namespace GameTheory.Tests.FictitiousPlayPotential

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature (Fin 1) where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def form : GameForm (Fin 1) :=
  GameForm.deterministic signature fun profile => profile 0

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
  have hi : ∀ profile : Profile signature,
      PayoffIntegrable (form.play profile) reward := by
    intro profile
    exact payoffIntegrable_pure _ _
  have h := isExactPotential_of_identicalInterests
    (F := form) reward hi
  simpa [form, expect_pure] using h

theorem firstBelief :
    game.form.empiricalBelief history 1 = game.form.purify allFalse := by
  funext who
  show (PMF.uniformOfFintype (Fin 1)).map
      (fun round : Fin 1 => history round.val who) = PMF.pure false
  have hconstant : (fun round : Fin 1 => history round.val who) =
      fun _ => false := by
    funext round
    have hround : round = 0 := Subsingleton.elim _ _
    subst round
    rfl
  rw [hconstant]
  exact PMF.map_const _ false

theorem expectedUtility_update
    (mixedProfile : Profile game.form.sig.mixed)
    (replacement : PMF Bool)
    (hwhole : UtilityIntegrable game.utility 0
      (game.form.mixed.play
        (Profile.update mixedProfile 0 replacement))) :
    expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update mixedProfile 0 replacement)) hwhole =
      expect replacement reward (payoffIntegrable_of_bounded
        replacement reward (C := 1) fun action => by
          cases action <;> norm_num [reward]) := by
  let updatedProfile := Profile.update mixedProfile 0 replacement
  let hcond : ∀ action, UtilityIntegrable game.utility 0
      (game.form.mixed.play
        (Profile.update updatedProfile 0 (PMF.pure action))) := by
    intro action
    exact payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by
      cases outcome <;> norm_num [game, reward]
  have havg := expectedUtility_mixed_eq_expect game.form game.utility
    updatedProfile 0 hwhole hcond
  have hpureValue : ∀ action,
      expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update updatedProfile 0 (PMF.pure action)))
          (hcond action) = reward action := by
    intro action
    have hprofile :
        Profile.update updatedProfile 0 (PMF.pure action) =
          game.form.purify (fun _ => action) := by
      funext who
      have hwho : who = 0 := Subsingleton.elim _ _
      subst who
      simp [GameForm.purify]
    have hlaw : game.form.mixed.play
        (Profile.update updatedProfile 0 (PMF.pure action)) = PMF.pure action := by
      rw [hprofile, GameForm.mixed_play_purify]
    have hguard := payoffIntegrable_congr_law hlaw (hcond action)
    rw [expectedUtility_congr_law game.utility 0 hlaw (hcond action) hguard,
      expectedUtility_pure]
  calc
    expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update mixedProfile 0 replacement)) hwhole =
      expect replacement
        (fun action => expectedUtility game.utility 0
          (game.form.mixed.play
            (Profile.update updatedProfile 0 (PMF.pure action)))
          (hcond action)) _ := havg
    _ = expect replacement reward
        (payoffIntegrable_of_bounded replacement reward (C := 1)
          (by intro action; cases action <;> norm_num [reward])) := by
      apply expect_congr_on_support
      · intro action _
        exact hpureValue action

/-- The inferior initial observation followed by `true` is genuine fictitious
play; no later action can improve on reward one. -/
theorem isFictitiousPlay : game.IsFictitiousPlay history := by
  intro t who replacement
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  rw [euPreference_apply]
  have hplayed : history (t + 1) 0 = true := by simp [history]
  let belief := game.form.empiricalBelief history (t + 1)
  let preferred := game.form.mixed.play
    (Profile.update belief 0 (PMF.pure (history (t + 1) 0)))
  let alternative := game.form.mixed.play
    (Profile.update belief 0 replacement)
  have hpreferred : UtilityIntegrable game.utility 0 preferred :=
    payoffIntegrable_of_bounded preferred _ (C := 1) fun outcome => by
      cases outcome <;> norm_num [game, reward]
  have halternative : UtilityIntegrable game.utility 0 alternative :=
    payoffIntegrable_of_bounded alternative _ (C := 1) fun outcome => by
      cases outcome <;> norm_num [game, reward]
  refine ⟨hpreferred, halternative, ?_⟩
  have hAltVal := expectedUtility_update belief replacement halternative
  have hPrefVal := expectedUtility_update belief (PMF.pure (history (t + 1) 0))
    hpreferred
  have hle := expect_mono
    (μ := replacement) (f := reward) (g := fun _ => 1)
    (fun action _ => by cases action <;> norm_num [reward])
    (payoffIntegrable_of_bounded replacement reward (C := 1)
      (by intro action; cases action <;> norm_num [reward]))
    (payoffIntegrable_constant replacement 1)
  rw [expect_constant] at hle
  rw [expect_pure] at hPrefVal
  norm_num [reward] at hPrefVal
  calc
    expectedUtility game.utility 0 alternative halternative =
        expect replacement reward _ := by
          simpa [alternative, belief] using hAltVal
    _ ≤ 1 := hle
    _ = expectedUtility game.utility 0 preferred hpreferred := by
      simpa [preferred, game, reward, hplayed] using hPrefVal.symm

theorem potential_abs_bound (profile : Profile signature) :
    |potential profile| ≤ 1 := by
  simp only [potential, reward]
  split <;> norm_num

/-- The first action chosen against the inferior empirical belief gains one. -/
theorem firstPlayedGain : game.playedGain history 0 0
    (payoffIntegrable_of_bounded
      (game.form.mixed.play (game.form.empiricalBelief history 1))
      (fun outcome => game.utility outcome 0) (C := 1)
      (by intro outcome; cases outcome <;> norm_num [game, reward]))
    (payoffIntegrable_of_bounded
      (game.form.mixed.play
        (Profile.update (game.form.empiricalBelief history 1) 0
          (PMF.pure (history 1 0))))
      (fun outcome => game.utility outcome 0) (C := 1)
      (by intro outcome; cases outcome <;> norm_num [game, reward])) = 1 := by
  rw [UtilityGame.playedGain, firstBelief]
  unfold UtilityGame.mixedGain
  have hprofile :
      Profile.update (game.form.purify allFalse) 0 (PMF.pure true) =
        game.form.purify (Profile.update allFalse 0 true) := by
    funext who
    have hwho : who = 0 := Subsingleton.elim _ _
    subst who
    simp [GameForm.purify]
  have hbaseLaw : game.form.mixed.play (game.form.purify allFalse) =
      PMF.pure false := by
    rw [GameForm.mixed_play_purify]
    rfl
  have hplayedLaw : game.form.mixed.play
      (Profile.update (game.form.purify allFalse) 0 (PMF.pure true)) =
        PMF.pure true := by
    rw [hprofile, GameForm.mixed_play_purify]
    rfl
  have hplayedSource := payoffIntegrable_of_bounded
    (game.form.mixed.play
      (Profile.update (game.form.empiricalBelief history 1) 0
        (PMF.pure (history 1 0))))
    (fun outcome => game.utility outcome 0) (C := 1)
    (by intro outcome; cases outcome <;> norm_num [game, reward])
  have hbase := payoffIntegrable_congr_law hbaseLaw.symm
    (payoffIntegrable_of_bounded (PMF.pure false)
      (fun outcome => game.utility outcome 0) (C := 1)
      (by intro outcome; cases outcome <;> norm_num [game, reward]))
  have hplayedPure := payoffIntegrable_of_bounded (PMF.pure true)
    (fun outcome => game.utility outcome 0) (C := 1)
    (by intro outcome; cases outcome <;> norm_num [game, reward])
  have hbasePure := payoffIntegrable_of_bounded (PMF.pure false)
    (fun outcome => game.utility outcome 0) (C := 1)
    (by intro outcome; cases outcome <;> norm_num [game, reward])
  have hplayedEq := expectedUtility_congr_law game.utility 0 hplayedLaw
    hplayedSource hplayedPure
  have hbaseEq := expectedUtility_congr_law game.utility 0 hbaseLaw
    hbase hbasePure
  simp [history]
  rw [hplayedEq, hbaseEq]
  simp [expectedUtility_pure, game, form, reward]

/-- The first empirical-potential increment is the nonzero half-step predicted
by the general recurrence. -/
theorem firstPotentialStep :
    game.form.mixedPotential potential
        (Profile.update (game.form.empiricalBelief history 1) 0
          (game.form.empiricalMarginal history 0 2))
        (payoffIntegrable_of_bounded
          (independentProduct (Profile.update
            (game.form.empiricalBelief history 1) 0
            (game.form.empiricalMarginal history 0 2))) potential
          potential_abs_bound) -
      game.form.mixedPotential potential (game.form.empiricalBelief history 1)
        (payoffIntegrable_of_bounded
          (independentProduct (game.form.empiricalBelief history 1)) potential
          potential_abs_bound) = 1 / 2 := by
  have hplay : game.IsFictitiousPlay history := isFictitiousPlay
  obtain ⟨hnext, hstep⟩ :=
    UtilityGame.IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub
      (G := game) exactPotential history 0 0
      (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := game) hplay 0 0)
      (UtilityGame.IsFictitiousPlay.deviation_integrable (G := game) hplay 0 0
        (PMF.pure (history 1 0)))
      (payoffIntegrable_of_bounded
        (independentProduct (game.form.empiricalBelief history 1)) potential
        potential_abs_bound)
      (payoffIntegrable_of_bounded
        (independentProduct (Profile.update
          (game.form.empiricalBelief history 1) 0 (PMF.pure (history 1 0))))
        potential potential_abs_bound)
  have hvalue := firstPlayedGain
  have hstep' :
      game.form.mixedPotential potential
          (Profile.update (game.form.empiricalBelief history 1) 0
            (game.form.empiricalMarginal history 0 2))
          (payoffIntegrable_of_bounded
            (independentProduct (Profile.update
              (game.form.empiricalBelief history 1) 0
              (game.form.empiricalMarginal history 0 2))) potential
            potential_abs_bound) -
        game.form.mixedPotential potential (game.form.empiricalBelief history 1)
          (payoffIntegrable_of_bounded
            (independentProduct (game.form.empiricalBelief history 1)) potential
            potential_abs_bound) =
      (1 / (0 + 2 : ℝ)) * game.playedGain history 0 0
          (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := game) hplay 0 0)
          (UtilityGame.IsFictitiousPlay.deviation_integrable (G := game) hplay 0 0
            (PMF.pure (history 1 0))) := by
    simpa using hstep
  rw [hvalue] at hstep'
  norm_num at hstep' ⊢
  exact hstep'

/-- The generic aggregate-improvement bound specializes to a process with a
strictly positive first played gain. -/
theorem firstImprovementBound :
    game.mixedImprovement (game.form.empiricalBelief history 1)
        (fun who action => UtilityGame.IsFictitiousPlay.deviation_integrable
          (G := game) isFictitiousPlay 0 who (PMF.pure action)) ≤
      game.weightedPlayedGain history 0
        (fun who => UtilityGame.IsFictitiousPlay.incumbent_integrable
          (G := game) isFictitiousPlay 0 who)
        (fun who => UtilityGame.IsFictitiousPlay.deviation_integrable
          (G := game) isFictitiousPlay 0 who
            (PMF.pure (history 1 who))) :=
  UtilityGame.IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
    (G := game) isFictitiousPlay 0

/-- The quantitative one-coordinate estimate applies to the same nonzero first
step; it is not proved only for constant trajectories. -/
theorem firstPotentialStep_abs_bound :
    |game.form.mixedPotential potential
          (Profile.update (game.form.empiricalBelief history 1) 0
            (game.form.empiricalMarginal history 0 2))
          (payoffIntegrable_of_bounded
            (independentProduct (Profile.update
              (game.form.empiricalBelief history 1) 0
              (game.form.empiricalMarginal history 0 2))) potential
            potential_abs_bound) -
        game.form.mixedPotential potential (game.form.empiricalBelief history 1)
          (payoffIntegrable_of_bounded
            (independentProduct (game.form.empiricalBelief history 1)) potential
            potential_abs_bound)| ≤
      (1 / (0 + 2 : ℝ)) * (2 * 1) := by
  simpa using
    (game.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential potential_abs_bound history
      (game.form.empiricalBelief history 1) 0 0 rfl)

/-- The uniform `4C/(t+2)` gain-stability estimate includes the changed
player's own coordinate. -/
theorem firstGainStep_abs_bound :
    |game.mixedPotentialGainOfAbsBound potential potential_abs_bound
          (Profile.update (game.form.empiricalBelief history 1) 0
            (game.form.empiricalMarginal history 0 2)) 0 true -
        game.mixedPotentialGainOfAbsBound potential potential_abs_bound
          (game.form.empiricalBelief history 1) 0 true| ≤
      (1 / (0 + 2 : ℝ)) * (4 * 1) := by
  simpa using
    (game.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
      potential potential_abs_bound history
      (game.form.empiricalBelief history 1) true 0 rfl)

theorem firstAggregatePlayedGain :
    game.aggregatePlayedGain history 0
      (fun who => UtilityGame.IsFictitiousPlay.incumbent_integrable
        (G := game) isFictitiousPlay 0 who)
      (fun who => UtilityGame.IsFictitiousPlay.deviation_integrable
        (G := game) isFictitiousPlay 0 who
          (PMF.pure (history 1 who))) = 1 := by
  rw [UtilityGame.aggregatePlayedGain]
  simpa using firstPlayedGain

/-- The all-player sweep is concrete even in the minimal hostile fixture: its
single update produces the next empirical belief. -/
theorem firstAdvanceAll :
    game.advanceMarginals history 0 Finset.univ.toList
        (game.form.empiricalBelief history 1) =
      game.form.empiricalBelief history 2 := by
  simpa using game.advanceMarginals_univ_eq_empiricalBelief_succ history 0

/-- The Lyapunov lower bound is exercised on the same path whose first-order
played-gain term is nonzero. -/
theorem firstLyapunovBound :
    (1 / (0 + 2 : ℝ)) * game.aggregatePlayedGain history 0
        (fun who => UtilityGame.IsFictitiousPlay.incumbent_integrable
          (G := game) isFictitiousPlay 0 who)
        (fun who => UtilityGame.IsFictitiousPlay.deviation_integrable
          (G := game) isFictitiousPlay 0 who
            (PMF.pure (history 1 who))) -
        ((Fintype.card (Fin 1) : ℝ) * (Fintype.card (Fin 1) : ℝ)) *
          ((1 / (0 + 2 : ℝ)) ^ 2 * (4 * 1)) ≤
      game.form.mixedPotential potential (game.form.empiricalBelief history 2)
          (payoffIntegrable_of_bounded
            (independentProduct (game.form.empiricalBelief history 2)) potential
            potential_abs_bound) -
        game.form.mixedPotential potential (game.form.empiricalBelief history 1)
          (payoffIntegrable_of_bounded
            (independentProduct (game.form.empiricalBelief history 1)) potential
            potential_abs_bound) := by
  simpa using
    (UtilityGame.IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge
      (G := game) exactPotential potential_abs_bound isFictitiousPlay 0)

end GameTheory.Tests.FictitiousPlayPotential
