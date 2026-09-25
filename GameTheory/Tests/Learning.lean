/-
Discriminating finite trace for no-regret learning.

Two players receive one exactly when their Boolean actions agree. The trace is
coordinated in round zero and mismatched in round one. Player zero therefore
has strictly positive regret in the second round, so the resulting approximate
CCE theorem is not a zero-payoff or already-equilibrium tautology.
-/

import GameTheory.Core.Learning

noncomputable section

namespace GameTheory.Tests.Learning

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) :=
  GameForm.deterministic signature fun profile => (profile 0, profile 1)

def utility (outcome : Bool × Bool) (_who : Fin 2) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility := utility

@[simp]
theorem game_play (profile : Profile signature) :
    game.form.play profile = PMF.pure (profile 0, profile 1) :=
  rfl

@[simp]
theorem game_utility (outcome : Bool × Bool) (who : Fin 2) :
    game.utility outcome who = utility outcome who :=
  rfl

def coordinated : Profile signature := fun _ => false

def mismatched : Profile signature := fun who =>
  if who = 0 then true else false

def roundLaw (round : Fin 2) : PMF (Profile signature) :=
  if round = 0 then PMF.pure coordinated else PMF.pure mismatched

private theorem utilityIntegrable (who : Fin 2) (law : PMF (Bool × Bool)) :
    UtilityIntegrable utility who law := by
  apply payoffIntegrable_of_bounded law (fun outcome => utility outcome who)
    (C := 1)
  rintro ⟨left, right⟩
  cases who
  all_goals by_cases h : left = right <;> simp [utility, h]

/-- The finite base outcome laws integrate each player's utility. -/
theorem baseIntegrable (who : Fin 2)
    (law : PMF (Profile signature)) :
    UtilityIntegrable utility who (game.form.outcomeLaw law) :=
  utilityIntegrable who (game.form.outcomeLaw law)

/-- The finite deviating outcome laws integrate each player's utility. -/
theorem deviationIntegrable (who : Fin 2)
    (replacement : Bool) (law : PMF (Profile signature)) :
    UtilityIntegrable utility who
      (law.bind fun profile => game.form.play
        (Profile.update profile who replacement)) := by
  apply payoffIntegrable_of_bounded
    (law.bind fun profile => game.form.play
      (Profile.update profile who replacement))
    (fun outcome => utility outcome who) (C := 1)
  rintro ⟨left, right⟩
  cases who
  all_goals by_cases h : left = right <;> simp [utility, h]

/-- The trace has genuinely positive external regret: after the mismatched
round, player zero would have gained one by committing to `false`. -/
theorem externalRegret_second_round :
    game.externalRegret (roundLaw 1) 0 false
      (baseIntegrable 0 (roundLaw 1))
      (deviationIntegrable 0 false (roundLaw 1)) = 1 := by
  simp [UtilityGame.externalRegret, roundLaw, game, form, utility, mismatched,
    expectedUtility_pure]

/-- Every fixed deviation has cumulative regret at most one on the two-round
trace. This is a finite calculation, not an assumed learning guarantee. -/
theorem cumulativeExternalRegret_le_one :
    ∀ who replacement,
      (∑ round, game.externalRegret (roundLaw round) who replacement
        (baseIntegrable who (roundLaw round))
        (deviationIntegrable who replacement (roundLaw round))) ≤ 1 := by
  intro who replacement
  simp_rw [UtilityGame.externalRegret]
  refine Fin.cases ?_ (fun who => ?_) who
  · cases replacement <;>
    norm_num [roundLaw, UtilityGame.externalRegret, game, form, utility, expectedUtility,
      coordinated, mismatched, Fin.sum_univ_two, expectedUtility_pure, expect_pure,
      Profile.update]
  · refine Fin.cases ?_ (fun who => Fin.elim0 who) who
    rw [Fin.succ_zero_eq_one']
    cases replacement <;>
      norm_num [roundLaw, UtilityGame.externalRegret, game, form, utility, expectedUtility,
        coordinated, mismatched, Fin.sum_univ_two, expectedUtility_pure, expect_pure,
        Profile.update]

/-- The no-regret reduction turns the checked cumulative bound into a
`1 / 2`-coarse correlated equilibrium guarantee. -/
theorem timeAverage_isHalfCoarseCorrelatedEq :
    IsεCoarseCorrelatedEq game.form game.utility (1 / 2)
      (game.form.timeAverage roundLaw) := by
  simpa using game.timeAverage_isεCoarseCorrelatedEq_of_regret_le
    (roundLaw := roundLaw) (R := 1)
    (hbase := fun round who => baseIntegrable who (roundLaw round))
    (hdev := fun round who action =>
      deviationIntegrable who action (roundLaw round))
    (hregret := cumulativeExternalRegret_le_one)

/-- The tolerance is meaningful: the time average is not an exact CCE because
player zero gains `1 / 2` by always choosing `false`. -/
theorem timeAverage_not_coarseCorrelatedEq :
    ¬ IsCoarseCorrelatedEq game.form game.preference
      (game.form.timeAverage roundLaw) := by
  rw [game.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero]
  intro h
  rw [game.isεCoarseCorrelatedEq_iff_externalRegret_le] at h
  have hnonpos := h 0 false
  rcases hnonpos with ⟨hbase, hdev, hle⟩
  have hvalue : game.externalRegret (game.form.timeAverage roundLaw) 0 false
      hbase hdev = 1 / 2 := by
    rw [game.externalRegret_timeAverage
      (hbase := fun round => baseIntegrable 0 (roundLaw round))
      (hdev := fun round => deviationIntegrable 0 false (roundLaw round))]
    norm_num [UtilityGame.externalRegret, roundLaw, game, form, utility,
      expectedUtility, expect_pure, coordinated, mismatched, Fin.sum_univ_two]
  have hle' : game.externalRegret (game.form.timeAverage roundLaw) 0 false
      hbase hdev ≤ 0 := hle
  rw [hvalue] at hle'
  norm_num at hle'

/-! ### Independent self-play API -/

/-- Constant coordinated independent self-play has zero regret and therefore
induces an exact coarse correlated equilibrium through the product-law bridge. -/
theorem coordinated_independentSelfPlay_isCoarseCorrelatedEq :
    let mixedProfile : Profile signature.mixed := fun _ => PMF.pure false
    IsεCoarseCorrelatedEq game.form game.utility 0
      (game.form.timeAverage fun _ : Fin 1 => independentProduct mixedProfile) := by
  dsimp
  simpa using game.selfPlay_timeAverage_isεCoarseCorrelatedEq
    (lo := fun _ => 0) (width := 1)
    (hband := by
      intro who ⟨left, right⟩
      cases who
      all_goals by_cases h : left = right <;> norm_num [utility, h])
    (mixedProfile := fun _ : Fin 1 => fun _ => PMF.pure false)
    (bound := 0) (by
      intro who action
      have hbase : expectedUtility game.utility who
          (game.form.mixed.play (fun _ => PMF.pure false))
          (utilityIntegrable who
            (game.form.mixed.play (fun _ => PMF.pure false))) = 1 := by
        have hprofile : (fun _ : Fin 2 => PMF.pure false) =
            game.form.purify coordinated := by
          funext player
          simp [GameForm.purify, coordinated]
        rw [hprofile, GameForm.mixed_play_purify]
        simp [game, form, utility, coordinated, expectedUtility_pure]
      have hdev : expectedUtility game.utility who
          (game.form.mixed.play
            (Profile.update (fun _ => PMF.pure false) who (PMF.pure action)))
          (utilityIntegrable who
            (game.form.mixed.play
              (Profile.update (fun _ => PMF.pure false) who (PMF.pure action))))
          ≤ 1 := by
        let law := game.form.mixed.play
          (Profile.update (fun _ => PMF.pure false) who (PMF.pure action))
        have hmono := expect_mono
          (μ := law)
          (hfg := fun outcome _ => by
            by_cases h : outcome.1 = outcome.2 <;> simp [utility, h])
          (utilityIntegrable who law) (payoffIntegrable_constant law 1)
        calc
          expectedUtility game.utility who law (utilityIntegrable who law) =
              expect law (fun outcome => utility outcome who)
                (utilityIntegrable who law) := rfl
          _ ≤ expect law (fun _ => (1 : ℝ))
                (payoffIntegrable_constant law 1) := hmono
          _ = 1 := expect_constant law 1 (payoffIntegrable_constant law 1)
      simp only [Fin.sum_univ_one]
      rw [hbase]
      linarith)

end GameTheory.Tests.Learning
