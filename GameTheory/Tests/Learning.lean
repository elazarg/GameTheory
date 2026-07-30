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

open Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) where
  sig := signature
  play profile := FinDist.pure (profile 0, profile 1)

def utility (outcome : Bool × Bool) (_who : Fin 2) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility := utility

@[simp]
theorem game_play (profile : Profile signature) :
    game.form.play profile = FinDist.pure (profile 0, profile 1) :=
  rfl

@[simp]
theorem game_utility (outcome : Bool × Bool) (who : Fin 2) :
    game.utility outcome who = utility outcome who :=
  rfl

def coordinated : Profile signature := fun _ => false

def mismatched : Profile signature := fun who =>
  if who = 0 then true else false

def roundLaw (round : Fin 2) : FinDist (Profile signature) :=
  if round = 0 then FinDist.pure coordinated else FinDist.pure mismatched

/-- The trace has genuinely positive external regret: after the mismatched
round, player zero would have gained one by committing to `false`. -/
theorem externalRegret_second_round :
    game.externalRegret (roundLaw 1) 0 false = 1 := by
  rw [game.externalRegret_eq_expect_gain]
  rw [show roundLaw 1 = FinDist.pure mismatched by norm_num [roundLaw]]
  rw [FinDist.expect_pure, game_play, game_play, expectedUtility_pure,
    expectedUtility_pure]
  norm_num [game_utility, utility, mismatched]

/-- Every fixed deviation has cumulative regret at most one on the two-round
trace. This is a finite calculation, not an assumed learning guarantee. -/
theorem cumulativeExternalRegret_le_one :
    ∀ who replacement,
      (∑ round, game.externalRegret (roundLaw round) who replacement) ≤ 1 := by
  intro who replacement
  simp_rw [game.externalRegret_eq_expect_gain]
  refine Fin.cases ?_ (fun who => ?_) who
  · cases replacement <;>
    norm_num [roundLaw, game, form, utility, expectedUtility, coordinated,
      mismatched, Fin.sum_univ_two, FinDist.expect_pure, Profile.update]
  · refine Fin.cases ?_ (fun who => Fin.elim0 who) who
    rw [Fin.succ_zero_eq_one']
    cases replacement <;>
      norm_num [roundLaw, game, form, utility, expectedUtility, coordinated,
        mismatched, Fin.sum_univ_two, FinDist.expect_pure, Profile.update]

/-- The no-regret reduction turns the checked cumulative bound into a
`1 / 2`-coarse correlated equilibrium guarantee. -/
theorem timeAverage_isHalfCoarseCorrelatedEq :
    game.IsεCoarseCorrelatedEq (1 / 2)
      (game.timeAverage roundLaw) := by
  simpa using game.timeAverage_isεCoarseCorrelatedEq_of_regret_le
    (roundLaw := roundLaw) (R := 1) cumulativeExternalRegret_le_one

/-- The tolerance is meaningful: the time average is not an exact CCE because
player zero gains `1 / 2` by always choosing `false`. -/
theorem timeAverage_not_coarseCorrelatedEq :
    ¬ IsCoarseCorrelatedEq game.form game.preference
      (game.timeAverage roundLaw) := by
  rw [game.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero]
  intro h
  have hnonpos := h 0 false
  rw [game.externalRegret_timeAverage] at hnonpos
  simp_rw [game.externalRegret_eq_expect_gain] at hnonpos
  norm_num [roundLaw, game, form, utility, expectedUtility, coordinated,
    mismatched, Fin.sum_univ_two, FinDist.expect_pure] at hnonpos

end GameTheory.Tests.Learning
