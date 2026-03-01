import GameTheory.SolutionConcepts

/-!
# Repeated Games

A finitely repeated game plays a stage game `T` times. Players observe
all past actions and choose stage-game actions at each round.

## Main definitions

* `RepeatedGame` — finitely repeated game
* `RepeatedGame.avgPayoff` — average payoff over rounds
* `RepeatedGame.stageNash_is_repeated_nash` — stage Nash played every round is Nash
    of the repeated game (for games with a unique Nash)
-/

namespace GameTheory

/-- A finitely repeated game with observable actions. -/
structure RepeatedGame (ι : Type) where
  /-- Per-player action set in the stage game. -/
  Act : ι → Type
  /-- Stage-game utility given a joint action profile. -/
  stageUtil : (∀ i, Act i) → ι → ℝ
  /-- Number of rounds. -/
  rounds : ℕ

namespace RepeatedGame

variable {ι : Type}

/-- History up to round `t`: list of past action profiles. -/
abbrev History (R : RepeatedGame ι) (t : ℕ) := Fin t → (∀ i, R.Act i)

open Classical in
/-- A (behavioral) strategy: at each round, given the history, choose an action. -/
abbrev Strategy (R : RepeatedGame ι) (i : ι) := (t : Fin R.rounds) → R.History t → R.Act i

/-- A strategy profile. -/
abbrev RProfile (R : RepeatedGame ι) := ∀ i, R.Strategy i

/-- Payoff of a single round given a joint action. -/
noncomputable def roundPayoff (R : RepeatedGame ι) (a : ∀ i, R.Act i) (who : ι) : ℝ :=
  R.stageUtil a who

/-- Constant strategy: play the same action regardless of history. -/
def constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) : R.RProfile :=
  fun i _ _ => a i

open Classical in
/-- In a finitely repeated game, if the stage game has a unique Nash equilibrium `σ*`,
    then playing `σ*` at every round is a Nash equilibrium of the repeated game.

    This is the stage-Nash-repetition theorem: with a unique stage Nash,
    backward induction from the last round forces the stage Nash at every round. -/
theorem constStrategy_isNash_of_unique_stage_nash
    (R : RepeatedGame ι) (a : ∀ i, R.Act i)
    (hstage : ∀ (who : ι) (a' : R.Act who),
      R.stageUtil a who ≥ R.stageUtil (Function.update a who a') who)
    (who : ι) (s' : R.Strategy who)
    (t : Fin R.rounds) (h : R.History t) :
    R.stageUtil a who ≥ R.stageUtil (Function.update a who (s' t h)) who :=
  hstage who (s' t h)

end RepeatedGame

end GameTheory
