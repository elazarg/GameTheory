import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# Repeated Games

A finitely repeated game plays a stage game `T` times. Players observe
all past actions and choose stage-game actions at each round.

## Main definitions

* `RepeatedGame` — finitely repeated game
* `RepeatedGame.play` — action profile generated at each round
* `RepeatedGame.avgPayoff` — average payoff over rounds
* `RepeatedGame.totalPayoff` — total payoff (sum over rounds)
* `RepeatedGame.toKernelGame` — bridge to `KernelGame`

## Main results

* `RepeatedGame.constStrategy_isNash` — stage Nash repeated every round is Nash
    of the repeated game
-/

namespace GameTheory

open Math.Probability

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

/-- Generate the action profile at round `t` by running strategies on the history
    built from earlier rounds. -/
noncomputable def play (R : RepeatedGame ι) (σ : R.RProfile) : Fin R.rounds → (∀ i, R.Act i) :=
  fun t => fun i => σ i t (fun k => R.play σ (Fin.castLT k (by omega)))
termination_by t => t.val
decreasing_by exact k.isLt

/-- Average payoff over all rounds. -/
noncomputable def avgPayoff (R : RepeatedGame ι) (σ : R.RProfile) (who : ι) : ℝ :=
  if R.rounds = 0 then 0
  else (1 / R.rounds : ℝ) * ∑ t : Fin R.rounds, R.stageUtil (R.play σ t) who

/-- Total payoff (sum over rounds). -/
noncomputable def totalPayoff (R : RepeatedGame ι) (σ : R.RProfile) (who : ι) : ℝ :=
  ∑ t : Fin R.rounds, R.stageUtil (R.play σ t) who

/-- Constant strategy: play the same action regardless of history. -/
def constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) : R.RProfile :=
  fun i _ _ => a i

open Classical in
/-- Convert to a `KernelGame` using total payoff as utility. -/
noncomputable def toKernelGame (R : RepeatedGame ι) : KernelGame ι :=
  KernelGame.ofEU R.Strategy (fun σ i => R.totalPayoff σ i)

open Classical in
/-- Play under a constant strategy always produces the same action profile. -/
theorem play_constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) (t : Fin R.rounds) :
    R.play (R.constStrategy a) t = a := by
  ext i; simp [play, constStrategy]

open Classical in
/-- Total payoff under constant strategy = rounds × stage payoff. -/
theorem totalPayoff_constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) (who : ι) :
    R.totalPayoff (R.constStrategy a) who =
    R.rounds * R.stageUtil a who := by
  simp only [totalPayoff, play_constStrategy]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

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

open Classical in
/-- If `a` is a stage-game Nash equilibrium, then the constant strategy profile
    playing `a` every round is a Nash equilibrium of the repeated game
    (with respect to total payoff / `toKernelGame`). -/
theorem constStrategy_isNash (R : RepeatedGame ι) (a : ∀ i, R.Act i)
    (hstage : ∀ (who : ι) (a' : R.Act who),
      R.stageUtil a who ≥ R.stageUtil (Function.update a who a') who) :
    R.toKernelGame.IsNash (R.constStrategy a) := by
  intro who s'
  simp only [toKernelGame, KernelGame.eu_ofEU, totalPayoff]
  apply Finset.sum_le_sum
  intro t _
  rw [R.play_constStrategy a t]
  -- The deviation play at round t uses `Function.update (constStrategy a) who s'`
  -- This equals `Function.update a who (s' t history)` for some history
  set σ' := Function.update (R.constStrategy a) who s'
  have hplay : R.play σ' t =
      Function.update a who (s' t (fun k => R.play σ' (Fin.castLT k (by omega)))) := by
    ext i
    simp only [play, σ']
    by_cases h : i = who
    · subst h; simp [Function.update]
    · simp [Function.update, h, constStrategy]
  rw [hplay]
  exact hstage who _

end RepeatedGame

end GameTheory
