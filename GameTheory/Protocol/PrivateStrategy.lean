/-
# Realizing private strategy memory by behavioral policies

A strategy may keep private memory and correlate its responses across
activations. Its memory is internal to the strategy, not part of any game
history. Conditioning on the player's own input/output transcript gives one
behavioral policy with the same external law against every adaptive
environment: the final environment state and the whole transcript agree, not
only payoffs.

The environment evolves from its state and the emitted output, independently
of private memory given that output, and inputs are observations of the
environment state.
-/

import GameTheory.Math.Probability.Conditioning

noncomputable section

namespace GameTheory.Protocol.PrivateStrategy

open GameTheory.Math.Probability

universe um ui uo ue

/-- A strategy with private memory: an initial memory law, and a joint law of
output and next memory for each memory and input. -/
structure Strategy (Memory : Type um) (Input : Type ui) (Output : Type uo) where
  /-- The law of the initial memory. -/
  initial : PMF Memory
  /-- The joint law of the output and the next memory. -/
  respond : Memory → Input → PMF (Output × Memory)

variable {Memory : Type um} {Input : Type ui} {Output : Type uo}

/-- The player's own inputs and outputs, most recent first. It contains no
environment state beyond what the player observed. -/
abbrev Transcript (Input : Type ui) (Output : Type uo) := List (Input × Output)

/-- The law of private memory given the player's own transcript. -/
def posterior (strategy : Strategy Memory Input Output) :
    Transcript Input Output → PMF Memory
  | [] => strategy.initial
  | (input, output) :: past =>
      (fiberPosterior ((posterior strategy past).bind fun memory =>
          strategy.respond memory input) Prod.fst output).map Prod.snd

/-- The behavioral policy of a strategy: the output law given the transcript
and the current input. It does not depend on the environment. -/
def behavioral (strategy : Strategy Memory Input Output)
    (past : Transcript Input Output) (input : Input) : PMF Output :=
  ((posterior strategy past).bind fun memory => strategy.respond memory input).map Prod.fst

variable {Environment : Type ue}

/-- Run a strategy with its private memory for a number of activations,
returning the final environment state and the transcript. -/
def runPrivate (strategy : Strategy Memory Input Output) (observe : Environment → Input)
    (advance : Environment → Output → PMF Environment) :
    ℕ → Transcript Input Output → Environment → Memory →
      PMF (Environment × Transcript Input Output)
  | 0, past, state, _ => PMF.pure (state, past)
  | count + 1, past, state, memory =>
      (strategy.respond memory (observe state)).bind fun response =>
        (advance state response.1).bind fun next =>
          runPrivate strategy observe advance count ((observe state, response.1) :: past)
            next response.2

/-- Run a transcript-local behavioral policy for a number of activations. -/
def runBehavioral (policy : Transcript Input Output → Input → PMF Output)
    (observe : Environment → Input) (advance : Environment → Output → PMF Environment) :
    ℕ → Transcript Input Output → Environment → PMF (Environment × Transcript Input Output)
  | 0, past, state => PMF.pure (state, past)
  | count + 1, past, state =>
      (policy past (observe state)).bind fun output =>
        (advance state output).bind fun next =>
          runBehavioral policy observe advance count ((observe state, output) :: past) next

/-- **Behavioral realization of private memory.** Against every adaptive
environment, the behavioral policy of a strategy has the same law of final
state and transcript as the strategy run with its private memory. -/
theorem realize (strategy : Strategy Memory Input Output) (observe : Environment → Input)
    (advance : Environment → Output → PMF Environment) (count : ℕ)
    (past : Transcript Input Output) (state : Environment) :
    (posterior strategy past).bind (runPrivate strategy observe advance count past state) =
      runBehavioral (behavioral strategy) observe advance count past state := by
  induction count generalizing past state with
  | zero => simp [runPrivate, runBehavioral]
  | succ count ih =>
      let law := (posterior strategy past).bind fun memory =>
        strategy.respond memory (observe state)
      calc
        _ = law.bind (fun response => (advance state response.1).bind fun next =>
            runPrivate strategy observe advance count ((observe state, response.1) :: past)
              next response.2) := by simp only [law, runPrivate, PMF.bind_bind]
        _ = (behavioral strategy past (observe state)).bind fun output =>
            (posterior strategy ((observe state, output) :: past)).bind fun memory =>
              (advance state output).bind fun next =>
                runPrivate strategy observe advance count ((observe state, output) :: past)
                  next memory := by
            conv_lhs => arg 1; rw [eq_bind_fst_fiberPosterior_snd law]
            simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, behavioral, posterior, law]
        _ = (behavioral strategy past (observe state)).bind fun output =>
            (advance state output).bind fun next =>
              (posterior strategy ((observe state, output) :: past)).bind
                (runPrivate strategy observe advance count ((observe state, output) :: past)
                  next) := by
            apply bind_congr_on_support _
            intro output _
            exact PMF.bind_comm ..
        _ = _ := by
            simp only [ih, runBehavioral]

end GameTheory.Protocol.PrivateStrategy
