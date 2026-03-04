import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# Stochastic Games

A stochastic game (Shapley, 1953) extends a normal-form game with states
and probabilistic transitions between states depending on the joint action.

## Main definitions

* `StochasticGame` — stochastic game with states, actions, and transitions
* `StochasticGame.MarkovStrategy` — stationary (Markov) strategy
* `StochasticGame.stagePayoff` — single-stage expected payoff
* `StochasticGame.stageKernelGame` — stage game at a state as a `KernelGame`

## Main results

* `IsMarkovNash_iff_all_stage_nash` — Markov Nash ↔ stage-game Nash at every state
-/

namespace GameTheory

open Math.Probability

/-- A stochastic game: at each state, players choose actions simultaneously,
    receive payoffs, and the game transitions to a new state. -/
structure StochasticGame (ι : Type) where
  /-- State space. -/
  State : Type
  /-- Per-player action set (may depend on state). -/
  Act : ι → Type
  /-- Stage payoff given state and joint action. -/
  stagePayoff : State → (∀ i, Act i) → ι → ℝ
  /-- Transition kernel: given state and joint action, distribution over next state. -/
  transition : State → (∀ i, Act i) → PMF State
  /-- Discount factor in [0, 1). -/
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

namespace StochasticGame

variable {ι : Type}

/-- A Markov (stationary) strategy: action depends only on current state. -/
abbrev MarkovStrategy (G : StochasticGame ι) (i : ι) := G.State → G.Act i

/-- A Markov strategy profile. -/
abbrev MarkovProfile (G : StochasticGame ι) := ∀ i, G.MarkovStrategy i

/-- Single-stage expected payoff at a given state under a Markov profile. -/
noncomputable def stageEU (G : StochasticGame ι) (σ : G.MarkovProfile)
    (s : G.State) (who : ι) : ℝ :=
  G.stagePayoff s (fun i => σ i s) who

open Classical in
/-- Markov Nash equilibrium: no player can improve by unilateral deviation
    of their Markov strategy at any single state.
    (This is a stage-game Nash condition, not the full discounted-payoff Nash.) -/
def IsMarkovNash (G : StochasticGame ι) (σ : G.MarkovProfile) : Prop :=
  ∀ (s : G.State) (who : ι) (a' : G.Act who),
    G.stagePayoff s (fun i => σ i s) who ≥
    G.stagePayoff s (Function.update (fun i => σ i s) who a') who

open Classical in
/-- The stage game at state `s` as a `KernelGame`. -/
noncomputable def stageKernelGame (G : StochasticGame ι) (s : G.State) : KernelGame ι :=
  KernelGame.ofEU G.Act (fun a i => G.stagePayoff s a i)

open Classical in
/-- Markov Nash ↔ the Markov profile induces a Nash equilibrium
    at every state's stage game. -/
theorem isMarkovNash_iff_all_stage_nash (G : StochasticGame ι) (σ : G.MarkovProfile) :
    G.IsMarkovNash σ ↔ ∀ s : G.State,
      (G.stageKernelGame s).IsNash (fun i => σ i s) := by
  constructor
  · intro hMN s who a'
    simp only [stageKernelGame, KernelGame.eu_ofEU]
    exact hMN s who (a' )
  · intro hN s who a'
    have h := hN s who a'
    simp only [stageKernelGame, KernelGame.eu_ofEU] at h
    exact h

end StochasticGame

end GameTheory
