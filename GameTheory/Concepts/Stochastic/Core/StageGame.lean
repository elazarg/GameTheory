/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Core.Basic
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Existence.NashExistenceMixed

/-!
# Stage Games, Mixed Stage Payoffs, and Markov Profiles

The one-shot stage game of a stochastic game at a fixed state, expected
stage payoffs of mixed action profiles, Markov (state-dependent, mixed)
behavior profiles, and the existence of per-state mixed stage-game Nash
equilibria (Nash's theorem plus choice over states).

These are the stage-level ingredients shared by the proved special cases of
the uniform equilibrium existence problem (see
`GameTheory.Concepts.Stochastic.Classes.Absorbing` and
`GameTheory.Concepts.Stochastic.Classes.TransitionIndependent`).

## Main definitions

* `StochasticGame.stageGame` — the stage game at a state as a `KernelGame`
  with pure joint actions as outcomes
* `StochasticGame.mixedStageEU` — expected stage payoff of a mixed action
  profile at a state
* `StochasticGame.markovBehaviorProfile` — Markov play of state-dependent
  mixed actions
* `StochasticGame.IsMixedStageNash` — per-state mixed stage-Nash property

## Main results

* `StochasticGame.exists_isMixedStageNash` — mixed stage-game Nash
  equilibria can be chosen at every state simultaneously
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

/-- The stage game at state `s`, presented with pure joint actions as
outcomes.  Unlike `stageKernelGame` (built from `KernelGame.ofEU`), the
outcome carrier here is finite whenever the action sets are, which is what
mixed Nash existence needs. -/
def stageGame (G : StochasticGame ι) (s : G.State) : KernelGame ι :=
  KernelGame.ofPureEU G.Act fun a => G.stagePayoff s a

/-- Expected stage payoff of the mixed action profile `m` at state `s`. -/
def mixedStageEU (G : StochasticGame ι) [Fintype ι] (s : G.State)
    (m : ∀ i, PMF (G.Act i)) (who : ι) : ℝ :=
  expect (pmfPi m) fun a => G.stagePayoff s a who

/-- The Markov behavior profile that plays the mixed action `x s i` whenever
the current state is `s`, regardless of the rest of the history. -/
def markovBehaviorProfile (G : StochasticGame ι)
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) : G.BehaviorProfile :=
  fun i _ h => x h.2 i

@[simp] theorem stageActionDist_markovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι]
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist (G.markovBehaviorProfile x) h = pmfPi (x h.2) :=
  rfl

/-- Deviating from Markov play chooses the deviator's current mixed action
and keeps the opponents' Markov mixed actions at the current state. -/
theorem stageActionDist_update_markovBehaviorProfile
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) (who : ι)
    (dev : G.BehaviorStrategy who) {t : ℕ} (h : G.Hist t) :
    G.stageActionDist
        (Function.update (G.markovBehaviorProfile x) who dev) h =
      pmfPi (Function.update (x h.2) who (dev t h)) := by
  unfold stageActionDist
  congr 1
  funext j
  by_cases hj : j = who
  · subst hj
    simp
  · simp [Function.update_of_ne hj, markovBehaviorProfile]

theorem stageEUAt_markovBehaviorProfile (G : StochasticGame ι) [Fintype ι]
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) {t : ℕ} (h : G.Hist t)
    (who : ι) :
    G.stageEUAt (G.markovBehaviorProfile x) h who =
      G.mixedStageEU h.2 (x h.2) who :=
  rfl

/-- `x` plays a mixed stage-game Nash equilibrium at every state: no player
can improve any state's expected stage payoff by a unilateral mixed
deviation. -/
def IsMixedStageNash (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (x : (s : G.State) → ∀ i, PMF (G.Act i)) : Prop :=
  ∀ (s : G.State) (who : ι) (d : PMF (G.Act who)),
    G.mixedStageEU s (Function.update (x s) who d) who ≤
      G.mixedStageEU s (x s) who

/-- Mixed stage-game Nash equilibria can be chosen at every state
simultaneously (Nash's theorem plus choice over states). -/
theorem exists_isMixedStageNash (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] :
    ∃ x : (s : G.State) → ∀ i, PMF (G.Act i), G.IsMixedStageNash x := by
  have hex : ∀ s : G.State, ∃ m : ∀ i, PMF (G.Act i),
      ∀ (who : ι) (d : PMF (G.Act who)),
        G.mixedStageEU s (Function.update m who d) who ≤
          G.mixedStageEU s m who := by
    intro s
    haveI : ∀ i, Finite ((G.stageGame s).Strategy i) :=
      fun i => inferInstanceAs (Finite (G.Act i))
    haveI : ∀ i, Nonempty ((G.stageGame s).Strategy i) :=
      fun i => inferInstanceAs (Nonempty (G.Act i))
    haveI : Finite (G.stageGame s).Outcome :=
      inferInstanceAs (Finite G.JointAct)
    obtain ⟨m, hm⟩ := (G.stageGame s).mixed_nash_exists
    refine ⟨m, fun who d => ?_⟩
    have h1 := hm who d
    rw [KernelGame.mixedExtension_eu, KernelGame.mixedExtension_eu] at h1
    simpa [mixedStageEU, stageGame] using h1
  choose x hx using hex
  exact ⟨x, hx⟩

end StochasticGame

end GameTheory
