/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Repeated.Basic

/-!
# Uniform Equilibrium

A repeated-game strategy profile is a uniform equilibrium if its long-run
average payoff exists and, for every `ε > 0`, it is an ε-Nash equilibrium of
every sufficiently long finitely repeated game under average payoffs
(Aumann–Maschler; Mertens–Neyman; Sorin): a single horizon threshold `T₀`,
depending only on `ε`, works for all longer truncations.  Payoff convergence
is part of the concept — without it, profiles whose average payoffs oscillate
forever (e.g. alternating distinct stage Nash equilibria over ever-longer
blocks) would qualify despite having no long-run payoff.

## Main definitions

* `KernelGame.IsεFiniteRepeatedNash` — ε-Nash equilibrium of the `T`-stage
  finitely repeated game under average payoffs
* `KernelGame.IsUniformεEquilibrium` — ε-Nash of every sufficiently long
  finitely repeated game
* `KernelGame.IsUniformEquilibrium` — uniform ε-equilibrium for every `ε > 0`

## Main results

* `stationaryRepeatedProfile_isUniformEquilibrium_of_isNash` —
  stationary repetition of a stage-game Nash equilibrium is a uniform
  equilibrium
-/

noncomputable section

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- ε-Nash equilibrium of the `T`-stage finitely repeated game under average
payoffs: no unilateral replacement of a whole history-dependent repeated
strategy gains more than `ε`. -/
def IsεFiniteRepeatedNash (G : KernelGame ι) [DecidableEq ι] (T : ℕ) (ε : ℝ)
    (σ : G.RepeatedProfile) : Prop :=
  ∀ who (dev : G.RepeatedStrategy who),
    G.finiteAveragePayoff T σ who + ε ≥
      G.finiteAveragePayoff T (Function.update σ who dev) who

/-- Uniform ε-equilibrium: an ε-Nash equilibrium of every sufficiently long
finitely repeated game, with a single horizon threshold. -/
def IsUniformεEquilibrium (G : KernelGame ι) [DecidableEq ι] (ε : ℝ)
    (σ : G.RepeatedProfile) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.IsεFiniteRepeatedNash T ε σ

/-- Uniform equilibrium: the long-run average payoff exists, and the profile
is a uniform ε-equilibrium for every positive `ε`. -/
def IsUniformEquilibrium (G : KernelGame ι) [DecidableEq ι]
    (σ : G.RepeatedProfile) : Prop :=
  (∃ v : Payoff ι, G.HasLongRunAveragePayoff σ v) ∧
    ∀ ε : ℝ, 0 < ε → G.IsUniformεEquilibrium ε σ

/-- Stationary repetition of a stage-game Nash equilibrium is a uniform
equilibrium: its long-run average payoff is the stage payoff, and it is an
exact Nash equilibrium of every nonempty finite truncation. -/
theorem stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    (G : KernelGame ι) [DecidableEq ι] {σ : Profile G} (hN : G.IsNash σ) :
    G.IsUniformEquilibrium (G.stationaryRepeatedProfile σ) := by
  refine ⟨⟨G.eu σ, G.hasLongRunAveragePayoff_stationaryRepeatedProfile σ⟩,
    fun ε hε => ?_⟩
  refine ⟨1, fun T hT who dev => ?_⟩
  have hT0 : T ≠ 0 := by omega
  rw [G.finiteAveragePayoff_stationaryRepeatedProfile hT0]
  have hle : G.finiteAveragePayoff T
      (Function.update (G.stationaryRepeatedProfile σ) who dev) who ≤
        G.eu σ who := by
    refine G.finiteAveragePayoff_le_of_forall_stageEU_le (fun t => ?_) hT0
    rw [G.repeatedPlay_update_stationaryRepeatedProfile σ who dev t]
    exact hN who _
  linarith

end KernelGame

end GameTheory
