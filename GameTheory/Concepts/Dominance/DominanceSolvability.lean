/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Dominance.DominanceNash
import Math.Probability

/-!
# Solvability in dominant strategies

A game is *dominant-strategy solvable* if every player has a strictly dominant
strategy. In such a game, there is a unique Nash equilibrium.

This is a stronger property than the textbook notion of *dominance solvability*
(iterated elimination of dominated strategies leaving a unique surviving
profile); every dominant-strategy-solvable game is dominance-solvable, but not
conversely. The unqualified name is reserved for that weaker, standard notion
(not yet formalized), so the dominant-strategy notion is qualified here.

## Main definitions

* `IsDominantStrategySolvable` — every player has a strictly dominant strategy

## Main results

* `IsDominantStrategySolvable.unique_nash` — the unique Nash equilibrium
* `IsDominantStrategySolvable.nash_is_dominant` — the Nash profile consists of dominant strategies
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

/-- A game is *dominant-strategy solvable* if every player has a strictly
dominant strategy (stronger than textbook dominance solvability). -/
def IsDominantStrategySolvable : Prop :=
  ∀ who : ι, ∃ s : G.Strategy who, G.IsStrictDominant who s

open Classical in
/-- The dominant strategy profile. -/
noncomputable def IsDominantStrategySolvable.dominantProfile
    (h : G.IsDominantStrategySolvable) : Profile G :=
  fun i => (h i).choose

/-- The dominant strategy profile is Nash (follows from dominant_is_nash). -/
theorem IsDominantStrategySolvable.isNash (h : G.IsDominantStrategySolvable) :
    G.IsNash (h.dominantProfile G) := by
  classical
  apply dominant_is_nash
  intro i
  have hdom := (h i).choose_spec
  exact hdom.toDominant

open Classical in
/-- In a dominance-solvable game, the Nash equilibrium is unique:
    any Nash profile must use the dominant strategy for each player. -/
theorem IsDominantStrategySolvable.nash_unique
    (h : G.IsDominantStrategySolvable) {σ : Profile G} (hN : G.IsNash σ) :
    σ = h.dominantProfile G := by
  funext i
  have hdom := (h i).choose_spec
  have hbr : G.IsBestResponse i σ (σ i) := by
    intro s'
    have h := hN i s'
    simpa [Function.update_eq_self] using h
  exact hdom.unique_best_response σ hbr

/-- Combining: the dominant profile is the unique Nash equilibrium. -/
theorem IsDominantStrategySolvable.exists_unique_nash (h : G.IsDominantStrategySolvable) :
    ∃! σ : Profile G, G.IsNash σ :=
  ⟨h.dominantProfile G, h.isNash G, fun _ hN => (h.nash_unique G hN)⟩

end KernelGame

end GameTheory
