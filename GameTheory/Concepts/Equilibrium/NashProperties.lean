/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Foundations.BestResponse
import GameTheory.Concepts.Foundations.Deviation
import Math.Probability

/-!
# Nash Equilibrium Properties

General properties and characterizations of Nash equilibria.

## Main results

* `isNash_iff_no_improving` — Nash ↔ no improving deviation exists
* `isNash_update_bestResponse` — replacing a player's strategy by another best
  response preserves their EU
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

open Classical in
/-- Nash equilibrium ↔ no player has a strictly improving deviation. -/
theorem isNash_iff_no_improving (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ¬ ∃ (who : ι) (s' : G.Strategy who),
      G.eu (Function.update σ who s') who > G.eu σ who := by
  constructor
  · intro hN ⟨who, s', himprove⟩
    have := hN who s'
    linarith
  · intro h who s'
    by_contra hlt
    push Not at hlt
    exact h ⟨who, s', hlt⟩

open Classical in
/-- Nash equilibrium ↔ no strictly improving unilateral deviation map exists. -/
theorem isNash_iff_no_improving_unilateralDeviation (G : KernelGame ι) {σ : Profile G} :
    G.IsNash σ ↔ ¬ ∃ (who : ι) (dev : G.Strategy who → G.Strategy who),
      G.euAfterDeviation who (G.unilateralDeviation who dev) σ > G.eu σ who := by
  constructor
  · intro hN ⟨who, dev, himprove⟩
    have hle := hN who (dev (σ who))
    have hnot :
        ¬ G.euAfterDeviation who (G.unilateralDeviation who dev) σ > G.eu σ who := by
      simpa [KernelGame.euAfterDeviation, KernelGame.unilateralDeviation] using not_lt_of_ge hle
    exact hnot himprove
  · intro h who s'
    by_contra hlt
    have himprove :
        G.euAfterDeviation who (G.unilateralDeviation who (fun _ => s')) σ > G.eu σ who := by
      simpa [KernelGame.euAfterDeviation, KernelGame.unilateralDeviation] using hlt
    exact h ⟨who, fun _ => s', himprove⟩

open Classical in
/-- Nash is preserved by a player replacing their strategy with another
    best response (when both are best responses). -/
theorem isNash_update_bestResponse
    {G : KernelGame ι} {σ : Profile G} (hN : G.IsNash σ)
    {who : ι} {s' : G.Strategy who}
    (hbr : G.IsBestResponse who σ s') :
    G.eu (Function.update σ who s') who = G.eu σ who := by
  apply le_antisymm
  · have := hN who s'; linarith
  · have h1 := hbr (σ who)
    rw [Function.update_eq_self] at h1
    linarith

end KernelGame

end GameTheory
