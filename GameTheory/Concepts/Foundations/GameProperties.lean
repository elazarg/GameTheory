/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameProperties
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Preference-Parameterized Game Properties

Concept-level bridges for game properties whose core EU versions live in
`GameTheory.Core.GameProperties`.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- `KernelGame.ParetoDominatesFor` delegates to `GameForm.ParetoDominatesFor`. -/
def ParetoDominatesFor (G : KernelGame ι)
    (pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ τ : Profile G) : Prop :=
  G.toGameForm.ParetoDominatesFor pref spref σ τ

/-- `KernelGame.IsParetoEfficientFor` delegates to `GameForm.IsParetoEfficientFor`. -/
def IsParetoEfficientFor (G : KernelGame ι)
    (pref spref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : Profile G) : Prop :=
  G.toGameForm.IsParetoEfficientFor pref spref σ

/-- EU Pareto dominance is exactly Pareto dominance with `euPref`/`euStrictPref`. -/
theorem ParetoDominates_iff_ParetoDominatesFor_eu (G : KernelGame ι)
    (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔ G.ParetoDominatesFor
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) ≥ expect d₂ (fun ω => G.utility ω who))
      (fun who d₁ d₂ => expect d₁ (fun ω => G.utility ω who) > expect d₂ (fun ω => G.utility ω who))
      σ τ := by
  simp [ParetoDominates, ParetoDominatesFor, GameForm.ParetoDominatesFor, KernelGame.eu]

end KernelGame

end GameTheory
