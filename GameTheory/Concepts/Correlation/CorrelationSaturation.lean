/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelationRegimes
import GameTheory.Concepts.Correlation.DominantCorrelatedEq

/-!
# GameTheory.Concepts.Correlation.CorrelationSaturation

**Correlation saturation**: a game is saturated when no correlation device buys
anything beyond public randomization over its mixed Nash equilibria. Every
correlated equilibrium is already realizable as a public signal that selects a
mixed Nash equilibrium (`PublicSignalNash.isCorrelatedEq`, in
`CorrelationRegimes.lean`, gives the reverse containment for free, for any
game). Saturation is the nontrivial direction: `IsCorrelatedEq` gives nothing
that `PublicSignalNash` didn't already.

This is strictly more general than a game having a unique (dominant-strategy)
equilibrium: any game whose correlated-equilibrium polytope coincides with the
convex hull of its mixed-Nash payoffs is saturated, even with many equilibria.
The dominant-strategy case is the degenerate one-signal instance.

Provides:
- `IsCorrelationSaturated` — every correlated equilibrium is a public-signal-Nash
  law.
- `strictDominant_isCorrelationSaturated` — a strictly dominant-strategy profile
  saturates correlation, via the single constant signal selecting it.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- **Correlation saturation.** Every correlated equilibrium of `G` is realizable
as a public signal selecting a mixed Nash equilibrium: correlation devices add
nothing beyond public randomization over `G`'s Nash equilibria. -/
def IsCorrelationSaturated (G : KernelGame ι) [Fintype ι] : Prop :=
  ∀ μ : PMF (Profile G), G.IsCorrelatedEq μ →
    ∃ (Signal : Type) (ν : PMF Signal) (play : Signal → Profile G.mixedExtension),
      G.PublicSignalNash ν play ∧ μ = G.publicCorrelatedLaw ν play

/-- **Dominant strategies saturate correlation.** With a strictly dominant
strategy for every player, the only correlated equilibrium is the point mass at
the dominant-strategy profile, which is trivially a (single, constant) public
signal selecting a mixed Nash equilibrium. -/
theorem strictDominant_isCorrelationSaturated [Fintype ι] [Finite G.Outcome]
    {σ : Profile G} (hdom : ∀ i, G.IsStrictDominant i (σ i)) :
    G.IsCorrelationSaturated := by
  intro μ hCE
  have hμ : μ = PMF.pure σ := (G.strictDominant_isCorrelatedEq_iff hdom).mp hCE
  refine ⟨PUnit, PMF.pure PUnit.unit, fun _ => G.pureMixedProfile σ, ?_, ?_⟩
  · intro _ _
    exact (G.dominant_is_nash σ (fun i => (hdom i).toDominant)).pureMixedProfile_isNash
  · rw [hμ]
    unfold publicCorrelatedLaw
    rw [PMF.pure_bind]
    exact (Math.PMFProduct.pmfPi_pure σ).symm

end KernelGame

end GameTheory
