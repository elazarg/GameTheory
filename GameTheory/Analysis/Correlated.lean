/-
# Existence of correlated equilibria

Every finite game has a correlated equilibrium, and hence a coarse correlated
equilibrium.  Nothing new has to be fixed: Nash existence supplies a product
law, the canonical mixed-to-correlated bridge interprets it as a recommendation
scheme, and forgetting recommendation dependence gives the coarse result.

This module deliberately lives in `Analysis` because it consumes mixed-Nash
existence.  The bridges themselves remain in the topology-free core.
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι] {F : GameForm ι}
variable [∀ i, Fintype (F.sig.Strategy i)] [∀ i, Nonempty (F.sig.Strategy i)]

/-- **Every finite game has a correlated equilibrium.**  The outcome type need
not be finite and its utility need not be supplied with a separate bound:
finite support makes every expectation used by the canonical semantics finite. -/
theorem exists_isCorrelatedEq (utility : F.sig.Outcome → ι → ℝ) :
    ∃ law : FinDist (Profile F.sig), IsCorrelatedEq F (euPreference utility) law := by
  obtain ⟨mixedProfile, hnash⟩ := exists_isNash_mixed utility
  exact ⟨FinDist.pi mixedProfile, hnash.isCorrelatedEq_pi⟩

/-- **Every finite game has a coarse correlated equilibrium.** -/
theorem exists_isCoarseCorrelatedEq (utility : F.sig.Outcome → ι → ℝ) :
    ∃ law : FinDist (Profile F.sig), IsCoarseCorrelatedEq F (euPreference utility) law := by
  obtain ⟨mixedProfile, hnash⟩ := exists_isNash_mixed utility
  exact ⟨FinDist.pi mixedProfile, hnash.isCoarseCorrelatedEq_pi⟩

end GameTheory
