import GameTheory.Concepts.CorrelatedNashMixed
import GameTheory.Theorems.NashExistenceMixed

/-!
# Correlated Equilibrium Existence

Every finite game has a correlated equilibrium (and a coarse correlated equilibrium).
This follows from Nash existence in mixed strategies.

## Main results

- `correlatedEq_exists` — every finite game has a correlated equilibrium
- `mixed_nash_isCoarseCorrelatedEq` — mixed Nash → coarse correlated equilibrium
- `coarseCorrelatedEq_exists` — every finite game has a coarse correlated equilibrium
-/

namespace GameTheory

open Math.Probability
namespace KernelGame
open Math.PMFProduct

variable {ι : Type} [DecidableEq ι]

set_option linter.unusedFintypeInType false in
open Classical in
/-- Every finite game has a correlated equilibrium. -/
theorem correlatedEq_exists
    (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ := by
  obtain ⟨σ, hN⟩ := G.mixed_nash_exists
  exact ⟨pmfPi σ, G.mixed_nash_isCorrelatedEq σ hN⟩

set_option linter.unusedFintypeInType false in
open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium.
    Corollary of `mixed_nash_isCorrelatedEq` via `toCoarseCorrelatedEq`. -/
theorem mixed_nash_isCoarseCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCoarseCorrelatedEq (pmfPi σ) :=
  (G.mixed_nash_isCorrelatedEq σ hN).toCoarseCorrelatedEq

set_option linter.unusedFintypeInType false in
open Classical in
/-- Every finite game has a coarse correlated equilibrium.
    Corollary of `correlatedEq_exists` via `toCoarseCorrelatedEq`. -/
theorem coarseCorrelatedEq_exists
    (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  obtain ⟨μ, hCE⟩ := G.correlatedEq_exists
  exact ⟨μ, hCE.toCoarseCorrelatedEq⟩

end KernelGame
end GameTheory
