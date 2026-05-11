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

attribute [local instance] Fintype.ofFinite

variable {ι : Type} [DecidableEq ι]

open Classical in
/-- Every finite game has a correlated equilibrium. -/
theorem correlatedEq_exists
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ := by
  obtain ⟨σ, hN⟩ := G.mixed_nash_exists
  exact ⟨pmfPi σ, G.mixed_nash_isCorrelatedEq σ hN⟩

open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium under bounded utility.
    Corollary of `mixed_nash_isCorrelatedEq_of_bounded` via `toCoarseCorrelatedEq`. -/
theorem mixed_nash_isCoarseCorrelatedEq_of_bounded
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Finite (G.Strategy i)]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ)
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    G.IsCoarseCorrelatedEq (pmfPi σ) :=
  (G.mixed_nash_isCorrelatedEq_of_bounded σ hN hbd).toCoarseCorrelatedEq

open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium.
    Corollary of `mixed_nash_isCorrelatedEq` via `toCoarseCorrelatedEq`. -/
theorem mixed_nash_isCoarseCorrelatedEq
    {G : KernelGame ι}
    [Fintype ι] [∀ i, Finite (G.Strategy i)] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCoarseCorrelatedEq (pmfPi σ) := by
  let C : ι → ℝ := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose
  have hbd : ∀ who ω, |G.utility ω who| ≤ C who := fun who =>
    (Math.Probability.exists_abs_bound_of_finite
      (fun ω => G.utility ω who)).choose_spec
  exact G.mixed_nash_isCoarseCorrelatedEq_of_bounded σ hN hbd

open Classical in
/-- Every finite game has a coarse correlated equilibrium.
    Corollary of `correlatedEq_exists` via `toCoarseCorrelatedEq`. -/
theorem coarseCorrelatedEq_exists
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  obtain ⟨μ, hCE⟩ := G.correlatedEq_exists
  exact ⟨μ, hCE.toCoarseCorrelatedEq⟩

end KernelGame
end GameTheory
