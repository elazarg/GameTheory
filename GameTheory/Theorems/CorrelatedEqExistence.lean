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
/-- Every finite-player, finite-strategy game with bounded utility has a
    correlated equilibrium; the outcome carrier need not be finite. -/
theorem correlatedEq_exists_of_bounded
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ := by
  obtain ⟨σ, hN⟩ := G.mixed_nash_exists_of_bounded hbd
  exact ⟨pmfPi σ, G.mixed_nash_isCorrelatedEq_of_bounded σ hN hbd⟩

open Classical in
/-- Every finite game has a correlated equilibrium. -/
theorem correlatedEq_exists
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCorrelatedEq μ := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact G.correlatedEq_exists_of_bounded hbd

open Classical in
/-- A mixed Nash profile induces a coarse correlated equilibrium under bounded utility.
    Corollary of `mixed_nash_isCorrelatedEq_of_bounded` via `toCoarseCorrelatedEq`. -/
theorem mixed_nash_isCoarseCorrelatedEq_of_bounded
    {G : KernelGame ι}
    [Fintype ι]
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
    [Fintype ι] [Finite G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i))
    (hN : G.mixedExtension.IsNash σ) :
    G.IsCoarseCorrelatedEq (pmfPi σ) := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact G.mixed_nash_isCoarseCorrelatedEq_of_bounded σ hN hbd

open Classical in
/-- Every finite-player, finite-strategy game with bounded utility has a coarse
    correlated equilibrium; the outcome carrier need not be finite. -/
theorem coarseCorrelatedEq_exists_of_bounded
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {C : ι → ℝ} (hbd : ∀ who ω, |G.utility ω who| ≤ C who) :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  obtain ⟨μ, hCE⟩ := G.correlatedEq_exists_of_bounded hbd
  exact ⟨μ, hCE.toCoarseCorrelatedEq⟩

open Classical in
/-- Every finite game has a coarse correlated equilibrium.
    Corollary of `correlatedEq_exists` via `toCoarseCorrelatedEq`. -/
theorem coarseCorrelatedEq_exists
    (G : KernelGame ι)
    [Finite ι] [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Finite G.Outcome] :
    ∃ μ : PMF (Profile G), G.IsCoarseCorrelatedEq μ := by
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact G.coarseCorrelatedEq_exists_of_bounded hbd

end KernelGame
end GameTheory
