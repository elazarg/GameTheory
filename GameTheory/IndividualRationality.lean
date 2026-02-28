import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# GameTheory.IndividualRationality

Properties of individual rationality for kernel-based games.

Provides:
- `IsIndividuallyRational.mono` — weakening the reservation utility preserves IR
- `IsIndividuallyRational.of_pareto_dominates` — Pareto improvement preserves IR
- `IsIndividuallyRational.sup` — IR w.r.t. the pointwise max of two reservation utilities
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Weakening the reservation utility preserves individual rationality:
    if σ is IR w.r.t. `r` and `r' i ≤ r i` for all `i`, then σ is IR w.r.t. `r'`. -/
theorem IsIndividuallyRational.mono {G : KernelGame ι} {r r' : ι → ℝ}
    {σ : Profile G} (hIR : G.IsIndividuallyRational r σ)
    (hle : ∀ i, r' i ≤ r i) : G.IsIndividuallyRational r' σ :=
  fun i => le_trans (hle i) (hIR i)

/-- A Pareto improvement preserves individual rationality:
    if σ Pareto-dominates τ and τ is IR w.r.t. `r`, then σ is IR w.r.t. `r`. -/
theorem IsIndividuallyRational.of_pareto_dominates {G : KernelGame ι} {r : ι → ℝ}
    {σ τ : Profile G} (hdom : G.ParetoDominates σ τ)
    (hIR : G.IsIndividuallyRational r τ) : G.IsIndividuallyRational r σ :=
  fun i => le_trans (hIR i) (hdom.1 i)

/-- IR w.r.t. two reservation utilities implies IR w.r.t. their pointwise max. -/
theorem IsIndividuallyRational.sup {G : KernelGame ι} {r₁ r₂ : ι → ℝ}
    {σ : Profile G} (h1 : G.IsIndividuallyRational r₁ σ)
    (h2 : G.IsIndividuallyRational r₂ σ) :
    G.IsIndividuallyRational (fun i => max (r₁ i) (r₂ i)) σ :=
  fun i => max_le (h1 i) (h2 i)

end KernelGame

end GameTheory
