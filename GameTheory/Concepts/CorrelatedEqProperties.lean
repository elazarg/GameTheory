import GameTheory.Concepts.SolutionConcepts
import Math.Probability

/-!
# GameTheory.Concepts.CorrelatedEqProperties

Structural properties of correlated and coarse correlated equilibria.

Provides:
- `IsCorrelatedEq.toCoarseCorrelatedEq` -- every CE is a CCE
- `deviateDistribution_id` -- the identity deviation leaves the distribution unchanged
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- Every correlated equilibrium is a coarse correlated equilibrium.

A constant deviation `fun _ => s'` is a special case of a recommendation-dependent
deviation, so the CE condition (which quantifies over all deviations) implies the
CCE condition (which only considers constant deviations). The two deviation
distributions are definitionally equal: `deviateProfile σ who (fun _ => s')` reduces
to `Function.update σ who s'`. -/
theorem IsCorrelatedEq.toCoarseCorrelatedEq {μ : PMF (Profile G)}
    (hce : G.IsCorrelatedEq μ) : G.IsCoarseCorrelatedEq μ := by
  intro who s'
  exact hce who (fun _ => s')

/-- The identity deviation leaves the profile distribution unchanged.

`deviateProfile σ who id = Function.update σ who (σ who) = σ`, so the
deviation distribution `μ.bind (fun σ => pure (deviateProfile σ who id))`
simplifies to `μ.bind pure = μ`.
Delegates to `GameForm.deviateDistributionFn_id`. -/
theorem deviateDistribution_id (G : KernelGame ι) (μ : PMF (Profile G)) (who : ι) :
    G.deviateDistribution μ who _root_.id = μ := by
  simpa [KernelGame.deviateDistribution,
    KernelGame.unilateralDeviationDistribution,
    KernelGame.unilateralDeviation] using
    (KernelGame.deviationDistribution_id (G := G) μ)

end KernelGame
end GameTheory
