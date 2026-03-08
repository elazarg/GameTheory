import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Concepts.CorrelatedEqProperties

Structural properties of correlated and coarse correlated equilibria.

Provides:
- `IsCorrelatedEq.toCoarseCorrelatedEq` -- every CE is a CCE
- `unilateralDeviationDistribution_id` -- identity unilateral deviation leaves
  distribution unchanged
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- Every correlated equilibrium is a coarse correlated equilibrium.

A constant deviation `fun _ => s'` is a special case of a recommendation-dependent
deviation, so the CE condition (which quantifies over all deviations) implies the
CCE condition (which only considers constant deviations). The two deviation
distributions are definitionally equal: `unilateralDeviation G who (fun _ => s') σ` reduces
to `Function.update σ who s'`. -/
theorem IsCorrelatedEq.toCoarseCorrelatedEq {μ : PMF (Profile G)}
    (hce : G.IsCorrelatedEq μ) : G.IsCoarseCorrelatedEq μ := by
  intro who s'
  exact hce who (fun _ => s')

/-- The identity deviation leaves the profile distribution unchanged.

`unilateralDeviation G who id σ = Function.update σ who (σ who) = σ`, so the
deviation distribution `μ.bind (fun σ => pure (unilateralDeviation G who id σ))`
simplifies to `μ.bind pure = μ`.
Delegates to `GameForm.deviateDistributionFn_id`. -/
theorem unilateralDeviationDistribution_id
    (G : KernelGame ι) (μ : PMF (Profile G)) (who : ι) :
    G.unilateralDeviationDistribution μ who _root_.id = μ := by
  simp [KernelGame.unilateralDeviationDistribution, KernelGame.unilateralDeviation]

end KernelGame
end GameTheory
