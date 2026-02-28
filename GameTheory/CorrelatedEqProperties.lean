import GameTheory.SolutionConcepts

/-!
# GameTheory.CorrelatedEqProperties

Structural properties of correlated and coarse correlated equilibria.

Provides:
- `IsCorrelatedEq.toCoarseCorrelatedEq` — every CE is a CCE
- `deviateDistribution_id` — the identity deviation leaves the distribution unchanged
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

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
simplifies to `μ.bind pure = μ`. -/
theorem deviateDistribution_id (G : KernelGame ι) (μ : PMF (Profile G)) (who : ι) :
    G.deviateDistribution μ who _root_.id = μ := by
  simp only [deviateDistribution, deviateProfile, _root_.id]
  conv_lhs => arg 2; ext σ; rw [Function.update_eq_self]
  exact PMF.bind_pure μ

end KernelGame
end GameTheory
