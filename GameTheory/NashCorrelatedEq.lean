import GameTheory.SolutionConcepts

/-!
# GameTheory.NashCorrelatedEq

Bridges between Nash equilibria and correlated/coarse correlated equilibria.

Provides:
- `nash_pure_isCorrelatedEq` — a pure Nash profile, embedded as `PMF.pure σ`,
  is a correlated equilibrium.
- `nash_pure_isCoarseCorrelatedEq` — a pure Nash profile, embedded as `PMF.pure σ`,
  is a coarse correlated equilibrium.

The key observation is that under a point-mass distribution `PMF.pure σ`, the
correlated expected utility reduces to the standard expected utility, and any
deviation map collapses to a single unilateral deviation that the Nash condition
already handles.
-/

namespace GameTheory

variable {ι : Type}

namespace KernelGame

/-- A pure Nash equilibrium, embedded as a point-mass distribution, is a correlated
    equilibrium. Under `PMF.pure σ`, the deviation distribution collapses to a single
    profile `Function.update σ who (dev (σ who))`, so the CE incentive constraint
    reduces to the Nash condition. -/
theorem nash_pure_isCorrelatedEq {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) : G.IsCorrelatedEq (PMF.pure σ) := by
  intro who dev
  unfold correlatedEu
  simp only [correlatedOutcome]
  unfold deviateDistribution deviateProfile
  simp only [Kernel.pushforward_apply, PMF.pure_bind]
  exact hN who (dev (σ who))

/-- A pure Nash equilibrium, embedded as a point-mass distribution, is a coarse
    correlated equilibrium. Under `PMF.pure σ`, the constant deviation distribution
    collapses to `PMF.pure (Function.update σ who s')`, so the CCE incentive constraint
    reduces to the Nash condition. -/
theorem nash_pure_isCoarseCorrelatedEq {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) : G.IsCoarseCorrelatedEq (PMF.pure σ) := by
  intro who s'
  unfold correlatedEu
  simp only [correlatedOutcome]
  unfold constDeviateDistribution
  simp only [Kernel.pushforward_apply, PMF.pure_bind]
  exact hN who s'

end KernelGame

end GameTheory
