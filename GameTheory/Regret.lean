import GameTheory.CorrelatedEqProperties
import Math.Probability

/-!
# Regret and No-Regret Characterizations

Regret measures how much a player could gain by deviating from a
recommended strategy. This connects correlated equilibrium to the
no-regret learning framework.

## Main definitions

* `KernelGame.swapRegret` — swap regret for a recommendation-dependent deviation
* `KernelGame.externalRegret` — external regret for a constant deviation

## Main results

* `isCorrelatedEq_iff_noSwapRegret` — CE ↔ no swap regret
* `isCoarseCorrelatedEq_iff_noExternalRegret` — CCE ↔ no external regret
* `swapRegret_id` — regret of the identity deviation is zero
* `externalRegret_le_swapRegret` — external regret is a special case of swap regret
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} (G : KernelGame ι)

/-- Swap regret: expected gain from deviation `dev` for player `who`
    under correlated distribution `μ`. Positive regret means the deviation
    is profitable. -/
noncomputable def swapRegret (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) : ℝ :=
  G.correlatedEu (G.deviateDistribution μ who dev) who - G.correlatedEu μ who

/-- External regret: expected gain from switching to constant strategy `s'`
    for player `who`. -/
noncomputable def externalRegret (μ : PMF (Profile G)) (who : ι)
    (s' : G.Strategy who) : ℝ :=
  G.correlatedEu (G.constDeviateDistribution μ who s') who - G.correlatedEu μ who

/-- The identity deviation has zero swap regret. -/
theorem swapRegret_id (μ : PMF (Profile G)) (who : ι) :
    G.swapRegret μ who _root_.id = 0 := by
  simp [swapRegret, deviateDistribution_id]

/-- External regret is swap regret with a constant deviation function. -/
theorem externalRegret_eq_swapRegret_const (μ : PMF (Profile G)) (who : ι)
    (s' : G.Strategy who) :
    G.externalRegret μ who s' = G.swapRegret μ who (fun _ => s') := by
  simp [externalRegret, swapRegret, constDeviateDistribution, deviateDistribution,
    deviateProfile]

/-- Correlated equilibrium ↔ no swap regret: `μ` is a CE iff every
    recommendation-dependent deviation has nonpositive regret. -/
theorem isCorrelatedEq_iff_noSwapRegret {μ : PMF (Profile G)} :
    G.IsCorrelatedEq μ ↔ ∀ who dev, G.swapRegret μ who dev ≤ 0 := by
  simp [IsCorrelatedEq, swapRegret, correlatedEu]

/-- Coarse correlated equilibrium ↔ no external regret. -/
theorem isCoarseCorrelatedEq_iff_noExternalRegret {μ : PMF (Profile G)} :
    G.IsCoarseCorrelatedEq μ ↔ ∀ who s', G.externalRegret μ who s' ≤ 0 := by
  simp [IsCoarseCorrelatedEq, externalRegret, correlatedEu]

/-- No swap regret implies no external regret (CE → CCE via regret). -/
theorem noSwapRegret_imp_noExternalRegret {μ : PMF (Profile G)}
    (h : ∀ who dev, G.swapRegret μ who dev ≤ 0) :
    ∀ who s', G.externalRegret μ who s' ≤ 0 := by
  intro who s'
  rw [externalRegret_eq_swapRegret_const]
  exact h who _

end KernelGame

end GameTheory
