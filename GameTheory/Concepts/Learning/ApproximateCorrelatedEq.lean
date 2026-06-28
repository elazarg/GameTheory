/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.Regret

/-!
# Approximate correlated equilibria

ε-relaxations of (coarse) correlated equilibrium and their regret characterizations,
mirroring `KernelGame.IsεNash`. These are the equilibrium targets of no-regret learning:
the time-average of a play sequence with cumulative regret `R` is an `(R/T)`-correlated
equilibrium, so sublinear regret gives an ε-equilibrium with ε → 0.

## Main definitions

* `KernelGame.IsεCoarseCorrelatedEq` — no player gains more than ε from a constant deviation
* `KernelGame.IsεCorrelatedEq` — no player gains more than ε from a swap deviation

## Main results

* `isεCoarseCorrelatedEq_iff_externalRegret_le` — ε-CCE ↔ every external regret ≤ ε
* `isεCorrelatedEq_iff_swapRegret_le` — ε-CE ↔ every swap regret ≤ ε
* `IsεCoarseCorrelatedEq.mono` / `IsεCorrelatedEq.mono` — monotone in ε
* `isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero` / `isCorrelatedEq_iff_isεCorrelatedEq_zero`
  — the exact equilibrium is the 0-approximate one
* `IsεCorrelatedEq.toCoarse` — an ε-CE is an ε-CCE (the ε-level analogue of CE ⇒ CCE)
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

/-- An `ε`-coarse correlated equilibrium: no player can gain more than `ε` in expected
    utility by a constant unilateral deviation. -/
def IsεCoarseCorrelatedEq (ε : ℝ) (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.correlatedEu μ who + ε ≥ G.correlatedEu (G.constantDeviationDistribution μ who s') who

/-- An `ε`-correlated equilibrium: no player can gain more than `ε` in expected utility
    by a recommendation-dependent deviation. -/
def IsεCorrelatedEq (ε : ℝ) (μ : PMF (Profile G)) : Prop :=
  ∀ (who : ι) (dev : G.Strategy who → G.Strategy who),
    G.correlatedEu μ who + ε ≥ G.correlatedEu (G.unilateralDeviationDistribution μ who dev) who

/-- An `ε`-coarse correlated equilibrium is exactly a distribution all of whose external
    regrets are at most `ε`. -/
theorem isεCoarseCorrelatedEq_iff_externalRegret_le {ε : ℝ} {μ : PMF (Profile G)} :
    G.IsεCoarseCorrelatedEq ε μ ↔ ∀ who s', G.externalRegret μ who s' ≤ ε := by
  unfold IsεCoarseCorrelatedEq externalRegret
  constructor
  · intro h who s'; have := h who s'; linarith
  · intro h who s'; have := h who s'; linarith

/-- An `ε`-correlated equilibrium is exactly a distribution all of whose swap regrets are
    at most `ε`. -/
theorem isεCorrelatedEq_iff_swapRegret_le {ε : ℝ} {μ : PMF (Profile G)} :
    G.IsεCorrelatedEq ε μ ↔ ∀ who dev, G.swapRegret μ who dev ≤ ε := by
  unfold IsεCorrelatedEq swapRegret
  constructor
  · intro h who dev; have := h who dev; linarith
  · intro h who dev; have := h who dev; linarith

/-- `ε`-CCE is monotone in `ε`. -/
theorem IsεCoarseCorrelatedEq.mono {ε₁ ε₂ : ℝ} {μ : PMF (Profile G)}
    (h : G.IsεCoarseCorrelatedEq ε₁ μ) (hle : ε₁ ≤ ε₂) : G.IsεCoarseCorrelatedEq ε₂ μ := by
  intro who s'; have := h who s'; linarith

/-- `ε`-CE is monotone in `ε`. -/
theorem IsεCorrelatedEq.mono {ε₁ ε₂ : ℝ} {μ : PMF (Profile G)}
    (h : G.IsεCorrelatedEq ε₁ μ) (hle : ε₁ ≤ ε₂) : G.IsεCorrelatedEq ε₂ μ := by
  intro who dev; have := h who dev; linarith

/-- The exact coarse correlated equilibrium is the `0`-approximate one. -/
theorem isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero {μ : PMF (Profile G)} :
    G.IsCoarseCorrelatedEq μ ↔ G.IsεCoarseCorrelatedEq 0 μ := by
  rw [isCoarseCorrelatedEq_iff_noExternalRegret, isεCoarseCorrelatedEq_iff_externalRegret_le]

/-- The exact correlated equilibrium is the `0`-approximate one. -/
theorem isCorrelatedEq_iff_isεCorrelatedEq_zero {μ : PMF (Profile G)} :
    G.IsCorrelatedEq μ ↔ G.IsεCorrelatedEq 0 μ := by
  rw [isCorrelatedEq_iff_noSwapRegret, isεCorrelatedEq_iff_swapRegret_le]

/-- Every exact coarse correlated equilibrium is an `ε`-CCE for any `ε ≥ 0`. -/
theorem IsεCoarseCorrelatedEq.of_isCoarseCorrelatedEq {μ : PMF (Profile G)}
    (h : G.IsCoarseCorrelatedEq μ) {ε : ℝ} (hε : 0 ≤ ε) : G.IsεCoarseCorrelatedEq ε μ :=
  IsεCoarseCorrelatedEq.mono G ((G.isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero).1 h) hε

/-- Every exact correlated equilibrium is an `ε`-CE for any `ε ≥ 0`. -/
theorem IsεCorrelatedEq.of_isCorrelatedEq {μ : PMF (Profile G)}
    (h : G.IsCorrelatedEq μ) {ε : ℝ} (hε : 0 ≤ ε) : G.IsεCorrelatedEq ε μ :=
  IsεCorrelatedEq.mono G ((G.isCorrelatedEq_iff_isεCorrelatedEq_zero).1 h) hε

/-- An `ε`-correlated equilibrium is an `ε`-coarse correlated equilibrium (the `ε`-level
    analogue of CE ⇒ CCE, since external regret is a special case of swap regret). -/
theorem IsεCorrelatedEq.toCoarse {ε : ℝ} {μ : PMF (Profile G)}
    (h : G.IsεCorrelatedEq ε μ) : G.IsεCoarseCorrelatedEq ε μ := by
  rw [isεCoarseCorrelatedEq_iff_externalRegret_le]
  rw [isεCorrelatedEq_iff_swapRegret_le] at h
  intro who s'
  rw [externalRegret_eq_swapRegret_const]
  exact h who _

end KernelGame

end GameTheory
