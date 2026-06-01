/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelatedEqProperties
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

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

/-- Swap regret: expected gain from deviation `dev` for player `who`
    under correlated distribution `μ`. Positive regret means the deviation
    is profitable. -/
noncomputable def swapRegret (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) : ℝ :=
  G.correlatedEu (G.unilateralDeviationDistribution μ who dev) who - G.correlatedEu μ who

/-- External regret: expected gain from switching to constant strategy `s'`
    for player `who`. -/
noncomputable def externalRegret (μ : PMF (Profile G)) (who : ι)
    (s' : G.Strategy who) : ℝ :=
  G.correlatedEu (G.constantDeviationDistribution μ who s') who - G.correlatedEu μ who

/-- The identity deviation has zero swap regret. -/
theorem swapRegret_id (μ : PMF (Profile G)) (who : ι) :
    G.swapRegret μ who _root_.id = 0 := by
  simp [swapRegret, unilateralDeviationDistribution_id]

/-- External regret is swap regret with a constant deviation function. -/
theorem externalRegret_eq_swapRegret_const (μ : PMF (Profile G)) (who : ι)
    (s' : G.Strategy who) :
    G.externalRegret μ who s' = G.swapRegret μ who (fun _ => s') := by
  simp [externalRegret, swapRegret,
    KernelGame.constantDeviationDistribution, KernelGame.unilateralDeviationDistribution,
    KernelGame.deviationDistribution, KernelGame.constantDeviation, KernelGame.unilateralDeviation]

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

/-! ## Savage minimax-regret decision rule

A decision-theoretic regret notion (Savage 1951): a single decision
maker picks an action `a : A` knowing one of finitely many states
`ω : Ω` obtains. The *regret* of `a` at `ω` is what the agent would
have foregone relative to the best fixed action against `ω`:
`regret(a, ω) = max_b u(b, ω) - u(a, ω)`. The *minimax-regret rule*
selects an action minimizing the worst-case regret.

This is not a game-theoretic equilibrium notion but a decision
criterion under uncertainty about the state of nature; we record it
here for symmetry with the equilibrium-style regrets above. -/

namespace Savage

variable {A Ω : Type} [Fintype A] [Fintype Ω] [Nonempty A]

/-- Best attainable utility against state `ω` over the finite action
set `A` (a finite maximum). -/
noncomputable def bestUtility (u : A → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := A)) (fun a => u a ω)

/-- *Savage regret* of action `a` against state `ω`: how much utility
the decision maker foregoes by choosing `a` rather than the best
action for `ω`. -/
noncomputable def regret (u : A → Ω → ℝ) (a : A) (ω : Ω) : ℝ :=
  bestUtility u ω - u a ω

omit [Fintype Ω] in
theorem regret_nonneg (u : A → Ω → ℝ) (a : A) (ω : Ω) :
    0 ≤ regret u a ω := by
  simp only [regret, sub_nonneg, bestUtility]
  exact Finset.le_sup' (fun a => u a ω) (Finset.mem_univ a)

omit [Fintype Ω] in
theorem regret_eq_zero_iff_best (u : A → Ω → ℝ) (a : A) (ω : Ω) :
    regret u a ω = 0 ↔ u a ω = bestUtility u ω := by
  unfold regret
  constructor
  · intro h; linarith
  · intro h; linarith

/-- *Worst-case regret* (max over states) of action `a`. -/
noncomputable def maxRegret [Nonempty Ω] (u : A → Ω → ℝ) (a : A) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := Ω)) (fun ω => regret u a ω)

/-- An action is *minimax-regret* if it minimizes the worst-case
regret over states. -/
def IsMinimaxRegret [Nonempty Ω] (u : A → Ω → ℝ) (a : A) : Prop :=
  ∀ b : A, maxRegret u a ≤ maxRegret u b

/-- An action with zero regret at every state (a *uniformly best*
action) is minimax-regret. -/
theorem isMinimaxRegret_of_uniformlyBest [Nonempty Ω] (u : A → Ω → ℝ) (a : A)
    (h : ∀ ω, u a ω = bestUtility u ω) :
    IsMinimaxRegret u a := by
  intro b
  have ha_zero : maxRegret u a = 0 := by
    simp only [maxRegret, regret]
    apply le_antisymm
    · apply Finset.sup'_le
      intro ω _
      simp [h ω]
    · have : (0 : ℝ) ≤ bestUtility u (Classical.arbitrary Ω) - u a (Classical.arbitrary Ω) := by
        simp [h]
      have hpos := regret_nonneg u a (Classical.arbitrary Ω)
      have := Finset.le_sup' (fun ω => bestUtility u ω - u a ω) (Finset.mem_univ
        (Classical.arbitrary Ω))
      simp only [regret] at hpos
      have h_zero_at : bestUtility u (Classical.arbitrary Ω) -
          u a (Classical.arbitrary Ω) = 0 := by
        rw [h]; ring
      linarith
  have hb_nn : 0 ≤ maxRegret u b := by
    simp only [maxRegret]
    have h_some : (0 : ℝ) ≤ regret u b (Classical.arbitrary Ω) :=
      regret_nonneg u b _
    have := Finset.le_sup' (fun ω => regret u b ω) (Finset.mem_univ
      (Classical.arbitrary Ω))
    linarith
  rw [ha_zero]; exact hb_nn

end Savage

end GameTheory
