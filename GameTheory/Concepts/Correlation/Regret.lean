/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import Math.ProbabilityMassFunction

/-!
# Regret and No-Regret Characterizations

Regret measures how much a player could gain by deviating from a
recommended strategy. This connects correlated equilibrium to the
no-regret learning framework.

## Main definitions

* `KernelGame.swapRegret` — swap regret for a recommendation-dependent deviation
* `KernelGame.conditionalSwapRegret` — best conditional swap gain after one recommendation
* `KernelGame.externalRegret` — external regret for a constant deviation

## Main results

* `isCorrelatedEq_iff_noSwapRegret` — CE ↔ no swap regret
* `isCoarseCorrelatedEq_iff_noExternalRegret` — CCE ↔ no external regret
* `swapRegret_id` — regret of the identity deviation is zero
* `maxSwapRegret_eq_expect_conditionalSwapRegret` — max swap regret equals
  expected conditional swap regret
* `externalRegret_le_swapRegret` — external regret is a special case of swap regret
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

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

/-- Maximum swap regret of one player under a finite recommendation
distribution.  The identity deviation is available, so this quantity is always
nonnegative. -/
noncomputable def maxSwapRegret (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)] : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy who → G.Strategy who))
    (fun dev => G.swapRegret μ who dev)

theorem swapRegret_le_maxSwapRegret (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)]
    (dev : G.Strategy who → G.Strategy who) :
    G.swapRegret μ who dev ≤ G.maxSwapRegret μ who :=
  Finset.le_sup' (fun dev => G.swapRegret μ who dev) (Finset.mem_univ dev)

theorem maxSwapRegret_nonneg (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)] :
    0 ≤ G.maxSwapRegret μ who := by
  simpa [swapRegret_id] using
    (G.swapRegret_le_maxSwapRegret μ who _root_.id)

/-- Conditional one-signal swap regret for player `who` after recommendation
`si`. It is zero on zero-probability recommendations. -/
noncomputable def conditionalSwapRegret (μ : PMF (Profile G)) (who : ι)
    (si : G.Strategy who)
    [Fintype (G.Strategy who)] [Nonempty (G.Strategy who)] : ℝ :=
  if hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0 then
    Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy who))
      (fun a =>
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
          (fun θ => G.eu (Function.update θ who a) who - G.eu θ who))
  else 0

theorem conditionalGain_le_conditionalSwapRegret
    (μ : PMF (Profile G)) (who : ι) (si a : G.Strategy who)
    [Fintype (G.Strategy who)] [Nonempty (G.Strategy who)]
    (hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0) :
    expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
        (fun θ => G.eu (Function.update θ who a) who - G.eu θ who) ≤
      G.conditionalSwapRegret μ who si := by
  simp [conditionalSwapRegret, hsi,
    Finset.le_sup' (s := Finset.univ)
      (f := fun a =>
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
          (fun θ => G.eu (Function.update θ who a) who - G.eu θ who))
      (Finset.mem_univ a)]

theorem conditionalSwapRegret_nonneg
    (μ : PMF (Profile G)) (who : ι) (si : G.Strategy who)
    [Fintype (G.Strategy who)] [Nonempty (G.Strategy who)] :
    0 ≤ G.conditionalSwapRegret μ who si := by
  classical
  rw [conditionalSwapRegret]
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0
  · simp only [dif_pos hsi]
    have hzero :
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
            (fun θ => G.eu (Function.update θ who si) who - G.eu θ who) = 0 := by
      calc
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
            (fun θ => G.eu (Function.update θ who si) who - G.eu θ who)
            = expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
                (fun _ => 0) := by
                refine expect_congr_of_ne_zero _ _ _ ?_
                intro θ hθ
                have hθi := pmfCond_ne_zero_implies μ
                  (fun θ : Profile G => si = θ who) hsi hθ
                have hupdate : Function.update θ who si = θ := by
                  funext j
                  by_cases hj : j = who
                  · subst hj
                    simp [hθi.symm]
                  · simp [Function.update_of_ne hj]
                simp [hupdate]
        _ = 0 := by simp
    simpa [hzero] using
      (Finset.le_sup' (s := Finset.univ)
        (f := fun a =>
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
            (fun θ => G.eu (Function.update θ who a) who - G.eu θ who))
        (Finset.mem_univ si))
  · simp [hsi]

private theorem pmf_supportFinset_nonempty {α : Type*} [Fintype α]
    (μ : PMF α) :
    (Finset.univ.filter fun a : α => μ a ≠ 0).Nonempty := by
  classical
  rcases μ.support_nonempty with ⟨a, ha⟩
  exact ⟨a, Finset.mem_filter.mpr
    ⟨Finset.mem_univ a, by simpa [PMF.mem_support_iff] using ha⟩⟩

/-- Worst conditional swap regret over players and own recommendations.  Since
`conditionalSwapRegret` is defined to be zero at zero-probability
recommendations, this may range over all recommendations. -/
noncomputable def maxConditionalSwapRegret (μ : PMF (Profile G))
    [Fintype ι] [Nonempty ι]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := ι)) fun i =>
    Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i)) fun si =>
      G.conditionalSwapRegret μ i si

theorem conditionalSwapRegret_le_maxConditionalSwapRegret
    (μ : PMF (Profile G)) (who : ι) (si : G.Strategy who)
    [Fintype ι] [Nonempty ι]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    G.conditionalSwapRegret μ who si ≤ G.maxConditionalSwapRegret μ := by
  classical
  unfold maxConditionalSwapRegret
  exact (Finset.le_sup' (s := Finset.univ)
    (f := fun si : G.Strategy who => G.conditionalSwapRegret μ who si)
    (Finset.mem_univ si)).trans
      (Finset.le_sup' (s := Finset.univ)
        (f := fun i =>
          Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i)) fun si =>
            G.conditionalSwapRegret μ i si)
        (Finset.mem_univ who))

theorem maxConditionalSwapRegret_nonneg (μ : PMF (Profile G))
    [Fintype ι] [Nonempty ι]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    0 ≤ G.maxConditionalSwapRegret μ := by
  classical
  let who : ι := Classical.arbitrary ι
  let si : G.Strategy who := Classical.arbitrary (G.Strategy who)
  exact (G.conditionalSwapRegret_nonneg μ who si).trans
    (G.conditionalSwapRegret_le_maxConditionalSwapRegret μ who si)

/-- Worst supported realized sum of conditional swap regrets.  This is the
natural upper endpoint for pointwise-budget regret-paying recommendation
devices. -/
noncomputable def maxSupportedPointwiseConditionalSwapRegret
    [Fintype ι] [Fintype (Profile G)]
    (μ : PMF (Profile G))
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] : ℝ :=
  (Finset.univ.filter fun θ : Profile G => μ θ ≠ 0).sup'
    (pmf_supportFinset_nonempty μ) fun θ =>
      ∑ i, G.conditionalSwapRegret μ i (θ i)

theorem sum_conditionalSwapRegret_le_maxSupportedPointwiseConditionalSwapRegret
    [Fintype ι] [Fintype (Profile G)]
    (μ : PMF (Profile G))
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {θ : Profile G} (hθ : μ θ ≠ 0) :
    (∑ i, G.conditionalSwapRegret μ i (θ i)) ≤
      G.maxSupportedPointwiseConditionalSwapRegret μ := by
  classical
  unfold maxSupportedPointwiseConditionalSwapRegret
  exact Finset.le_sup' (s := Finset.univ.filter fun θ : Profile G => μ θ ≠ 0)
    (f := fun θ => ∑ i, G.conditionalSwapRegret μ i (θ i))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ θ, hθ⟩)

/-- Swap regret is the expected pointwise gain from applying the swap
deviation to the recommendation. -/
theorem swapRegret_eq_expect_gain [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    G.swapRegret μ who dev =
      expect μ (fun θ =>
        G.eu (Function.update θ who (dev (θ who))) who - G.eu θ who) := by
  rw [swapRegret, G.correlatedEu_unilateralDeviationDistribution_eq_expect_update μ who dev,
    G.correlatedEu_eq_expect_eu μ who, expect_sub]

/-- Swap regret decomposes as the sum, over recommendations, of each
recommendation's probability times the conditional gain from the action chosen
by the swap rule at that recommendation. -/
theorem swapRegret_eq_sum_conditionalGain [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι) [Fintype (G.Strategy who)]
    (dev : G.Strategy who → G.Strategy who) :
    G.swapRegret μ who dev =
      ∑ si : G.Strategy who,
        (pmfMass (μ := μ) (fun θ : Profile G => si = θ who)).toReal *
          if hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0 then
            expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
              (fun θ => G.eu (Function.update θ who (dev si)) who - G.eu θ who)
          else 0 := by
  classical
  rw [G.swapRegret_eq_expect_gain μ who dev]
  rw [expect_eq_sum_fiber_cond (μ := μ) (proj := fun θ : Profile G => θ who)
    (f := fun θ => G.eu (Function.update θ who (dev (θ who))) who - G.eu θ who)]
  refine Finset.sum_congr rfl ?_
  intro si _
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0
  · simp only [dif_pos hsi]
    congr 1
    refine expect_congr_of_ne_zero _ _ _ ?_
    intro θ hθ
    have hθi := pmfCond_ne_zero_implies μ
      (fun θ : Profile G => si = θ who) hsi hθ
    simp [hθi]
  · simp [hsi]

/-- The expectation of conditional swap regret is the probability-weighted sum
of the conditional regret at each recommendation. -/
theorem expect_conditionalSwapRegret_eq_sum [Finite (Profile G)]
    (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [Nonempty (G.Strategy who)] :
    expect μ (fun θ => G.conditionalSwapRegret μ who (θ who)) =
      ∑ si : G.Strategy who,
        (pmfMass (μ := μ) (fun θ : Profile G => si = θ who)).toReal *
          G.conditionalSwapRegret μ who si := by
  classical
  rw [expect_eq_sum_fiber_cond (μ := μ) (proj := fun θ : Profile G => θ who)
    (f := fun θ => G.conditionalSwapRegret μ who (θ who))]
  refine Finset.sum_congr rfl ?_
  intro si _
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0
  · simp only [dif_pos hsi]
    congr 1
    calc
      expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
          (fun θ => G.conditionalSwapRegret μ who (θ who))
          = expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
              (fun _ => G.conditionalSwapRegret μ who si) := by
              refine expect_congr_of_ne_zero _ _ _ ?_
              intro θ hθ
              have hθi := pmfCond_ne_zero_implies μ
                (fun θ : Profile G => si = θ who) hsi hθ
              simp [hθi]
      _ = G.conditionalSwapRegret μ who si := by simp
  · simp [hsi, conditionalSwapRegret]

theorem maxSwapRegret_le_expect_conditionalSwapRegret
    [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)] :
    G.maxSwapRegret μ who ≤
      expect μ (fun θ => G.conditionalSwapRegret μ who (θ who)) := by
  classical
  rw [G.expect_conditionalSwapRegret_eq_sum μ who]
  apply Finset.sup'_le
  intro dev _
  rw [G.swapRegret_eq_sum_conditionalGain μ who dev]
  refine Finset.sum_le_sum ?_
  intro si _
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0
  · simp only [dif_pos hsi]
    exact mul_le_mul_of_nonneg_left
      (G.conditionalGain_le_conditionalSwapRegret μ who si (dev si) hsi)
      ENNReal.toReal_nonneg
  · simp [hsi, conditionalSwapRegret]

theorem expect_conditionalSwapRegret_le_maxSwapRegret
    [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)] :
    expect μ (fun θ => G.conditionalSwapRegret μ who (θ who)) ≤
      G.maxSwapRegret μ who := by
  classical
  let best : G.Strategy who → G.Strategy who := fun si =>
    if hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0 then
      Classical.choose
        (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G.Strategy who))
          (fun a =>
            expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
              (fun θ => G.eu (Function.update θ who a) who - G.eu θ who)))
    else si
  have hbest :
      ∀ si (hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0),
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
            (fun θ => G.eu (Function.update θ who (best si)) who - G.eu θ who) =
          G.conditionalSwapRegret μ who si := by
    intro si hsi
    rw [conditionalSwapRegret]
    simp only [dif_pos hsi]
    dsimp [best]
    rw [dif_pos hsi]
    exact (Classical.choose_spec
      (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G.Strategy who))
        (fun a =>
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ who) hsi)
            (fun θ => G.eu (Function.update θ who a) who - G.eu θ who)))).2.symm
  rw [G.expect_conditionalSwapRegret_eq_sum μ who]
  have hdev_eq :
      G.swapRegret μ who best =
        ∑ si : G.Strategy who,
          (pmfMass (μ := μ) (fun θ : Profile G => si = θ who)).toReal *
            G.conditionalSwapRegret μ who si := by
    rw [G.swapRegret_eq_sum_conditionalGain μ who best]
    refine Finset.sum_congr rfl ?_
    intro si _
    by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ who) ≠ 0
    · simp only [dif_pos hsi]
      rw [hbest si hsi]
    · simp [hsi, conditionalSwapRegret]
  rw [← hdev_eq]
  exact G.swapRegret_le_maxSwapRegret μ who best

theorem maxSwapRegret_eq_expect_conditionalSwapRegret
    [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι)
    [Fintype (G.Strategy who)] [DecidableEq (G.Strategy who)]
    [Nonempty (G.Strategy who)] :
    G.maxSwapRegret μ who =
      expect μ (fun θ => G.conditionalSwapRegret μ who (θ who)) :=
  le_antisymm (G.maxSwapRegret_le_expect_conditionalSwapRegret μ who)
    (G.expect_conditionalSwapRegret_le_maxSwapRegret μ who)

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
