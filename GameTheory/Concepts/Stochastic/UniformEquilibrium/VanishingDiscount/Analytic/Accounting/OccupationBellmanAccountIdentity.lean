/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkObstruction

/-!
# Bellman account identity for an oriented occupation row family

The occupation families used by the analytic program all share one shape.
A row is either a prescribed baseline transition out of a public state, or
a *response row* carrying a public source together with one action owned by
a fixed player.  The families differ only in which response rows they
admit -- every owned state/action pair, only the continuation-neutral ones,
and so on -- never in how a row is scored.

This file isolates that shape as an *ownership orientation*: a response
type together with its two projections

* `source : Response → G.State`, the public state a response row leaves;
* `action : Response → G.Act who`, the action of `who` that it plays.

The moving stage payoff, actual kernel and raw charge of a row are defined
once for an arbitrary orientation, and the Bellman account identity plus
its payoff-residual rearrangement are proved once.  Concrete orientations
(player-neutral rows, full player-owned rows) are instantiations.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Embed an oriented occupation row family into the raw family of all
baseline transitions and player-owned pure deviations. -/
def occupationRowEmbedding
    (who : ι) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who) :
    G.State ⊕ Response → G.State ⊕ (Σ owner : ι, G.State × G.Act owner)
  | .inl s => .inl s
  | .inr response => .inr ⟨who, source response, action response⟩

/-- Public source state left by an oriented occupation row. -/
def occupationRowSource
    {Response : Type} (source : Response → G.State) :
    G.State ⊕ Response → G.State
  | .inl s => s
  | .inr response => source response

/-- Moving actual transition kernel of an oriented occupation row. -/
def occupationRowKernelAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who) :
    G.State ⊕ Response → PMF G.State :=
  fun index =>
    germ.finkActualOccupationKernelAt ht
      (occupationRowEmbedding who source action index)

/-- Stage payoff associated with one moving oriented occupation row.
Baseline rows use prescribed play; response rows use the actual pure
unilateral deviation. -/
def occupationRowStageEUAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who) :
    G.State ⊕ Response → ℝ
  | .inl s =>
      G.finkStageEU (germ.finkPointAt ht) s who
  | .inr response =>
      G.mixedStageEU (source response)
        (Function.update
          (G.finkProfile (germ.finkPointAt ht) (source response))
          who (PMF.pure (action response))) who

/-- Moving charge of an oriented occupation row against a fixed bias:
baseline rows are free, while a response row carries its raw stage gain
plus its raw continuation gain against that bias. -/
def rawOccupationRowCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who) :
    ℝ → G.State ⊕ Response → ℝ
  | _, .inl _ => 0
  | t, .inr response =>
      germ.rawPureDeviationStageGainCurve
          t (source response) who (action response) +
        germ.rawPureDeviationContinuationGainCurve
          B t (source response) who (action response)

omit [DecidableEq G.State] in
/-- **Oriented Bellman account.**  The moving raw charge of an occupation
row is exactly the excess of its actual stage-plus-`B` continuation over
the prescribed stage-plus-`B` continuation at the same public source. -/
theorem occupationRow_bellmanAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who)
    (index : G.State ⊕ Response) :
    germ.occupationRowStageEUAt ht who source action index +
          expect
            (germ.occupationRowKernelAt ht who source action index)
            (fun state => B state who) =
      G.finkStageEU (germ.finkPointAt ht)
          (occupationRowSource source index) who +
        G.finkContinuationEU B (germ.finkPointAt ht)
          (occupationRowSource source index) who +
        germ.rawOccupationRowCharge B who source action t index := by
  cases index with
  | inl s =>
      change
        G.finkStageEU (germ.finkPointAt ht) s who +
              expect
                (G.finkStateKernel
                  (germ.finkPointAt ht) s)
                (fun state => B state who) =
          G.finkStageEU (germ.finkPointAt ht) s who +
            G.finkContinuationEU B
              (germ.finkPointAt ht) s who +
            0
      unfold finkContinuationEU
      rw [G.expect_finkStateKernel_eq]
      ring
  | inr response =>
      simp only [occupationRowStageEUAt, occupationRowKernelAt,
        occupationRowEmbedding,
        finkActualOccupationKernelAt, occupationKernel,
        occupationRowSource, rawOccupationRowCharge]
      rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht,
        germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt B ht,
        G.finkContinuationGain_eq_expect_stateKernels]
      unfold finkStageGain finkStageEU finkContinuationEU mixedStageEU
      rw [← G.expect_finkStateKernel_eq]
      ring

omit [DecidableEq G.State] in
/-- Rearranged form: a baseline Bellman residual plus the raw charge is the
entire owner payoff residual for the selected occupation row. -/
theorem occupationRow_payoffResidual_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target : ℝ) {Response : Type}
    (source : Response → G.State) (action : Response → G.Act who)
    (index : G.State ⊕ Response) :
    germ.occupationRowStageEUAt ht who source action index +
          expect
            (germ.occupationRowKernelAt ht who source action index)
            (fun state => B state who) -
          B (occupationRowSource source index) who -
          target =
      (G.finkStageEU (germ.finkPointAt ht)
            (occupationRowSource source index) who +
          G.finkContinuationEU B (germ.finkPointAt ht)
            (occupationRowSource source index) who -
          B (occupationRowSource source index) who -
          target) +
        germ.rawOccupationRowCharge B who source action t index := by
  rw [germ.occupationRow_bellmanAccount_eq B ht who source action index]
  ring

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
