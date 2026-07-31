/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralScaledPotential

/-!
# Player-neutral charge as an exact Bellman account

The moving raw charge used by the player-neutral occupation calendar is not
itself a stage payoff.  It is the exact difference between the deviating
stage-plus-continuation value and the prescribed stage-plus-continuation
value at the same public source.

This identity isolates the remaining datum needed to turn the analytic
calendar into an average-payoff cap: the prescribed baseline term

`finkStageEU + finkContinuationEU B - B source`

must be bounded by the desired owner target, up to a separately accumulated
residual.  The raw charged-flow account controls only the final charge term.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Stage payoff associated with one moving player-neutral occupation row.
Baseline rows use prescribed play; action rows use the actual pure
unilateral deviation. -/
def playerNeutralOccupationStageEUAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) :
    germ.PlayerNeutralOccupationIndex who → ℝ
  | .inl source =>
      G.finkStageEU (germ.finkPointAt ht) source who
  | .inr response =>
      G.mixedStageEU response.source
        (Function.update
          (G.finkProfile (germ.finkPointAt ht) response.source)
          who (PMF.pure response.1.2)) who

omit [DecidableEq G.State] in
/-- The moving raw charge is exactly the excess of actual
stage-plus-`B` continuation over its prescribed counterpart. -/
theorem playerNeutralOccupation_bellmanAccount_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (index : germ.PlayerNeutralOccupationIndex who) :
    germ.playerNeutralOccupationStageEUAt ht who index +
          expect
            (germ.finkPlayerNeutralOccupationKernelAt ht who index)
            (fun state => B state who) =
      G.finkStageEU (germ.finkPointAt ht)
          (germ.playerNeutralOccupationSource who index) who +
        G.finkContinuationEU B (germ.finkPointAt ht)
          (germ.playerNeutralOccupationSource who index) who +
        germ.rawPlayerNeutralOccupationCharge B who t index := by
  cases index with
  | inl source =>
      change
        G.finkStageEU (germ.finkPointAt ht) source who +
              expect
                (G.finkStateKernel
                  (germ.finkPointAt ht) source)
                (fun state => B state who) =
          G.finkStageEU (germ.finkPointAt ht) source who +
            G.finkContinuationEU B
              (germ.finkPointAt ht) source who +
            0
      unfold finkContinuationEU
      rw [G.expect_finkStateKernel_eq]
      ring
  | inr response =>
      simp only [playerNeutralOccupationStageEUAt,
        finkPlayerNeutralOccupationKernelAt,
        playerNeutralOccupationIndexEmbedding,
        finkActualOccupationKernelAt, occupationKernel,
        playerNeutralOccupationSource,
        rawPlayerNeutralOccupationCharge]
      rw [germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht,
        germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt B ht,
        G.finkContinuationGain_eq_expect_stateKernels]
      unfold finkStageGain finkStageEU finkContinuationEU mixedStageEU
      rw [← G.expect_finkStateKernel_eq]
      ring

omit [DecidableEq G.State] in
/-- Rearranged form: a baseline Bellman residual plus the raw charge is the
entire owner payoff residual for the selected occupation row. -/
theorem playerNeutralOccupation_payoffResidual_eq
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (target : ℝ)
    (index : germ.PlayerNeutralOccupationIndex who) :
    germ.playerNeutralOccupationStageEUAt ht who index +
          expect
            (germ.finkPlayerNeutralOccupationKernelAt ht who index)
            (fun state => B state who) -
          B (germ.playerNeutralOccupationSource who index) who -
          target =
      (G.finkStageEU (germ.finkPointAt ht)
            (germ.playerNeutralOccupationSource who index) who +
          G.finkContinuationEU B (germ.finkPointAt ht)
            (germ.playerNeutralOccupationSource who index) who -
          B (germ.playerNeutralOccupationSource who index) who -
          target) +
        germ.rawPlayerNeutralOccupationCharge B who t index := by
  rw [germ.playerNeutralOccupation_bellmanAccount_eq B ht who index]
  ring

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
