/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticPlayerNeutralScaledPotential
import GameTheory.Concepts.Stochastic.OccupationBellmanAccountIdentity

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

Both identities are the player-neutral instance of the generic oriented
account of `OccupationBellmanAccountIdentity`, whose orientation sends a
continuation-neutral response to its public source and its owned action.
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
/-- The player-neutral stage payoff is exactly the oriented row stage
payoff for the orientation reading a continuation-neutral response as its
public source together with its owned action.

The row-by-row form above is kept as the definition rather than as this
instantiation because downstream `simp only` calls unfold
`playerNeutralOccupationStageEUAt` and rely on its per-constructor
equations. -/
theorem playerNeutralOccupationStageEUAt_eq_occupationRow
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) :
    germ.playerNeutralOccupationStageEUAt ht who =
      germ.occupationRowStageEUAt ht who ContinuationNeutralAction.source
        (fun response => response.1.2) := by
  funext index
  cases index <;> rfl

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
  have account :=
    germ.occupationRow_bellmanAccount_eq B ht who
      ContinuationNeutralAction.source (fun response => response.1.2) index
  cases index <;> exact account

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
  have residual :=
    germ.occupationRow_payoffResidual_eq B ht who target
      ContinuationNeutralAction.source (fun response => response.1.2) index
  cases index <;> exact residual

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
