/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.BiasAlternative
import Math.Probability.AnalyticChargedOccupationFlow

/-!
# Analytic player-neutral occupation alternative

For one fixed player, restrict the raw analytic occupation family to the
prescribed baseline transitions and that player's continuation-neutral
actual actions. Against a fixed bias, the action columns carry their raw
stage-plus-continuation gain and the baseline columns carry zero charge.

The resulting analytic family specializes at the endpoint to the static
player-neutral occupation problem. The generic analytic charged-flow
alternative can therefore be applied without introducing formal action
reversals or actions owned by another player.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Embed the player-neutral operational family into the raw family of all
baseline transitions and player-owned pure deviations. -/
def playerNeutralOccupationIndexEmbedding
    {germ : G.AnalyticBellmanGerm} (who : ι) :
    germ.PlayerNeutralOccupationIndex who →
      G.State ⊕ (Σ owner : ι, G.State × G.Act owner)
  | .inl source => .inl source
  | .inr response =>
      .inr ⟨who, response.source, response.1.2⟩

/-- Moving actual occupation columns for the prescribed transitions and
one player's continuation-neutral pure actions. -/
def rawPlayerNeutralOccupationColumn
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ℝ → germ.PlayerNeutralOccupationIndex who → G.State → ℝ :=
  fun t index destination =>
    germ.rawAnalyticOccupationColumn t
      (playerNeutralOccupationIndexEmbedding who index) destination

/-- Moving charge against a fixed bias: baseline columns have zero charge,
while a continuation-neutral action carries its raw stage gain plus its raw
continuation gain against that bias. -/
def rawPlayerNeutralOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    ℝ → germ.PlayerNeutralOccupationIndex who → ℝ
  | _, .inl _ => 0
  | t, .inr response =>
      germ.rawPureDeviationStageGainCurve
          t response.source who response.1.2 +
        germ.rawPureDeviationContinuationGainCurve
          B t response.source who response.1.2

/-- Every coordinate of the moving player-neutral occupation family is
analytic at the endpoint. -/
theorem analytic_rawPlayerNeutralOccupationColumn
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∀ index destination,
      AnalyticAt ℝ
        (fun t =>
          germ.rawPlayerNeutralOccupationColumn
            who t index destination) 0 := by
  intro index destination
  exact germ.analytic_rawAnalyticOccupationColumn
    (playerNeutralOccupationIndexEmbedding who index) destination

omit [DecidableEq G.State] in
/-- Every moving player-neutral charge coordinate is analytic at the
endpoint. -/
theorem analytic_rawPlayerNeutralOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    ∀ index,
      AnalyticAt ℝ
        (fun t =>
          germ.rawPlayerNeutralOccupationCharge B who t index) 0 := by
  intro index
  cases index with
  | inl source =>
      exact analyticAt_const
  | inr response =>
      exact
        (analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStageGainCurve)
                response.source)) who) response.1.2).add
        (analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              (germ.analytic_rawPureDeviationContinuationGainCurve B))
                response.source)) who) response.1.2)

/-- At parameter zero the moving player-neutral columns are exactly the
static endpoint actual-occupation columns. -/
theorem rawPlayerNeutralOccupationColumn_zero
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    germ.rawPlayerNeutralOccupationColumn who 0 =
      actualOccupationColumn
        (germ.playerNeutralOccupationKernel who)
        (germ.playerNeutralOccupationSource who) := by
  funext index destination
  cases index with
  | inl source =>
      simp only [rawPlayerNeutralOccupationColumn,
        playerNeutralOccupationIndexEmbedding,
        rawAnalyticOccupationColumn,
        actualOccupationColumn,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource]
      rw [germ.rawStateKernelCurve_zero_eq_finkStateKernel]
      rfl
  | inr response =>
      simp only [rawPlayerNeutralOccupationColumn,
        playerNeutralOccupationIndexEmbedding,
        rawAnalyticOccupationColumn,
        actualOccupationColumn,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource,
        ContinuationNeutralAction.kernel,
        ContinuationNeutralAction.source]
      rw [
        germ.rawPureDeviationStateKernelCurve_zero_eq_endpointFinkPoint]
      rfl

omit [DecidableEq G.State] in
/-- At parameter zero the moving charge is exactly the static endpoint
player-neutral occupation charge. -/
theorem rawPlayerNeutralOccupationCharge_zero
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    germ.rawPlayerNeutralOccupationCharge B who 0 =
      germ.playerNeutralOccupationCharge B who := by
  funext index
  cases index with
  | inl source => rfl
  | inr response =>
      simp only [rawPlayerNeutralOccupationCharge,
        playerNeutralOccupationCharge, neutralActionCharge]
      rw [
        germ.rawPureDeviationStageGainCurve_zero_eq_endpointFinkPoint,
        germ.rawPureDeviationContinuationGainCurve_zero_eq_endpointFinkPoint]

/-- The analytic charged-flow alternative for the actual operational family
consisting of prescribed transitions and one fixed player's
continuation-neutral actions.

The circulation and scaled-potential branches concern this finite analytic
occupation system only; they do not by themselves construct a strategy,
punishment, or recurrent child. -/
theorem
    rawPlayerNeutralPositiveChargedCirculation_xor_scaledPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation
          (germ.rawPlayerNeutralOccupationColumn who)
          (germ.rawPlayerNeutralOccupationCharge B who)))
      (Nonempty
        (AnalyticScaledChargedOccupationPotential
          (germ.rawPlayerNeutralOccupationColumn who)
          (germ.rawPlayerNeutralOccupationCharge B who))) := by
  exact
    analyticPositiveChargedCirculation_xor_scaledPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)
      (germ.analytic_rawPlayerNeutralOccupationColumn who)
      (germ.analytic_rawPlayerNeutralOccupationCharge B who)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
