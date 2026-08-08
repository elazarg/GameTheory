/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicDeviationContinuationLedger

/-!
# Public-response enforcement from a processed harmonic account

This file is the direct downstream consumer of the deviation-law telescope
for a processed harmonic endpoint coordinate.

The input keeps every prescribed-play, monitoring, and total-budget
obligation of `PublicResponseEnforcementLedgerAt` explicit.  It also keeps
the historywise strategic deviation inequality explicit.  The only omitted
stochastic obligation is the continuation residual and its Cesàro estimate:
the residual is fixed to the endpoint-coordinate continuation drop, and the
processed-harmonic telescope proves its estimate under every unilateral
updated law.

The remaining numerical input `processedContinuation_rate` merely converts
the uniform finite telescope bound at the chosen horizon into the allocated
continuation error.  It contains no behavior law or strategic assertion.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- Enforcement data whose deviation continuation account is supplied by a
processed harmonic endpoint coordinate.

Compared with `PublicResponseEnforcementLedgerAt`, this structure omits the
choice of `continuationResidual` and the law-indexed
`continuationResidual_cesaro` proof.  All other strategic and accounting
obligations remain visible. -/
structure ProcessedHarmonicPublicResponseEnforcementData
    (jet : germ.LowerValueJet)
    (P : G.PublicPhaseProfile) (initial : G.State)
    (target : Payoff ι) (error : ℝ) where
  horizon : ℕ
  lowerLoss : ι → G.HistoryPotential
  upperLoss : ι → G.HistoryPotential
  monitoringResidual :
    ∀ who, G.BehaviorStrategy who → G.HistoryPotential
  monitoringError : ℝ
  continuationError : ℝ
  error_nonneg : 0 ≤ error
  horizon_ge_two : 2 ≤ horizon
  lower_stage : ∀ who (stage : ℕ) (history : G.Hist stage),
    target who ≤
      G.stageEUAt P.behaviorProfile history who +
        lowerLoss who stage history
  upper_stage : ∀ who (stage : ℕ) (history : G.Hist stage),
    G.stageEUAt P.behaviorProfile history who ≤
      target who + upperLoss who stage history
  deviation_stage :
    ∀ who (deviation : G.BehaviorStrategy who)
        (stage : ℕ) (history : G.Hist stage),
      G.stageEUAt
          (Function.update P.behaviorProfile who deviation)
          history who ≤
        target who +
          monitoringResidual who deviation stage history +
          jet.deviationContinuationResidual
            (Function.update P.behaviorProfile who deviation)
            who stage history
  lowerLoss_cesaro : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ * ∑ stage ∈ Finset.range total,
      G.expectedHistoryValue P.behaviorProfile initial
        (lowerLoss who) stage ≤
      error
  upperLoss_cesaro : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ * ∑ stage ∈ Finset.range total,
      G.expectedHistoryValue P.behaviorProfile initial
        (upperLoss who) stage ≤
      error
  monitoringResidual_cesaro :
    ∀ who (deviation : G.BehaviorStrategy who) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ * ∑ stage ∈ Finset.range total,
          G.expectedHistoryValue
            (Function.update P.behaviorProfile who deviation)
            initial (monitoringResidual who deviation) stage ≤
          monitoringError
  processedContinuation_rate : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        (2 * finiteStatePotentialBound
          (jet.endpointCoordinatePotential who)) ≤
      continuationError
  deviation_budget : monitoringError + continuationError ≤ error

namespace ProcessedHarmonicPublicResponseEnforcementData

variable {P : G.PublicPhaseProfile} {initial : G.State}
  {target : Payoff ι} {error : ℝ}
  {jet : germ.LowerValueJet}

/-- The processed endpoint-coordinate telescope fills exactly the omitted
continuation fields and produces an ordinary public-response enforcement
ledger. -/
def toPublicResponseEnforcementLedgerAt
    (data :
      jet.ProcessedHarmonicPublicResponseEnforcementData
        P initial target error) :
    G.PublicResponseEnforcementLedgerAt P initial target error where
  horizon := data.horizon
  lowerLoss := data.lowerLoss
  upperLoss := data.upperLoss
  monitoringResidual := data.monitoringResidual
  continuationResidual := fun who deviation =>
    jet.deviationContinuationResidual
      (Function.update P.behaviorProfile who deviation) who
  monitoringError := data.monitoringError
  continuationError := data.continuationError
  error_nonneg := data.error_nonneg
  horizon_ge_two := data.horizon_ge_two
  lower_stage := data.lower_stage
  upper_stage := data.upper_stage
  deviation_stage := data.deviation_stage
  lowerLoss_cesaro := data.lowerLoss_cesaro
  upperLoss_cesaro := data.upperLoss_cesaro
  monitoringResidual_cesaro := data.monitoringResidual_cesaro
  continuationResidual_cesaro := by
    exact
      (jet.deviationStage_and_continuationCesaro_of_processedAccount
        P.behaviorProfile initial target data.monitoringResidual
        data.deviation_stage data.horizon data.continuationError
        data.processedContinuation_rate).2
  deviation_budget := data.deviation_budget

omit [DecidableEq G.State] in
/-- The completed operational ledger compiles immediately to a public-phase
punishment system. -/
theorem toIsPublicPhasePunishmentSystemAt
    (data :
      jet.ProcessedHarmonicPublicResponseEnforcementData
        P initial target error) :
    G.IsPublicPhasePunishmentSystemAt initial target error :=
  data.toPublicResponseEnforcementLedgerAt
    |>.toIsPublicPhasePunishmentSystemAt

omit [DecidableEq G.State] in
/-- The same data are accepted by the adaptive-potential verifier. -/
theorem toIsAdaptivePotentialCertificateAt
    (data :
      jet.ProcessedHarmonicPublicResponseEnforcementData
        P initial target error) :
    G.IsAdaptivePotentialCertificateAt initial target error :=
  data.toPublicResponseEnforcementLedgerAt
    |>.toIsAdaptivePotentialCertificateAt

end ProcessedHarmonicPublicResponseEnforcementData
end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
