/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptivePotentialSystem
import GameTheory.Concepts.Stochastic.PublicResponseCredibilityBoundary

/-!
# Compiling an operational public-response ledger

A public detector and its concentration estimates control statistical error.
They do not themselves compare a deviator's payoff with the target.  This file
isolates the additional strategic inequality in a form strictly narrower than
an adaptive-potential certificate.

The data below have constant target potentials.  Recommended play is bounded
above and below by two implementation ledgers.  After a unilateral deviation,
the stage payoff is bounded by the target plus:

* a monitoring residual, intended to be discharged by detector accounting;
* a continuation residual, intended to be discharged by the punishment or
  continuation construction.

Separate Cesàro bounds on those residuals compile to a genuine public-phase
punishment system and hence to the existing adaptive certificate.  No
potential, harmonicity, or certificate field is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Operational payoff and accounting data for a public response.

`deviation_stage` is the irreducible credibility input: it says that the
implemented response converts detected behavior and the chosen continuation
into an actual payoff ceiling.  The remaining deviation fields only account
for the two residual terms in that ceiling. -/
structure PublicResponseEnforcementLedgerAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (P : PublicPhaseProfile G) (s₀ : G.State)
    (v : Payoff ι) (error : ℝ) where
  horizon : ℕ
  lowerLoss : ι → G.HistoryPotential
  upperLoss : ι → G.HistoryPotential
  monitoringResidual :
    ∀ i, G.BehaviorStrategy i → G.HistoryPotential
  continuationResidual :
    ∀ i, G.BehaviorStrategy i → G.HistoryPotential
  monitoringError : ℝ
  continuationError : ℝ
  error_nonneg : 0 ≤ error
  horizon_ge_two : 2 ≤ horizon
  lower_stage : ∀ i (time : ℕ) (history : G.Hist time),
    v i ≤
      G.stageEUAt P.behaviorProfile history i +
        lowerLoss i time history
  upper_stage : ∀ i (time : ℕ) (history : G.Hist time),
    G.stageEUAt P.behaviorProfile history i ≤
      v i + upperLoss i time history
  deviation_stage : ∀ i (deviation : G.BehaviorStrategy i)
      (time : ℕ) (history : G.Hist time),
    G.stageEUAt
        (Function.update P.behaviorProfile i deviation)
        history i ≤
      v i +
        monitoringResidual i deviation time history +
        continuationResidual i deviation time history
  lowerLoss_cesaro : ∀ i total, horizon ≤ total →
    (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
      G.expectedHistoryValue P.behaviorProfile s₀
        (lowerLoss i) time ≤
      error
  upperLoss_cesaro : ∀ i total, horizon ≤ total →
    (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
      G.expectedHistoryValue P.behaviorProfile s₀
        (upperLoss i) time ≤
      error
  monitoringResidual_cesaro :
    ∀ i (deviation : G.BehaviorStrategy i) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
          G.expectedHistoryValue
            (Function.update P.behaviorProfile i deviation)
            s₀ (monitoringResidual i deviation) time ≤
          monitoringError
  continuationResidual_cesaro :
    ∀ i (deviation : G.BehaviorStrategy i) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
          G.expectedHistoryValue
            (Function.update P.behaviorProfile i deviation)
            s₀ (continuationResidual i deviation) time ≤
          continuationError
  deviation_budget : monitoringError + continuationError ≤ error

namespace PublicResponseEnforcementLedgerAt

variable [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {P : PublicPhaseProfile G} {s₀ : G.State}
  {v : Payoff ι} {error : ℝ}

/-- The constant target, read as a phase potential. -/
def targetPhasePotential (who : ι) (_ : P.Phase) : ℝ :=
  v who

/-- Monitoring and continuation residuals form the deviation charge. -/
def deviationCharge
    (ledger : G.PublicResponseEnforcementLedgerAt P s₀ v error)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    G.HistoryPotential :=
  fun time history =>
    ledger.monitoringResidual who deviation time history +
      ledger.continuationResidual who deviation time history

/-- The operational response ledger supplies a genuine public-phase
punishment system with constant target potentials. -/
def toPublicPhasePunishmentSystemAt
    (ledger : G.PublicResponseEnforcementLedgerAt P s₀ v error) :
    PublicPhasePunishmentSystemAt G P s₀ v error where
  horizon := ledger.horizon
  lowerPotential := fun who _ => v who
  upperPotential := fun who _ => v who
  deviationPotential := fun who _ => v who
  lowerCharge := ledger.lowerLoss
  upperCharge := ledger.upperLoss
  deviationCharge := ledger.deviationCharge
  horizon_ge_two := ledger.horizon_ge_two
  lower_initial := by
    intro who
    simpa using ledger.error_nonneg
  upper_initial := by
    intro who
    simpa using ledger.error_nonneg
  deviation_initial := by
    intro who
    simpa using ledger.error_nonneg
  lower_subharmonic := by
    intro who time history
    simp [PublicPhaseProfile.historyPotential,
      historyContinuationEU]
  lower_stage := ledger.lower_stage
  upper_superharmonic := by
    intro who time history
    simp [PublicPhaseProfile.historyPotential,
      historyContinuationEU]
  upper_stage := ledger.upper_stage
  deviation_superharmonic := by
    intro who deviation time history
    simp [PublicPhaseProfile.historyPotential,
      historyContinuationEU]
  deviation_stage := by
    intro who deviation time history
    simpa [PublicPhaseProfile.historyPotential,
      deviationCharge, add_assoc] using
        ledger.deviation_stage who deviation time history
  lower_charge_cesaro := ledger.lowerLoss_cesaro
  upper_charge_cesaro := ledger.upperLoss_cesaro
  deviation_charge_cesaro := by
    intro who deviation total htotal
    have hmonitor :=
      ledger.monitoringResidual_cesaro who deviation total htotal
    have hcontinuation :=
      ledger.continuationResidual_cesaro who deviation total htotal
    have hadd := add_le_add hmonitor hcontinuation
    change
      (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
          G.expectedHistoryValue
            (Function.update P.behaviorProfile who deviation)
            s₀
            (fun time history =>
              ledger.monitoringResidual who deviation time history +
                ledger.continuationResidual who deviation time history)
            time ≤
        error
    have hrewrite :
        (total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
            G.expectedHistoryValue
              (Function.update P.behaviorProfile who deviation)
              s₀
              (fun time history =>
                ledger.monitoringResidual who deviation time history +
                  ledger.continuationResidual who deviation time history)
              time =
          ((total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
              G.expectedHistoryValue
                (Function.update P.behaviorProfile who deviation)
                s₀ (ledger.monitoringResidual who deviation) time) +
            ((total : ℝ)⁻¹ * ∑ time ∈ Finset.range total,
              G.expectedHistoryValue
                (Function.update P.behaviorProfile who deviation)
                s₀ (ledger.continuationResidual who deviation) time) := by
      simp only [expectedHistoryValue, expect_add,
        Finset.sum_add_distrib, mul_add]
    rw [hrewrite]
    exact hadd.trans ledger.deviation_budget

/-- Existential public-phase packaging of the operational ledger. -/
theorem toIsPublicPhasePunishmentSystemAt
    (ledger : G.PublicResponseEnforcementLedgerAt P s₀ v error) :
    G.IsPublicPhasePunishmentSystemAt s₀ v error :=
  ⟨P, ⟨ledger.toPublicPhasePunishmentSystemAt⟩⟩

/-- Positive compiler from the public-response enforcement inequality and
its two quantitative accounts to the verifier's adaptive certificate. -/
theorem toIsAdaptivePotentialCertificateAt
    (ledger : G.PublicResponseEnforcementLedgerAt P s₀ v error) :
    G.IsAdaptivePotentialCertificateAt s₀ v error :=
  G.isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
    s₀ v error ledger.toIsPublicPhasePunishmentSystemAt

end PublicResponseEnforcementLedgerAt

namespace CredibleResponseNoAutomaticCertificate

open ActionDetectorNoAutomaticCloser

/-- The one-state profitable-response example cannot carry an enforcement
ledger.  Therefore the missing `deviation_stage` interface cannot be inferred
from target attainment and a centered positive-drift public detector. -/
theorem no_publicResponseEnforcementLedgerAt_feasibleTarget :
    ¬∃ P : PublicPhaseProfile game,
      Nonempty
        (game.PublicResponseEnforcementLedgerAt
          P () feasibleTarget (1 / 4 : ℝ)) := by
  rintro ⟨P, ⟨ledger⟩⟩
  exact not_isAdaptivePotentialCertificateAt_feasibleTarget
    ledger.toIsAdaptivePotentialCertificateAt

end CredibleResponseNoAutomaticCertificate

end StochasticGame
end GameTheory
