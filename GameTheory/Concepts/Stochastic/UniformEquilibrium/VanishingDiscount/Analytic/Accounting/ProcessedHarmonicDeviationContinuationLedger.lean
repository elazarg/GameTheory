/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicResponseRealization
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Architectures.PublicResponse.EnforcementCompiler

/-!
# Deviation-law continuation ledgers for processed harmonic accounts

The processed-harmonic state account does apply under an arbitrary
unilateral updated law, but only to one precisely identified term.  If `H`
is the selected endpoint-coordinate potential, that term is

`H(current) - E[H(next) | history]`.

It is the negative conditional mean of the realized account increment.
Under the updated law's own history distribution its cumulative expectation
telescopes, and is bounded above by twice the finite-state bound of `H`.

This does not prove the strategic `deviation_stage` field of
`PublicResponseEnforcementLedgerAt`.  The missing sufficient interface is
the historywise Bellman inequality saying that the deviator's stage payoff
is at most the target, monitoring residual, and this exact continuation
drop.  The final theorems below separate that strategic input from the
automatic account discharge.

The one-state example records the sharp boundary: a constant continuation
account has zero residual under every law while a unilateral action can
still have a positive stage gain.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Math Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- The endpoint coordinate of a lower jet, viewed as a history potential. -/
def endpointCoordinateHistoryPotential
    (jet : germ.LowerValueJet) (who : ι) :
    G.HistoryPotential :=
  fun _ history => jet.endpointCoordinatePotential who history.2

/-- The continuation drop of the endpoint-coordinate account under the
given behavior profile's actual one-step law. -/
def deviationContinuationResidual
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (who : ι) :
    G.HistoryPotential :=
  fun _ history =>
    jet.endpointCoordinatePotential who history.2 -
      G.historyContinuationEU profile
        (jet.endpointCoordinateHistoryPotential who) history

omit [DecidableEq G.State] in
/-- The continuation residual is exactly the negative conditional mean of
the realized processed-harmonic account increment.  The identity holds for
every behavior profile; no stationarity or prescribed-law assumption is
used. -/
theorem deviationContinuationResidual_eq_neg_expectedAccountIncrement
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (who : ι) {stage : ℕ} (history : G.Hist stage) :
    jet.deviationContinuationResidual profile who stage history =
      -expect
        (behaviorStateStep profile history)
        (fun successor =>
          jet.endpointCoordinatePotential who successor -
            jet.endpointCoordinatePotential who history.2) := by
  unfold deviationContinuationResidual
    endpointCoordinateHistoryPotential historyContinuationEU
    behaviorStateStep
  rw [expect_bind]
  simp only [expect_sub, expect_const]
  ring

omit [DecidableEq G.State] in
/-- One-step expected continuation residual under the actual history law is
the drop of the expected endpoint-coordinate account. -/
theorem expected_deviationContinuationResidual_eq_sub
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (initial : G.State) (who : ι) (stage : ℕ) :
    G.expectedHistoryValue profile initial
        (jet.deviationContinuationResidual profile who) stage =
      G.expectedHistoryValue profile initial
          (jet.endpointCoordinateHistoryPotential who) stage -
      G.expectedHistoryValue profile initial
          (jet.endpointCoordinateHistoryPotential who) (stage + 1) := by
  have successor :=
    G.expectedHistoryValue_succ profile initial
      (jet.endpointCoordinateHistoryPotential who) stage
  unfold deviationContinuationResidual
  unfold expectedHistoryValue at successor ⊢
  rw [expect_sub, successor]
  rfl

omit [DecidableEq G.State] in
/-- Exact finite-horizon telescope for the continuation residual. -/
theorem sum_expected_deviationContinuationResidual_eq
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (initial : G.State) (who : ι) (total : ℕ) :
    (∑ stage ∈ Finset.range total,
        G.expectedHistoryValue profile initial
          (jet.deviationContinuationResidual profile who) stage) =
      G.expectedHistoryValue profile initial
          (jet.endpointCoordinateHistoryPotential who) 0 -
        G.expectedHistoryValue profile initial
          (jet.endpointCoordinateHistoryPotential who) total := by
  simp_rw [
    jet.expected_deviationContinuationResidual_eq_sub
      profile initial who]
  exact Finset.sum_range_sub' _ _

omit [DecidableEq G.State] in
/-- The endpoint-coordinate history account has the same uniform
finite-state bound under every behavior law. -/
theorem abs_expected_endpointCoordinateHistoryPotential_le
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (initial : G.State) (who : ι) (stage : ℕ) :
    |G.expectedHistoryValue profile initial
        (jet.endpointCoordinateHistoryPotential who) stage| ≤
      finiteStatePotentialBound
        (jet.endpointCoordinatePotential who) := by
  unfold expectedHistoryValue
  apply abs_expect_le_of_abs_le
  intro history
  simpa [endpointCoordinateHistoryPotential,
    endpointCoordinateAccount, statePotentialAccount] using
    jet.abs_endpointCoordinateAccount_le who
      (fun _ => history.2) 0

omit [DecidableEq G.State] in
/-- Uniform cumulative upper bound for the continuation residual under an
arbitrary behavior law. -/
theorem sum_expected_deviationContinuationResidual_le
    (jet : germ.LowerValueJet) (profile : G.BehaviorProfile)
    (initial : G.State) (who : ι) (total : ℕ) :
    (∑ stage ∈ Finset.range total,
        G.expectedHistoryValue profile initial
          (jet.deviationContinuationResidual profile who) stage) ≤
      2 * finiteStatePotentialBound
        (jet.endpointCoordinatePotential who) := by
  rw [jet.sum_expected_deviationContinuationResidual_eq
    profile initial who total]
  have hzero :=
    jet.abs_expected_endpointCoordinateHistoryPotential_le
      profile initial who 0
  have htotal :=
    jet.abs_expected_endpointCoordinateHistoryPotential_le
      profile initial who total
  rw [abs_le] at hzero htotal
  linarith

omit [DecidableEq G.State] in
/-- Specialization to every unilateral update of a prescribed profile. -/
theorem sum_expected_deviationContinuationResidual_update_le
    (jet : germ.LowerValueJet) (prescribed : G.BehaviorProfile)
    (initial : G.State) (who : ι)
    (deviation : G.BehaviorStrategy who) (total : ℕ) :
    (∑ stage ∈ Finset.range total,
        G.expectedHistoryValue
          (Function.update prescribed who deviation) initial
          (jet.deviationContinuationResidual
            (Function.update prescribed who deviation) who)
          stage) ≤
      2 * finiteStatePotentialBound
        (jet.endpointCoordinatePotential who) :=
  jet.sum_expected_deviationContinuationResidual_le
    (Function.update prescribed who deviation) initial who total

/-- Exact strategic interface still required to use the account as the
`continuationResidual` in a public-response enforcement ledger. -/
def HasProcessedHarmonicDeviationStageBound
    (jet : germ.LowerValueJet)
    (prescribed : G.BehaviorProfile) (target : Payoff ι)
    (monitoringResidual :
      ∀ who, G.BehaviorStrategy who → G.HistoryPotential) :
    Prop :=
  ∀ who (deviation : G.BehaviorStrategy who)
      (stage : ℕ) (history : G.Hist stage),
    G.stageEUAt
        (Function.update prescribed who deviation)
        history who ≤
      target who +
        monitoringResidual who deviation stage history +
        jet.deviationContinuationResidual
          (Function.update prescribed who deviation) who stage history

omit [DecidableEq G.State] in
/-- Once the historywise strategic interface is supplied, its continuation
term is automatically a valid Cesàro ledger under every unilateral updated
law.  The displayed rate condition is the only numerical conversion needed
for a chosen ledger horizon and continuation error. -/
theorem deviationStage_and_continuationCesaro_of_processedAccount
    (jet : germ.LowerValueJet)
    (prescribed : G.BehaviorProfile) (initial : G.State)
    (target : Payoff ι)
    (monitoringResidual :
      ∀ who, G.BehaviorStrategy who → G.HistoryPotential)
    (strategic :
      jet.HasProcessedHarmonicDeviationStageBound
        prescribed target monitoringResidual)
    (horizon : ℕ) (continuationError : ℝ)
    (rate :
      ∀ who total, horizon ≤ total →
        (total : ℝ)⁻¹ *
            (2 * finiteStatePotentialBound
              (jet.endpointCoordinatePotential who)) ≤
          continuationError) :
    (∀ who (deviation : G.BehaviorStrategy who)
        (stage : ℕ) (history : G.Hist stage),
      G.stageEUAt
          (Function.update prescribed who deviation)
          history who ≤
        target who +
          monitoringResidual who deviation stage history +
          jet.deviationContinuationResidual
            (Function.update prescribed who deviation)
            who stage history) ∧
      (∀ who (deviation : G.BehaviorStrategy who) total,
        horizon ≤ total →
          (total : ℝ)⁻¹ *
              ∑ stage ∈ Finset.range total,
                G.expectedHistoryValue
                  (Function.update prescribed who deviation)
                  initial
                  (jet.deviationContinuationResidual
                    (Function.update prescribed who deviation) who)
                  stage ≤
            continuationError) := by
  constructor
  · exact strategic
  · intro who deviation total htotal
    have hsum :=
      jet.sum_expected_deviationContinuationResidual_update_le
        prescribed initial who deviation total
    have hnonneg : 0 ≤ (total : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    exact
      (mul_le_mul_of_nonneg_left hsum hnonneg).trans
        (rate who total htotal)

end LowerValueJet
end AnalyticBellmanGerm

namespace ProcessedHarmonicContinuationBoundary

open ActionDetectorNoAutomaticCloser
open CredibleResponseNoAutomaticCertificate
open Math.Probability

/-- A constant continuation account has zero residual under every behavior
law and at every history. -/
theorem zeroContinuationResidual_eq_zero
    (profile : game.BehaviorProfile)
    {stage : ℕ} (history : game.Hist stage) :
    (0 : ℝ) -
        game.historyContinuationEU profile
          (fun _ _ => (0 : ℝ)) history =
      0 := by
  simp [historyContinuationEU]

/-- The continuation account alone cannot imply the strategic stage bound:
in the one-state game the pure-`true` deviation has stage payoff one while
the target, monitoring term, and constant-account continuation residual are
all zero. -/
theorem no_deviationStage_from_zeroContinuationAccount
    (profile : game.BehaviorProfile) :
    ¬∀ (stage : ℕ) (history : game.Hist stage),
      game.stageEUAt
          (Function.update profile () pureTrueDeviation)
          history () ≤
        feasibleTarget () +
          (0 : ℝ) +
          ((0 : ℝ) -
            game.historyContinuationEU
              (Function.update profile () pureTrueDeviation)
              (fun _ _ => (0 : ℝ)) history) := by
  intro bound
  let history : game.Hist 0 := (Fin.elim0, ())
  have h := bound 0 history
  rw [zeroContinuationResidual_eq_zero] at h
  simp only [feasibleTarget, add_zero] at h
  have profile_eq :
      Function.update profile () pureTrueDeviation =
        game.stationaryBehaviorProfile
          (fun _ : Player => PMF.pure true) := by
    funext owner stage history
    have owner_eq : owner = () := Subsingleton.elim _ _
    subst owner
    simp [pureTrueDeviation,
      StochasticGame.stationaryBehaviorProfile]
  rw [profile_eq] at h
  unfold stageEUAt at h
  rw [game.stageActionDist_stationaryBehaviorProfile] at h
  rw [Math.PMFProduct.pmfPi_pure, expect_pure] at h
  change (if true then (1 : ℝ) else 0) ≤ 0 at h
  norm_num at h

end ProcessedHarmonicContinuationBoundary

end StochasticGame
end GameTheory
