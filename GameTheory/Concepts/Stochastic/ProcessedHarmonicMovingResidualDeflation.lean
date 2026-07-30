/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ProcessedHarmonicQuotientAccount
import GameTheory.Concepts.Stochastic.PlayerNeutralStrictSetDeflation

/-!
# Deflating moving residuals of harmonic quotient corrections

Endpoint harmonicity leaves one exact positive-parameter term: the
prescribed moving-kernel residual.  This file removes a separate
sublinearity premise for that term whenever it is supported on a previously
deflated strict transition set.

An invisible response embeds canonically into the full player-neutral
occupation family.  Pulling a strict set back along this embedding preserves
the same positive drift margin, so its predictable behavioral mass is
sublinear.  Every uniformly bounded moving residual supported on that
pulled-back set therefore has sublinear expected absolute cumulative cost.

Combining this derived cost with the automatic harmonic-correction slack
ledger yields one complete sublinear moving-correction budget.  The remaining
hypothesis is pointwise support: outside the already deflated strict set, the
moving-baseline residual must vanish.  Without either this support condition
or a separate vanishing calendar envelope, a fixed nonzero residual can be
paid on every round and need not be sublinear.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- Canonical embedding of an invisible neutral response into the full
player-neutral occupation family of the same owner. -/
def invisibleNeutralOccupationIndex
    {who : ι} (response : germ.InvisibleNeutralAction who) :
    germ.PlayerNeutralOccupationIndex who :=
  .inr ⟨response.1, response.property.1⟩

omit [DecidableEq G.State] in
@[simp]
theorem playerNeutralOccupationKernel_invisibleNeutralOccupationIndex
    {who : ι} (response : germ.InvisibleNeutralAction who) :
    germ.playerNeutralOccupationKernel who
        (invisibleNeutralOccupationIndex response) =
      response.kernel :=
  rfl

omit [DecidableEq G.State] in
@[simp]
theorem playerNeutralOccupationSource_invisibleNeutralOccupationIndex
    {who : ι} (response : germ.InvisibleNeutralAction who) :
    germ.playerNeutralOccupationSource who
        (invisibleNeutralOccupationIndex response) =
      response.source :=
  rfl

variable
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {strictJet : GaugeFixedPotentialJet P anchor}

/-- Pullback of a previously deflated full player-neutral strict set to the
invisible responses governed by one harmonic quotient family. -/
def invisibleStrictIndexSet
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet) :
    Finset (germ.InvisibleNeutralAction who) := by
  classical
  exact Finset.univ.filter fun response =>
    invisibleNeutralOccupationIndex response ∈ C.strictIndexSet

theorem mem_invisibleStrictIndexSet_iff
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    (response : germ.InvisibleNeutralAction who) :
    response ∈ invisibleStrictIndexSet C ↔
      invisibleNeutralOccupationIndex response ∈ C.strictIndexSet := by
  classical
  simp [invisibleStrictIndexSet]

/-- Every invisible endpoint response has nonnegative drift under the
strict-set potential. -/
theorem invisibleStrict_drift_nonneg
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    (response : germ.InvisibleNeutralAction who) :
    0 ≤
      transitionPotentialDrift
        (fun action : germ.InvisibleNeutralAction who => action.kernel)
        (fun action : germ.InvisibleNeutralAction who => action.source)
        C.potential response := by
  simpa only [transitionPotentialDrift,
    playerNeutralOccupationKernel_invisibleNeutralOccupationIndex,
    playerNeutralOccupationSource_invisibleNeutralOccupationIndex,
    PlayerNeutralStrictLeadingDrift.normalizedDrift] using
      C.drift_nonneg (invisibleNeutralOccupationIndex response)

/-- The original strict margin remains valid on the pulled-back invisible
strict set. -/
theorem strictMargin_le_invisibleStrict_drift
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    {response : germ.InvisibleNeutralAction who}
    (response_mem : response ∈ invisibleStrictIndexSet C) :
    C.strictMargin ≤
      transitionPotentialDrift
        (fun action : germ.InvisibleNeutralAction who => action.kernel)
        (fun action : germ.InvisibleNeutralAction who => action.source)
        C.potential response := by
  have margin :=
    C.strictMargin_le_normalizedDrift
      ((mem_invisibleStrictIndexSet_iff C response).mp response_mem)
  simpa only [transitionPotentialDrift,
    playerNeutralOccupationKernel_invisibleNeutralOccupationIndex,
    playerNeutralOccupationSource_invisibleNeutralOccupationIndex,
    PlayerNeutralStrictLeadingDrift.normalizedDrift] using margin

/-- Expected predictable behavioral mass placed on the pulled-back
invisible strict set. -/
def invisibleStrictExpectedMass
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  transitionSetExpectedMass initial
    (fun response : germ.InvisibleNeutralAction who => response.kernel)
    selection (invisibleStrictIndexSet C) T

/-- Strict-set deflation automatically supplies a sublinear behavioral mass
budget after restriction to invisible responses. -/
theorem invisibleStrictExpectedMass_sublinear
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n)) :
    IsAsymptoticallySublinear
      (invisibleStrictExpectedMass C initial selection) := by
  unfold invisibleStrictExpectedMass
  exact transitionSetExpectedMass_isAsymptoticallySublinear
    initial
    (fun response : germ.InvisibleNeutralAction who => response.kernel)
    (fun response : germ.InvisibleNeutralAction who => response.source)
    selection (invisibleStrictIndexSet C)
    C.potential C.strictMargin_pos C.bounded
    source_compatible
    (invisibleStrict_drift_nonneg C)
    (fun _ response_mem =>
      strictMargin_le_invisibleStrict_drift C response_mem)

/-- Finite bound for a fixed positive-parameter moving-baseline residual
over all invisible responses. -/
def HarmonicInvisibleQuotientCorrection.movingResidualBound
    {lowerJet : germ.LowerValueJet}
    {family : lowerJet.InvisibleNeutralQuotientFamily who}
    (correction :
      lowerJet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius) : ℝ :=
  ∑ response : germ.InvisibleNeutralAction who,
    |correction.movingBaselineResidualAt ht response.source|

omit [DecidableEq G.State] in
/-- Every fixed moving residual is bounded by its finite-family absolute
sum. -/
theorem
    HarmonicInvisibleQuotientCorrection.abs_movingBaselineResidualAt_le
    {lowerJet : germ.LowerValueJet}
    {family : lowerJet.InvisibleNeutralQuotientFamily who}
    (correction :
      lowerJet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (response : germ.InvisibleNeutralAction who) :
    |correction.movingBaselineResidualAt ht response.source| ≤
      correction.movingResidualBound ht := by
  exact Finset.single_le_sum
    (fun other _ =>
      abs_nonneg
        (correction.movingBaselineResidualAt ht other.source))
    (Finset.mem_univ response)

/-- A moving residual supported on the previously deflated strict set has
sublinear expected absolute cumulative cost.  The strict-set mass budget,
not a new residual-ledger premise, proves the conclusion. -/
theorem
    HarmonicInvisibleQuotientCorrection.movingResidualCost_sublinear_of_support
    {lowerJet : germ.LowerValueJet}
    {family : lowerJet.InvisibleNeutralQuotientFamily who}
    (correction :
      lowerJet.HarmonicInvisibleQuotientCorrection who family)
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (supported :
      ∀ response,
        response ∉ invisibleStrictIndexSet C →
          correction.movingBaselineResidualAt ht response.source = 0) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (fun response : germ.InvisibleNeutralAction who =>
                  response.kernel)
                selection))
            (T + 1))
          (fun history =>
            |mixedTransitionCostSum selection
              (fun response =>
                correction.movingBaselineResidualAt
                  ht response.source)
              T history|)) := by
  apply exceptionalMixedTransitionCost_isAsymptoticallySublinear
    initial
    (fun response : germ.InvisibleNeutralAction who => response.kernel)
    selection
    (fun response =>
      correction.movingBaselineResidualAt ht response.source)
    (invisibleStrictIndexSet C)
    (correction.movingResidualBound ht)
  · exact supported
  · intro response _
    exact correction.abs_movingBaselineResidualAt_le ht response
  · exact invisibleStrictExpectedMass_sublinear C
      initial selection source_compatible

/-- Total moving-correction budget: automatic nonnegative corrected-gain
slack plus the absolute cumulative moving-baseline residual. -/
def HarmonicInvisibleQuotientCorrection.movingCorrectionBudget
    {lowerJet : germ.LowerValueJet}
    {family : lowerJet.InvisibleNeutralQuotientFamily who}
    (correction :
      lowerJet.HarmonicInvisibleQuotientCorrection who family)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (T : ℕ) : ℝ :=
  (∑ stage ∈ Finset.range T,
      correction.expectedMixedSlackStage initial selection stage) +
    expect
      (adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (mixedTransitionComparison
            (fun response : germ.InvisibleNeutralAction who =>
              response.kernel)
            selection))
        (T + 1))
      (fun history =>
        |mixedTransitionCostSum selection
          (fun response =>
            correction.movingBaselineResidualAt ht response.source)
          T history|)

/-- Combined ledger theorem.  Processed harmonic quotient/slack accounting
and strict-set exceptional-mass deflation together make the entire moving
correction budget sublinear, with no separate residual-sublinearity
premise. -/
theorem
    HarmonicInvisibleQuotientCorrection.movingCorrectionBudget_sublinear
    {lowerJet : germ.LowerValueJet}
    (span : germ.EndpointHarmonicJetSpan)
    (processed : lowerJet.factor 0 ∈ span.carrier)
    {family : lowerJet.InvisibleNeutralQuotientFamily who}
    (correction :
      lowerJet.HarmonicInvisibleQuotientCorrection who family)
    (C : germ.PlayerNeutralStrictLeadingDrift B who strictJet)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) germ.radius)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.InvisibleNeutralAction who))
    (source_compatible :
      ∀ n history response,
        selection n history response ≠ 0 →
          response.source = history (Fin.last n))
    (supported :
      ∀ response,
        response ∉ invisibleStrictIndexSet C →
          correction.movingBaselineResidualAt ht response.source = 0) :
    IsAsymptoticallySublinear
      (correction.movingCorrectionBudget
        ht initial selection) := by
  unfold movingCorrectionBudget
  exact
    (correction.mixedSlackStageLedger_sublinear
      span processed initial selection source_compatible).add
      (correction.movingResidualCost_sublinear_of_support
        C ht initial selection source_compatible supported)

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
