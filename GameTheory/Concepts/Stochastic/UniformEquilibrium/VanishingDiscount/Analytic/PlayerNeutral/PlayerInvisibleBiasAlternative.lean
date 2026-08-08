/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticHarmonicAdjustmentClosure
import Math.Probability.ChargedOccupationAlternative

/-!
# Playerwise occupation alternative for invisible neutral actions

Fix an endpoint bias vector `B`. For each player, this file collects the
state/action pairs that are both continuation-neutral at the analytic
Bellman endpoint and analytically invisible. The charged occupation
alternative is then applied to the actual endpoint pure-deviation kernels.

The baseline-augmented form keeps the alternatives owner preserving:

* one player's baseline transitions and actual deviations carry a normalized
  positive charged circulation; or
* one vector correction simultaneously controls every player's indexed
  actions.

The correction branch records its exact algebraic content. The corrected
gain for `B - C` is bounded by the on-profile drift of `C`. The same drift is
nonnegative at every state. No rank descent, target preservation, or
punishment credibility is asserted in the circulation branch.
-/

noncomputable section

open Math Math.Probability

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- A state/action pair for one player that is continuation-neutral at the
endpoint and whose analytic mixing-coordinate germ is identically zero on
the positive side. -/
def InvisibleNeutralAction
    (germ : G.AnalyticBellmanGerm) (who : ι) :=
  { response : G.State × G.Act who //
    G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint response.1 who response.2 = 0 ∧
      ¬germ.IsAnalyticallyVisibleAction response.1 who response.2 }

noncomputable instance instFintypeInvisibleNeutralAction
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    Fintype (germ.InvisibleNeutralAction who) := by
  letI : Finite G.State := Finite.of_fintype G.State
  letI : Finite (G.Act who) := Finite.of_fintype (G.Act who)
  letI : Finite (G.State × G.Act who) := inferInstance
  letI : Finite
      { response : G.State × G.Act who //
        G.finkContinuationGain germ.endpointValue
            germ.endpointFinkPoint response.1 who response.2 = 0 ∧
          ¬germ.IsAnalyticallyVisibleAction
            response.1 who response.2 } :=
    Subtype.finite
  change Fintype
    { response : G.State × G.Act who //
      G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint response.1 who response.2 = 0 ∧
        ¬germ.IsAnalyticallyVisibleAction response.1 who response.2 }
  exact Fintype.ofFinite _

/-- The source state of an invisible neutral action. -/
def InvisibleNeutralAction.source
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.InvisibleNeutralAction who) : G.State :=
  response.1.1

/-- The actual endpoint pure-deviation kernel of an invisible neutral
action. -/
def InvisibleNeutralAction.kernel
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.InvisibleNeutralAction who) : PMF G.State :=
  G.finkPureDeviationStateKernel germ.endpointFinkPoint
    response.source who response.1.2

/-- Static improvement charged to an invisible neutral action at endpoint
bias `B`. -/
def invisibleNeutralCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (response : germ.InvisibleNeutralAction who) : ℝ :=
  G.finkStageGain germ.endpointFinkPoint
      response.source who response.1.2 +
    G.finkContinuationGain B germ.endpointFinkPoint
      response.source who response.1.2

/-- Baseline transitions together with one player's invisible neutral
deviations. No deviation owned by another player occurs in this index. -/
abbrev PlayerInvisibleOccupationIndex
    (germ : G.AnalyticBellmanGerm) (who : ι) :=
  G.State ⊕ germ.InvisibleNeutralAction who

/-- The actual endpoint kernel attached to a baseline-augmented player
index. -/
def playerInvisibleOccupationKernel
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    germ.PlayerInvisibleOccupationIndex who → PMF G.State
  | .inl source =>
      G.finkStateKernel germ.endpointFinkPoint source
  | .inr response => response.kernel

/-- The source state attached to a baseline-augmented player index. -/
def playerInvisibleOccupationSource
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    germ.PlayerInvisibleOccupationIndex who → G.State
  | .inl source => source
  | .inr response => response.source

/-- Baseline indices have zero charge; invisible neutral deviations carry
their static improvement at `B`. -/
def playerInvisibleOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    germ.PlayerInvisibleOccupationIndex who → ℝ
  | .inl _ => 0
  | .inr response => germ.invisibleNeutralCharge B who response

/-- A correction controls all invisible neutral actions when its baseline
drift is nonnegative and every corrected gain is at most that baseline
drift. -/
def IsInvisibleNeutralBiasCorrection
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) : Prop :=
  (∀ source who,
      0 ≤ G.finkContinuationResidual C
        germ.endpointFinkPoint source who) ∧
    ∀ who (response : germ.InvisibleNeutralAction who),
      G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 +
          G.finkContinuationGain (B - C)
            germ.endpointFinkPoint
            response.source who response.1.2 ≤
        G.finkContinuationResidual C
          germ.endpointFinkPoint response.source who

omit [DecidableEq G.State] in
/-- A deviation continuation gain plus the baseline residual is the
source-based drift of the actual deviation kernel. -/
theorem invisibleNeutral_continuationGain_add_residual
    (germ : G.AnalyticBellmanGerm)
    (C : G.State → Payoff ι) (who : ι)
    (response : germ.InvisibleNeutralAction who) :
    G.finkContinuationGain C germ.endpointFinkPoint
          response.source who response.1.2 +
        G.finkContinuationResidual C germ.endpointFinkPoint
          response.source who =
      expect response.kernel (fun state => C state who) -
        C response.source who := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  unfold finkContinuationResidual finkContinuationEU
  rw [← G.expect_finkStateKernel_eq]
  change
    (expect response.kernel (fun state => C state who) -
          expect (G.finkStateKernel germ.endpointFinkPoint response.source)
            (fun state => C state who)) +
        (expect (G.finkStateKernel germ.endpointFinkPoint response.source)
            (fun state => C state who) -
          C response.source who) =
      expect response.kernel (fun state => C state who) -
        C response.source who
  ring

omit [DecidableEq G.State] in
/-- The corrected-gain inequality is exactly the action part of the
source-based drift-potential inequality. -/
theorem invisibleNeutral_correctedGain_le_residual_iff
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) (who : ι)
    (response : germ.InvisibleNeutralAction who) :
    G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 +
          G.finkContinuationGain (B - C)
            germ.endpointFinkPoint
            response.source who response.1.2 ≤
        G.finkContinuationResidual C
          germ.endpointFinkPoint response.source who ↔
      germ.invisibleNeutralCharge B who response ≤
        expect response.kernel (fun state => C state who) -
          C response.source who := by
  rw [G.finkContinuationGain_sub]
  constructor
  · intro h
    have hid :=
      germ.invisibleNeutral_continuationGain_add_residual
        C who response
    dsimp only [invisibleNeutralCharge] at h ⊢
    linarith
  · intro h
    have hid :=
      germ.invisibleNeutral_continuationGain_add_residual
        C who response
    dsimp only [invisibleNeutralCharge] at h ⊢
    linarith

omit [DecidableEq G.State] in
/-- The augmented drift-potential branch for one player is equivalent to a
nonnegative baseline drift plus all corrected-gain inequalities for that
player. -/
theorem playerInvisible_driftPotential_iff
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) (who : ι) :
    (∀ index : germ.PlayerInvisibleOccupationIndex who,
      germ.playerInvisibleOccupationCharge B who index ≤
        expect (germ.playerInvisibleOccupationKernel who index)
            (fun state => C state who) -
          C (germ.playerInvisibleOccupationSource who index) who) ↔
      (∀ source,
        0 ≤ G.finkContinuationResidual C
          germ.endpointFinkPoint source who) ∧
      ∀ response : germ.InvisibleNeutralAction who,
        G.finkStageGain germ.endpointFinkPoint
            response.source who response.1.2 +
            G.finkContinuationGain (B - C)
              germ.endpointFinkPoint
              response.source who response.1.2 ≤
          G.finkContinuationResidual C
            germ.endpointFinkPoint response.source who := by
  constructor
  · intro h
    constructor
    · intro source
      have hsource := h (Sum.inl source)
      dsimp only [playerInvisibleOccupationCharge,
        playerInvisibleOccupationKernel,
        playerInvisibleOccupationSource] at hsource
      unfold finkContinuationResidual finkContinuationEU
      rw [← G.expect_finkStateKernel_eq]
      exact hsource
    · intro response
      rw [germ.invisibleNeutral_correctedGain_le_residual_iff]
      simpa only [playerInvisibleOccupationCharge,
        playerInvisibleOccupationKernel,
        playerInvisibleOccupationSource] using h (Sum.inr response)
  · rintro ⟨hbaseline, haction⟩ index
    rcases index with source | response
    · dsimp only [playerInvisibleOccupationCharge,
        playerInvisibleOccupationKernel,
        playerInvisibleOccupationSource]
      have hsource := hbaseline source
      unfold finkContinuationResidual finkContinuationEU at hsource
      rw [← G.expect_finkStateKernel_eq] at hsource
      exact hsource
    · have hresponse := haction response
      rw [germ.invisibleNeutral_correctedGain_le_residual_iff] at hresponse
      simpa only [playerInvisibleOccupationCharge,
        playerInvisibleOccupationKernel,
        playerInvisibleOccupationSource] using hresponse

/-- Deviation-only charged occupation alternative for one player. -/
theorem
    normalizedInvisibleNeutralCirculation_xor_driftPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    Xor
      (HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun response : germ.InvisibleNeutralAction who =>
            response.kernel)
          (fun response => response.source))
        (germ.invisibleNeutralCharge B who))
      (∃ potential : G.State → ℝ,
        ∀ response : germ.InvisibleNeutralAction who,
          germ.invisibleNeutralCharge B who response ≤
            expect response.kernel potential -
              potential response.source) :=
  normalizedPositiveChargedCirculation_xor_driftPotential
    (fun response : germ.InvisibleNeutralAction who =>
      response.kernel)
    (fun response => response.source)
    (germ.invisibleNeutralCharge B who)

/-- Baseline-augmented charged occupation alternative for one player. -/
theorem
    normalizedPlayerInvisibleCirculation_xor_driftPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    Xor
      (HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerInvisibleOccupationKernel who)
          (germ.playerInvisibleOccupationSource who))
        (germ.playerInvisibleOccupationCharge B who))
      (∃ potential : G.State → ℝ,
        ∀ index : germ.PlayerInvisibleOccupationIndex who,
          germ.playerInvisibleOccupationCharge B who index ≤
            expect (germ.playerInvisibleOccupationKernel who index)
                potential -
              potential
                (germ.playerInvisibleOccupationSource who index)) :=
  normalizedPositiveChargedCirculation_xor_driftPotential
    (germ.playerInvisibleOccupationKernel who)
    (germ.playerInvisibleOccupationSource who)
    (germ.playerInvisibleOccupationCharge B who)

/-- **Owner-preserving global alternative.**

Either one player has a normalized positive circulation using only baseline
transitions and that player's actual invisible neutral deviations, or one
assembled correction vector controls every indexed action. -/
theorem
    exists_playerInvisibleCirculation_xor_biasCorrection
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) :
    Xor
      (∃ who,
        HasNormalizedPositiveChargedCirculation
          (actualOccupationColumn
            (germ.playerInvisibleOccupationKernel who)
            (germ.playerInvisibleOccupationSource who))
          (germ.playerInvisibleOccupationCharge B who))
      (∃ C : G.State → Payoff ι,
        germ.IsInvisibleNeutralBiasCorrection B C) := by
  classical
  rw [xor_def]
  by_cases hcirculation :
      ∃ who,
        HasNormalizedPositiveChargedCirculation
          (actualOccupationColumn
            (germ.playerInvisibleOccupationKernel who)
            (germ.playerInvisibleOccupationSource who))
          (germ.playerInvisibleOccupationCharge B who)
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨C, hC⟩
    obtain ⟨who, hwho⟩ := hcirculation
    have hpotential :
        ∃ potential : G.State → ℝ,
          ∀ index : germ.PlayerInvisibleOccupationIndex who,
            germ.playerInvisibleOccupationCharge B who index ≤
              expect (germ.playerInvisibleOccupationKernel who index)
                  potential -
                potential
                  (germ.playerInvisibleOccupationSource who index) := by
      refine ⟨fun state => C state who, ?_⟩
      apply
        (germ.playerInvisible_driftPotential_iff
          B C who).2
      exact ⟨fun source => hC.1 source who,
        fun response => hC.2 who response⟩
    have halt :=
      germ.normalizedPlayerInvisibleCirculation_xor_driftPotential
        B who
    rw [xor_def] at halt
    rcases halt with halt | halt
    · exact halt.2 hpotential
    · exact halt.2 hwho
  · refine Or.inr ⟨?_, hcirculation⟩
    have hpotential :
        ∀ who,
          ∃ potential : G.State → ℝ,
            ∀ index : germ.PlayerInvisibleOccupationIndex who,
              germ.playerInvisibleOccupationCharge B who index ≤
                expect
                    (germ.playerInvisibleOccupationKernel who index)
                    potential -
                  potential
                    (germ.playerInvisibleOccupationSource who index) := by
      intro who
      have halt :=
        germ.normalizedPlayerInvisibleCirculation_xor_driftPotential
          B who
      rw [xor_def] at halt
      rcases halt with halt | halt
      · exact False.elim (hcirculation ⟨who, halt.1⟩)
      · exact halt.1
    choose potential hpotentialSpec using hpotential
    let C : G.State → Payoff ι :=
      fun state who => potential who state
    refine ⟨C, ?_⟩
    constructor
    · intro source who
      have hwho :=
        (germ.playerInvisible_driftPotential_iff
          B C who).1 (by
            simpa only [C] using hpotentialSpec who)
      exact hwho.1 source
    · intro who response
      have hwho :=
        (germ.playerInvisible_driftPotential_iff
          B C who).1 (by
            simpa only [C] using hpotentialSpec who)
      exact hwho.2 response

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
