/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticHarmonicAdjustmentClosure
import GameTheory.Concepts.Stochastic.FinkConstraintPublicResponse
import GameTheory.Concepts.Stochastic.SeparateBiasStationaryCertificate
import Math.Probability.OwnerChargedOccupationAlternative
import Math.Probability.PositiveChargedCirculationClass

/-!
# Playerwise bias alternative for all continuation-neutral actions

Fix an analytic Bellman endpoint and a candidate on-profile bias `B`. For
each player, augment the prescribed transition at every state with all of
that player's actual pure deviations that preserve the endpoint target.

The owner-preserving charged-occupation alternative gives exactly two cases:

* one player has a normalized positive charged circulation using only the
  prescribed transitions and that player's actual neutral deviations; or
* one vector correction has nonnegative prescribed drift and makes every
  target-neutral corrected gain satisfy the required Bellman inequality.

Unlike the invisible-action specialization, the correction branch covers
every target-neutral pure action. Combined with the separate-bias stationary
verifier, this is the complete finite verification side of the alternative.
The circulation branch still makes no entry or punishment claim.
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

/-- A state/action pair for one player whose pure-deviation continuation
preserves the analytic endpoint target. -/
def ContinuationNeutralAction
    (germ : G.AnalyticBellmanGerm) (who : ι) :=
  { response : G.State × G.Act who //
    G.finkContinuationGain germ.endpointValue
      germ.endpointFinkPoint response.1 who response.2 = 0 }

noncomputable instance instFintypeContinuationNeutralAction
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    Fintype (germ.ContinuationNeutralAction who) := by
  letI : Finite G.State := Finite.of_fintype G.State
  letI : Finite (G.Act who) := Finite.of_fintype (G.Act who)
  letI : Finite (G.State × G.Act who) := inferInstance
  letI : Finite
      { response : G.State × G.Act who //
        G.finkContinuationGain germ.endpointValue
          germ.endpointFinkPoint response.1 who response.2 = 0 } :=
    Subtype.finite
  change Fintype
    { response : G.State × G.Act who //
      G.finkContinuationGain germ.endpointValue
        germ.endpointFinkPoint response.1 who response.2 = 0 }
  exact Fintype.ofFinite _

/-- Source state of a continuation-neutral pure action. -/
def ContinuationNeutralAction.source
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.ContinuationNeutralAction who) : G.State :=
  response.1.1

/-- Actual endpoint pure-deviation kernel of a continuation-neutral action. -/
def ContinuationNeutralAction.kernel
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.ContinuationNeutralAction who) : PMF G.State :=
  G.finkPureDeviationStateKernel germ.endpointFinkPoint
    response.source who response.1.2

/-- Static target-neutral improvement at endpoint bias `B`. -/
def neutralActionCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (response : germ.ContinuationNeutralAction who) : ℝ :=
  G.finkStageGain germ.endpointFinkPoint
      response.source who response.1.2 +
    G.finkContinuationGain B germ.endpointFinkPoint
      response.source who response.1.2

/-- Prescribed transitions augmented with one player's actual
continuation-neutral deviations. -/
abbrev PlayerNeutralOccupationIndex
    (germ : G.AnalyticBellmanGerm) (who : ι) :=
  G.State ⊕ germ.ContinuationNeutralAction who

/-- Actual endpoint kernel for a player-neutral occupation index. -/
def playerNeutralOccupationKernel
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    germ.PlayerNeutralOccupationIndex who → PMF G.State
  | .inl source =>
      G.finkStateKernel germ.endpointFinkPoint source
  | .inr response => response.kernel

/-- Source state for a player-neutral occupation index. -/
def playerNeutralOccupationSource
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    germ.PlayerNeutralOccupationIndex who → G.State
  | .inl source => source
  | .inr response => response.source

/-- Prescribed indices have zero charge; neutral deviations carry their
static improvement at `B`. -/
def playerNeutralOccupationCharge
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι) :
    germ.PlayerNeutralOccupationIndex who → ℝ
  | .inl _ => 0
  | .inr response => germ.neutralActionCharge B who response

/-- A vector correction with nonnegative prescribed drift that controls every
target-neutral pure action. -/
def IsNeutralBiasCorrection
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) : Prop :=
  (∀ source who,
      0 ≤ G.finkContinuationResidual C
        germ.endpointFinkPoint source who) ∧
    ∀ who (response : germ.ContinuationNeutralAction who),
      G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 +
          G.finkContinuationGain (B - C)
            germ.endpointFinkPoint
            response.source who response.1.2 ≤
        G.finkContinuationResidual C
          germ.endpointFinkPoint response.source who

omit [DecidableEq G.State] in
/-- The corrected neutral gain inequality is equivalent to the operational
drift inequality for the original charge. -/
theorem neutralAction_correctedGain_le_residual_iff
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) (who : ι)
    (response : germ.ContinuationNeutralAction who) :
    G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2 +
          G.finkContinuationGain (B - C)
            germ.endpointFinkPoint
            response.source who response.1.2 ≤
        G.finkContinuationResidual C
          germ.endpointFinkPoint response.source who ↔
      germ.neutralActionCharge B who response ≤
        expect response.kernel (fun state => C state who) -
          C response.source who := by
  rw [G.finkContinuationGain_sub]
  have hid :
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
            expect
              (G.finkStateKernel
                germ.endpointFinkPoint response.source)
              (fun state => C state who)) +
          (expect
              (G.finkStateKernel
                germ.endpointFinkPoint response.source)
              (fun state => C state who) -
            C response.source who) =
        expect response.kernel (fun state => C state who) -
          C response.source who
    ring
  dsimp only [neutralActionCharge] at hid ⊢
  constructor <;> intro h <;> linarith

omit [DecidableEq G.State] in
/-- The augmented ownerwise drift-potential branch is exactly a neutral-bias
correction in one player coordinate. -/
theorem playerNeutral_driftPotential_iff
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι) (who : ι) :
    (∀ index : germ.PlayerNeutralOccupationIndex who,
      germ.playerNeutralOccupationCharge B who index ≤
        expect (germ.playerNeutralOccupationKernel who index)
            (fun state => C state who) -
          C (germ.playerNeutralOccupationSource who index) who) ↔
      (∀ source,
        0 ≤ G.finkContinuationResidual C
          germ.endpointFinkPoint source who) ∧
      ∀ response : germ.ContinuationNeutralAction who,
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
      dsimp only [playerNeutralOccupationCharge,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource] at hsource
      unfold finkContinuationResidual finkContinuationEU
      rw [← G.expect_finkStateKernel_eq]
      exact hsource
    · intro response
      rw [germ.neutralAction_correctedGain_le_residual_iff]
      simpa only [playerNeutralOccupationCharge,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource] using h (Sum.inr response)
  · rintro ⟨hbaseline, haction⟩ index
    rcases index with source | response
    · dsimp only [playerNeutralOccupationCharge,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource]
      have hsource := hbaseline source
      unfold finkContinuationResidual finkContinuationEU at hsource
      rw [← G.expect_finkStateKernel_eq] at hsource
      exact hsource
    · have hresponse := haction response
      rw [germ.neutralAction_correctedGain_le_residual_iff] at hresponse
      simpa only [playerNeutralOccupationCharge,
        playerNeutralOccupationKernel,
        playerNeutralOccupationSource] using hresponse

/-- **Owner-preserving target-neutral alternative.**

Either one player has a normalized positive charged circulation made from
prescribed transitions and that player's actual target-neutral deviations,
or one correction vector controls every target-neutral pure action. -/
theorem exists_playerNeutralCirculation_xor_biasCorrection
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) :
    Xor
      (∃ who,
        HasNormalizedPositiveChargedCirculation
          (actualOccupationColumn
            (germ.playerNeutralOccupationKernel who)
            (germ.playerNeutralOccupationSource who))
          (germ.playerNeutralOccupationCharge B who))
      (∃ C : G.State → Payoff ι,
        germ.IsNeutralBiasCorrection B C) := by
  classical
  have halt :=
    exists_ownerCirculation_xor_driftPotentialFamily
      germ.playerNeutralOccupationKernel
      germ.playerNeutralOccupationSource
      (germ.playerNeutralOccupationCharge B)
  rw [xor_def] at halt ⊢
  rcases halt with halt | halt
  · refine Or.inl ⟨halt.1, ?_⟩
    rintro ⟨C, hC⟩
    apply halt.2
    refine ⟨fun who state => C state who, ?_⟩
    intro who
    exact
      (germ.playerNeutral_driftPotential_iff B C who).2
        ⟨fun source => hC.1 source who,
          fun response => hC.2 who response⟩
  · refine Or.inr ⟨?_, halt.2⟩
    obtain ⟨potential, hpotential⟩ := halt.1
    let C : G.State → Payoff ι :=
      fun state who => potential who state
    refine ⟨C, ?_⟩
    constructor
    · intro source who
      exact
        ((germ.playerNeutral_driftPotential_iff B C who).1
          (by simpa only [C] using hpotential who)).1 source
    · intro who response
      exact
        ((germ.playerNeutral_driftPotential_iff B C who).1
          (by simpa only [C] using hpotential who)).2 response

omit [DecidableEq G.State] in
/-- The correction branch closes the stationary verification problem once
`B` is an exact on-profile bias.

The endpoint target is automatically harmonic and excessive. The correction
supplies the upper on-profile inequality and every target-neutral pure-action
inequality, so the separate-bias verifier absorbs all strict target losses. -/
theorem IsNeutralBiasCorrection.isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (B C : G.State → Payoff ι)
    (hcorrection : germ.IsNeutralBiasCorrection B C)
    (s₀ : G.State)
    (honProfile : ∀ source who,
      germ.endpointValue source who + B source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => B next who))) :
    G.IsUniformEquilibriumPayoff
      s₀ (germ.endpointValue s₀) := by
  have hharmonic :
      ∀ source who,
        germ.endpointValue source who =
          expect
            (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => germ.endpointValue next who)) := by
    intro source who
    have hzero :=
      congrFun
        (congrFun
          germ.finkContinuationResidualVector_endpointValue_eq_zero
          source) who
    have hcontinuation :
        G.finkContinuationEU germ.endpointValue
            germ.endpointFinkPoint source who =
          germ.endpointValue source who :=
      sub_eq_zero.mp
        (by
          simpa [finkContinuationResidualVector,
            finkContinuationResidual] using hzero)
    simpa [finkContinuationEU,
      germ.finkProfile_endpointFinkPoint] using hcontinuation.symm
  have hexcessive :
      ∀ source who (action : G.Act who),
        expect
            (Math.PMFProduct.pmfPi
              (Function.update
                (germ.endpointProfile source) who (PMF.pure action)))
            (fun jointAction =>
              expect (G.transition source jointAction)
                (fun next => germ.endpointValue next who)) ≤
          germ.endpointValue source who := by
    intro source who action
    have hgain :=
      germ.finkContinuationGain_endpointValue_nonpos
        source who action
    unfold finkContinuationGain at hgain
    rw [germ.finkProfile_endpointFinkPoint] at hgain
    linarith [hharmonic source who]
  apply
    G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBiasCorrection_on_neutral
      s₀ germ.endpointProfile germ.endpointValue B C
      hharmonic hexcessive honProfile
  · intro source who
    have hresidual := hcorrection.1 source who
    unfold finkContinuationResidual finkContinuationEU at hresidual
    rw [germ.finkProfile_endpointFinkPoint] at hresidual
    linarith
  · intro source who action hneutral
    let response : germ.ContinuationNeutralAction who :=
      ⟨(source, action), by
        unfold finkContinuationGain
        rw [germ.finkProfile_endpointFinkPoint]
        linarith [hharmonic source who]⟩
    have haction := hcorrection.2 who response
    change
      G.finkStageGain germ.endpointFinkPoint source who action +
          G.finkContinuationGain (B - C)
            germ.endpointFinkPoint source who action ≤
        G.finkContinuationResidual C
          germ.endpointFinkPoint source who
      at haction
    unfold finkStageGain finkContinuationGain
      finkContinuationResidual finkContinuationEU at haction
    rw [germ.finkProfile_endpointFinkPoint] at haction
    simp only [Pi.sub_apply] at haction
    simp_rw [expect_sub] at haction ⊢
    linarith [honProfile source who]

/-- With an exact on-profile bias, the finite target-neutral obstruction is
now entirely concentrated in one player's positive operational circulation.
If no such circulation exists, the assembled correction closes the uniform
equilibrium verification problem. -/
theorem playerNeutralCirculation_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (s₀ : G.State)
    (honProfile : ∀ source who,
      germ.endpointValue source who + B source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => B next who))) :
    (∃ who,
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) := by
  have halt :=
    germ.exists_playerNeutralCirculation_xor_biasCorrection B
  rw [xor_def] at halt
  rcases halt with halt | halt
  · exact Or.inl halt.1
  · obtain ⟨C, hC⟩ := halt.1
    exact Or.inr (hC.isUniformEquilibriumPayoff germ B C s₀ honProfile)

/-- Class-localized form of the player-neutral branch.  The positive
circulation has a communicating class with positive aggregate original
Bellman charge and an internal positive-mass representative.  No external
entry claim is made. -/
theorem
    playerNeutralPositiveClass_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (s₀ : G.State)
    (honProfile : ∀ source who,
      germ.endpointValue source who + B source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => B next who))) :
    (∃ who,
      Nonempty
        (PositiveChargedCirculationClass
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who)
          (germ.playerNeutralOccupationCharge B who))) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) := by
  rcases
      germ.playerNeutralCirculation_or_isUniformEquilibriumPayoff
        B s₀ honProfile with hcirculation | huniform
  · obtain ⟨who, hwho⟩ := hcirculation
    exact Or.inl
      ⟨who,
        hwho.exists_positiveChargedClass
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who)
          (germ.playerNeutralOccupationCharge B who)⟩
  · exact Or.inr huniform

/-- A normalized player-neutral circulation contains an actual neutral
deviation with strictly positive static Bellman charge. Prescribed indices
cannot be selected because their charge is zero. -/
theorem exists_positive_neutralActionCharge_of_circulation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (hcirculation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who)) :
    ∃ response : germ.ContinuationNeutralAction who,
      0 < germ.neutralActionCharge B who response := by
  obtain ⟨mass, hmass, -, hcharge⟩ := hcirculation
  have hpositive :
      ∃ index : germ.PlayerNeutralOccupationIndex who,
        0 <
          mass index *
            germ.playerNeutralOccupationCharge B who index := by
    by_contra hnone
    push Not at hnone
    have hsum :
        (∑ index,
          mass index *
            germ.playerNeutralOccupationCharge B who index) ≤ 0 :=
      Finset.sum_nonpos fun index _ => hnone index
    rw [hcharge] at hsum
    norm_num at hsum
  obtain ⟨index, hindex⟩ := hpositive
  rcases index with source | response
  · simp only [playerNeutralOccupationCharge, mul_zero] at hindex
    exact False.elim (lt_irrefl 0 hindex)
  · refine ⟨response, ?_⟩
    exact pos_of_mul_pos_right hindex (hmass (Sum.inr response))

omit [DecidableEq G.State] in
/-- The finite stationary branch may be reported without the auxiliary
circulation weights: either the endpoint target is verified, or one fixed
player-owned target-neutral action has strictly positive static Bellman
charge. The circulation remains available when recurrent accounting is
needed. -/
theorem exists_positiveNeutralAction_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (s₀ : G.State)
    (honProfile : ∀ source who,
      germ.endpointValue source who + B source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => B next who))) :
    (∃ who, ∃ response : germ.ContinuationNeutralAction who,
      0 < germ.neutralActionCharge B who response) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) := by
  classical
  rcases
      germ.playerNeutralCirculation_or_isUniformEquilibriumPayoff
        B s₀ honProfile with hcirculation | huniform
  · obtain ⟨who, hwho⟩ := hcirculation
    exact Or.inl
      ⟨who,
        germ.exists_positive_neutralActionCharge_of_circulation
          B who hwho⟩
  · exact Or.inr huniform

/-- A positive static charge of one target-neutral actual action is already
an operational public response at the endpoint: either its stage gain is
positive, or its continuation gain supplies a bounded centered transition
monitor. -/
noncomputable def ContinuationNeutralAction.publicConstraintResponse
    {germ : G.AnalyticBellmanGerm} {who : ι}
    (response : germ.ContinuationNeutralAction who)
    (B : G.State → Payoff ι)
    (hpositive : 0 < germ.neutralActionCharge B who response) :
    G.FinkPublicConstraintResponse
      germ.endpointFinkPoint B response.source who response.1.2 := by
  by_cases hstage :
      0 <
        G.finkStageGain germ.endpointFinkPoint
          response.source who response.1.2
  · exact FinkPublicConstraintResponse.stage hstage
  · have hcontinuation :
        0 <
          G.finkContinuationGain B germ.endpointFinkPoint
            response.source who response.1.2 := by
      dsimp only [neutralActionCharge] at hpositive
      linarith
    exact
      FinkPublicConstraintResponse.transition
        (G.finkPublicTransitionChargeOfContinuationGainPos
          germ.endpointFinkPoint B response.source who
          response.1.2 hcontinuation)

/-- Public-response form of the stationary branch reduction. -/
theorem exists_publicConstraintResponse_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (s₀ : G.State)
    (honProfile : ∀ source who,
      germ.endpointValue source who + B source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => B next who))) :
    (∃ who, ∃ response : germ.ContinuationNeutralAction who,
      Nonempty
        (G.FinkPublicConstraintResponse
          germ.endpointFinkPoint B response.source who response.1.2)) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) := by
  rcases
      germ.exists_positiveNeutralAction_or_isUniformEquilibriumPayoff
        B s₀ honProfile with hresponse | huniform
  · obtain ⟨who, response, hpositive⟩ := hresponse
    exact Or.inl
      ⟨who, response,
        ⟨response.publicConstraintResponse B hpositive⟩⟩
  · exact Or.inr huniform

omit [DecidableEq G.State] in
/-- A Poisson correction for a finite-bias seed produces the exact
on-profile endpoint bias required by the ownerwise neutral alternative. -/
theorem FiniteBiasSeed.onProfileBias_H_sub
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    (K : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint) :
    ∀ source who,
      germ.endpointValue source who + (seed.H - K) source who =
        G.mixedStageEU source (germ.endpointProfile source) who +
          expect (Math.PMFProduct.pmfPi (germ.endpointProfile source))
            (fun action =>
              expect (G.transition source action)
                (fun next => (seed.H - K) next who)) := by
  intro source who
  have hcoordinate :=
    congrFun (congrFun hPoisson source) who
  unfold finkBellmanForcingVector
    finkContinuationResidualVector
    finkContinuationResidual at hcoordinate
  change
    germ.endpointValue source who + seed.H source who -
          G.finkStageEU germ.endpointFinkPoint source who -
          G.finkContinuationEU seed.H
            germ.endpointFinkPoint source who =
      -(G.finkContinuationEU K
          germ.endpointFinkPoint source who - K source who)
    at hcoordinate
  rw [← germ.finkProfile_endpointFinkPoint]
  change
    germ.endpointValue source who + (seed.H - K) source who =
      G.finkStageEU germ.endpointFinkPoint source who +
        G.finkContinuationEU (seed.H - K)
          germ.endpointFinkPoint source who
  rw [G.finkContinuationEU_sub]
  simp only [Pi.sub_apply] at hcoordinate ⊢
  linarith

/-- In the finite-bias/Poisson branch, either verification is complete or
one player carries the sole remaining normalized positive neutral-action
circulation. No coherent stage-adjustment hypothesis is needed for this
dichotomy. -/
theorem FiniteBiasSeed.playerNeutralCirculation_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (K : G.State → Payoff ι)
    (s₀ : G.State)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint) :
    (∃ who,
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge (seed.H - K) who)) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) :=
  germ.playerNeutralCirculation_or_isUniformEquilibriumPayoff
    (seed.H - K) s₀ (seed.onProfileBias_H_sub K hPoisson)

omit [DecidableEq G.State] in
/-- Fixed-action form of the finite-bias/Poisson branch reduction. -/
theorem FiniteBiasSeed.exists_positiveNeutralAction_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (K : G.State → Payoff ι)
    (s₀ : G.State)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint) :
    (∃ who, ∃ response : germ.ContinuationNeutralAction who,
      0 <
        germ.neutralActionCharge
          (seed.H - K) who response) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) := by
  classical
  exact
    germ.exists_positiveNeutralAction_or_isUniformEquilibriumPayoff
      (seed.H - K) s₀ (seed.onProfileBias_H_sub K hPoisson)

/-- Operational public-response form of the finite-bias/Poisson branch. -/
theorem FiniteBiasSeed.exists_publicConstraintResponse_or_isUniformEquilibriumPayoff
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (K : G.State → Payoff ι)
    (s₀ : G.State)
    (hPoisson :
      G.finkBellmanForcingVector
          germ.endpointValue seed.H germ.endpointFinkPoint =
        -G.finkContinuationResidualVector
          K germ.endpointFinkPoint) :
    (∃ who, ∃ response : germ.ContinuationNeutralAction who,
      Nonempty
        (G.FinkPublicConstraintResponse
          germ.endpointFinkPoint (seed.H - K)
          response.source who response.1.2)) ∨
      G.IsUniformEquilibriumPayoff
        s₀ (germ.endpointValue s₀) :=
  germ.exists_publicConstraintResponse_or_isUniformEquilibriumPayoff
    (seed.H - K) s₀ (seed.onProfileBias_H_sub K hPoisson)

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
