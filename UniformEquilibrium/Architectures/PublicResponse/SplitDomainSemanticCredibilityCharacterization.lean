/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Architectures.PublicResponse.SplitDomainNeutralOccupationConverse

/-!
# Split-domain semantic credibility characterization

For one supplied finite public response architecture, semantic credibility
has two different all-start domains:

* prescribed delivery is required at every configuration in the split
  delivery union;
* player `who`'s unilateral cap is required at every configuration in that
  player's owner arena, against every behavioral deviation.

This file packages those quantifiers with one common `O(1/T)` constant and
proves that they are equivalent to a nonempty gain--bias packet.  The packet
contains the two target conditions and the two finite Poisson/bias families
on exactly the same domains.

The reverse implication is the explicit split-domain gain--bias verifier.
The forward implication uses the history-semantic target converse and the
neutral-occupation converse, so no recurrent-coverage hypothesis or
recurrent-class claim occurs in the statement or proof.  This is a
characterization of a **supplied finite architecture**; it does not construct
one or claim that finite public architectures exhaust uniform equilibria.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

namespace FiniteResponseArchitecture
namespace SplitResponseDomain

variable {initial : G.State} {A : G.FiniteResponseArchitecture initial}
  [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- The finite algebraic packet equivalent to split-domain semantic
credibility.

It is a `Type`, rather than a proposition-only wrapper, so a consumer can use
the two bias functions carried by a witness. -/
structure GainBiasPacket
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι) where
  /-- Prescribed Poisson bias, indexed by payoff owner. -/
  prescribedBias : ι → A.Config → ℝ
  /-- Unilateral super-solution bias, indexed by deviating owner. -/
  unilateralBias : ι → A.Config → ℝ
  /-- (T0): the target is harmonic under prescribed play on the delivery
  union. -/
  prescribedTargetHarmonic :
    ∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who
  /-- (Ti): each owner target is superharmonic under every pure unilateral
  row in that owner's arena. -/
  unilateralTargetSuperharmonic :
    ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who
  /-- (A2): exact prescribed Poisson equation on the delivery union. -/
  prescribedBias_eq :
    ∀ (who : ι) (z : A.Config), D.delivery z →
      u z who + prescribedBias who z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) (prescribedBias who)
  /-- (A4): unilateral Bellman super-solution on the selected owner's
  arena. -/
  unilateralBias_le :
    ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act))
              (unilateralBias who) ≤
          u z who + unilateralBias who z

/-- A witness of exact all-start semantic credibility on the split domains.

One nonnegative constant controls prescribed delivery for every owner and
delivery configuration, and unilateral exploitability for every owner,
owner-arena configuration, behavioral deviation and positive horizon. -/
structure SemanticCredibilityWitness
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι) where
  /-- Common finite-horizon remainder constant. -/
  remainderBound : ℝ
  /-- The common remainder constant is nonnegative. -/
  remainderBound_nonneg : 0 ≤ remainderBound
  /-- Prescribed play delivers the local target with common `O(1/T)` error
  at every configuration of the delivery union. -/
  prescribedDelivery :
    ∀ (who : ι) (z : A.Config), D.delivery z →
      ∀ {T : ℕ}, 0 < T →
        |G.finiteAveragePayoff (A.publicState z) T
            (A.rebase z).phaseProfile.behaviorProfile who - u z who| ≤
          remainderBound / T
  /-- Every behavioral deviation is capped with the same `O(1/T)` error at
  every configuration of the deviator's owner arena. -/
  unilateralCap :
    ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ (dev : G.BehaviorStrategy who) {T : ℕ}, 0 < T →
        G.finiteAveragePayoff (A.publicState z) T
            (Function.update (A.rebase z).phaseProfile.behaviorProfile
              who dev) who ≤
          u z who + remainderBound / T

/-- Exact all-start semantic credibility as a proposition.  The witness is
kept behind `Nonempty`, so proof irrelevance does not erase its quantitative
remainder constant. -/
def IsSemanticallyCredible
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι) : Prop :=
  Nonempty (D.SemanticCredibilityWitness u)

namespace SemanticCredibilityWitness

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- The common `O(1/T)` remainder vanishes. -/
theorem tendsto_remainder
    {D : A.SplitResponseDomain} {u : A.Config → Payoff ι}
    (h : D.SemanticCredibilityWitness u) :
    Tendsto (fun T : ℕ => h.remainderBound / T) atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat h.remainderBound

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- The quantitative delivery clause implies ordinary shifted semantic
delivery on the full delivery union. -/
theorem tendsto_prescribedDelivery
    {D : A.SplitResponseDomain} {u : A.Config → Payoff ι}
    (h : D.SemanticCredibilityWitness u)
    (who : ι) (z : A.Config) (hz : D.delivery z) :
    Tendsto (fun T : ℕ =>
      G.finiteAveragePayoff (A.publicState z) T
        (A.rebase z).phaseProfile.behaviorProfile who)
      atTop (nhds (u z who)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have habs : Tendsto (fun T : ℕ =>
      |G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who - u z who|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
      exact h.prescribedDelivery who z hz (by omega)
    · exact h.tendsto_remainder
  simpa only [Real.norm_eq_abs] using habs

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- The quantitative unilateral clause has the eventual form consumed by
the semantic converse. -/
theorem eventually_unilateralCap
    {D : A.SplitResponseDomain} {u : A.Config → Payoff ι}
    (h : D.SemanticCredibilityWitness u)
    (who : ι) (z : A.Config) (hz : D.unilateral who z)
    (dev : G.BehaviorStrategy who) :
    ∀ᶠ T : ℕ in atTop,
      G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile
            who dev) who ≤
        u z who + h.remainderBound / T := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
  exact h.unilateralCap who z hz dev (by omega)

end SemanticCredibilityWitness

/-- **Fixed-class characterization.** A supplied split-domain response
architecture is semantically credible exactly when its target admits the
finite gain--bias packet on the same delivery and owner domains.

No recurrent-coverage or recurrent-class condition is assumed. -/
theorem isSemanticallyCredible_iff_nonempty_gainBiasPacket
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι) :
    D.IsSemanticallyCredible u ↔ Nonempty (D.GainBiasPacket u) := by
  constructor
  · rintro ⟨hsemantic⟩
    have hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
        Tendsto (fun T : ℕ =>
          G.finiteAveragePayoff (A.publicState z) T
            (A.rebase z).phaseProfile.behaviorProfile who)
          atTop (nhds (u z who)) :=
      fun who z hz => hsemantic.tendsto_prescribedDelivery who z hz
    have hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
          G.finiteAveragePayoff (A.publicState z) T
            (Function.update (A.rebase z).phaseProfile.behaviorProfile
              who dev) who ≤
            u z who + hsemantic.remainderBound / T :=
      fun who z hz dev => hsemantic.eventually_unilateralCap who z hz dev
    have htarget :=
      D.targetConditions_of_tendsto_finiteAverage_and_unilateralCap
        hdelivery (fun T : ℕ => hsemantic.remainderBound / T)
        hsemantic.tendsto_remainder hcap
    obtain ⟨prescribedBias, unilateralBias,
        hprescribedBias, hunilateralBias⟩ :=
      D.exists_gainBiases_of_historyDelivery_and_unilateralCap
        hdelivery (fun T : ℕ => hsemantic.remainderBound / T)
        hsemantic.tendsto_remainder hcap
    exact ⟨{
      prescribedBias := prescribedBias
      unilateralBias := unilateralBias
      prescribedTargetHarmonic := htarget.1
      unilateralTargetSuperharmonic := htarget.2
      prescribedBias_eq := hprescribedBias
      unilateralBias_le := hunilateralBias
    }⟩
  · rintro ⟨packet⟩
    obtain ⟨M, hM, -, -, hdelivery, hcap⟩ :=
      A.exists_splitDomainGainBiasVerifier D
        packet.prescribedTargetHarmonic
        packet.unilateralTargetSuperharmonic
        packet.prescribedBias packet.unilateralBias
        packet.prescribedBias_eq packet.unilateralBias_le
    exact ⟨{
      remainderBound := M
      remainderBound_nonneg := hM
      prescribedDelivery := hdelivery
      unilateralCap := hcap
    }⟩

end SplitResponseDomain
end FiniteResponseArchitecture
end StochasticGame
end GameTheory
