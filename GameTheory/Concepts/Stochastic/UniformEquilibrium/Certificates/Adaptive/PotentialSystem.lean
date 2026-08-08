/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.PhaseCertificate

/-!
# Explicit adaptive potential systems

`IsAdaptivePotentialCertificateAt` is intentionally a proposition expressed
as one long existential.  Composition arguments need to name and transport
its witness.  This file gives that witness a structure without strengthening
or weakening any condition.

The equivalence theorem below is the acceptance test: constructing an
`AdaptivePotentialSystemAt` is exactly constructing the existing verifier
input, not a new intermediate promise.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- Named data underlying one expectation-level adaptive potential
certificate at a fixed profile, entry state, target, and error. -/
structure AdaptivePotentialSystemAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (profile : G.BehaviorProfile)
    (s₀ : G.State) (v : Payoff ι) (error : ℝ) where
  horizon : ℕ
  lowerPotential : ι → G.HistoryPotential
  upperPotential : ι → G.HistoryPotential
  deviationPotential : ι → G.HistoryPotential
  lowerCharge : ι → ℕ → ℝ
  upperCharge : ι → ℕ → ℝ
  deviationCharge : ∀ i, G.BehaviorStrategy i → ℕ → ℝ
  horizon_ge_two : 2 ≤ horizon
  lower_initial : ∀ i,
    |lowerPotential i 0 (G.emptyHist s₀) - v i| ≤ error
  upper_initial : ∀ i,
    |upperPotential i 0 (G.emptyHist s₀) - v i| ≤ error
  deviation_initial : ∀ i,
    |deviationPotential i 0 (G.emptyHist s₀) - v i| ≤ error
  lower_submartingale : ∀ i time,
    G.expectedHistoryValue profile s₀ (lowerPotential i) time ≤
      G.expectedHistoryValue profile s₀ (lowerPotential i) (time + 1)
  lower_stage : ∀ i time,
    G.expectedHistoryValue profile s₀ (lowerPotential i) time ≤
      G.expectedStagePayoff profile s₀ time i +
        lowerCharge i time
  upper_supermartingale : ∀ i time,
    G.expectedHistoryValue profile s₀ (upperPotential i) (time + 1) ≤
      G.expectedHistoryValue profile s₀ (upperPotential i) time
  upper_stage : ∀ i time,
    G.expectedStagePayoff profile s₀ time i ≤
      G.expectedHistoryValue profile s₀ (upperPotential i) time +
        upperCharge i time
  deviation_supermartingale :
    ∀ i (deviation : G.BehaviorStrategy i) time,
      G.expectedHistoryValue
          (Function.update profile i deviation) s₀
          (deviationPotential i) (time + 1) ≤
        G.expectedHistoryValue
          (Function.update profile i deviation) s₀
          (deviationPotential i) time
  deviation_stage :
    ∀ i (deviation : G.BehaviorStrategy i) time,
      G.expectedStagePayoff
          (Function.update profile i deviation) s₀ time i ≤
        G.expectedHistoryValue
            (Function.update profile i deviation) s₀
            (deviationPotential i) time +
          deviationCharge i deviation time
  lower_charge_cesaro : ∀ i total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ time ∈ Finset.range total, lowerCharge i time ≤
      error
  upper_charge_cesaro : ∀ i total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ time ∈ Finset.range total, upperCharge i time ≤
      error
  deviation_charge_cesaro :
    ∀ i (deviation : G.BehaviorStrategy i) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ *
            ∑ time ∈ Finset.range total,
              deviationCharge i deviation time ≤
          error

namespace AdaptivePotentialSystemAt

variable {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)]
  {profile : G.BehaviorProfile}
  {s₀ : G.State} {v : Payoff ι} {error : ℝ}

/-- Forget the named packaging and supply the existing verifier input. -/
theorem toIsAdaptivePotentialCertificateAt
    (system : G.AdaptivePotentialSystemAt profile s₀ v error) :
    G.IsAdaptivePotentialCertificateAt s₀ v error := by
  exact ⟨profile, system.horizon,
    system.lowerPotential, system.upperPotential,
    system.deviationPotential, system.lowerCharge,
    system.upperCharge, system.deviationCharge,
    system.horizon_ge_two, system.lower_initial,
    system.upper_initial, system.deviation_initial,
    system.lower_submartingale, system.lower_stage,
    system.upper_supermartingale, system.upper_stage,
    system.deviation_supermartingale, system.deviation_stage,
    system.lower_charge_cesaro, system.upper_charge_cesaro,
    system.deviation_charge_cesaro⟩

end AdaptivePotentialSystemAt

/-- The named witness is definitionally equivalent to the original nested
existential certificate interface. -/
theorem isAdaptivePotentialCertificateAt_iff_exists_system
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (error : ℝ) :
    G.IsAdaptivePotentialCertificateAt s₀ v error ↔
      ∃ profile : G.BehaviorProfile,
        Nonempty (G.AdaptivePotentialSystemAt profile s₀ v error) := by
  constructor
  · rintro ⟨profile, horizon,
      lowerPotential, upperPotential, deviationPotential,
      lowerCharge, upperCharge, deviationCharge,
      horizon_ge_two, lower_initial, upper_initial, deviation_initial,
      lower_submartingale, lower_stage,
      upper_supermartingale, upper_stage,
      deviation_supermartingale, deviation_stage,
      lower_charge_cesaro, upper_charge_cesaro,
      deviation_charge_cesaro⟩
    exact ⟨profile, ⟨{
      horizon := horizon
      lowerPotential := lowerPotential
      upperPotential := upperPotential
      deviationPotential := deviationPotential
      lowerCharge := lowerCharge
      upperCharge := upperCharge
      deviationCharge := deviationCharge
      horizon_ge_two := horizon_ge_two
      lower_initial := lower_initial
      upper_initial := upper_initial
      deviation_initial := deviation_initial
      lower_submartingale := lower_submartingale
      lower_stage := lower_stage
      upper_supermartingale := upper_supermartingale
      upper_stage := upper_stage
      deviation_supermartingale := deviation_supermartingale
      deviation_stage := deviation_stage
      lower_charge_cesaro := lower_charge_cesaro
      upper_charge_cesaro := upper_charge_cesaro
      deviation_charge_cesaro := deviation_charge_cesaro
    }⟩⟩
  · rintro ⟨profile, ⟨system⟩⟩
    exact system.toIsAdaptivePotentialCertificateAt

/-- Expose the precise adaptive system constructed by a public-phase
punishment certificate, retaining its actual behavior profile. -/
def PublicPhasePunishmentSystemAt.toAdaptivePotentialSystemAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {profile : PublicPhaseProfile G}
    {s₀ : G.State} {v : Payoff ι} {error : ℝ}
    (certificate :
      PublicPhasePunishmentSystemAt G profile s₀ v error) :
    G.AdaptivePotentialSystemAt
      profile.behaviorProfile s₀ v error where
  horizon := certificate.horizon
  lowerPotential := fun i =>
    profile.historyPotential (certificate.lowerPotential i)
  upperPotential := fun i =>
    profile.historyPotential (certificate.upperPotential i)
  deviationPotential := fun i =>
    profile.historyPotential (certificate.deviationPotential i)
  lowerCharge := fun i time =>
    G.expectedHistoryValue profile.behaviorProfile s₀
      (certificate.lowerCharge i) time
  upperCharge := fun i time =>
    G.expectedHistoryValue profile.behaviorProfile s₀
      (certificate.upperCharge i) time
  deviationCharge := fun i deviation time =>
    G.expectedHistoryValue
      (Function.update profile.behaviorProfile i deviation) s₀
      (certificate.deviationCharge i deviation) time
  horizon_ge_two := certificate.horizon_ge_two
  lower_initial := certificate.lower_initial
  upper_initial := certificate.upper_initial
  deviation_initial := certificate.deviation_initial
  lower_submartingale := by
    intro i time
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _
      (certificate.lower_subharmonic i time)
  lower_stage := by
    intro i time
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [expect_add] using
      expect_mono (G.histDist profile.behaviorProfile s₀ time) _ _
        (certificate.lower_stage i time)
  upper_supermartingale := by
    intro i time
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _
      (certificate.upper_superharmonic i time)
  upper_stage := by
    intro i time
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [expect_add] using
      expect_mono (G.histDist profile.behaviorProfile s₀ time) _ _
        (certificate.upper_stage i time)
  deviation_supermartingale := by
    intro i deviation time
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _
      (certificate.deviation_superharmonic i deviation time)
  deviation_stage := by
    intro i deviation time
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [expect_add] using
      expect_mono
        (G.histDist
          (Function.update profile.behaviorProfile i deviation)
          s₀ time) _ _
        (certificate.deviation_stage i deviation time)
  lower_charge_cesaro := certificate.lower_charge_cesaro
  upper_charge_cesaro := certificate.upper_charge_cesaro
  deviation_charge_cesaro := certificate.deviation_charge_cesaro

end StochasticGame
end GameTheory
