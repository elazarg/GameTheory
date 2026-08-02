/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ResponseArchitecturePurePrefixLaw

/-!
# Split-domain prescribed-bias converse

Shifted prescribed delivery does more than force target harmonicity.  On the
delivery union, harmonicity makes the Cesaro average of the target constant,
while delivery identifies the Cesaro average of the prescribed reward with
that same target.  Their difference is the prescribed Poisson charge, so its
mean-ergodic component vanishes and a prescribed bias exists.

This module formalizes that argument for the inertly restricted kernel used by
`SplitDomainGainBiasVerifier`, first from configuration-kernel delivery and
then from ordinary history-semantic finite-average delivery.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture
namespace SplitResponseDomain

variable {initial : G.State} {A : G.FiniteResponseArchitecture initial}
  [Fintype ι] [DecidableEq ι]

/-- Prescribed iteration from the delivery domain remains in that domain. -/
theorem delivery_iter_prescribed {z : A.Config} (D : A.SplitResponseDomain)
    (hz : D.delivery z) : ∀ (t : ℕ) (y : A.Config),
      y ∈ (Math.PMFIter.iter A.prescribedConfigDist t z).support →
        D.delivery y := by
  intro t
  induction t with
  | zero =>
      intro y hy
      have hyz : y = z := by simpa using hy
      simpa [hyz] using hz
  | succ t ih =>
      intro y hy
      rw [Math.PMFIter.iter_succ', PMF.mem_support_bind_iff] at hy
      obtain ⟨x, hx, hy⟩ := hy
      exact D.delivery_closed x (ih x hx) y hy

/-- The inert restriction agrees with the prescribed kernel at every finite
time when started inside the delivery domain. -/
theorem iter_restrictedPrescribedKernel_eq {z : A.Config}
    (D : A.SplitResponseDomain) (hz : D.delivery z) : ∀ t : ℕ,
      Math.PMFIter.iter (D.restrictedPrescribedKernel A) t z =
        Math.PMFIter.iter A.prescribedConfigDist t z := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Math.PMFIter.iter_succ', Math.PMFIter.iter_succ', ih]
      apply bind_congr_on_support
      intro y hy
      simp [restrictedPrescribedKernel,
        D.delivery_iter_prescribed hz t y hy]

/-- Local target harmonicity keeps the target expectation constant along all
prescribed iterates started in the delivery domain. -/
theorem expect_iter_prescribed_target_eq
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hT0 : ∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who)
    (who : ι) {z : A.Config} (hz : D.delivery z) : ∀ t : ℕ,
      expect (Math.PMFIter.iter A.prescribedConfigDist t z)
        (fun y => u y who) = u z who := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Math.PMFIter.iter_succ', expect_bind]
      rw [expect_congr_on_support _ _ _ (fun y hy =>
        hT0 who y (D.delivery_iter_prescribed hz t y hy))]
      exact ih

/-- At every delivery start, each restricted charge iterate is target minus
the corresponding prescribed expected reward. -/
theorem expect_iter_restrictedPrescribedPoissonCharge_eq
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hT0 : ∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who)
    (who : ι) {z : A.Config} (hz : D.delivery z) (t : ℕ) :
    expect (Math.PMFIter.iter (D.restrictedPrescribedKernel A) t z)
        (D.prescribedPoissonCharge A u who) =
      u z who - expect (Math.PMFIter.iter A.prescribedConfigDist t z)
        (fun y => A.prescribedStagePayoff y who) := by
  classical
  rw [D.iter_restrictedPrescribedKernel_eq hz t]
  calc
    expect (Math.PMFIter.iter A.prescribedConfigDist t z)
        (D.prescribedPoissonCharge A u who) =
        expect (Math.PMFIter.iter A.prescribedConfigDist t z)
          (fun y => u y who - A.prescribedStagePayoff y who) :=
      expect_congr_on_support _ _ _ fun y hy => by
        simp [prescribedPoissonCharge,
          D.delivery_iter_prescribed hz t y hy]
    _ = expect (Math.PMFIter.iter A.prescribedConfigDist t z)
          (fun y => u y who) -
        expect (Math.PMFIter.iter A.prescribedConfigDist t z)
          (fun y => A.prescribedStagePayoff y who) := by
      rw [expect_sub]
    _ = u z who - expect (Math.PMFIter.iter A.prescribedConfigDist t z)
          (fun y => A.prescribedStagePayoff y who) := by
      rw [D.expect_iter_prescribed_target_eq hT0 who hz t]

/-- Configuration-kernel shifted delivery makes the complete vector Cesaro
average of the restricted prescribed Poisson charge converge to zero. -/
theorem tendsto_restrictedPrescribedPoissonCharge_zero
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who))) (who : ι) :
    Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator
          (D.restrictedPrescribedKernel A)) ^ t)
          (D.prescribedPoissonCharge A u who)) atTop (nhds 0) := by
  classical
  have hT0 := D.prescribedTargetHarmonic_of_tendsto_configCesaro hdelivery
  apply tendsto_pi_nhds.2
  intro z
  simp only [Pi.zero_apply, Pi.smul_apply, Finset.sum_apply,
    Math.MeanErgodic.markovOperator_pow_apply]
  by_cases hz : D.delivery z
  · have hlimit : Tendsto (fun T : ℕ =>
        u z who - A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ => u z who) atTop
          (nhds (u z who)) := tendsto_const_nhds
      simpa using hconst.sub (hdelivery who z hz)
    apply hlimit.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
    rw [Finset.sum_congr rfl fun t _ =>
      D.expect_iter_restrictedPrescribedPoissonCharge_eq hT0 who hz t]
    unfold prescribedConfigCesaroPayoff
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hTne : (T : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hT)
    simp only [smul_eq_mul, nsmul_eq_mul]
    field_simp
  · have hterm : ∀ t : ℕ,
        expect (Math.PMFIter.iter (D.restrictedPrescribedKernel A) t z)
          (D.prescribedPoissonCharge A u who) = 0 := by
      intro t
      rw [Math.PMFIter.iter_of_terminal (by
        simp [restrictedPrescribedKernel, hz]), expect_pure]
      simp [prescribedPoissonCharge, hz]
    simpa only [hterm, Finset.sum_const_zero, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Configuration-kernel shifted delivery therefore synthesizes a prescribed
Poisson bias on the full delivery union. -/
theorem exists_prescribedBias_of_tendsto_configCesaro
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who))) (who : ι) :
    ∃ bias : A.Config → ℝ, ∀ z : A.Config, D.delivery z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias :=
  D.exists_prescribedBias_of_tendsto_cesaro_zero A u who
    (D.tendsto_restrictedPrescribedPoissonCharge_zero hdelivery who)

variable [Finite G.State] [∀ i, Finite (G.Act i)]

/-- Ordinary history-semantic shifted delivery synthesizes the same
prescribed Poisson bias. -/
theorem exists_prescribedBias_of_tendsto_finiteAverage
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ =>
        G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who)
        atTop (nhds (u z who))) (who : ι) :
    ∃ bias : A.Config → ℝ, ∀ z : A.Config, D.delivery z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias := by
  apply D.exists_prescribedBias_of_tendsto_configCesaro
  intro player z hz
  exact A.tendsto_prescribedConfigCesaroPayoff_of_finiteAverage z player
    (u z player) (hdelivery player z hz)

/-- History-semantic shifted delivery and unilateral caps, together with the
owner-local neutral-occupation condition, synthesize both Q96 bias families.
Thus after the strategic hypotheses have supplied (T0) and (Ti), (N) is the
only additional input needed by the existing controlled-Farkas theorem for
the unilateral bias. -/
theorem exists_gainBiases_of_historyDelivery_cap_and_neutralOccupation
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ =>
        G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who)
        atTop (nhds (u z who)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T)
    (hN : A.IsNeutralOccupationNonpositiveOn D.ownerRegion u) :
    ∃ prescribedBias unilateralBias : ι → A.Config → ℝ,
      (∀ (who : ι) (z : A.Config), D.delivery z →
        u z who + prescribedBias who z = A.prescribedStagePayoff z who +
          expect (A.prescribedConfigDist z) (prescribedBias who)) ∧
      (∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ act : G.Act who,
          A.stagePayoffAt who z (PMF.pure act) +
              expect (A.nextConfigDist who z (PMF.pure act))
                (unilateralBias who) ≤
            u z who + unilateralBias who z) := by
  have htarget :=
    D.targetConditions_of_tendsto_finiteAverage_and_unilateralCap
      hdelivery error herror hcap
  have hconfig : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who)) := by
    intro who z hz
    exact A.tendsto_prescribedConfigCesaroPayoff_of_finiteAverage z who
      (u z who) (hdelivery who z hz)
  exact D.exists_gainBiases_of_cesaro_targetOccupation A htarget.2 hN
    (fun who => D.tendsto_restrictedPrescribedPoissonCharge_zero hconfig who)

end SplitResponseDomain
end FiniteResponseArchitecture
end StochasticGame
end GameTheory
