/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SplitDomainGainBiasVerifier

/-!
# Split-domain asymptotic converse

This module isolates the two elementary converse steps behind the gain--bias
criterion.  They are stated directly for the finite configuration kernel:

* shifted prescribed Cesaro delivery forces target harmonicity (A1/T0);
* an asymptotic cap on a pure one-step deviation followed by prescribed play
  forces owner-arena target superharmonicity (A3/Ti).

The statements deliberately do not identify configuration-kernel rollouts
with the history semantics of a response architecture.  That finite-horizon
law is a separate bridge, and is the only extra ingredient needed to feed
ordinary history-level delivery and unilateral-cap hypotheses into these
results.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

section ConfigurationCesaro

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)
  [Fintype ι] [DecidableEq ι]

/-- The average expected prescribed stage payoff for player `who`, started at
configuration `z`, computed directly from the iterated configuration kernel.
At horizon zero this uses Lean's standard convention `0⁻¹ = 0`. -/
noncomputable def prescribedConfigCesaroPayoff
    (who : ι) (z : A.Config) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
    expect (Math.PMFIter.iter A.prescribedConfigDist t z)
      (fun y => A.prescribedStagePayoff y who)

/-- Payoff of the configuration-level experiment that first uses the pure
row `act` for player `who` at `z`, and then follows prescribed play for `T`
further stages. -/
noncomputable def purePrefixConfigCesaroPayoff
    (who : ι) (z : A.Config) (act : G.Act who)
    (T : ℕ) : ℝ :=
  (A.stagePayoffAt who z (PMF.pure act) +
      (T : ℝ) * expect (A.nextConfigDist who z (PMF.pure act))
        (fun y => A.prescribedConfigCesaroPayoff who y T)) /
    ((T : ℝ) + 1)

namespace SplitResponseDomain

variable {A : G.FiniteResponseArchitecture initial}

/-- Finite-state mean ergodicity turns prescribed Cesaro delivery at every
shifted node of the delivery domain into harmonicity of the delivered target
on that domain. -/
theorem prescribedTargetHarmonic_of_tendsto_configCesaro
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who))) :
    ∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who := by
  classical
  intro who
  obtain ⟨o, bias, ho, -, hmean⟩ :=
    Math.MeanErgodic.exists_harmonic_add_poisson A.prescribedConfigDist
      (fun y => A.prescribedStagePayoff y who)
  have hcoord : ∀ z : A.Config,
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (o z)) := by
    intro z
    have hz := ((continuous_apply z).tendsto o).comp hmean
    change Tendsto (fun T : ℕ =>
      ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator A.prescribedConfigDist) ^ t)
          (fun y => A.prescribedStagePayoff y who)) z)
      atTop (nhds (o z)) at hz
    simpa [prescribedConfigCesaroPayoff, Function.comp_apply,
      Finset.sum_apply,
      Math.MeanErgodic.markovOperator_pow_apply, Pi.smul_apply] using hz
  have hu_eq_o : ∀ z : A.Config, D.delivery z → u z who = o z := by
    intro z hz
    exact tendsto_nhds_unique (hdelivery who z hz) (hcoord z)
  intro z hz
  calc
    expect (A.prescribedConfigDist z) (fun y => u y who) =
        expect (A.prescribedConfigDist z) o :=
      Math.ProbabilityMassFunction.expect_congr_on_support _ _ _
        (fun y hy => hu_eq_o y (D.delivery_closed z hz y hy))
    _ = o z := ho z
    _ = u z who := (hu_eq_o z hz).symm

/-- Expectation under a fixed finite PMF preserves pointwise convergence on
its support.  The support-only formulation is useful for closed response
domains, where no convergence claim is available outside the relevant arena.
-/
private theorem tendsto_expect_of_tendsto_on_support
    {S : Type*} [Finite S] (μ : PMF S) (f : ℕ → S → ℝ) (g : S → ℝ)
    (h : ∀ s ∈ μ.support, Tendsto (fun T : ℕ => f T s)
      atTop (nhds (g s))) :
    Tendsto (fun T : ℕ => expect μ (f T)) atTop (nhds (expect μ g)) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  simp_rw [expect_eq_sum]
  apply tendsto_finsetSum (s := Finset.univ)
  intro s _
  by_cases hs : s ∈ μ.support
  · exact tendsto_const_nhds.mul (h s hs)
  · have hμ : μ s = 0 := by
      by_contra hne
      exact hs ((PMF.mem_support_iff μ s).2 hne)
    simp [hμ]

/-- A pure one-stage deviation followed by a prescribed tail converges to
the expected target after the deviating transition.  The bounded first-stage
reward disappears after normalization. -/
theorem tendsto_purePrefixConfigCesaroPayoff
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who)))
    (who : ι) (z : A.Config) (hz : D.unilateral who z)
    (act : G.Act who) :
    Tendsto (fun T : ℕ =>
      A.purePrefixConfigCesaroPayoff who z act T) atTop
      (nhds (expect (A.nextConfigDist who z (PMF.pure act))
        (fun y => u y who))) := by
  classical
  let μ := A.nextConfigDist who z (PMF.pure act)
  have htail : Tendsto (fun T : ℕ => expect μ
      (fun y => A.prescribedConfigCesaroPayoff who y T)) atTop
      (nhds (expect μ (fun y => u y who))) := by
    apply tendsto_expect_of_tendsto_on_support μ
    intro y hy
    exact hdelivery who y
      (D.unilateral_delivery who y
        (D.unilateral_closed who z hz act y hy))
  have hinv : Tendsto (fun T : ℕ => (1 : ℝ) / ((T : ℝ) + 1)) atTop
      (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hratio : Tendsto (fun T : ℕ => (T : ℝ) / ((T : ℝ) + 1)) atTop
      (nhds 1) := by
    have heq : (fun T : ℕ => (T : ℝ) / ((T : ℝ) + 1)) =
        fun T : ℕ => 1 - (1 : ℝ) / ((T : ℝ) + 1) := by
      funext T
      have hden : (T : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [heq]
    simpa using tendsto_const_nhds.sub hinv
  have hfirst : Tendsto (fun T : ℕ =>
      A.stagePayoffAt who z (PMF.pure act) *
        ((1 : ℝ) / ((T : ℝ) + 1))) atTop (nhds 0) := by
    simpa using hinv.const_mul (A.stagePayoffAt who z (PMF.pure act))
  have hsum := hfirst.add (hratio.mul htail)
  have heq : (fun T : ℕ =>
      A.purePrefixConfigCesaroPayoff who z act T) = fun T : ℕ =>
        A.stagePayoffAt who z (PMF.pure act) *
            ((1 : ℝ) / ((T : ℝ) + 1)) +
          ((T : ℝ) / ((T : ℝ) + 1)) *
            expect μ (fun y => A.prescribedConfigCesaroPayoff who y T) := by
    funext T
    have hden : (T : ℝ) + 1 ≠ 0 := by positivity
    simp only [purePrefixConfigCesaroPayoff, μ]
    field_simp
  rw [heq]
  simpa using hsum

/-- If every pure one-step rollout is eventually capped by the target plus a
vanishing error, shifted prescribed delivery forces target superharmonicity
on each owner's unilateral arena. -/
theorem unilateralTargetSuperharmonic_of_eventually_purePrefixCap
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who, ∀ᶠ T : ℕ in atTop,
        A.purePrefixConfigCesaroPayoff who z act T ≤ u z who + error T) :
    ∀ (who : ι) (z : A.Config), D.unilateral who z →
    ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who := by
  intro who z hz act
  have hright : Tendsto (fun T : ℕ => u z who + error T) atTop
      (nhds (u z who + 0)) := tendsto_const_nhds.add herror
  have hle := le_of_tendsto_of_tendsto
    (D.tendsto_purePrefixConfigCesaroPayoff hdelivery who z hz act)
    hright (hcap who z hz act)
  simpa using hle

/-- Combined configuration-kernel converse for the target clauses (A1) and
(A3) on the gain-bias criterion's exact split domains. -/
theorem targetConditions_of_configCesaroDelivery_and_purePrefixCap
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ => A.prescribedConfigCesaroPayoff who z T)
        atTop (nhds (u z who)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who, ∀ᶠ T : ℕ in atTop,
        A.purePrefixConfigCesaroPayoff who z act T ≤ u z who + error T) :
    (∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who) ∧
    (∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who) :=
  ⟨D.prescribedTargetHarmonic_of_tendsto_configCesaro hdelivery,
    D.unilateralTargetSuperharmonic_of_eventually_purePrefixCap
      hdelivery error herror hcap⟩

end SplitResponseDomain
end ConfigurationCesaro

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
