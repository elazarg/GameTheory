/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Singleton
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Differential privacy and implementation price

An ε-differentially private outcome kernel limits unilateral payoff changes
when utilities are nonnegative and uniformly bounded. Combined with the
singleton-price theorem, this gives a reusable implementation-price upper bound.

The same finite PMF duality also gives a converse-style characterization: if
utilities may range over every `[0,U]`-valued function, the worst-case singleton
price is exactly `U` times the total unilateral outcome variation at the target.
For nonnegative utilities without an upper bound, the multiplicative
expected-utility inequality is equivalent to the pointwise differential-privacy
condition.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- Unilateral ε-differential privacy for a kernel game: changing one player's
strategy can multiply every outcome probability by at most `exp ε`. -/
def IsEpsilonDifferentiallyPrivate (G : KernelGame ι) (ε : ℝ) : Prop :=
  ∀ (i : ι) (σ : Profile G) (s : G.Strategy i) (ω : G.Outcome),
    ((G.outcomeKernel (Function.update σ i s)) ω).toReal ≤
      Real.exp ε * ((G.outcomeKernel σ) ω).toReal

section StrategicIndistinguishability

variable {G : KernelGame ι}

/-- Positive total variation between the outcome distribution at `σ` and the
distribution after player `i` deviates to `s`. -/
noncomputable def unilateralOutcomeVariationAt (G : KernelGame ι)
    [Fintype G.Outcome] (σ : Profile G) (i : ι) (s : G.Strategy i) : ℝ :=
  Math.Probability.pmfPositiveVariation
    (G.outcomeKernel (Function.update σ i s)) (G.outcomeKernel σ)

/-- The largest unilateral outcome-distribution movement available to player
`i` at the target profile. -/
noncomputable def unilateralOutcomeVariation (G : KernelGame ι)
    [Fintype G.Outcome] (z : Profile G) (i : ι)
    [Fintype (G.Strategy i)] [Nonempty (G.Strategy i)] : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
    (fun s : G.Strategy i => G.unilateralOutcomeVariationAt z i s)

theorem unilateralOutcomeVariationAt_nonneg [Fintype G.Outcome]
    (z : Profile G) (i : ι) (s : G.Strategy i) :
    0 ≤ G.unilateralOutcomeVariationAt z i s :=
  Math.Probability.pmfPositiveVariation_nonneg _ _

theorem unilateralOutcomeVariation_nonneg [Fintype G.Outcome]
    (z : Profile G) (i : ι)
    [Fintype (G.Strategy i)] [Nonempty (G.Strategy i)] :
    0 ≤ G.unilateralOutcomeVariation z i := by
  exact (G.unilateralOutcomeVariationAt_nonneg z i (z i)).trans
    (Finset.le_sup' (s := Finset.univ)
      (f := fun s : G.Strategy i => G.unilateralOutcomeVariationAt z i s)
      (Finset.mem_univ (z i)))

open Classical in
/-- A deviation attaining the finite outcome-variation maximum. -/
noncomputable def maxOutcomeVariationDeviation (G : KernelGame ι)
    [Fintype G.Outcome] (z : Profile G) (i : ι)
    [Fintype (G.Strategy i)] [Nonempty (G.Strategy i)] : G.Strategy i :=
  (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G.Strategy i))
    (fun s : G.Strategy i => G.unilateralOutcomeVariationAt z i s)).choose

theorem unilateralOutcomeVariationAt_maxOutcomeVariationDeviation
    [Fintype G.Outcome] (z : Profile G) (i : ι)
    [Fintype (G.Strategy i)] [Nonempty (G.Strategy i)] :
    G.unilateralOutcomeVariationAt z i (G.maxOutcomeVariationDeviation z i) =
      G.unilateralOutcomeVariation z i := by
  classical
  exact (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G.Strategy i))
    (fun s : G.Strategy i => G.unilateralOutcomeVariationAt z i s)).choose_spec.2.symm

/-- The variation price of a target is the sum over players of their largest
unilateral total-variation movement in the outcome kernel. -/
noncomputable def singletonOutcomeVariationPrice (G : KernelGame ι)
    [Fintype ι] [Fintype G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) : ℝ :=
  ∑ i, G.unilateralOutcomeVariation z i

theorem implementationGap_le_mul_unilateralOutcomeVariation
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)] {U : ℝ} (hU : 0 ≤ U)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) (i : ι) :
    G.implementationGap z i ≤ U * G.unilateralOutcomeVariation z i := by
  classical
  unfold implementationGap implementationGapAt
  apply Finset.sup'_le
  intro s _
  have htv :
      G.eu (Function.update z i s) i - G.eu (Function.update z i (z i)) i ≤
        U * G.unilateralOutcomeVariationAt z i s := by
    unfold KernelGame.eu unilateralOutcomeVariationAt
    simpa [Function.update_eq_self] using
      Math.Probability.expect_sub_le_mul_pmfPositiveVariation
        (G.outcomeKernel (Function.update z i s)) (G.outcomeKernel z)
        (fun ω => G.utility ω i) (fun ω => hutil_nonneg ω i)
        (fun ω => hutil_le ω i)
  exact htv.trans
    (mul_le_mul_of_nonneg_left
      (Finset.le_sup' (s := Finset.univ)
        (f := fun s : G.Strategy i => G.unilateralOutcomeVariationAt z i s)
        (Finset.mem_univ s)) hU)

/-- For `[0,U]` utilities, the singleton implementation price is bounded by
`U` times the target's total unilateral outcome variation. -/
theorem implPrice_singleton_le_mul_singletonOutcomeVariationPrice
    [Fintype ι] [Nonempty ι] [Fintype G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {U : ℝ} (hU : 0 ≤ U)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      U * G.singletonOutcomeVariationPrice z := by
  rw [implPrice_singleton (G := G) z, singletonOutcomeVariationPrice,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    G.implementationGap_le_mul_unilateralOutcomeVariation hU hutil_nonneg hutil_le z i

open Classical in
/-- A utility profile that realizes the total-variation bound player by player. -/
noncomputable def outcomeVariationWitnessUtility (G : KernelGame ι)
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) (U : ℝ) : G.Outcome → Payoff ι :=
  fun ω i =>
    Math.Probability.pmfPositiveVariationWitness
      (G.outcomeKernel (Function.update z i (G.maxOutcomeVariationDeviation z i)))
      (G.outcomeKernel z) U ω

theorem outcomeVariationWitnessUtility_nonneg
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) {U : ℝ} (hU : 0 ≤ U) :
    ∀ ω i, 0 ≤ G.outcomeVariationWitnessUtility z U ω i := by
  intro ω i
  exact Math.Probability.pmfPositiveVariationWitness_nonneg _ _ hU ω

theorem outcomeVariationWitnessUtility_le
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) {U : ℝ} (hU : 0 ≤ U) :
    ∀ ω i, G.outcomeVariationWitnessUtility z U ω i ≤ U := by
  intro ω i
  exact Math.Probability.pmfPositiveVariationWitness_le _ _ hU ω

/-- The same game form as `G`, equipped with the utility profile that realizes
the total-variation implementation-price bound. -/
noncomputable def outcomeVariationWitnessGame (G : KernelGame ι)
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) (U : ℝ) : KernelGame ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  utility := G.outcomeVariationWitnessUtility z U
  outcomeKernel := G.outcomeKernel

/-- Inherited finite strategy instances for the variation-witness game. Named
so downstream theorem statements can use the same definitional instance data. -/
@[reducible]
def outcomeVariationWitnessGameStrategyFintype (G : KernelGame ι)
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) (U : ℝ) :
    ∀ i, Fintype ((G.outcomeVariationWitnessGame z U).Strategy i) :=
  fun i => inferInstanceAs (Fintype (G.Strategy i))

/-- Inherited nonempty strategy instances for the variation-witness game. -/
@[reducible]
def outcomeVariationWitnessGameStrategyNonempty (G : KernelGame ι)
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) (U : ℝ) :
    ∀ i, Nonempty ((G.outcomeVariationWitnessGame z U).Strategy i) :=
  fun i => inferInstanceAs (Nonempty (G.Strategy i))

theorem implementationGap_outcomeVariationWitnessUtility
    [Fintype G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)] {U : ℝ} (hU : 0 ≤ U)
    (z : Profile G) (i : ι) :
    @implementationGap ι _ (G.outcomeVariationWitnessGame z U)
      z (G.outcomeVariationWitnessGameStrategyFintype z U)
      (G.outcomeVariationWitnessGameStrategyNonempty z U) i =
      U * G.unilateralOutcomeVariation z i := by
  classical
  letI :
      Fintype ((G.outcomeVariationWitnessGame z U).Outcome) :=
    inferInstanceAs (Fintype G.Outcome)
  letI :
      ∀ j, Fintype ((G.outcomeVariationWitnessGame z U).Strategy j) :=
    G.outcomeVariationWitnessGameStrategyFintype z U
  letI :
      ∀ j, Nonempty ((G.outcomeVariationWitnessGame z U).Strategy j) :=
    G.outcomeVariationWitnessGameStrategyNonempty z U
  have hupper :
      (G.outcomeVariationWitnessGame z U).implementationGap z i ≤
        U * G.unilateralOutcomeVariation z i := by
    have h :
        (G.outcomeVariationWitnessGame z U).implementationGap z i ≤
          U * (G.outcomeVariationWitnessGame z U).unilateralOutcomeVariation z i :=
      implementationGap_le_mul_unilateralOutcomeVariation
        (G := G.outcomeVariationWitnessGame z U) hU
        (G.outcomeVariationWitnessUtility_nonneg z hU)
        (G.outcomeVariationWitnessUtility_le z hU) z i
    change (G.outcomeVariationWitnessGame z U).implementationGap z i ≤
      U * (G.outcomeVariationWitnessGame z U).unilateralOutcomeVariation z i
    exact h
  have hmaxSub :
      (G.outcomeVariationWitnessGame z U).eu
          (Function.update z i (G.maxOutcomeVariationDeviation z i)) i -
        (G.outcomeVariationWitnessGame z U).eu z i ≤
          (G.outcomeVariationWitnessGame z U).implementationGap z i :=
    implementationGap_ge
      (G := G.outcomeVariationWitnessGame z U)
      z i (G.maxOutcomeVariationDeviation z i)
  have hrealize :
      (G.outcomeVariationWitnessGame z U).eu
            (Function.update z i (G.maxOutcomeVariationDeviation z i)) i -
          (G.outcomeVariationWitnessGame z U).eu z i =
        U * G.unilateralOutcomeVariation z i := by
    change
      Math.Probability.expect
          (G.outcomeKernel (Function.update z i (G.maxOutcomeVariationDeviation z i)))
          (Math.Probability.pmfPositiveVariationWitness
            (G.outcomeKernel (Function.update z i (G.maxOutcomeVariationDeviation z i)))
            (G.outcomeKernel z) U) -
        Math.Probability.expect (G.outcomeKernel z)
          (Math.Probability.pmfPositiveVariationWitness
            (G.outcomeKernel (Function.update z i (G.maxOutcomeVariationDeviation z i)))
            (G.outcomeKernel z) U) =
          U * G.unilateralOutcomeVariation z i
    rw [Math.Probability.expect_sub_pmfPositiveVariationWitness]
    exact congrArg (fun x => U * x)
      (unilateralOutcomeVariationAt_maxOutcomeVariationDeviation (G := G) z i)
  have hlower :
      U * G.unilateralOutcomeVariation z i ≤
        (G.outcomeVariationWitnessGame z U).implementationGap z i := by
    simpa [hrealize] using hmaxSub
  exact le_antisymm hupper hlower

/-- The total-variation bound is sharp: some `[0,U]`-valued utilities on the
same game form attain it as the singleton implementation price. -/
theorem implPrice_singleton_outcomeVariationWitnessUtility
    [Fintype ι] [Nonempty ι] [Fintype G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {U : ℝ} (hU : 0 ≤ U) (z : Profile G) :
    (G.outcomeVariationWitnessGame z U).implPrice
        ({(z : Profile (G.outcomeVariationWitnessGame z U))} :
          Set (Profile
            (G.outcomeVariationWitnessGame z U))) =
      U * G.singletonOutcomeVariationPrice z := by
  classical
  letI :
      Fintype ((G.outcomeVariationWitnessGame z U).Outcome) :=
    inferInstanceAs (Fintype G.Outcome)
  letI :
      ∀ j, Fintype ((G.outcomeVariationWitnessGame z U).Strategy j) :=
    fun j => inferInstanceAs (Fintype (G.Strategy j))
  letI :
      ∀ j, Nonempty ((G.outcomeVariationWitnessGame z U).Strategy j) :=
    fun j => inferInstanceAs (Nonempty (G.Strategy j))
  let zW : Profile (G.outcomeVariationWitnessGame z U) := z
  change (G.outcomeVariationWitnessGame z U).implPrice
      ({zW} : Set (Profile (G.outcomeVariationWitnessGame z U))) =
    U * G.singletonOutcomeVariationPrice z
  rw [(@implPrice_singleton ι _ (G := G.outcomeVariationWitnessGame z U)
      (G.outcomeVariationWitnessGameStrategyFintype z U)
      (G.outcomeVariationWitnessGameStrategyNonempty z U)
      (inferInstance : Fintype ι) (inferInstance : Nonempty ι)
      (inferInstance : Finite ((G.outcomeVariationWitnessGame z U).Outcome)) zW),
    singletonOutcomeVariationPrice, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    by
      simpa [zW] using implementationGap_outcomeVariationWitnessUtility (G := G) hU z i

theorem isEpsilonDifferentiallyPrivate_iff_expect_le_exp_mul_expect
    [Finite G.Outcome] {ε : ℝ} :
    G.IsEpsilonDifferentiallyPrivate ε ↔
      ∀ (i : ι) (σ : Profile G) (s : G.Strategy i) (u : G.Outcome → ℝ),
        (∀ ω, 0 ≤ u ω) →
          Math.Probability.expect (G.outcomeKernel (Function.update σ i s)) u ≤
            Real.exp ε * Math.Probability.expect (G.outcomeKernel σ) u := by
  constructor
  · intro hDP i σ s u hu
    exact (Math.Probability.expect_le_mul_expect_iff_pmf_le_mul
      (G.outcomeKernel (Function.update σ i s)) (G.outcomeKernel σ)).mpr
      (hDP i σ s) u hu
  · intro h i σ s ω
    exact (Math.Probability.expect_le_mul_expect_iff_pmf_le_mul
      (G.outcomeKernel (Function.update σ i s)) (G.outcomeKernel σ)).mp
      (fun u hu => h i σ s u hu) ω

theorem isEpsilonDifferentiallyPrivate_iff_expect_gain_le_exp_sub_one_mul_expect
    [Finite G.Outcome] {ε : ℝ} :
    G.IsEpsilonDifferentiallyPrivate ε ↔
      ∀ (i : ι) (σ : Profile G) (s : G.Strategy i) (u : G.Outcome → ℝ),
        (∀ ω, 0 ≤ u ω) →
          Math.Probability.expect (G.outcomeKernel (Function.update σ i s)) u -
              Math.Probability.expect (G.outcomeKernel σ) u ≤
            (Real.exp ε - 1) *
              Math.Probability.expect (G.outcomeKernel σ) u := by
  rw [isEpsilonDifferentiallyPrivate_iff_expect_le_exp_mul_expect]
  constructor
  · intro h i σ s u hu
    have hle := h i σ s u hu
    linarith
  · intro h i σ s u hu
    have hle := h i σ s u hu
    linarith

end StrategicIndistinguishability

omit [DecidableEq ι] in
/-- A pointwise upper bound on realized utilities bounds expected utility. -/
theorem eu_le_of_utility_le {G : KernelGame ι} [Finite G.Outcome]
    (who : ι) {U : ℝ}
    (hutil : ∀ ω : G.Outcome, G.utility ω who ≤ U) (σ : Profile G) :
    G.eu σ who ≤ U := by
  classical
  letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
  unfold KernelGame.eu
  rw [expect_eq_sum]
  calc
    (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω who)
        ≤ ∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * U := by
          exact Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hutil ω) ENNReal.toReal_nonneg
    _ = U * ∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
    _ = U := by
          rw [pmf_toReal_sum_one]
          ring

/-- Differential privacy converts expected utility after a unilateral deviation
into a multiplicative bound by `exp ε`. -/
theorem eu_update_le_exp_mul_eu_of_differentialPrivate {G : KernelGame ι}
    [Finite G.Outcome] {ε : ℝ}
    (hDP : G.IsEpsilonDifferentiallyPrivate ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (σ : Profile G) (i : ι) (s : G.Strategy i) :
    G.eu (Function.update σ i s) i ≤ Real.exp ε * G.eu σ i := by
  classical
  letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
  unfold KernelGame.eu
  rw [expect_eq_sum, expect_eq_sum]
  calc
    (∑ ω : G.Outcome,
        (G.outcomeKernel (Function.update σ i s) ω).toReal * G.utility ω i)
        ≤ ∑ ω : G.Outcome,
            (Real.exp ε * (G.outcomeKernel σ ω).toReal) * G.utility ω i := by
          exact Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_right (hDP i σ s ω) (hutil_nonneg ω i)
    _ = Real.exp ε *
          ∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring

/-- Under ε-differential privacy and utilities in `[0,U]`, one player's
unilateral deviation gain is at most `(exp ε - 1) * U`. -/
theorem eu_update_sub_le_dp_bound {G : KernelGame ι} [Finite G.Outcome]
    {ε U : ℝ}
    (hDP : G.IsEpsilonDifferentiallyPrivate ε) (hε : 0 ≤ ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (σ : Profile G) (i : ι) (s : G.Strategy i) :
    G.eu (Function.update σ i s) i - G.eu σ i ≤
      (Real.exp ε - 1) * U := by
  have hmult := eu_update_le_exp_mul_eu_of_differentialPrivate
    (G := G) hDP hutil_nonneg σ i s
  have hbase_le := eu_le_of_utility_le (G := G) i (fun ω => hutil_le ω i) σ
  have hcoef_nonneg : 0 ≤ Real.exp ε - 1 := sub_nonneg.mpr (Real.one_le_exp hε)
  calc
    G.eu (Function.update σ i s) i - G.eu σ i
        ≤ Real.exp ε * G.eu σ i - G.eu σ i := by
          exact sub_le_sub_right hmult _
    _ = (Real.exp ε - 1) * G.eu σ i := by ring
    _ ≤ (Real.exp ε - 1) * U :=
          mul_le_mul_of_nonneg_left hbase_le hcoef_nonneg

/-- Under ε-differential privacy and utilities in `[0,U]`, every singleton
implementation-gap coordinate is at most `(exp ε - 1) * U`. -/
theorem implementationGap_le_dp_bound {G : KernelGame ι}
    [Finite G.Outcome] [∀ i, Fintype (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)] {ε U : ℝ}
    (hDP : G.IsEpsilonDifferentiallyPrivate ε) (hε : 0 ≤ ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) (i : ι) :
    G.implementationGap z i ≤ (Real.exp ε - 1) * U := by
  classical
  unfold implementationGap implementationGapAt
  apply Finset.sup'_le
  intro s _
  simpa [Function.update_eq_self] using
    eu_update_sub_le_dp_bound (G := G) hDP hε hutil_nonneg hutil_le z i s

/-- Differential-privacy implementation-price bound, stated as a player-sum.
This is the most direct corollary of the singleton price formula. -/
theorem implPrice_singleton_le_sum_dp_bound {G : KernelGame ι}
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {ε U : ℝ}
    (hDP : G.IsEpsilonDifferentiallyPrivate ε) (hε : 0 ≤ ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      ∑ _i : ι, (Real.exp ε - 1) * U := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [implPrice_singleton (G := G) z]
  exact Finset.sum_le_sum fun i _ =>
    implementationGap_le_dp_bound (G := G) hDP hε hutil_nonneg hutil_le z i

/-- Differential-privacy implementation-price bound in the usual `n · bound`
form. -/
theorem implPrice_singleton_le_card_mul_dp_bound {G : KernelGame ι}
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {ε U : ℝ}
    (hDP : G.IsEpsilonDifferentiallyPrivate ε) (hε : 0 ≤ ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      (Fintype.card ι : ℝ) * ((Real.exp ε - 1) * U) := by
  calc
    G.implPrice ({z} : Set (Profile G))
        ≤ ∑ _i : ι, (Real.exp ε - 1) * U :=
          implPrice_singleton_le_sum_dp_bound (G := G) hDP hε hutil_nonneg hutil_le z
    _ = (Fintype.card ι : ℝ) * ((Real.exp ε - 1) * U) := by
          simp [Finset.sum_const, nsmul_eq_mul]

end KernelGame

end GameTheory
