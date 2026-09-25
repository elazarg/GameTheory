/-
# EXP-108: separation of asymptotic payoff aggregations

This is the smallest compiled order-of-limits seam for EXP-108.  A stage
sequence and its pointwise complement are sampled with equal probability.  The
same finite-support law is used for finite Cesaro averages, pathwise liminf,
and pathwise limsup; no stochastic runner or measure layer is introduced.

The remaining construction obligation is deliberately explicit in the
hypotheses of `fair_two_point_order_limits`: a concrete rapidly growing
alternating block sequence must provide the four endpoint facts.  The intended
endpoints are `B 0 = 2`, `B (k + 1) = B k ^ 2`, with alternating values on
`[B k, B (k + 1))`.  Proving the associated Nat.find block-index estimates is
the uncompiled part of this experiment; no existence claim is hidden here.
-/

import GameTheory.Math.Probability.ExpectationMixture
import GameTheory.Math.Probability.Mixture
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section

open scoped BigOperators
open scoped Topology
open Filter

namespace GameTheory.Experimental.PostArchitecture

open GameTheory.Math.Probability

/-! ## One-based Cesaro averages and the fair two-point law -/

/-- The Cesaro average over the first `n + 1` stages. -/
def cesaroAverage (stage : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), stage i

/-- The pointwise unit complement of a real-valued stage-payoff sequence. -/
def complementSequence (stage : ℕ → ℝ) : ℕ → ℝ :=
  fun n => 1 - stage n

/-- A fair law on one sequence and its complement. -/
def fairTwoPointLaw (stage : ℕ → ℝ) : PMF (ℕ → ℝ) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure stage) (PMF.pure (complementSequence stage))

/-- The concrete fair selector has finite support, so every real observable on
its support has an actual-law integrability guard. -/
theorem fairTwoPointLaw_support_finite (stage : ℕ → ℝ) :
    (fairTwoPointLaw stage).support.Finite := by
  apply Set.Finite.subset
    ((Set.finite_insert).2 (Set.finite_singleton (complementSequence stage)))
  intro path hpath
  by_contra hnot
  have hnot' : path ≠ stage ∧ path ≠ complementSequence stage := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_not] using hnot
  have hfirst : PMF.pure stage path = 0 := by
    simp [PMF.pure_apply, hnot'.1]
  have hsecond : PMF.pure (complementSequence stage) path = 0 := by
    simp [PMF.pure_apply, hnot'.2]
  have hmass : fairTwoPointLaw stage path ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hpath
  rw [fairTwoPointLaw, mix_apply, hfirst, hsecond] at hmass
  simp at hmass

/-- Finite support supplies an integrability certificate for this fixture law. -/
theorem fairTwoPointIntegrable (stage : ℕ → ℝ) (f : (ℕ → ℝ) → ℝ) :
    PayoffIntegrable (fairTwoPointLaw stage) f :=
  payoffIntegrable_of_finite_support (fairTwoPointLaw stage) f
    (fairTwoPointLaw_support_finite stage)

/-- The fair selector expectation is the average of its two point masses. -/
theorem expect_fairTwoPointLaw (stage : ℕ → ℝ) (f : (ℕ → ℝ) → ℝ) :
    expect (fairTwoPointLaw stage) f (fairTwoPointIntegrable stage f) =
      (1 / 2 : ℝ) * f stage + (1 / 2 : ℝ) * f (complementSequence stage) := by
  classical
  let hstage := payoffIntegrable_of_finite_support (PMF.pure stage) f
    (by simp)
  let hcomplement := payoffIntegrable_of_finite_support
    (PMF.pure (complementSequence stage)) f
    (by simp)
  calc
    expect (fairTwoPointLaw stage) f (fairTwoPointIntegrable stage f) =
        expect (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure stage) (PMF.pure (complementSequence stage))) f
          (payoffIntegrable_mix _ _ _ _ _ f hstage hcomplement) := rfl
    _ = (1 / 2 : ℝ) * expect (PMF.pure stage) f hstage +
        (1 / 2 : ℝ) * expect (PMF.pure (complementSequence stage)) f hcomplement :=
      by
        simpa only [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] using
          (expect_mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure stage) (PMF.pure (complementSequence stage)) f hstage hcomplement)
    _ = _ := by rw [expect_pure, expect_pure]

@[simp]
theorem cesaroAverage_complement (stage : ℕ → ℝ) (n : ℕ) :
    cesaroAverage (complementSequence stage) n =
      1 - cesaroAverage stage n := by
  unfold cesaroAverage complementSequence
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

@[simp]
theorem expect_fair_cesaroAverage (stage : ℕ → ℝ) (n : ℕ) :
    expect (fairTwoPointLaw stage) (fun path => cesaroAverage path n)
        (fairTwoPointIntegrable stage _) = (1 / 2 : ℝ) := by
  rw [expect_fairTwoPointLaw, cesaroAverage_complement]
  ring

theorem tendsto_expect_fair_cesaroAverage (stage : ℕ → ℝ) :
    Tendsto
      (fun n => expect (fairTwoPointLaw stage)
        (fun path => cesaroAverage path n) (fairTwoPointIntegrable stage _))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  convert (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))) using 1
  funext n
  exact expect_fair_cesaroAverage stage n

/-! ## The generic hostile-slice theorem -/

/--
Given explicit liminf/limsup endpoint facts for a stage sequence and its
complement, the fair two-point law separates all three EXP-108 aggregations:
expected pathwise liminf, the limit of expected finite averages, and expected
pathwise limsup.  The four endpoint equalities are the exact assumptions that
the intended rapidly growing alternating-block construction must discharge.
-/
theorem fair_two_point_order_limits (stage : ℕ → ℝ)
    (hstage_liminf :
      Filter.liminf (fun n => cesaroAverage stage n) atTop = 0)
    (hstage_limsup :
      Filter.limsup (fun n => cesaroAverage stage n) atTop = 1)
    (hcomplement_liminf :
      Filter.liminf (fun n => cesaroAverage (complementSequence stage) n)
        atTop = 0)
    (hcomplement_limsup :
      Filter.limsup (fun n => cesaroAverage (complementSequence stage) n)
        atTop = 1) :
    expect (fairTwoPointLaw stage)
        (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop)
        (fairTwoPointIntegrable stage _) = 0 ∧
    (∀ n, expect (fairTwoPointLaw stage)
      (fun path => cesaroAverage path n) (fairTwoPointIntegrable stage _) = (1 / 2 : ℝ)) ∧
    Tendsto
      (fun n => expect (fairTwoPointLaw stage)
        (fun path => cesaroAverage path n) (fairTwoPointIntegrable stage _))
      atTop (𝓝 (1 / 2 : ℝ)) ∧
    expect (fairTwoPointLaw stage)
        (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop)
        (fairTwoPointIntegrable stage _) = 1 ∧
    expect (fairTwoPointLaw stage)
        (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop)
        (fairTwoPointIntegrable stage _) ≠
      (1 / 2 : ℝ) ∧
    expect (fairTwoPointLaw stage)
        (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop)
        (fairTwoPointIntegrable stage _) ≠
      (1 / 2 : ℝ) := by
  have hLiminf :
      expect (fairTwoPointLaw stage)
          (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop)
          (fairTwoPointIntegrable stage _) =
        (1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * 0 := by
    rw [expect_fairTwoPointLaw, hstage_liminf, hcomplement_liminf]
  have hLimsup :
      expect (fairTwoPointLaw stage)
          (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop)
          (fairTwoPointIntegrable stage _) =
        (1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 1 := by
    rw [expect_fairTwoPointLaw, hstage_limsup, hcomplement_limsup]
  have hLiminfZero :
      expect (fairTwoPointLaw stage)
          (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop)
          (fairTwoPointIntegrable stage _) =
        0 := by
    rw [hLiminf]
    norm_num
  have hLimsupOne :
      expect (fairTwoPointLaw stage)
          (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop)
          (fairTwoPointIntegrable stage _) =
        1 := by
    rw [hLimsup]
    norm_num
  refine ⟨hLiminfZero, fun n => expect_fair_cesaroAverage stage n,
    tendsto_expect_fair_cesaroAverage stage, hLimsupOne, ?_, ?_⟩
  · rw [hLiminfZero]
    norm_num
  · rw [hLimsupOne]
    norm_num

end GameTheory.Experimental.PostArchitecture
