/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.TotalVariation

/-!
# Distinguishing Tests for Finite PMFs

Observer tests compare two finite probability laws by the difference between
their expected outputs. Unit-bounded real tests and Boolean tests are both
bounded by total variation, and each class contains a test attaining the bound.

## Main definitions

* `pmfTestAdvantage` — absolute expectation gap of a real-valued test
* `IsUnitBoundedTest` — a test taking values in `[0, 1]`
* `pmfBooleanAdvantage` — acceptance-probability gap of a Boolean test

## Main results

* `pmfTestAdvantage_le_pmfTV` — bounded-test upper bound
* `exists_unitBoundedTest_advantage_eq_pmfTV` — bounded tests attain TV
* `pmfBooleanAdvantage_le_pmfTV` — Boolean-test upper bound
* `exists_booleanTest_advantage_eq_pmfTV` — Boolean tests attain TV
-/

namespace Math
namespace Probability

/-- Absolute expectation gap achieved by a real-valued test. -/
noncomputable def pmfTestAdvantage {Ω : Type*}
    (μ ν : PMF Ω) (test : Ω → ℝ) : ℝ :=
  |expect μ test - expect ν test|

/-- A real-valued observer test whose output lies in the unit interval. -/
def IsUnitBoundedTest {Ω : Type*} (test : Ω → ℝ) : Prop :=
  ∀ ω, 0 ≤ test ω ∧ test ω ≤ 1

/-- Every unit-bounded real test has advantage at most total variation. -/
theorem pmfTestAdvantage_le_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (test : Ω → ℝ) (htest : IsUnitBoundedTest test) :
    pmfTestAdvantage μ ν test ≤ pmfTV μ ν := by
  unfold pmfTestAdvantage
  simpa using abs_expect_sub_le_range_mul_pmfTV μ ν test
    (L := 0) (U := 1) (fun ω => (htest ω).1) (fun ω => (htest ω).2)

/-- Canonical unit-bounded test accepting exactly where `μ` has more mass than
`ν`. -/
noncomputable def pmfTVTestWitness {Ω : Type*} (μ ν : PMF Ω) : Ω → ℝ :=
  pmfPositiveVariationWitness μ ν 1

theorem pmfTVTestWitness_unitBounded {Ω : Type*} (μ ν : PMF Ω) :
    IsUnitBoundedTest (pmfTVTestWitness μ ν) := by
  intro ω
  exact ⟨pmfPositiveVariationWitness_nonneg μ ν zero_le_one ω,
    pmfPositiveVariationWitness_le μ ν zero_le_one ω⟩

theorem pmfTVTestWitness_advantage {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    pmfTestAdvantage μ ν (pmfTVTestWitness μ ν) = pmfTV μ ν := by
  have hdiff :
      expect μ (pmfTVTestWitness μ ν) -
          expect ν (pmfTVTestWitness μ ν) = pmfTV μ ν := by
    simpa [pmfTVTestWitness] using
      expect_sub_pmfPositiveVariationWitness μ ν 1
  rw [pmfTestAdvantage, hdiff, abs_of_nonneg (pmfTV_nonneg μ ν)]

theorem exists_unitBoundedTest_advantage_eq_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    ∃ test : Ω → ℝ,
      IsUnitBoundedTest test ∧ pmfTestAdvantage μ ν test = pmfTV μ ν :=
  ⟨pmfTVTestWitness μ ν, pmfTVTestWitness_unitBounded μ ν,
    pmfTVTestWitness_advantage μ ν⟩

theorem pmfTV_le_iff_unitBoundedTest_advantage_le {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (ε : ℝ) :
    pmfTV μ ν ≤ ε ↔
      ∀ test : Ω → ℝ, IsUnitBoundedTest test →
        pmfTestAdvantage μ ν test ≤ ε := by
  constructor
  · intro h test htest
    exact le_trans (pmfTestAdvantage_le_pmfTV μ ν test htest) h
  · intro h
    rw [← pmfTVTestWitness_advantage μ ν]
    exact h (pmfTVTestWitness μ ν) (pmfTVTestWitness_unitBounded μ ν)

/-- Acceptance-probability gap achieved by a Boolean observer test. -/
noncomputable def pmfBooleanAdvantage {Ω : Type*}
    (μ ν : PMF Ω) (test : Ω → Bool) : ℝ :=
  |((μ.map test) true).toReal - ((ν.map test) true).toReal|

theorem expect_bool_accept (d : PMF Bool) :
    expect d (fun b => if b then (1 : ℝ) else 0) = (d true).toReal := by
  rw [expect_eq_sum]
  simp

theorem pmfBooleanAdvantage_eq_testAdvantage {Ω : Type*}
    (μ ν : PMF Ω) (test : Ω → Bool) :
    pmfBooleanAdvantage μ ν test =
      pmfTestAdvantage μ ν (fun ω => if test ω then 1 else 0) := by
  unfold pmfBooleanAdvantage pmfTestAdvantage
  rw [← expect_bool_accept (μ.map test), ← expect_bool_accept (ν.map test),
    expect_map, expect_map]

theorem pmfBooleanAdvantage_le_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (test : Ω → Bool) :
    pmfBooleanAdvantage μ ν test ≤ pmfTV μ ν := by
  rw [pmfBooleanAdvantage_eq_testAdvantage]
  apply pmfTestAdvantage_le_pmfTV
  intro ω
  by_cases h : test ω = true <;> simp [h]

/-- Canonical Boolean test accepting exactly where `μ` has more mass than
`ν`. -/
noncomputable def pmfTVBooleanWitness {Ω : Type*} (μ ν : PMF Ω) : Ω → Bool :=
  fun ω => decide (0 < (μ ω).toReal - (ν ω).toReal)

theorem pmfTVBooleanWitness_advantage {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    pmfBooleanAdvantage μ ν (pmfTVBooleanWitness μ ν) = pmfTV μ ν := by
  rw [pmfBooleanAdvantage_eq_testAdvantage]
  have hwitness :
      (fun ω => if pmfTVBooleanWitness μ ν ω then (1 : ℝ) else 0) =
        pmfTVTestWitness μ ν := by
    funext ω
    simp only [pmfTVBooleanWitness, pmfTVTestWitness,
      pmfPositiveVariationWitness, decide_eq_true_eq]
  rw [hwitness, pmfTVTestWitness_advantage]

theorem exists_booleanTest_advantage_eq_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) :
    ∃ test : Ω → Bool, pmfBooleanAdvantage μ ν test = pmfTV μ ν :=
  ⟨pmfTVBooleanWitness μ ν, pmfTVBooleanWitness_advantage μ ν⟩

theorem pmfTV_le_iff_booleanTest_advantage_le {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (ε : ℝ) :
    pmfTV μ ν ≤ ε ↔ ∀ test : Ω → Bool, pmfBooleanAdvantage μ ν test ≤ ε := by
  constructor
  · intro h test
    exact le_trans (pmfBooleanAdvantage_le_pmfTV μ ν test) h
  · intro h
    rw [← pmfTVBooleanWitness_advantage μ ν]
    exact h (pmfTVBooleanWitness μ ν)

end Probability
end Math
