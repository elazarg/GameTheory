/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.StationaryCommunicatingClass

/-!
# Debt transport is stationary Markov monodromy

A closed word of nonnegative debt transports is naturally a Markov kernel on
the time-expanded player set.  The debt vector is a stationary, generally
non-full-support weight.  The full-support hypothesis in the standard return
theorem is stronger than this application needs: nonnegativity everywhere
and positivity at the source of the selected edge suffice.

Thus every positive debt-transfer edge lies on a recurrent support cycle.
The resulting object is a Markov/transportation-polytope object, not a group
in general.  A permutation or group orbit appears only after a deterministic
extremalization which is not asserted here.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S : Type*}

/-- **A positive stationary edge returns without full support.**

For a finite Markov kernel with a nonnegative stationary weight, a support
edge whose source has positive weight can be followed by a support path back
to that source.  Zero-weight states elsewhere are harmless. -/
theorem supportStep_returns_of_stationary_nonnegative
    [Fintype S]
    (kernel : S → PMF S) (weight : S → ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    {source destination : S}
    (hsource : 0 < weight source)
    (hstep : PMFSupportStep kernel source destination) :
    PMFReachable kernel destination source := by
  classical
  by_contra hnotReachable
  let reachable : Finset S :=
    Finset.univ.filter fun state =>
      PMFReachable kernel destination state
  have hdestination : destination ∈ reachable := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ destination,
        Relation.ReflTransGen.refl⟩
  have hsourceOutside : source ∉ reachable := by
    simpa [reachable] using hnotReachable
  have hclosed :
      ∀ ⦃current⦄, current ∈ reachable →
        ∀ ⦃next⦄, PMFSupportStep kernel current next →
          next ∈ reachable := by
    intro current hcurrent next hnext
    have hreachCurrent :
        PMFReachable kernel destination current := by
      simpa [reachable] using hcurrent
    have hreachNext :
        PMFReachable kernel destination next :=
      hreachCurrent.tail hnext
    simpa [reachable] using hreachNext
  let indicator : S → ℝ :=
    fun state => if state ∈ reachable then 1 else 0
  have hexpect_one :
      ∀ current, current ∈ reachable →
        expect (kernel current) indicator = 1 := by
    intro current hcurrent
    rw [expect_eq_sum]
    calc
      (∑ next,
          (kernel current next).toReal * indicator next) =
          ∑ next, (kernel current next).toReal := by
        apply Finset.sum_congr rfl
        intro next _
        by_cases hnext : next ∈ reachable
        · simp [indicator, hnext]
        · have hkernelZero : kernel current next = 0 := by
            by_contra hkernel
            exact hnext (hclosed hcurrent hkernel)
          simp [indicator, hnext, hkernelZero]
      _ = 1 := pmf_toReal_sum_one (kernel current)
  have hexpect_nonneg :
      ∀ current, 0 ≤ expect (kernel current) indicator := by
    intro current
    apply expect_nonneg
    intro state
    by_cases hstate : state ∈ reachable <;>
      simp [indicator, hstate]
  have hexpect_source_pos :
      0 < expect (kernel source) indicator := by
    rw [expect_eq_sum]
    apply Finset.sum_pos'
    · intro state _
      apply mul_nonneg ENNReal.toReal_nonneg
      by_cases hstate : state ∈ reachable <;>
        simp [indicator, hstate]
    · refine ⟨destination, Finset.mem_univ _, ?_⟩
      simp only [indicator, if_pos hdestination, mul_one]
      exact ENNReal.toReal_pos hstep
        (PMF.apply_ne_top (kernel source) destination)
  have hdiffPos :
      0 <
        ∑ current,
          ((weight current *
                expect (kernel current) indicator) -
            weight current * indicator current) := by
    apply Finset.sum_pos'
    · intro current _
      by_cases hcurrent : current ∈ reachable
      · rw [hexpect_one current hcurrent]
        simp [indicator, hcurrent]
      · have hnonneg := hexpect_nonneg current
        have hindicator : indicator current = 0 := by
          simp [indicator, hcurrent]
        rw [hindicator, mul_zero, sub_zero]
        exact mul_nonneg (hweight current) hnonneg
    · refine ⟨source, Finset.mem_univ _, ?_⟩
      have hindicator : indicator source = 0 := by
        simp [indicator, hsourceOutside]
      rw [hindicator, mul_zero, sub_zero]
      exact mul_pos hsource hexpect_source_pos
  have hdiff :
      (∑ current, weight current *
          expect (kernel current) indicator) -
          ∑ current, weight current * indicator current =
        ∑ current,
          ((weight current *
                expect (kernel current) indicator) -
            weight current * indicator current) := by
    rw [Finset.sum_sub_distrib]
  have hstrict :
      (∑ current, weight current * indicator current) <
        ∑ current, weight current *
          expect (kernel current) indicator := by
    linarith
  have heq :=
    stationary_expectation kernel weight hstationary indicator
  linarith

/-- A finite stationary debt monodromy.  This is the abstract return kernel
obtained by composing a closed word of normalized nonnegative debt
transports. -/
structure StationaryDebtMonodromy (S : Type*) [Fintype S] where
  kernel : S → PMF S
  debt : S → ℝ
  debt_nonneg : ∀ state, 0 ≤ debt state
  stationary : ∀ destination,
    ∑ source, debt source * (kernel source destination).toReal =
      debt destination

namespace StationaryDebtMonodromy

/-- Every positive edge in a stationary debt monodromy lies on a support
cycle. -/
theorem supportEdge_returns
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    PMFReachable M.kernel destination source :=
  supportStep_returns_of_stationary_nonnegative
    M.kernel M.debt M.debt_nonneg M.stationary hsource hstep

/-- A positive stationary edge also forces positive debt at its destination.
This identifies the positive-debt support as a closed recurrent carrier. -/
theorem debt_pos_of_supportEdge
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    0 < M.debt destination := by
  rw [← M.stationary destination]
  apply Finset.sum_pos'
  · intro state _
    exact mul_nonneg (M.debt_nonneg state) ENNReal.toReal_nonneg
  · refine ⟨source, Finset.mem_univ _, ?_⟩
    exact mul_pos hsource
      (ENNReal.toReal_pos hstep
        (PMF.apply_ne_top (M.kernel source) destination))

/-- Positive support edges are mutually reachable. -/
theorem supportEdge_communicates
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    PMFCommunicates M.kernel source destination :=
  ⟨Relation.ReflTransGen.single hstep,
    M.supportEdge_returns hsource hstep⟩

end StationaryDebtMonodromy

end Probability
end Math
