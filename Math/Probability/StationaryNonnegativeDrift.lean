/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.HarmonicClosedClass
import Math.Probability.StationaryCommunicatingClass

/-!
# Nonnegative drift under a stationary finite-state weight

For a finite Markov kernel, stationarity makes the weighted sum of every
potential drift vanish. If the weight and all drifts are nonnegative, the
drift therefore vanishes at each state carrying positive weight.

This elementary observation gives harmonicity on any closed communicating
class on which a stationary weight has full support. The existing finite
maximum principle then makes the potential constant on that class. All
statements use explicit stationarity, positivity, closure, and communication
hypotheses; no recurrence assumption is inferred from terminology.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S : Type*}

/-- One-step expected drift of a real potential under a Markov kernel. -/
def kernelDrift
    (kernel : S → PMF S) (potential : S → ℝ) (state : S) : ℝ :=
  expect (kernel state) potential - potential state

/-- A stationary weight makes the weighted total drift of every potential
equal to zero. Neither positivity nor normalization of the weight is needed.
-/
theorem sum_weight_mul_kernelDrift_eq_zero
    [Fintype S]
    (kernel : S → PMF S) (weight potential : S → ℝ)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination) :
    (∑ state, weight state * kernelDrift kernel potential state) = 0 := by
  simp_rw [kernelDrift, mul_sub]
  rw [Finset.sum_sub_distrib,
    stationary_expectation kernel weight hstationary potential]
  exact sub_self _

/-- If a stationary weight and every drift are nonnegative, then the drift
vanishes at each state carrying strictly positive weight. -/
theorem kernelDrift_eq_zero_of_stationary_weight_pos
    [Fintype S]
    (kernel : S → PMF S) (weight potential : S → ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (hdrift : ∀ state, 0 ≤ kernelDrift kernel potential state)
    (state : S) (hstate : 0 < weight state) :
    kernelDrift kernel potential state = 0 := by
  have hterms :
      ∀ other ∈ (Finset.univ : Finset S),
        0 ≤ weight other * kernelDrift kernel potential other := by
    intro other _
    exact mul_nonneg (hweight other) (hdrift other)
  have hterm :
      weight state * kernelDrift kernel potential state = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp
      (sum_weight_mul_kernelDrift_eq_zero
        kernel weight potential hstationary)
      state (Finset.mem_univ state)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hstate)

/-- A full-support stationary nonnegative weight turns a globally
nonnegative drift into pointwise harmonicity. -/
theorem harmonic_of_stationary_fullSupport_nonnegativeDrift
    [Fintype S]
    (kernel : S → PMF S) (weight potential : S → ℝ)
    (hweight : ∀ state, 0 < weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (hdrift : ∀ state, 0 ≤ kernelDrift kernel potential state) :
    ∀ state, potential state = expect (kernel state) potential := by
  intro state
  have hzero :=
    kernelDrift_eq_zero_of_stationary_weight_pos
      kernel weight potential (fun other => (hweight other).le)
      hstationary hdrift state (hweight state)
  exact (sub_eq_zero.mp hzero).symm

namespace ReachableClosedClass

variable [Fintype S] [DecidableEq S]
  {kernel : S → PMF S} {initial : S}

/-- A nonnegative stationary weight which is positive throughout a closed
communicating class forces a nonnegative-drift potential to be harmonic on
that class. The weight may also carry mass outside the class. -/
theorem harmonic_of_stationary_weight_pos
    (C : ReachableClosedClass kernel initial)
    (weight potential : S → ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (hpositive :
      ∀ state, state ∈ C.states → 0 < weight state)
    (hdrift : ∀ state, 0 ≤ kernelDrift kernel potential state) :
    ∀ state, state ∈ C.states →
      potential state = expect (kernel state) potential := by
  intro state hstate
  have hzero :=
    kernelDrift_eq_zero_of_stationary_weight_pos
      kernel weight potential hweight hstationary hdrift
      state (hpositive state hstate)
  exact (sub_eq_zero.mp hzero).symm

/-- Under the same explicit hypotheses, the potential is constant on the
closed communicating class. -/
theorem eq_on_class_of_stationary_weight_pos
    (C : ReachableClosedClass kernel initial)
    (weight potential : S → ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (hpositive :
      ∀ state, state ∈ C.states → 0 < weight state)
    (hdrift : ∀ state, 0 ≤ kernelDrift kernel potential state) :
    ∀ ⦃left⦄, left ∈ C.states →
      ∀ ⦃right⦄, right ∈ C.states →
        potential left = potential right :=
  C.harmonic_eq_on_class potential
    (C.harmonic_of_stationary_weight_pos
      weight potential hweight hstationary hpositive hdrift)

end ReachableClosedClass

/-- For a globally full-support stationary kernel, a nonnegative-drift
potential is constant between any two mutually reachable states. The
full-support hypothesis is used to make each communication class closed. -/
theorem eq_of_stationary_fullSupport_of_communicates
    [Fintype S]
    (kernel : S → PMF S) (weight potential : S → ℝ)
    (hweight : ∀ state, 0 < weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (hdrift : ∀ state, 0 ≤ kernelDrift kernel potential state)
    {left right : S}
    (hcommunicates : PMFCommunicates kernel left right) :
    potential left = potential right := by
  classical
  let C :=
    reachableClosedClass_of_stationary_fullSupport
      kernel weight hweight hstationary left
  apply C.eq_on_class_of_stationary_weight_pos
    weight potential (fun state => (hweight state).le)
    hstationary
    (fun state _ => hweight state) hdrift
  · exact C.entry_mem
  · apply (mem_pmfCommunicationClass_iff kernel left right).mpr
    exact hcommunicates

end Probability
end Math
