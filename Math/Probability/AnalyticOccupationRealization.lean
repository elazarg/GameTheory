/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticOccupationFlow
import Math.Probability.ChargedOccupationAlternative
import Math.ProbabilityMassFunction

/-!
# Realization of analytic occupation flows

A nonnegative balanced family of source-indexed transition masses is the
joint stationary occupation measure of a randomized source policy. This
file records the finite algebra needed to normalize that measure.

The distinguished mass in an `AnalyticPositiveCirculation` is exactly a
positive power. Analyticity bounds the total pole-cleared mass from above,
so its normalized stationary frequency has a power-law lower bound with the
same exponent.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

/-- A finite nonnegative real weight vector of total mass one, regarded as
an actual probability mass function. -/
def finiteRealWeightsPMF
    {α : Type*} [Fintype α]
    (weight : α → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (weight a)) (by
    rw [← ENNReal.ofReal_one, ← hsum]
    exact
      (ENNReal.ofReal_sum_of_nonneg
        (fun a _ => hweight a)).symm)

@[simp]
theorem finiteRealWeightsPMF_apply
    {α : Type*} [Fintype α]
    (weight : α → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) (a : α) :
    finiteRealWeightsPMF weight hweight hsum a =
      ENNReal.ofReal (weight a) := by
  simp [finiteRealWeightsPMF, PMF.ofFintype_apply]

@[simp]
theorem finiteRealWeightsPMF_toReal
    {α : Type*} [Fintype α]
    (weight : α → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum : ∑ a, weight a = 1) (a : α) :
    (finiteRealWeightsPMF weight hweight hsum a).toReal =
      weight a := by
  rw [finiteRealWeightsPMF_apply]
  exact ENNReal.toReal_ofReal (hweight a)

/-- Total outgoing occupation mass at one source state. -/
def occupationSourceMass
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ) (s : S) : ℝ :=
  ∑ i with source i = s, mass i

/-- Total mass of a finite occupation vector. -/
def occupationTotalMass
    [Fintype I] (mass : I → ℝ) : ℝ :=
  ∑ i, mass i

/-- States carrying positive outgoing occupation mass. Using this finite
support as a type avoids inventing an arbitrary transition rule at
zero-mass states. -/
def occupationActiveStates
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ) : Finset S :=
  Finset.univ.filter fun s =>
    0 < occupationSourceMass source mass s

/-- Operational indices whose transition is consumed at `s`. -/
def occupationSourceFiber
    [Fintype I] [DecidableEq S]
    (source : I → S) (s : S) : Finset I :=
  Finset.univ.filter fun i => source i = s

theorem occupationActiveState_sourceMass_pos
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (s : occupationActiveStates source mass) :
    0 < occupationSourceMass source mass s.1 := by
  have hs := s.property
  change s.1 ∈ Finset.univ.filter
    (fun u => 0 < occupationSourceMass source mass u) at hs
  exact (Finset.mem_filter.mp hs).2

theorem occupationSourceFiber_source_eq
    [Fintype I] [DecidableEq S]
    (source : I → S) {s : S}
    (i : occupationSourceFiber source s) :
    source i.1 = s := by
  have hi := i.property
  change i.1 ∈ Finset.univ.filter
    (fun j => source j = s) at hi
  exact (Finset.mem_filter.mp hi).2

/-- Conditional randomized choice weights induced by an occupation vector.
At a zero-mass state all weights are zero; such states receive zero mass in
the associated invariant distribution and may be completed arbitrarily. -/
def occupationConditionalWeight
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (s : S) (i : I) : ℝ :=
  if source i = s then mass i / occupationSourceMass source mass s else 0

theorem occupationSourceMass_nonneg
    [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (s : S) :
    0 ≤ occupationSourceMass source mass s := by
  exact Finset.sum_nonneg fun i _ => hmass i

theorem occupationTotalMass_pos_of_coordinate_pos
    [Fintype I] {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) {i₀ : I}
    (hi₀ : 0 < mass i₀) :
    0 < occupationTotalMass mass := by
  exact hi₀.trans_le
    (Finset.single_le_sum
      (fun i _ => hmass i) (Finset.mem_univ i₀))

theorem occupationSourceMass_pos_of_coordinate_pos
    [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) {i₀ : I}
    (hi₀ : 0 < mass i₀) :
    0 < occupationSourceMass source mass (source i₀) := by
  exact hi₀.trans_le
    (Finset.single_le_sum
      (fun i _ => hmass i)
      (by simp))

/-- Source masses partition the total occupation mass. -/
theorem sum_occupationSourceMass
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ) :
    ∑ s, occupationSourceMass source mass s =
      occupationTotalMass mass := by
  simp only [occupationSourceMass, occupationTotalMass]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_eq_single (source i)]
  · simp
  · intro s hs
    simp [Ne.symm hs]

/-- Positive total mass normalizes the source masses to a probability
vector. -/
theorem sum_normalizedOccupationSourceMass
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (htotal : 0 < occupationTotalMass mass) :
    ∑ s,
        occupationSourceMass source mass s /
          occupationTotalMass mass = 1 := by
  rw [← Finset.sum_div, sum_occupationSourceMass]
  exact div_self (ne_of_gt htotal)

/-- Removing the zero-source-mass states does not change total mass. -/
theorem sum_activeOccupationSourceMass
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) :
    (∑ s : occupationActiveStates source mass,
        occupationSourceMass source mass s.1) =
      occupationTotalMass mass := by
  classical
  rw [← sum_occupationSourceMass source mass]
  rw [← Finset.sum_subtype
    (occupationActiveStates source mass)
    (fun _ => Iff.rfl)
    (occupationSourceMass source mass)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  have hnot :
      ¬0 < occupationSourceMass source mass s := by
    simpa [occupationActiveStates] using hs
  exact le_antisymm (not_lt.mp hnot)
    (occupationSourceMass_nonneg source hmass s)

/-- Summing over the source fiber recovers its source mass. -/
theorem sum_sourceFiberMass
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ) (s : S) :
    (∑ i : occupationSourceFiber source s, mass i.1) =
      occupationSourceMass source mass s := by
  classical
  rw [← Finset.sum_subtype
    (occupationSourceFiber source s)
    (fun _ => Iff.rfl) mass]
  simp [occupationSourceFiber, occupationSourceMass]

/-- The normalized source masses as a genuine PMF on their positive
support. -/
def occupationInvariantPMF
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass) :
    PMF (occupationActiveStates source mass) :=
  finiteRealWeightsPMF
    (fun s =>
      occupationSourceMass source mass s.1 /
        occupationTotalMass mass)
    (fun s =>
      div_nonneg
        (occupationSourceMass_nonneg source hmass s.1)
        htotal.le)
    (by
      rw [← Finset.sum_div,
        sum_activeOccupationSourceMass source hmass]
      exact div_self (ne_of_gt htotal))

@[simp]
theorem occupationInvariantPMF_toReal
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (s : occupationActiveStates source mass) :
    (occupationInvariantPMF source mass hmass htotal s).toReal =
      occupationSourceMass source mass s.1 /
        occupationTotalMass mass := by
  rw [occupationInvariantPMF, finiteRealWeightsPMF_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg
      (occupationSourceMass_nonneg source hmass s.1)
      htotal.le)

/-- At an active state, normalize exactly the operational indices consumed
at that source. -/
def occupationPolicyPMF
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s) :
    PMF (occupationSourceFiber source s) :=
  finiteRealWeightsPMF
    (fun i =>
      mass i.1 / occupationSourceMass source mass s)
    (fun i =>
      div_nonneg (hmass i.1) hsource.le)
    (by
      rw [← Finset.sum_div, sum_sourceFiberMass]
      exact div_self (ne_of_gt hsource))

@[simp]
theorem occupationPolicyPMF_toReal
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s)
    (i : occupationSourceFiber source s) :
    (occupationPolicyPMF source mass hmass hsource i).toReal =
      mass i.1 / occupationSourceMass source mass s := by
  rw [occupationPolicyPMF, finiteRealWeightsPMF_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (hmass i.1) hsource.le)

/-- Randomize among the operational transitions at one active source and
then execute the selected stochastic kernel. -/
def occupationOperationalKernel
    [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s) :
    PMF S :=
  (occupationPolicyPMF source mass hmass hsource).bind
    fun i => kernel i.1

theorem occupationOperationalKernel_toReal
    [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s)
    (destination : S) :
    (occupationOperationalKernel
      kernel source mass hmass hsource destination).toReal =
      ∑ i : occupationSourceFiber source s,
        (mass i.1 / occupationSourceMass source mass s) *
          (kernel i.1 destination).toReal := by
  rw [occupationOperationalKernel,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [occupationPolicyPMF_toReal]

theorem sum_occupationConditionalWeight
    [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ} {s : S}
    (hsource : 0 < occupationSourceMass source mass s) :
    ∑ i, occupationConditionalWeight source mass s i = 1 := by
  simp only [occupationConditionalWeight]
  rw [← Finset.sum_filter]
  calc
    (∑ i ∈ (Finset.univ.filter fun i => source i = s),
        mass i / occupationSourceMass source mass s) =
        (∑ i ∈ (Finset.univ.filter fun i => source i = s),
          mass i) / occupationSourceMass source mass s := by
      simpa using
        (Finset.sum_div
          (Finset.univ.filter fun i => source i = s)
          mass (occupationSourceMass source mass s)).symm
    _ = 1 := div_self (ne_of_gt hsource)

theorem occupationConditionalWeight_nonneg
    [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (s : S) (i : I) :
    0 ≤ occupationConditionalWeight source mass s i := by
  by_cases hi : source i = s
  · simp only [occupationConditionalWeight, if_pos hi]
    exact div_nonneg (hmass i)
      (occupationSourceMass_nonneg source hmass s)
  · simp [occupationConditionalWeight, hi]

/-- Multiplying the conditional choice probability by its source mass
recovers the original joint occupation coordinate. -/
theorem occupationSourceMass_mul_conditionalWeight
    [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (s : S) (i : I) :
    occupationSourceMass source mass s *
        occupationConditionalWeight source mass s i =
      if source i = s then mass i else 0 := by
  by_cases hi : source i = s
  · rw [if_pos hi]
    simp only [occupationConditionalWeight, if_pos hi]
    by_cases hsource :
        occupationSourceMass source mass s = 0
    · have hi_le :
          mass i ≤ occupationSourceMass source mass s := by
        apply Finset.single_le_sum
          (fun j _ => hmass j)
        simp [hi]
      have himass : mass i = 0 := by
        rw [hsource] at hi_le
        exact le_antisymm hi_le (hmass i)
      simp [hsource, himass]
    · field_simp
  · simp [occupationConditionalWeight, hi]

/-- Balance of actual source-consuming columns is exactly the stationarity
equation for the unnormalized source occupation masses. -/
theorem occupationSourceMass_eq_arrival_of_balance
    [Fintype I] [DecidableEq S]
    (kernel : I → S → ℝ) (source : I → S)
    (mass : I → ℝ)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          (kernel i destination -
            if destination = source i then 1 else 0) = 0)
    (destination : S) :
    occupationSourceMass source mass destination =
      ∑ i, mass i * kernel i destination := by
  have h := hbalance destination
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  have hsource :
      (∑ i, mass i *
          if destination = source i then 1 else 0) =
        occupationSourceMass source mass destination := by
    simp only [occupationSourceMass]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : source i = destination
    · simp [hi]
    · simp [hi, Ne.symm hi]
  rw [hsource] at h
  linarith

/-- The conditional source policy induced by a nonnegative balanced
occupation vector leaves the normalized source masses invariant. States of
zero source mass are irrelevant to this identity and can be assigned any
source-compatible fallback transition. -/
theorem normalizedSourceMass_stationary
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → S → ℝ) (source : I → S)
    {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          (kernel i destination -
            if destination = source i then 1 else 0) = 0)
    (destination : S) :
    (∑ s,
        (occupationSourceMass source mass s /
            occupationTotalMass mass) *
          ∑ i,
            occupationConditionalWeight source mass s i *
              kernel i destination) =
      occupationSourceMass source mass destination /
        occupationTotalMass mass := by
  have htotal_ne : occupationTotalMass mass ≠ 0 :=
    ne_of_gt htotal
  calc
    (∑ s,
        (occupationSourceMass source mass s /
            occupationTotalMass mass) *
          ∑ i,
            occupationConditionalWeight source mass s i *
              kernel i destination) =
        (∑ s, ∑ i,
          (occupationSourceMass source mass s *
              occupationConditionalWeight source mass s i) *
            kernel i destination) /
          occupationTotalMass mass := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ =
        (∑ s, ∑ i,
          (if source i = s then mass i else 0) *
            kernel i destination) /
          occupationTotalMass mass := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      rw [occupationSourceMass_mul_conditionalWeight
        source hmass]
    _ =
        (∑ i, mass i * kernel i destination) /
          occupationTotalMass mass := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_eq_single (source i)]
      · simp
      · intro s hs
        simp [Ne.symm hs]
    _ =
        occupationSourceMass source mass destination /
          occupationTotalMass mass := by
      rw [occupationSourceMass_eq_arrival_of_balance
        kernel source mass hbalance destination]

theorem occupationSourceMass_eq_zero_of_not_active
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) {s : S}
    (hs : s ∉ occupationActiveStates source mass) :
    occupationSourceMass source mass s = 0 := by
  have hnot :
      ¬0 < occupationSourceMass source mass s := by
    simpa [occupationActiveStates] using hs
  exact le_antisymm (not_lt.mp hnot)
    (occupationSourceMass_nonneg source hmass s)

/-- Balance closes the positive source support: an operational transition
selected at an active state assigns no mass to a state outside that support.
This is the point that makes the subtype kernel honest, with no arbitrary
zero-mass completion. -/
theorem occupationOperationalKernel_eq_zero_of_not_active
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          ((kernel i destination).toReal -
            if destination = source i then 1 else 0) = 0)
    {s : S} (hsource : 0 < occupationSourceMass source mass s)
    {destination : S}
    (hdestination :
      destination ∉ occupationActiveStates source mass) :
    occupationOperationalKernel
        kernel source mass hmass hsource destination = 0 := by
  have hsourceZero :
      occupationSourceMass source mass destination = 0 :=
    occupationSourceMass_eq_zero_of_not_active
      source hmass hdestination
  have harrival :
      ∑ i, mass i * (kernel i destination).toReal = 0 := by
    rw [← occupationSourceMass_eq_arrival_of_balance
      (fun i u => (kernel i u).toReal)
      source mass hbalance destination]
    exact hsourceZero
  apply
    (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top
        (occupationOperationalKernel
          kernel source mass hmass hsource)
        destination)
      ENNReal.zero_ne_top).mp
  rw [ENNReal.toReal_zero]
  rw [occupationOperationalKernel_toReal
    kernel source mass hmass hsource]
  apply Finset.sum_eq_zero
  intro i _
  have htermNonneg :
      0 ≤ mass i.1 * (kernel i.1 destination).toReal :=
    mul_nonneg (hmass i.1) ENNReal.toReal_nonneg
  have htermLe :
      mass i.1 * (kernel i.1 destination).toReal ≤
        ∑ j, mass j * (kernel j destination).toReal :=
    Finset.single_le_sum
      (fun j _ => by
        exact mul_nonneg (hmass j)
          (show 0 ≤ (kernel j destination).toReal from
            ENNReal.toReal_nonneg))
      (Finset.mem_univ i.1)
  have hterm :
      mass i.1 * (kernel i.1 destination).toReal = 0 := by
    rw [harrival] at htermLe
    exact le_antisymm htermLe htermNonneg
  calc
    (mass i.1 / occupationSourceMass source mass s) *
        (kernel i.1 destination).toReal =
      (mass i.1 * (kernel i.1 destination).toReal) /
        occupationSourceMass source mass s := by ring
    _ = 0 := by rw [hterm, zero_div]

/-- The induced Markov kernel restricted to the finite positive-source
support. -/
def occupationActiveKernel
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          ((kernel i destination).toReal -
            if destination = source i then 1 else 0) = 0)
    (s : occupationActiveStates source mass) :
    PMF (occupationActiveStates source mass) :=
  finiteRealWeightsPMF
    (fun destination =>
      (occupationOperationalKernel kernel source mass hmass
        (occupationActiveState_sourceMass_pos
          source mass s) destination.1).toReal)
    (fun _ => ENNReal.toReal_nonneg)
    (by
      rw [← Math.Probability.pmf_toReal_sum_one
        (occupationOperationalKernel
          kernel source mass hmass
            (occupationActiveState_sourceMass_pos
              source mass s))]
      rw [← Finset.sum_subtype
        (occupationActiveStates source mass)
        (fun _ => Iff.rfl)
        (fun destination =>
          (occupationOperationalKernel kernel source mass hmass
            (occupationActiveState_sourceMass_pos
              source mass s) destination).toReal)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro destination _ hdestination
      rw [occupationOperationalKernel_eq_zero_of_not_active
        kernel source hmass hbalance
          (occupationActiveState_sourceMass_pos
            source mass s) hdestination]
      rfl)

@[simp]
theorem occupationActiveKernel_toReal
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          ((kernel i destination).toReal -
            if destination = source i then 1 else 0) = 0)
    (s destination : occupationActiveStates source mass) :
    (occupationActiveKernel
      kernel source mass hmass hbalance s destination).toReal =
      (occupationOperationalKernel
        kernel source mass hmass
          (occupationActiveState_sourceMass_pos
            source mass s) destination.1).toReal := by
  rw [occupationActiveKernel, finiteRealWeightsPMF_apply]
  exact ENNReal.toReal_ofReal ENNReal.toReal_nonneg

theorem occupationOperationalKernel_toReal_eq_conditional
    [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s)
    (destination : S) :
    (occupationOperationalKernel
      kernel source mass hmass hsource destination).toReal =
      ∑ i,
        occupationConditionalWeight source mass s i *
          (kernel i destination).toReal := by
  rw [occupationOperationalKernel_toReal
    kernel source mass hmass hsource]
  calc
    (∑ i : occupationSourceFiber source s,
        (mass i.1 / occupationSourceMass source mass s) *
          (kernel i.1 destination).toReal) =
        ∑ i : occupationSourceFiber source s,
          occupationConditionalWeight source mass s i.1 *
            (kernel i.1 destination).toReal := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : source i.1 = s :=
        occupationSourceFiber_source_eq source i
      simp [occupationConditionalWeight, hi]
    _ =
        ∑ i,
          occupationConditionalWeight source mass s i *
            (kernel i destination).toReal := by
      rw [← Finset.sum_subtype
        (occupationSourceFiber source s)
        (fun _ => Iff.rfl)
        (fun i =>
          occupationConditionalWeight source mass s i *
            (kernel i destination).toReal)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hne : source i ≠ s := by
        simpa [occupationSourceFiber] using hi
      simp [occupationConditionalWeight, hne]

/-- The operational policy PMF is exactly the source-conditioned occupation
mass when tested against any real reward on operational indices. -/
theorem occupationPolicy_reward_eq_conditional
    [Fintype I] [DecidableEq S]
    (source : I → S) (mass reward : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    {s : S} (hsource : 0 < occupationSourceMass source mass s) :
    (∑ i : occupationSourceFiber source s,
        (occupationPolicyPMF
          source mass hmass hsource i).toReal * reward i.1) =
      ∑ i,
        occupationConditionalWeight source mass s i * reward i := by
  calc
    (∑ i : occupationSourceFiber source s,
        (occupationPolicyPMF
          source mass hmass hsource i).toReal * reward i.1) =
        ∑ i : occupationSourceFiber source s,
          occupationConditionalWeight source mass s i.1 *
            reward i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [occupationPolicyPMF_toReal]
      have hisource : source i.1 = s :=
        occupationSourceFiber_source_eq source i
      simp [occupationConditionalWeight, hisource]
    _ =
        ∑ i,
          occupationConditionalWeight source mass s i *
            reward i := by
      rw [← Finset.sum_subtype
        (occupationSourceFiber source s)
        (fun _ => Iff.rfl)
        (fun i =>
          occupationConditionalWeight source mass s i * reward i)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hne : source i ≠ s := by
        simpa [occupationSourceFiber] using hi
      simp [occupationConditionalWeight, hne]

/-- Testing normalized source masses and their conditional weights against
an operational reward recovers its normalized mass-weighted average. This
identity does not use transition balance. -/
theorem normalizedSourcePolicy_reward_eq
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (reward : I → ℝ) :
    (∑ s,
        (occupationSourceMass source mass s /
            occupationTotalMass mass) *
          ∑ i,
            occupationConditionalWeight source mass s i *
              reward i) =
      (∑ i, mass i * reward i) /
        occupationTotalMass mass := by
  calc
    (∑ s,
        (occupationSourceMass source mass s /
            occupationTotalMass mass) *
          ∑ i,
            occupationConditionalWeight source mass s i *
              reward i) =
        (∑ s, ∑ i,
          (occupationSourceMass source mass s *
              occupationConditionalWeight source mass s i) *
            reward i) /
          occupationTotalMass mass := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ =
        (∑ s, ∑ i,
          (if source i = s then mass i else 0) *
            reward i) /
          occupationTotalMass mass := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      rw [occupationSourceMass_mul_conditionalWeight
        source hmass]
    _ =
        (∑ i, mass i * reward i) /
          occupationTotalMass mass := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_eq_single (source i)]
      · simp
      · intro s hs
        simp [Ne.symm hs]

/-- The actual invariant PMF followed by the actual source policy realizes
the normalized mass-weighted operational reward. -/
theorem occupationInvariantPMF_policyReward_eq
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (reward : I → ℝ) :
    (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          ∑ i : occupationSourceFiber source s.1,
            (occupationPolicyPMF source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s) i).toReal *
              reward i.1) =
      (∑ i, mass i * reward i) /
        occupationTotalMass mass := by
  calc
    (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          ∑ i : occupationSourceFiber source s.1,
            (occupationPolicyPMF source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s) i).toReal *
              reward i.1) =
        ∑ s : occupationActiveStates source mass,
          (occupationSourceMass source mass s.1 /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s.1 i *
                reward i := by
      apply Finset.sum_congr rfl
      intro s _
      rw [occupationInvariantPMF_toReal,
        occupationPolicy_reward_eq_conditional]
    _ =
        ∑ s,
          (occupationSourceMass source mass s /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s i *
                reward i := by
      rw [← Finset.sum_subtype
        (occupationActiveStates source mass)
        (fun _ => Iff.rfl)
        (fun s =>
          (occupationSourceMass source mass s /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s i *
                reward i)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      rw [occupationSourceMass_eq_zero_of_not_active
        source hmass hs]
      simp
    _ =
        (∑ i, mass i * reward i) /
          occupationTotalMass mass :=
      normalizedSourcePolicy_reward_eq
        source hmass reward

/-- Positive mass-weighted reward yields positive stationary operational
reward. This is the unconditional conclusion of a positive charged
circulation once its charge has been identified with an actual stage reward
up to a balanced potential coboundary. -/
theorem occupationInvariantPMF_policyReward_pos
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (reward : I → ℝ)
    (hreward : 0 < ∑ i, mass i * reward i) :
    0 <
      ∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          ∑ i : occupationSourceFiber source s.1,
            (occupationPolicyPMF source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s) i).toReal *
              reward i.1 := by
  rw [occupationInvariantPMF_policyReward_eq
    source hmass htotal reward]
  exact div_pos hreward htotal

/-- A normalized charged circulation has positive stationary stage reward
when, with its actual forward sign, the charge is stage reward plus a
potential coboundary. Balance cancels the coboundary.

The decomposition hypothesis is essential: a formally reversed statistical
charge does not by itself identify a profitable forward stage response. -/
theorem occupationInvariantPMF_stageReward_eq_of_chargeDecomposition
    [Fintype S] [Fintype I] [DecidableEq S]
    (column : I → S → ℝ) (source : I → S)
    {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (charge stage : I → ℝ) (potential : S → ℝ)
    (hbalance :
      ∀ destination,
        ∑ i, mass i * column i destination = 0)
    (hcharge : ∑ i, mass i * charge i = 1)
    (hdecompose :
      ∀ i, charge i =
        stage i + ∑ destination,
          potential destination * column i destination) :
    (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          ∑ i : occupationSourceFiber source s.1,
            (occupationPolicyPMF source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s) i).toReal *
              stage i.1) =
      1 / occupationTotalMass mass := by
  have hdrift :=
    balancedMass_weightedPotentialDrift_eq_zero
      column mass hbalance potential
  have hstage : ∑ i, mass i * stage i = 1 := by
    calc
      (∑ i, mass i * stage i) =
          (∑ i, mass i * charge i) -
            ∑ i, mass i *
              (∑ destination,
                potential destination * column i destination) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [hdecompose i]
        ring
      _ = 1 := by rw [hcharge, hdrift, sub_zero]
  rw [occupationInvariantPMF_policyReward_eq
    source hmass htotal stage, hstage]

/-- A positive stationary operational reward is witnessed at some active
source state. The witness is an entry state for the stationary response
itself; this theorem does not claim that the state is reachable from an
external parent construction. -/
theorem exists_activeState_policyReward_pos
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (reward : I → ℝ)
    (hreward : 0 < ∑ i, mass i * reward i) :
    ∃ s : occupationActiveStates source mass,
      0 <
        ∑ i : occupationSourceFiber source s.1,
          (occupationPolicyPMF source mass hmass
            (occupationActiveState_sourceMass_pos
              source mass s) i).toReal *
            reward i.1 := by
  have havg :=
    occupationInvariantPMF_policyReward_pos
      source hmass htotal reward hreward
  by_contra hnone
  push Not at hnone
  have hnonpos :
      (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          ∑ i : occupationSourceFiber source s.1,
            (occupationPolicyPMF source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s) i).toReal *
              reward i.1) ≤ 0 := by
    exact Finset.sum_nonpos fun s _ =>
      mul_nonpos_of_nonneg_of_nonpos
        ENNReal.toReal_nonneg (hnone s)
  exact (not_lt_of_ge hnonpos) havg

/-- The PMF of normalized active source masses is invariant under the
induced active-state Markov kernel. -/
theorem occupationInvariantPMF_stationary
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          ((kernel i destination).toReal -
            if destination = source i then 1 else 0) = 0)
    (destination : occupationActiveStates source mass) :
    (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          (occupationActiveKernel
            kernel source mass hmass hbalance s destination).toReal) =
      (occupationInvariantPMF
        source mass hmass htotal destination).toReal := by
  have hfull :=
    normalizedSourceMass_stationary
      (fun i u => (kernel i u).toReal)
      source hmass htotal hbalance destination.1
  calc
    (∑ s : occupationActiveStates source mass,
        (occupationInvariantPMF
          source mass hmass htotal s).toReal *
          (occupationActiveKernel
            kernel source mass hmass hbalance s destination).toReal) =
        ∑ s : occupationActiveStates source mass,
          (occupationSourceMass source mass s.1 /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s.1 i *
                (kernel i destination.1).toReal := by
      apply Finset.sum_congr rfl
      intro s _
      rw [occupationInvariantPMF_toReal,
        occupationActiveKernel_toReal,
        occupationOperationalKernel_toReal_eq_conditional]
    _ =
        ∑ s,
          (occupationSourceMass source mass s /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s i *
                (kernel i destination.1).toReal := by
      rw [← Finset.sum_subtype
        (occupationActiveStates source mass)
        (fun _ => Iff.rfl)
        (fun s =>
          (occupationSourceMass source mass s /
              occupationTotalMass mass) *
            ∑ i,
              occupationConditionalWeight source mass s i *
                (kernel i destination.1).toReal)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      rw [occupationSourceMass_eq_zero_of_not_active
        source hmass hs]
      simp
    _ =
        occupationSourceMass source mass destination.1 /
          occupationTotalMass mass := hfull
    _ =
        (occupationInvariantPMF
          source mass hmass htotal destination).toReal := by
      rw [occupationInvariantPMF_toReal]

/-- Under the invariant source law followed by the conditional operational
policy, an individual positive-mass transition is selected with exactly its
normalized occupation frequency. -/
theorem exists_operationalIndex_with_normalizedFrequency
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) {mass : I → ℝ}
    (hmass : ∀ i, 0 ≤ mass i)
    (htotal : 0 < occupationTotalMass mass)
    {i₀ : I} (hi₀ : 0 < mass i₀) :
    ∃ (s₀ : occupationActiveStates source mass)
        (j₀ : occupationSourceFiber source s₀.1),
      s₀.1 = source i₀ ∧
        j₀.1 = i₀ ∧
        (occupationInvariantPMF
            source mass hmass htotal s₀).toReal *
          (occupationPolicyPMF
            source mass hmass
              (occupationActiveState_sourceMass_pos
                source mass s₀) j₀).toReal =
          mass i₀ / occupationTotalMass mass := by
  have hsource :
      0 < occupationSourceMass source mass (source i₀) :=
    occupationSourceMass_pos_of_coordinate_pos
      source hmass hi₀
  let s₀ : occupationActiveStates source mass :=
    ⟨source i₀, by
      simp [occupationActiveStates, hsource]⟩
  let j₀ : occupationSourceFiber source s₀.1 :=
    ⟨i₀, by
      simp [occupationSourceFiber, s₀]⟩
  refine ⟨s₀, j₀, rfl, rfl, ?_⟩
  rw [occupationInvariantPMF_toReal,
    occupationPolicyPMF_toReal]
  dsimp only [j₀, s₀]
  field_simp

namespace AnalyticPositiveCirculation

/-- The normalized invariant frequency of the distinguished transition has
the same power-law exponent as its pole-cleared mass. -/
theorem exists_distinguishedFrequency_powerLowerBound
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {i₀ : I}
    (C : AnalyticPositiveCirculation column i₀) :
    ∃ bound : ℝ, 0 < bound ∧
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        0 < occupationTotalMass (C.mass t) ∧
          (1 / bound) * t ^ C.poleOrder ≤
            C.mass t i₀ /
              occupationTotalMass (C.mass t) := by
  have hanalytic :
      ∀ i, AnalyticAt ℝ (fun t => C.mass t i) 0 := by
    have h := C.analytic_mass
    rw [analyticAt_pi_iff] at h
    exact h
  let bound : ℝ :=
    ∑ i, |C.mass 0 i| + Fintype.card I + 1
  have hbound_pos : 0 < bound := by
    dsimp only [bound]
    positivity
  have hcoordinateBound :
      ∀ i,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          C.mass t i ≤ |C.mass 0 i| + 1 := by
    intro i
    have hcontinuous :
        ContinuousAt (fun t => C.mass t i) 0 :=
      (hanalytic i).continuousAt
    have hnear :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          dist (C.mass t i) (C.mass 0 i) < 1 :=
      ((Metric.tendsto_nhds.mp hcontinuous) 1 zero_lt_one).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hnear] with t ht
    have habs :
        |C.mass t i| < |C.mass 0 i| + 1 := by
      calc
        |C.mass t i| =
            |(C.mass t i - C.mass 0 i) + C.mass 0 i| := by
              ring_nf
        _ ≤ |C.mass t i - C.mass 0 i| + |C.mass 0 i| :=
          abs_add_le _ _
        _ < 1 + |C.mass 0 i| := by
          simpa [Real.dist_eq] using
            add_lt_add_right ht |C.mass 0 i|
        _ = |C.mass 0 i| + 1 := by ring
    exact (le_abs_self _).trans habs.le
  have htotalBound :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        occupationTotalMass (C.mass t) ≤ bound := by
    filter_upwards [Filter.eventually_all.2 hcoordinateBound] with t ht
    calc
      occupationTotalMass (C.mass t) ≤
          ∑ i, (|C.mass 0 i| + 1) :=
        Finset.sum_le_sum fun i _ => ht i
      _ ≤ bound := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]
        dsimp only [bound]
        norm_num
  refine ⟨bound, hbound_pos, ?_⟩
  filter_upwards [C.eventual, htotalBound,
    self_mem_nhdsWithin] with t ht hbound htpos
  have hpow_pos : 0 < t ^ C.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  have htotal_pos :
      0 < occupationTotalMass (C.mass t) :=
    occupationTotalMass_pos_of_coordinate_pos
      ht.1 (i₀ := i₀) (by rw [ht.2.1]; exact hpow_pos)
  refine ⟨htotal_pos, ?_⟩
  rw [ht.2.1]
  have hbound_nonneg : 0 ≤ bound := hbound_pos.le
  have htotal_nonneg :
      0 ≤ occupationTotalMass (C.mass t) := htotal_pos.le
  calc
    (1 / bound) * t ^ C.poleOrder =
        t ^ C.poleOrder / bound := by ring
    _ ≤
        t ^ C.poleOrder /
          occupationTotalMass (C.mass t) := by
      exact div_le_div_of_nonneg_left hpow_pos.le
        htotal_pos hbound

end AnalyticPositiveCirculation

end Probability
end Math
