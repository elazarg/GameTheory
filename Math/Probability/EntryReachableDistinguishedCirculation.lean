/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.EntryReachableChargedClass

/-!
# Entry-reachable distinguished occupation circulations

A balanced occupation may have components that cannot be reached from a
supplied entry.  If the source of one positive-mass distinguished transition
is reachable, the component visible from the entry can nevertheless be
retained and normalized so that this transition has unit total charge.

The reachability hypothesis is essential.  Its omission is refuted by
`ChargeLossCounterexample.unrestricted_positive_but_restricted_not`.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S I : Type*}

/-- Indicator charge carried by one distinguished occupation index. -/
def distinguishedOccupationCharge
    [DecidableEq I] (distinguished index : I) : ℝ :=
  if index = distinguished then 1 else 0

/-- Keep only mass whose source is available-reachable from an entry. -/
noncomputable def reachableSourceMass
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ) (index : I) : ℝ := by
  classical
  exact
    if AvailableReachable kernel source entry (source index) then
      mass index
    else 0

theorem reachableSourceMass_eq_of_reachable
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ) (index : I)
    (hreachable :
      AvailableReachable kernel source entry (source index)) :
    reachableSourceMass kernel source entry mass index = mass index := by
  classical
  simp [reachableSourceMass, hreachable]

theorem reachableSourceMass_eq_zero_of_not_reachable
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ) (index : I)
    (hreachable :
      ¬AvailableReachable kernel source entry (source index)) :
    reachableSourceMass kernel source entry mass index = 0 := by
  classical
  simp [reachableSourceMass, hreachable]

/-- Restrict a balanced mass to sources reachable from an entry.

Stationarity implies that no positive mass can flow from an unreachable
source into the forward-closed reachable set.  Consequently the restriction
remains balanced. -/
theorem reachableSourceMass_balance
    [Finite S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ)
    (hmass : ∀ index, 0 ≤ mass index)
    (hbalance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0) :
    ∀ destination,
      ∑ index,
          reachableSourceMass kernel source entry mass index *
            actualOccupationColumn kernel source index destination =
        0 := by
  letI : Fintype S := Fintype.ofFinite S
  classical
  let reachable : S → Prop :=
    AvailableReachable kernel source entry
  let potential : S → ℝ := fun state =>
    if reachable state then 1 else 0
  have hforward {current next : S}
      (hcurrent : reachable current)
      (hstep : AvailableSupportStep kernel source current next) :
      reachable next :=
    hcurrent.tail hstep
  have hkernelExpect_eq_one (index : I)
      (hsource : reachable (source index)) :
      expect (kernel index) potential = 1 := by
    calc
      expect (kernel index) potential =
          expect (kernel index) (fun _ => (1 : ℝ)) := by
        apply ProbabilityMassFunction.expect_congr_of_ne_zero
        intro destination hdestination
        have hstep :
            AvailableSupportStep kernel source
              (source index) destination :=
          ⟨index, rfl, hdestination⟩
        simp [potential, hforward hsource hstep]
      _ = 1 := expect_const _ _
  have hdrift_nonneg (index : I) :
      0 ≤
        expect (kernel index) potential -
          potential (source index) := by
    by_cases hsource : reachable (source index)
    · rw [hkernelExpect_eq_one index hsource]
      simp [potential, hsource]
    · have hexpect :
          0 ≤ expect (kernel index) potential := by
        apply expect_nonneg
        intro state
        by_cases hstate : reachable state <;>
          simp [potential, hstate]
      simpa [potential, hsource] using hexpect
  have hweighted_nonneg (index : I) :
      0 ≤ mass index *
        (expect (kernel index) potential -
          potential (source index)) :=
    mul_nonneg (hmass index) (hdrift_nonneg index)
  have hweighted_sum :
      (∑ index, mass index *
        (expect (kernel index) potential -
          potential (source index))) = 0 := by
    calc
      (∑ index, mass index *
        (expect (kernel index) potential -
          potential (source index))) =
          ∑ index, mass index *
            (∑ state, potential state *
              actualOccupationColumn kernel source index state) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [potential_pair_actualOccupationColumn]
      _ = 0 :=
        balancedMass_weightedPotentialDrift_eq_zero
          (actualOccupationColumn kernel source)
          mass hbalance potential
  have hweighted_zero (index : I) :
      mass index *
          (expect (kernel index) potential -
            potential (source index)) =
        0 := by
    exact
      congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg
          hweighted_nonneg).mp hweighted_sum)
        index
  intro destination
  by_cases hdestination : reachable destination
  · have hunreachable_zero (index : I)
        (hsource : ¬reachable (source index)) :
        mass index *
            actualOccupationColumn kernel source index destination =
          0 := by
      have hsource_ne : destination ≠ source index := by
        intro heq
        apply hsource
        rwa [← heq]
      have hcoordinate_le :
          (kernel index destination).toReal ≤
            expect (kernel index) potential := by
        calc
          (kernel index destination).toReal =
              expect (kernel index) (Pi.single destination 1) := by
            symm
            exact expect_pi_single (kernel index) destination
          _ ≤ expect (kernel index) potential := by
            apply expect_mono
            intro state
            by_cases hstate : state = destination
            · subst state
              simp [potential, hdestination]
            · by_cases hstateReachable : reachable state <;>
                simp [hstate, potential, hstateReachable]
      have hmul_le :
          mass index * (kernel index destination).toReal ≤
            mass index * expect (kernel index) potential :=
        mul_le_mul_of_nonneg_left hcoordinate_le (hmass index)
      have hright :
          mass index * expect (kernel index) potential = 0 := by
        simpa [potential, hsource] using hweighted_zero index
      have hleft_nonneg :
          0 ≤ mass index * (kernel index destination).toReal :=
        mul_nonneg (hmass index) ENNReal.toReal_nonneg
      have hprobability :
          mass index * (kernel index destination).toReal = 0 := by
        rw [hright] at hmul_le
        exact le_antisymm hmul_le hleft_nonneg
      simpa [actualOccupationColumn, hsource_ne] using hprobability
    calc
      (∑ index,
          reachableSourceMass kernel source entry mass index *
            actualOccupationColumn kernel source index destination) =
          ∑ index,
            mass index *
              actualOccupationColumn kernel source index destination := by
        apply Finset.sum_congr rfl
        intro index _
        by_cases hsource : reachable (source index)
        · rw [reachableSourceMass_eq_of_reachable
            kernel source entry mass index hsource]
        · rw [reachableSourceMass_eq_zero_of_not_reachable
            kernel source entry mass index hsource,
            zero_mul, hunreachable_zero index hsource]
      _ = 0 := hbalance destination
  · apply Finset.sum_eq_zero
    intro index _
    by_cases hsource : reachable (source index)
    · have hkernel_zero : kernel index destination = 0 := by
        by_contra hkernel
        apply hdestination
        exact hforward hsource ⟨index, rfl, hkernel⟩
      have hsource_ne : destination ≠ source index := by
        intro heq
        apply hdestination
        simpa [heq] using hsource
      rw [reachableSourceMass_eq_of_reachable
        kernel source entry mass index hsource]
      simp [actualOccupationColumn, hkernel_zero, hsource_ne]
    · rw [reachableSourceMass_eq_zero_of_not_reachable
        kernel source entry mass index hsource, zero_mul]

/-- A reachable positive-mass distinguished transition yields a normalized
entry-reachable circulation carrying its indicator charge.

No claim is made about an unrelated pre-existing charge function. -/
theorem exists_entryReachable_distinguishedCirculation
    [Fintype S] [Fintype I] [DecidableEq S] [DecidableEq I]
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ)
    (hmass : ∀ index, 0 ≤ mass index)
    (hbalance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0)
    (distinguished : I)
    (hdistinguished : 0 < mass distinguished)
    (hreachable :
      AvailableReachable kernel source entry
        (source distinguished)) :
    Nonempty
      (EntryReachablePositiveChargedCirculation
        kernel source
        (distinguishedOccupationCharge distinguished)
        entry) := by
  classical
  let reachableMass : I → ℝ :=
    reachableSourceMass kernel source entry mass
  have hreachableMass_nonneg :
      ∀ index, 0 ≤ reachableMass index := by
    intro index
    by_cases hindex :
        AvailableReachable kernel source entry (source index)
    · change
        0 ≤ reachableSourceMass kernel source entry mass index
      rw [reachableSourceMass_eq_of_reachable
        kernel source entry mass index hindex]
      exact hmass index
    · change
        0 ≤ reachableSourceMass kernel source entry mass index
      rw [reachableSourceMass_eq_zero_of_not_reachable
        kernel source entry mass index hindex]
  have hreachableMass_balance :
      ∀ destination,
        ∑ index, reachableMass index *
          actualOccupationColumn kernel source index destination = 0 := by
    simpa only [reachableMass] using
      reachableSourceMass_balance
        kernel source entry mass hmass hbalance
  have hreachableMass_distinguished :
      reachableMass distinguished = mass distinguished := by
    exact reachableSourceMass_eq_of_reachable
      kernel source entry mass distinguished hreachable
  let normalizedMass : I → ℝ := fun index =>
    reachableMass index / mass distinguished
  have hnormalizedMass_nonneg :
      ∀ index, 0 ≤ normalizedMass index := by
    intro index
    exact div_nonneg
      (hreachableMass_nonneg index) hdistinguished.le
  have hnormalizedMass_balance :
      ∀ destination,
        ∑ index, normalizedMass index *
          actualOccupationColumn kernel source index destination = 0 := by
    intro destination
    calc
      (∑ index, normalizedMass index *
        actualOccupationColumn kernel source index destination) =
          (∑ index, reachableMass index *
            actualOccupationColumn kernel source index destination) /
              mass distinguished := by
        simp only [normalizedMass, div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = 0 := by
        rw [hreachableMass_balance destination, zero_div]
  have hnormalizedMass_charge :
      (∑ index, normalizedMass index *
        distinguishedOccupationCharge distinguished index) = 1 := by
    rw [Fintype.sum_eq_single distinguished]
    · simp [normalizedMass, distinguishedOccupationCharge,
        hreachableMass_distinguished,
        div_self (ne_of_gt hdistinguished)]
    · intro index hindex
      simp [distinguishedOccupationCharge, hindex]
  have hnormalizedSupport :
      ∀ index, 0 < normalizedMass index →
        AvailableReachable kernel source entry (source index) := by
    intro index hpositive
    by_contra hnot
    have hzero :=
      reachableSourceMass_eq_zero_of_not_reachable
        kernel source entry mass index hnot
    simp [normalizedMass, reachableMass, hzero] at hpositive
  have hrestricted :=
    restrict_positiveChargedCirculation_of_mass_support
      kernel source
      (distinguishedOccupationCharge distinguished) entry
      normalizedMass hnormalizedMass_nonneg
      hnormalizedMass_balance hnormalizedMass_charge
      hnormalizedSupport
  exact
    EntryReachablePositiveChargedCirculation.of_hasNormalizedPositiveChargedCirculation
      hrestricted

/-- The same hypotheses produce an entry-reachable closed communicating
class with positive aggregate distinguished-index charge. -/
theorem exists_entryReachable_distinguishedPositiveCommunicatingClass
    [Fintype S] [Fintype I] [DecidableEq S] [DecidableEq I]
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (mass : I → ℝ)
    (hmass : ∀ index, 0 ≤ mass index)
    (hbalance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0)
    (distinguished : I)
    (hdistinguished : 0 < mass distinguished)
    (hreachable :
      AvailableReachable kernel source entry
        (source distinguished)) :
    ∃ C : EntryReachablePositiveChargedCirculation
        kernel source
        (distinguishedOccupationCharge distinguished)
        entry,
      Nonempty (C.PositiveCommunicatingClass) := by
  obtain ⟨C⟩ :=
    exists_entryReachable_distinguishedCirculation
      kernel source entry mass hmass hbalance
      distinguished hdistinguished hreachable
  exact ⟨C, C.exists_positiveCommunicatingClass⟩

end Probability
end Math
