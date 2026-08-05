/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticChargedOccupationFlow

/-!
# Finite-owner analytic charged occupation flows

For each member of a finite owner set, consider a finite analytic family of
occupation columns and charges. Applying the analytic charged-flow
alternative owner by owner yields either a positive charged circulation for
one owner or a scaled charged-occupation potential for every owner.

The potential branch below synchronizes the individual clearing powers. It
uses the largest pole order and multiplies each lower-order potential by the
missing nonnegative power of the parameter. Thus the result has one common
pole order while retaining a separate analytic potential for each owner.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S Owner : Type*}

/-- Owner-indexed analytic charged-occupation potentials sharing one
pole-clearing order. Each owner may have its own finite index type. -/
structure AnalyticOwnerScaledChargedOccupationPotential
    [Fintype S] [Fintype Owner]
    (Index : Owner → Type*) [∀ owner, Fintype (Index owner)]
    (column : ∀ owner, ℝ → Index owner → S → ℝ)
    (charge : ∀ owner, ℝ → Index owner → ℝ) where
  poleOrder : ℕ
  potential : Owner → ℝ → S → ℝ
  analytic_potential :
    ∀ owner, AnalyticAt ℝ (potential owner) 0
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ owner index,
        t ^ poleOrder * charge owner t index ≤
          ∑ destination,
            potential owner t destination *
              column owner t index destination

/-- **Finite-owner analytic charged-flow alternative.**

Either one owner has a pole-cleared analytic positive charged circulation,
or all owners carry analytic scaled charged-occupation potentials with one
common pole-clearing order. The theorem only combines finite-dimensional
flow certificates; it assigns no strategic meaning to the owner index. -/
theorem
    exists_owner_analyticPositiveChargedCirculation_or_commonScaledPotential
    [Fintype S] [Fintype Owner]
    (Index : Owner → Type*) [∀ owner, Fintype (Index owner)]
    (column : ∀ owner, ℝ → Index owner → S → ℝ)
    (charge : ∀ owner, ℝ → Index owner → ℝ)
    (hcolumn :
      ∀ owner index destination,
        AnalyticAt ℝ
          (fun t => column owner t index destination) 0)
    (hcharge :
      ∀ owner index,
        AnalyticAt ℝ (fun t => charge owner t index) 0) :
    (∃ owner,
      Nonempty
        (AnalyticPositiveChargedCirculation
          (column owner) (charge owner))) ∨
    Nonempty
      (AnalyticOwnerScaledChargedOccupationPotential
        Index column charge) := by
  classical
  by_cases hCirculation :
      ∃ owner,
        Nonempty
          (AnalyticPositiveChargedCirculation
            (column owner) (charge owner))
  · exact Or.inl hCirculation
  · have hPotential (owner : Owner) :
        Nonempty
          (AnalyticScaledChargedOccupationPotential
            (column owner) (charge owner)) := by
      rcases
          analyticPositiveChargedCirculation_xor_scaledPotential
            (column owner) (charge owner)
            (hcolumn owner) (hcharge owner) with
        hOwnerCirculation | hOwnerPotential
      · exact False.elim
          (hCirculation ⟨owner, hOwnerCirculation.1⟩)
      · exact hOwnerPotential.1
    let ownerPotential (owner : Owner) :
        AnalyticScaledChargedOccupationPotential
          (column owner) (charge owner) :=
      Classical.choice (hPotential owner)
    let commonPoleOrder : ℕ :=
      Finset.univ.sup fun owner =>
        (ownerPotential owner).poleOrder
    let commonPotential : Owner → ℝ → S → ℝ :=
      fun owner t destination =>
        t ^
            (commonPoleOrder -
              (ownerPotential owner).poleOrder) *
          (ownerPotential owner).potential t destination
    right
    refine ⟨{
      poleOrder := commonPoleOrder
      potential := commonPotential
      analytic_potential := ?_
      eventual := ?_
    }⟩
    · intro owner
      rw [analyticAt_pi_iff]
      intro destination
      exact
        (analyticAt_id.pow
            (commonPoleOrder -
              (ownerPotential owner).poleOrder)).mul
          (analyticAt_pi_iff.mp
            (ownerPotential owner).analytic_potential destination)
    · have hAll :
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            ∀ owner,
              ∀ index,
                t ^ (ownerPotential owner).poleOrder *
                    charge owner t index ≤
                  ∑ destination,
                    (ownerPotential owner).potential t destination *
                      column owner t index destination :=
        Filter.eventually_all.mpr fun owner =>
          (ownerPotential owner).eventual
      filter_upwards [hAll, self_mem_nhdsWithin] with t ht htPositive
      intro owner index
      have hOrder :
          (ownerPotential owner).poleOrder ≤ commonPoleOrder :=
        Finset.le_sup (f := fun candidate =>
          (ownerPotential candidate).poleOrder)
          (Finset.mem_univ owner)
      have hPower :
          0 ≤
            t ^
              (commonPoleOrder -
                (ownerPotential owner).poleOrder) :=
        pow_nonneg (le_of_lt (mem_Ioi.mp htPositive)) _
      have hScaled :=
        mul_le_mul_of_nonneg_left (ht owner index) hPower
      have hPowFactor :
          t ^ commonPoleOrder =
            t ^
                (commonPoleOrder -
                  (ownerPotential owner).poleOrder) *
              t ^ (ownerPotential owner).poleOrder := by
        rw [← pow_add, Nat.sub_add_cancel hOrder]
      calc
        t ^ commonPoleOrder * charge owner t index =
            t ^
                (commonPoleOrder -
                  (ownerPotential owner).poleOrder) *
              (t ^ (ownerPotential owner).poleOrder *
                charge owner t index) := by
          rw [hPowFactor, mul_assoc]
        _ ≤
            t ^
                (commonPoleOrder -
                  (ownerPotential owner).poleOrder) *
              ∑ destination,
                (ownerPotential owner).potential t destination *
                  column owner t index destination :=
          hScaled
        _ =
            ∑ destination,
              commonPotential owner t destination *
                column owner t index destination := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro destination _
          simp only [commonPotential]
          ring

end Probability
end Math
