/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticChargedCirculationLeadingMass

/-!
# The lower-order branch of an analytic charged circulation

Suppose the first nonzero mass term of a pole-cleared analytic charged
circulation occurs strictly below the clearing order.  Dividing out that
first power leaves another honest analytic positive charged circulation.
Its pole order is the remaining degree, and its endpoint mass is the
nonzero, nonnegative, balanced, zero-charge leading circulation.

This is the exact positivity-preserving continuation available at this
point.  It decreases the pole order when the removed mass order is positive.
When the mass order is zero, it cannot decrease: the residual mass is already
nonzero at the endpoint, so extracting its leading mass again necessarily
returns order zero.  The final example shows that this stagnant case really
occurs.  Advancing further then requires a signed coefficient ladder; one
cannot obtain it by subtracting the endpoint mass while preserving
nonnegativity.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

namespace AnalyticPositiveChargedCirculation

/-- Divide the mass by its first nonzero scalar power.  In the lower-order
branch this retains an exact positive charged-circulation identity with the
remaining pole degree. -/
def LeadingMassJet.lowerOrderResidual
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder) :
    AnalyticPositiveChargedCirculation column charge where
  poleOrder := C.poleOrder - jet.order
  mass := jet.factor
  analytic_mass := jet.analytic_factor
  eventual := by
    filter_upwards [
      C.eventual,
      jet.mass_eq.filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
        t hC hmass ht
    have htpos : 0 < t := mem_Ioi.mp ht
    have hpow_ne : t ^ jet.order ≠ 0 :=
      pow_ne_zero jet.order (ne_of_gt htpos)
    refine ⟨?_, ?_, ?_⟩
    · intro index
      have hnonneg := hC.1 index
      rw [hmass] at hnonneg
      simp only [Pi.smul_apply, smul_eq_mul] at hnonneg
      exact (mul_nonneg_iff_of_pos_left
        (pow_pos htpos jet.order)).mp hnonneg
    · intro destination
      have hbalance := hC.2.1 destination
      rw [hmass] at hbalance
      simp only [Pi.smul_apply, smul_eq_mul] at hbalance
      have hfactored :
          t ^ jet.order *
              (∑ index,
                jet.factor t index * column t index destination) =
            0 := by
        rw [Finset.mul_sum]
        simpa only [mul_assoc] using hbalance
      exact (mul_eq_zero.mp hfactored).resolve_left hpow_ne
    · have hcharge := hC.2.2
      rw [hmass] at hcharge
      simp only [Pi.smul_apply, smul_eq_mul] at hcharge
      have hfactored :
          t ^ jet.order *
              (∑ index,
                jet.factor t index * charge t index) =
            t ^ C.poleOrder := by
        rw [Finset.mul_sum]
        simpa only [mul_assoc] using hcharge
      have hpole :
          C.poleOrder =
            jet.order + (C.poleOrder - jet.order) := by
        omega
      rw [hpole, pow_add] at hfactored
      exact mul_left_cancel₀ hpow_ne hfactored

/-- The residual pole degree is positive in the strict lower-order branch. -/
theorem LeadingMassJet.lowerOrderResidual_poleOrder_pos
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder) :
    0 < (jet.lowerOrderResidual horder).poleOrder := by
  change 0 < C.poleOrder - jet.order
  exact Nat.sub_pos_of_lt horder

/-- Removing a positive leading mass order strictly decreases the pole
degree. -/
theorem LeadingMassJet.lowerOrderResidual_poleOrder_lt
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder)
    (order_pos : 0 < jet.order) :
    (jet.lowerOrderResidual horder).poleOrder < C.poleOrder := by
  change C.poleOrder - jet.order < C.poleOrder
  omega

/-- Exact rank criterion: residualization decreases the pole degree precisely
when the removed leading order is positive. -/
theorem LeadingMassJet.lowerOrderResidual_poleOrder_lt_iff
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder) :
    (jet.lowerOrderResidual horder).poleOrder < C.poleOrder ↔
      0 < jet.order := by
  change C.poleOrder - jet.order < C.poleOrder ↔ 0 < jet.order
  omega

/-- The residual endpoint mass is exactly the original leading mass and is
therefore nonzero. -/
theorem LeadingMassJet.lowerOrderResidual_mass_zero_ne
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder) :
    (jet.lowerOrderResidual horder).mass 0 ≠ 0 :=
  jet.leading_ne_zero

/-- Any leading-mass extraction from a circulation whose endpoint mass is
already nonzero has order zero. -/
theorem LeadingMassJet.order_eq_zero_of_mass_zero_ne
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (mass_zero_ne : C.mass 0 ≠ 0) :
    jet.order = 0 := by
  by_contra horder
  have order_pos : 0 < jet.order := Nat.pos_of_ne_zero horder
  have hmass := jet.mass_eq.self_of_nhds
  have mass_zero : C.mass 0 = 0 := by
    rw [hmass]
    funext index
    simp [Nat.ne_of_gt order_pos]
  exact mass_zero_ne mass_zero

/-- Reapplying leading-mass extraction to the lower-order residual cannot
advance to a later coefficient: its mass order is necessarily zero. -/
theorem LeadingMassJet.lowerOrderResidual_next_order_eq_zero
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder)
    (next : (jet.lowerOrderResidual horder).LeadingMassJet) :
    next.order = 0 :=
  next.order_eq_zero_of_mass_zero_ne
    (jet.lowerOrderResidual_mass_zero_ne horder)

section StagnantExample

/-- Zero occupation columns for the two-coordinate delayed-charge example. -/
def delayedChargeColumn :
    ℝ → Bool → PUnit → ℝ :=
  fun _ _ _ => 0

/-- Only the second coordinate carries charge. -/
def delayedCharge :
    ℝ → Bool → ℝ :=
  fun _ index => if index then 1 else 0

/-- A constant zero-charge circulation plus a charged component appearing
at order `poleOrder`. -/
def delayedChargeMass (poleOrder : ℕ) :
    ℝ → Bool → ℝ :=
  fun t index => if index then t ^ poleOrder else 1

/-- The stagnant lower-order branch is realizable: a nonzero endpoint
zero-charge circulation can coexist with unit charge first appearing at any
positive later degree. -/
def delayedChargeCirculation (poleOrder : ℕ) :
    AnalyticPositiveChargedCirculation
      delayedChargeColumn delayedCharge where
  poleOrder := poleOrder
  mass := delayedChargeMass poleOrder
  analytic_mass := by
    rw [analyticAt_pi_iff]
    intro index
    cases index
    · simpa only [delayedChargeMass, Bool.false_eq_true, if_false] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0)
    · change AnalyticAt ℝ (fun x : ℝ => x ^ poleOrder) 0
      exact
        (show AnalyticAt ℝ (fun x : ℝ => x) 0 from analyticAt_id).pow
          poleOrder
  eventual := by
    filter_upwards [
      (self_mem_nhdsWithin :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
        t ht
    refine ⟨?_, ?_, ?_⟩
    · intro index
      cases index <;>
        simp [delayedChargeMass, pow_nonneg (le_of_lt (mem_Ioi.mp ht))]
    · intro destination
      simp [delayedChargeColumn]
    · simp [delayedChargeMass, delayedCharge]

/-- Its constant endpoint mass is an explicit leading jet of order zero. -/
def delayedChargeLeadingMassJet
    (poleOrder : ℕ) (poleOrder_pos : 0 < poleOrder) :
    (delayedChargeCirculation poleOrder).LeadingMassJet where
  order := 0
  factor := delayedChargeMass poleOrder
  analytic_factor := by
    rw [analyticAt_pi_iff]
    intro index
    cases index
    · simpa only [delayedChargeMass, Bool.false_eq_true, if_false] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) 0)
    · change AnalyticAt ℝ (fun x : ℝ => x ^ poleOrder) 0
      exact
        (show AnalyticAt ℝ (fun x : ℝ => x) 0 from analyticAt_id).pow
          poleOrder
  leading_ne_zero := by
    intro hzero
    have hfalse := congrFun hzero false
    simp [delayedChargeMass] at hfalse
  mass_eq := by
    filter_upwards [] with t
    simp [delayedChargeCirculation]
  leading_nonnegative := by
    intro index
    cases index <;> simp [delayedChargeMass]
  endpoint_balance := by
    intro destination
    simp [delayedChargeColumn]
  order_le_poleOrder := Nat.zero_le poleOrder
  endpoint_weightedCharge := by
    have hpole_ne : poleOrder ≠ 0 := Nat.ne_of_gt poleOrder_pos
    change
      (∑ index : Bool,
        delayedChargeMass poleOrder 0 index *
          delayedCharge 0 index) =
        if 0 = poleOrder then 1 else 0
    rw [if_neg (Nat.ne_of_lt poleOrder_pos)]
    simp [delayedChargeMass, delayedCharge, hpole_ne]

/-- In the explicit example, positivity-preserving residualization leaves
the pole degree unchanged. -/
theorem delayedChargeResidual_poleOrder_eq
    (poleOrder : ℕ) (poleOrder_pos : 0 < poleOrder) :
    ((delayedChargeLeadingMassJet poleOrder poleOrder_pos).lowerOrderResidual
      poleOrder_pos).poleOrder = poleOrder := by
  change poleOrder - 0 = poleOrder
  omega

end StagnantExample

end AnalyticPositiveChargedCirculation

end Probability
end Math
