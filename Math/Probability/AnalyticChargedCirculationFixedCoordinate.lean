/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection
import Math.Probability.AnalyticChargedCirculationLowerOrder

/-!
# A fixed charged coordinate of an analytic circulation

The exact moving charge identity of an analytic positive charged
circulation is already strong enough to select one fixed coordinate.  That
coordinate carries at least the average total charge on a punctured
neighborhood.  Since its mass is nonnegative, both its mass and its charge
are eventually strictly positive.

Continuity bounds the selected mass from above.  Dividing the average-share
bound by this fixed upper bound gives a power-law lower bound for the charge
itself, with the original pole-clearing order.

This conclusion remains valid in the stagnant order-zero lower branch.  It
is deliberately a moving-parameter coordinate witness, not an endpoint
circulation: one coordinate need not balance the occupation columns, and
its endpoint mass or endpoint charge may vanish.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

namespace AnalyticPositiveChargedCirculation

/-- One fixed coordinate carrying a quantitative share of the moving
charge of an analytic positive charged circulation. -/
structure FixedPositiveCoordinate
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge) where
  index : I
  massBound : ℝ
  massBound_pos : 0 < massBound
  chargeMargin : ℝ
  chargeMargin_pos : 0 < chargeMargin
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      0 < C.mass t index ∧
        C.mass t index ≤ massBound ∧
        (Fintype.card I : ℝ)⁻¹ * t ^ C.poleOrder ≤
          C.mass t index * charge t index ∧
        chargeMargin * t ^ C.poleOrder ≤ charge t index ∧
        0 < charge t index

/-- Every analytic positive charged circulation has a fixed coordinate
whose mass-charge product carries at least the average total charge.  The
coordinate's charge alone has a positive lower bound at the original
clearing order. -/
theorem exists_fixedPositiveCoordinate
    [Fintype S] [Fintype I] [Nonempty I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0) :
    Nonempty (FixedPositiveCoordinate C) := by
  let term : I → ℝ → ℝ := fun index t =>
    C.mass t index * charge t index
  have analytic_term :
      ∀ index, AnalyticAt ℝ (term index) 0 := by
    intro index
    exact
      (analyticAt_pi_iff.mp C.analytic_mass index).mul
        (analytic_charge index)
  obtain ⟨index, index_max⟩ :=
    finite_analytic_family_eventually_fixed_maximizer
      term analytic_term
  have card_pos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have average_share :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (Fintype.card I : ℝ)⁻¹ * t ^ C.poleOrder ≤
          term index t := by
    filter_upwards [index_max, C.eventual] with t hmax hC
    rw [← hC.2.2]
    rw [inv_mul_le_iff₀ card_pos]
    calc
      ∑ coordinate, C.mass t coordinate * charge t coordinate ≤
          ∑ _coordinate : I, term index t := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact hmax coordinate
      _ = (Fintype.card I : ℝ) * term index t := by simp
  have positive :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        0 < C.mass t index ∧ 0 < charge t index := by
    filter_upwards [
      average_share,
      C.eventual,
      self_mem_nhdsWithin] with t hshare hC ht
    have share_pos :
        0 <
          (Fintype.card I : ℝ)⁻¹ * t ^ C.poleOrder :=
      mul_pos (inv_pos.mpr card_pos)
        (pow_pos (mem_Ioi.mp ht) C.poleOrder)
    have product_pos :
        0 < C.mass t index * charge t index := by
      exact share_pos.trans_le hshare
    rcases mul_pos_iff.mp product_pos with
      both_pos | both_neg
    · exact both_pos
    · exact False.elim
        ((not_lt_of_ge (hC.1 index)) both_neg.1)
  let massBound : ℝ := |C.mass 0 index| + 1
  have massBound_pos : 0 < massBound := by
    dsimp only [massBound]
    linarith [abs_nonneg (C.mass 0 index)]
  have mass_bounded :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        C.mass t index ≤ massBound := by
    have abs_tendsto :
        Tendsto (fun t => |C.mass t index|)
          (nhds 0) (nhds |C.mass 0 index|) :=
      (analyticAt_pi_iff.mp C.analytic_mass index).continuousAt.abs.tendsto
    have abs_lt :
        ∀ᶠ t in nhds 0,
          |C.mass t index| < massBound :=
      abs_tendsto.eventually_lt_const
        (by
          dsimp only [massBound]
          linarith)
    filter_upwards [
      abs_lt.filter_mono nhdsWithin_le_nhds] with t ht
    exact (le_abs_self (C.mass t index)).trans ht.le
  let chargeMargin : ℝ :=
    ((Fintype.card I : ℝ) * massBound)⁻¹
  have chargeMargin_pos : 0 < chargeMargin := by
    exact inv_pos.mpr (mul_pos card_pos massBound_pos)
  have charge_lower :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        chargeMargin * t ^ C.poleOrder ≤ charge t index := by
    filter_upwards [
      average_share,
      positive,
      mass_bounded] with t hshare hpositive hmass
    have product_le :
        C.mass t index * charge t index ≤
          massBound * charge t index :=
      mul_le_mul_of_nonneg_right hmass hpositive.2.le
    calc
      chargeMargin * t ^ C.poleOrder =
          massBound⁻¹ *
            ((Fintype.card I : ℝ)⁻¹ *
              t ^ C.poleOrder) := by
        dsimp only [chargeMargin]
        field_simp
      _ ≤ massBound⁻¹ *
          (massBound * charge t index) := by
        exact mul_le_mul_of_nonneg_left
          (hshare.trans product_le)
          (inv_nonneg.mpr massBound_pos.le)
      _ = charge t index := by
        rw [← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt massBound_pos)]
        exact one_mul _
  exact ⟨{
    index := index
    massBound := massBound
    massBound_pos := massBound_pos
    chargeMargin := chargeMargin
    chargeMargin_pos := chargeMargin_pos
    eventual := by
      filter_upwards [
        positive,
        mass_bounded,
        average_share,
        charge_lower] with t hpositive hmass hshare hlower
      exact
        ⟨hpositive.1, hmass, hshare, hlower, hpositive.2⟩
  }⟩

/-- In particular, the positivity-preserving residual of every strict
lower-order leading jet has a fixed quantitative charged coordinate.  This
also covers the stagnant case in which the original leading order is zero.
-/
theorem LeadingMassJet.lowerOrderResidual_exists_fixedPositiveCoordinate
    [Fintype S] [Fintype I] [Nonempty I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : C.LeadingMassJet) (horder : jet.order < C.poleOrder)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0) :
    Nonempty
      (FixedPositiveCoordinate
        (jet.lowerOrderResidual horder)) :=
  (jet.lowerOrderResidual horder).exists_fixedPositiveCoordinate
    analytic_charge

namespace VanishingEndpointChargeCounterexample

/-- All occupation columns vanish in the endpoint-charge counterexample. -/
def column :
    ℝ → Bool → PUnit → ℝ :=
  fun _ _ _ => 0

/-- The second coordinate's charge vanishes to the prescribed order. -/
def charge (poleOrder : ℕ) :
    ℝ → Bool → ℝ :=
  fun t index => if index then t ^ poleOrder else 0

/-- Both coordinates have constant positive mass. -/
def mass :
    ℝ → Bool → ℝ :=
  fun _ _ => 1

/-- A positive analytic charged circulation can have nonzero endpoint mass
while every endpoint charge is zero. -/
def circulation (poleOrder : ℕ) :
    AnalyticPositiveChargedCirculation
      column (charge poleOrder) where
  poleOrder := poleOrder
  mass := mass
  analytic_mass := by
    rw [analyticAt_pi_iff]
    intro index
    exact analyticAt_const
  eventual := by
    filter_upwards [] with t
    refine ⟨fun _ => zero_le_one, ?_, ?_⟩
    · intro destination
      simp [column]
    · simp [mass, charge]

/-- When the clearing order is positive, the endpoint family has no
normalized positive charged circulation at all.  Thus a signed coefficient
ladder cannot generally be replaced by a later nonnegative endpoint
circulation. -/
theorem no_endpoint_positiveChargedCirculation
    (poleOrder : ℕ) (poleOrder_pos : 0 < poleOrder) :
    ¬HasNormalizedPositiveChargedCirculation
      (column 0) (charge poleOrder 0) := by
  rintro ⟨endpointMass, _mass_nonnegative, _balance, weightedCharge⟩
  have poleOrder_ne : poleOrder ≠ 0 :=
    Nat.ne_of_gt poleOrder_pos
  simp [charge, poleOrder_ne] at weightedCharge

end VanishingEndpointChargeCounterexample

end AnalyticPositiveChargedCirculation

end Probability
end Math
