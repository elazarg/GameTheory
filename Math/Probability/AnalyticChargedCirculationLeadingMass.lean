/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.Probability.AnalyticChargedOccupationFlow

/-!
# Leading Mass of an Analytic Charged Circulation

A pole-cleared analytic positive charged circulation cannot have the zero mass
germ: its weighted charge is an exact positive power on the punctured
interval.  This file extracts the first nonzero homogeneous mass coefficient.

When the columns and charges are analytic, that leading coefficient is a
nonzero nonnegative circulation for the endpoint columns.  Its order is no
larger than the clearing order.  At the endpoint its weighted charge is zero
below the clearing order and one at the clearing order.
-/

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

namespace AnalyticPositiveChargedCirculation

/-- The first nonzero homogeneous coefficient of the analytic mass in a
pole-cleared positive charged circulation. -/
structure LeadingMassJet
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge) where
  order : ℕ
  factor : ℝ → I → ℝ
  analytic_factor : AnalyticAt ℝ factor 0
  leading_ne_zero : factor 0 ≠ 0
  mass_eq :
    ∀ᶠ t in nhds 0, C.mass t = t ^ order • factor t
  leading_nonnegative : ∀ index, 0 ≤ factor 0 index
  endpoint_balance :
    ∀ destination,
      ∑ index, factor 0 index * column 0 index destination = 0
  order_le_poleOrder : order ≤ C.poleOrder
  endpoint_weightedCharge :
    (∑ index, factor 0 index * charge 0 index) =
      if order = C.poleOrder then 1 else 0

private theorem mass_order_ne_top
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge) :
    analyticOrderAt C.mass 0 ≠ ⊤ := by
  intro htop
  have hmass_zero :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), C.mass t = 0 :=
    (analyticOrderAt_eq_top.mp htop).filter_mono
      nhdsWithin_le_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  obtain ⟨t, ht, hzero, htpos⟩ :=
    (C.eventual.and
      (hmass_zero.and
        (self_mem_nhdsWithin :
          ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0))).exists
  have hpow_pos : 0 < t ^ C.poleOrder :=
    pow_pos htpos C.poleOrder
  rw [hzero] at ht
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at ht
  exact (ne_of_gt hpow_pos) ht.2.2.symm

private theorem eventual_factor_nonnegative
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (order : ℕ) (factor : ℝ → I → ℝ)
    (mass_eq :
      ∀ᶠ t in nhds 0, C.mass t = t ^ order • factor t) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0), ∀ index, 0 ≤ factor t index := by
  filter_upwards [
    C.eventual,
    mass_eq.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
      t ht hmass htpos
  intro index
  have hpow_pos : 0 < t ^ order := pow_pos htpos order
  have hmass_nonnegative := ht.1 index
  rw [hmass] at hmass_nonnegative
  simp only [Pi.smul_apply, smul_eq_mul] at hmass_nonnegative
  exact (mul_nonneg_iff_of_pos_left hpow_pos).mp hmass_nonnegative

private theorem endpoint_factor_nonnegative
    [Fintype I]
    {factor : ℝ → I → ℝ}
    (analytic_factor : AnalyticAt ℝ factor 0)
    (eventual_nonnegative :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), ∀ index, 0 ≤ factor t index) :
    ∀ index, 0 ≤ factor 0 index := by
  intro index
  have hlimit :
      Tendsto (fun t => factor t index)
        (nhdsWithin 0 (Ioi 0)) (nhds (factor 0 index)) :=
    (analyticAt_pi_iff.mp analytic_factor index).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
    (eventual_nonnegative.mono fun t ht => ht index)

private theorem eventual_factor_balance
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (order : ℕ) (factor : ℝ → I → ℝ)
    (mass_eq :
      ∀ᶠ t in nhds 0, C.mass t = t ^ order • factor t) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ destination,
        ∑ index, factor t index * column t index destination = 0 := by
  filter_upwards [
    C.eventual,
    mass_eq.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
      t ht hmass htpos
  intro destination
  have hbalance_raw := ht.2.1 destination
  rw [hmass] at hbalance_raw
  simp only [Pi.smul_apply, smul_eq_mul] at hbalance_raw
  have hbalance :
      t ^ order *
          (∑ index, factor t index * column t index destination) =
        0 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc] using hbalance_raw
  exact (mul_eq_zero.mp hbalance).resolve_left
    (pow_ne_zero order (ne_of_gt htpos))

private theorem endpoint_factor_balance
    [Finite S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    {factor : ℝ → I → ℝ}
    (analytic_factor : AnalyticAt ℝ factor 0)
    (eventual_balance :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ destination,
          ∑ index, factor t index * column t index destination = 0) :
    ∀ destination,
      ∑ index, factor 0 index * column 0 index destination = 0 := by
  intro destination
  let balance : ℝ → ℝ := fun t =>
    ∑ index, factor t index * column t index destination
  have balance_analytic : AnalyticAt ℝ balance 0 := by
    dsimp only [balance]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    exact (analyticAt_pi_iff.mp analytic_factor index).mul
      (analytic_column index destination)
  have balance_zero :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), balance t = 0 :=
    eventual_balance.mono fun t ht => ht destination
  have balance_limit :
      Tendsto balance (nhdsWithin 0 (Ioi 0)) (nhds (balance 0)) :=
    balance_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have zero_limit :
      Tendsto balance (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_const_nhds.congr'
      (balance_zero.mono fun _ ht => ht.symm)
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique balance_limit zero_limit

private theorem eventual_factor_weightedCharge
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (order : ℕ) (factor : ℝ → I → ℝ)
    (mass_eq :
      ∀ᶠ t in nhds 0, C.mass t = t ^ order • factor t) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ^ order * (∑ index, factor t index * charge t index) =
        t ^ C.poleOrder := by
  filter_upwards [
    C.eventual,
    mass_eq.filter_mono nhdsWithin_le_nhds] with
      t ht hmass
  have hcharge := ht.2.2
  rw [hmass] at hcharge
  simp only [Pi.smul_apply, smul_eq_mul] at hcharge
  rw [Finset.mul_sum]
  simpa only [mul_assoc] using hcharge

private theorem factor_order_le_poleOrder
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (order : ℕ) (factor : ℝ → I → ℝ)
    (analytic_factor : AnalyticAt ℝ factor 0)
    (weightedCharge :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ^ order * (∑ index, factor t index * charge t index) =
          t ^ C.poleOrder) :
    order ≤ C.poleOrder := by
  let weighted : ℝ → ℝ := fun t =>
    ∑ index, factor t index * charge t index
  have weighted_analytic : AnalyticAt ℝ weighted 0 := by
    dsimp only [weighted]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    exact (analyticAt_pi_iff.mp analytic_factor index).mul
      (analytic_charge index)
  by_contra hle
  have hpole_lt : C.poleOrder < order := Nat.lt_of_not_ge hle
  have horder :
      order = C.poleOrder + (order - C.poleOrder) := by
    omega
  have normalized_eq :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ^ (order - C.poleOrder) * weighted t = 1 := by
    filter_upwards [
      weightedCharge,
      (self_mem_nhdsWithin :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
        t ht htpos
    rw [horder, pow_add] at ht
    apply mul_left_cancel₀ (pow_ne_zero C.poleOrder (ne_of_gt htpos))
    simpa only [weighted, mul_assoc, mul_one] using ht
  let normalized : ℝ → ℝ := fun t =>
    t ^ (order - C.poleOrder) * weighted t
  have normalized_analytic : AnalyticAt ℝ normalized 0 := by
    exact analyticAt_id.pow (order - C.poleOrder) |>.mul weighted_analytic
  have normalized_limit :
      Tendsto normalized (nhdsWithin 0 (Ioi 0)) (nhds (normalized 0)) :=
    normalized_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have one_limit :
      Tendsto normalized (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
    tendsto_const_nhds.congr'
      (normalized_eq.mono fun _ ht => ht.symm)
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  have endpoint_eq : normalized 0 = 1 :=
    tendsto_nhds_unique normalized_limit one_limit
  have hdiff_ne : order - C.poleOrder ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt hpole_lt)
  simp [normalized, hdiff_ne] at endpoint_eq

private theorem endpoint_factor_weightedCharge
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (order : ℕ) (factor : ℝ → I → ℝ)
    (analytic_factor : AnalyticAt ℝ factor 0)
    (order_le : order ≤ C.poleOrder)
    (weightedCharge :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ^ order * (∑ index, factor t index * charge t index) =
          t ^ C.poleOrder) :
    (∑ index, factor 0 index * charge 0 index) =
      if order = C.poleOrder then 1 else 0 := by
  let weighted : ℝ → ℝ := fun t =>
    ∑ index, factor t index * charge t index
  have weighted_analytic : AnalyticAt ℝ weighted 0 := by
    dsimp only [weighted]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    exact (analyticAt_pi_iff.mp analytic_factor index).mul
      (analytic_charge index)
  have hpole :
      C.poleOrder = order + (C.poleOrder - order) := by
    omega
  have weighted_eq :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        weighted t = t ^ (C.poleOrder - order) := by
    filter_upwards [
      weightedCharge,
      (self_mem_nhdsWithin :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioi 0)] with
        t ht htpos
    rw [hpole, pow_add] at ht
    exact mul_left_cancel₀ (pow_ne_zero order (ne_of_gt htpos))
      (by simpa only [weighted, mul_assoc] using ht)
  have weighted_limit :
      Tendsto weighted (nhdsWithin 0 (Ioi 0)) (nhds (weighted 0)) :=
    weighted_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have power_limit :
      Tendsto weighted (nhdsWithin 0 (Ioi 0))
        (nhds (0 ^ (C.poleOrder - order))) :=
    (((analyticAt_id :
        AnalyticAt ℝ (fun t : ℝ => t) 0).pow
          (C.poleOrder - order)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr'
      (weighted_eq.mono fun _ ht => ht.symm)
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  have endpoint_eq :
      weighted 0 = 0 ^ (C.poleOrder - order) :=
    tendsto_nhds_unique weighted_limit power_limit
  rw [show (∑ index, factor 0 index * charge 0 index) = weighted 0 by rfl,
    endpoint_eq]
  by_cases heq : order = C.poleOrder
  · simp [heq]
  · have hlt : order < C.poleOrder := lt_of_le_of_ne order_le heq
    have hdiff_ne : C.poleOrder - order ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)
    simp [heq, hdiff_ne]

/-- Extract the nonzero nonnegative leading mass circulation at the endpoint.
The endpoint weighted charge records whether the first mass term occurs below
or exactly at the clearing order. -/
theorem exists_leadingMassJet
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge)
    (analytic_column :
      ∀ index destination,
        AnalyticAt ℝ (fun t => column t index destination) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0) :
    Nonempty (LeadingMassJet C) := by
  have order_ne_top := mass_order_ne_top C
  obtain ⟨factor, factor_analytic, factor_ne_zero, mass_eq_raw⟩ :=
    C.analytic_mass.analyticOrderAt_ne_top.mp order_ne_top
  let order := analyticOrderNatAt C.mass 0
  have mass_eq :
      ∀ᶠ t in nhds 0, C.mass t = t ^ order • factor t := by
    simpa only [order, sub_zero, Filter.EventuallyEq] using mass_eq_raw
  have factor_nonnegative :=
    eventual_factor_nonnegative C order factor mass_eq
  have factor_balance :=
    eventual_factor_balance C order factor mass_eq
  have weightedCharge :=
    eventual_factor_weightedCharge C order factor mass_eq
  have order_le :=
    factor_order_le_poleOrder C analytic_charge order factor
      factor_analytic weightedCharge
  exact ⟨{
    order := order
    factor := factor
    analytic_factor := factor_analytic
    leading_ne_zero := factor_ne_zero
    mass_eq := mass_eq
    leading_nonnegative :=
      endpoint_factor_nonnegative factor_analytic factor_nonnegative
    endpoint_balance :=
      endpoint_factor_balance analytic_column factor_analytic factor_balance
    order_le_poleOrder := order_le
    endpoint_weightedCharge :=
      endpoint_factor_weightedCharge C analytic_charge order factor
        factor_analytic order_le weightedCharge
  }⟩

/-- Below the clearing order, the endpoint leading circulation has zero
weighted charge. -/
theorem LeadingMassJet.endpoint_weightedCharge_eq_zero
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : LeadingMassJet C) (horder : jet.order < C.poleOrder) :
    ∑ index, jet.factor 0 index * charge 0 index = 0 := by
  rw [jet.endpoint_weightedCharge]
  simp [ne_of_lt horder]

/-- At the clearing order, the endpoint leading circulation retains unit
weighted charge. -/
theorem LeadingMassJet.endpoint_weightedCharge_eq_one
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    {C : AnalyticPositiveChargedCirculation column charge}
    (jet : LeadingMassJet C) (horder : jet.order = C.poleOrder) :
    ∑ index, jet.factor 0 index * charge 0 index = 1 := by
  rw [jet.endpoint_weightedCharge]
  simp [horder]

end AnalyticPositiveChargedCirculation

end Probability
end Math
