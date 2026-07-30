/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticChargedOccupationFlow

/-!
# Endpoint coefficients of analytic charged potentials

An analytic scaled charged-occupation potential and an endpoint normalized
positive circulation force complementarity at the endpoint coefficient.  In
particular, the pole-clearing order is positive, the endpoint potential has
nonnegative pairing with every endpoint column, and that pairing vanishes on
every positive-mass circulation column.

This is the strongest conclusion available for arbitrary columns.  Removing
a constant gauge preserves column pairings only when each column has
coordinate sum zero.  The final namespace gives a minimal counterexample:
with one state and two columns, a valid scaled potential can be pure gauge at
every order even though an endpoint normalized positive circulation exists.
Thus the generic data do not determine a first nonconstant gauge-fixed
coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Set

variable {S I : Type*}

/-- Subtract the value at one anchor state from every coordinate. -/
def gaugeFixAt
    (anchor : S) (potential : ℝ → S → ℝ) :
    ℝ → S → ℝ :=
  fun t state => potential t state - potential t anchor

/-- Gauge subtraction preserves pairing with a zero-sum column. -/
theorem sum_gaugeFixAt_mul_eq
    [Fintype S]
    (anchor : S) (potential : ℝ → S → ℝ)
    (column : ℝ → I → S → ℝ)
    {t : ℝ} {index : I}
    (column_zero_sum :
      ∑ state, column t index state = 0) :
    (∑ state,
        gaugeFixAt anchor potential t state *
          column t index state) =
      ∑ state,
        potential t state * column t index state := by
  simp only [gaugeFixAt, sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, column_zero_sum, mul_zero, sub_zero]

namespace AnalyticScaledChargedOccupationPotential

/-- The eventual scaled inequality remains valid at the endpoint by
analytic continuity. -/
theorem endpoint_scaled_inequality
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (index : I) :
    (0 : ℝ) ^ C.poleOrder * charge 0 index ≤
      ∑ state,
        C.potential 0 state * column 0 index state := by
  let lhs : ℝ → ℝ :=
    fun t => t ^ C.poleOrder * charge t index
  let rhs : ℝ → ℝ :=
    fun t =>
      ∑ state,
        C.potential t state * column t index state
  have lhs_analytic : AnalyticAt ℝ lhs 0 := by
    dsimp only [lhs]
    exact (analyticAt_id.pow _).mul (analytic_charge index)
  have rhs_analytic : AnalyticAt ℝ rhs 0 := by
    dsimp only [rhs]
    have rhs_eq :
        (fun t =>
          ∑ state,
            C.potential t state * column t index state) =
          ∑ state : S,
            (fun t => C.potential t state) *
              fun t => column t index state := by
      funext t
      simp
    rw [rhs_eq]
    exact Finset.analyticAt_sum Finset.univ fun state _ =>
      (analyticAt_pi_iff.mp C.analytic_potential state).mul
        (analytic_column index state)
  have lhs_tendsto :
      Tendsto lhs (nhdsWithin 0 (Ioi 0)) (nhds (lhs 0)) :=
    lhs_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have rhs_tendsto :
      Tendsto rhs (nhdsWithin 0 (Ioi 0)) (nhds (rhs 0)) :=
    rhs_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  exact le_of_tendsto_of_tendsto
    lhs_tendsto rhs_tendsto
    (C.eventual.mono fun _ inequality => inequality index)

/-- An endpoint normalized positive circulation rules out clearing order
zero. -/
theorem poleOrder_pos_of_endpointCirculation
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    0 < C.poleOrder := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  by_contra hpole
  have hpole_zero : C.poleOrder = 0 := Nat.eq_zero_of_not_pos hpole
  have inequalities :
      ∀ index,
        charge 0 index ≤
          ∑ state,
            C.potential 0 state * column 0 index state := by
    intro index
    simpa only [hpole_zero, pow_zero, one_mul] using
      C.endpoint_scaled_inequality
        analytic_column analytic_charge index
  have weighted_inequality :
      (∑ index, mass index * charge 0 index) ≤
        ∑ index, mass index *
          (∑ state,
            C.potential 0 state * column 0 index state) := by
    apply Finset.sum_le_sum
    intro index _
    exact mul_le_mul_of_nonneg_left
      (inequalities index) (mass_nonneg index)
  rw [charge_eq_one,
    balancedMass_weightedPotentialDrift_eq_zero
      (column 0) mass balance (C.potential 0)] at weighted_inequality
  norm_num at weighted_inequality

/-- The endpoint potential pairs nonnegatively with every endpoint column. -/
theorem endpoint_pair_nonneg
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0))
    (index : I) :
    0 ≤
      ∑ state,
        C.potential 0 state * column 0 index state := by
  have hpole :
      0 < C.poleOrder :=
    C.poleOrder_pos_of_endpointCirculation
      analytic_column analytic_charge circulation
  simpa only [zero_pow hpole.ne', zero_mul] using
    C.endpoint_scaled_inequality
      analytic_column analytic_charge index

/-- Endpoint complementarity for the original supplied circulation.

The returned mass is the circulation mass. Every column carrying positive
mass has zero pairing with the endpoint potential. -/
theorem exists_endpoint_complementary_mass
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    ∃ mass : I → ℝ,
      (∀ index, 0 ≤ mass index) ∧
      (∀ state,
        ∑ index, mass index * column 0 index state = 0) ∧
      (∑ index, mass index * charge 0 index = 1) ∧
      ∀ index, 0 < mass index →
        (∑ state,
          C.potential 0 state * column 0 index state) = 0 := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  refine
    ⟨mass, mass_nonneg, balance, charge_eq_one, ?_⟩
  have pair_nonneg :
      ∀ index,
        0 ≤ mass index *
          (∑ state,
            C.potential 0 state * column 0 index state) := by
    intro index
    exact mul_nonneg (mass_nonneg index)
      (C.endpoint_pair_nonneg
        analytic_column analytic_charge
        ⟨mass, mass_nonneg, balance, charge_eq_one⟩ index)
  have weighted_zero :
      ∑ index, mass index *
          (∑ state,
            C.potential 0 state * column 0 index state) = 0 :=
    balancedMass_weightedPotentialDrift_eq_zero
      (column 0) mass balance (C.potential 0)
  have each_zero :
      ∀ index,
        mass index *
          (∑ state,
            C.potential 0 state * column 0 index state) = 0 :=
    congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg pair_nonneg).mp
        weighted_zero)
  intro index mass_pos
  exact
    (mul_eq_zero.mp (each_zero index)).resolve_left
      (ne_of_gt mass_pos)

/-- First nonzero analytic coefficient of a gauge-fixed scaled potential. -/
structure GaugeFixedPotentialJet
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (anchor : S) where
  order : ℕ
  factor : ℝ → S → ℝ
  analytic_factor : AnalyticAt ℝ factor 0
  leading_ne_zero : factor 0 ≠ 0
  gauge_eq :
    ∀ᶠ t in nhds 0,
      gaugeFixAt anchor C.potential t =
        t ^ order • factor t

/-- Gauge fixing preserves analyticity of the pole-cleared potential. -/
theorem analytic_gaugeFixAt
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (anchor : S) :
    AnalyticAt ℝ (gaugeFixAt anchor C.potential) 0 := by
  rw [analyticAt_pi_iff]
  intro state
  exact
    (analyticAt_pi_iff.mp C.analytic_potential state).sub
      (analyticAt_pi_iff.mp C.analytic_potential anchor)

/-- Under zero-sum columns and an endpoint positive circulation, the
gauge-fixed scaled potential cannot vanish on a positive punctured
neighborhood. -/
theorem not_eventually_gaugeFixAt_eq_zero
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (anchor : S)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    ¬∀ᶠ t in nhdsWithin 0 (Ioi 0),
      gaugeFixAt anchor C.potential t = 0 := by
  obtain ⟨mass, mass_nonneg, _balance, charge_eq_one⟩ :=
    circulation
  let weightedCharge : ℝ → ℝ :=
    fun t => ∑ index, mass index * charge t index
  have weightedCharge_analytic :
      AnalyticAt ℝ weightedCharge 0 := by
    dsimp only [weightedCharge]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    exact analyticAt_const.mul (analytic_charge index)
  have weightedCharge_zero :
      weightedCharge 0 = 1 := by
    exact charge_eq_one
  have weightedCharge_eventually_pos :
      ∀ᶠ t in nhds 0, 0 < weightedCharge t := by
    apply weightedCharge_analytic.continuousAt.tendsto
    rw [weightedCharge_zero]
    exact Ioi_mem_nhds zero_lt_one
  intro gauge_eventually_zero
  have combined :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (∀ index,
          t ^ C.poleOrder * charge t index ≤
            ∑ state,
              C.potential t state * column t index state) ∧
        (∀ index, ∑ state, column t index state = 0) ∧
        gaugeFixAt anchor C.potential t = 0 ∧
        0 < weightedCharge t ∧ t ∈ Ioi (0 : ℝ) := by
    filter_upwards [
      C.eventual,
      column_zero_sum,
      gauge_eventually_zero,
      weightedCharge_eventually_pos.filter_mono
        nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with
        t inequality zero_sum gauge_zero
        weightedCharge_pos t_pos
    exact
      ⟨inequality, zero_sum, gauge_zero,
        weightedCharge_pos, t_pos⟩
  obtain ⟨t, inequality, zero_sum, gauge_zero,
      weightedCharge_pos, t_pos⟩ :=
    combined.exists
  have pairing_zero :
      ∀ index,
        (∑ state,
          C.potential t state * column t index state) = 0 := by
    intro index
    rw [← sum_gaugeFixAt_mul_eq
      anchor C.potential column (zero_sum index),
      gauge_zero]
    simp
  have scaled_charge_nonpos :
      ∀ index, t ^ C.poleOrder * charge t index ≤ 0 := by
    intro index
    simpa only [pairing_zero index] using inequality index
  have weighted_nonpos :
      t ^ C.poleOrder * weightedCharge t ≤ 0 := by
    dsimp only [weightedCharge]
    rw [Finset.mul_sum]
    calc
      (∑ index,
          t ^ C.poleOrder *
            (mass index * charge t index)) =
          ∑ index,
            mass index *
              (t ^ C.poleOrder * charge t index) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ ≤ ∑ index, mass index * 0 := by
        apply Finset.sum_le_sum
        intro index _
        exact mul_le_mul_of_nonneg_left
          (scaled_charge_nonpos index)
          (mass_nonneg index)
      _ = 0 := by simp
  exact
    (not_lt_of_ge weighted_nonpos)
      (mul_pos (pow_pos (mem_Ioi.mp t_pos) _)
        weightedCharge_pos)

/-- Zero-sum columns and an endpoint positive circulation produce a genuine
first nonzero analytic coefficient after gauge fixing.

No complementarity or face-descent conclusion is attached to this factor;
those require comparing its order with the pole-clearing order. -/
theorem exists_gaugeFixedPotentialJet
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge)
    (anchor : S)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    Nonempty (GaugeFixedPotentialJet C anchor) := by
  let gauge : ℝ → S → ℝ :=
    gaugeFixAt anchor C.potential
  have gauge_analytic : AnalyticAt ℝ gauge 0 :=
    C.analytic_gaugeFixAt anchor
  have order_ne_top :
      analyticOrderAt gauge 0 ≠ ⊤ := by
    intro order_top
    apply C.not_eventually_gaugeFixAt_eq_zero
      anchor analytic_charge column_zero_sum circulation
    exact
      (analyticOrderAt_eq_top.mp order_top).filter_mono
        nhdsWithin_le_nhds
  obtain ⟨factor, factor_analytic, factor_ne_zero, gauge_eq⟩ :=
    gauge_analytic.analyticOrderAt_ne_top.mp order_ne_top
  exact ⟨{
    order := analyticOrderNatAt gauge 0
    factor := factor
    analytic_factor := factor_analytic
    leading_ne_zero := factor_ne_zero
    gauge_eq := by
      simpa only [gauge, sub_zero, Filter.EventuallyEq] using
        gauge_eq
  }⟩

namespace GaugeFixedPotentialJet

/-- On the punctured zero-sum branch, the original scaled inequality can be
written directly in terms of the gauge-fixed analytic factor. -/
theorem eventual_scaledCharge_le_factorPair
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {C : AnalyticScaledChargedOccupationPotential column charge}
    {anchor : S}
    (jet : GaugeFixedPotentialJet C anchor)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        t ^ C.poleOrder * charge t index ≤
          t ^ jet.order *
            ∑ state,
              jet.factor t state * column t index state := by
  filter_upwards [
    C.eventual,
    column_zero_sum,
    jet.gauge_eq.filter_mono nhdsWithin_le_nhds] with
      t inequality zero_sum gauge_eq
  intro index
  calc
    t ^ C.poleOrder * charge t index ≤
        ∑ state,
          C.potential t state * column t index state :=
      inequality index
    _ =
        ∑ state,
          gaugeFixAt anchor C.potential t state *
            column t index state := by
      symm
      exact sum_gaugeFixAt_mul_eq
        anchor C.potential column (zero_sum index)
    _ =
        t ^ jet.order *
          ∑ state,
            jet.factor t state * column t index state := by
      rw [gauge_eq]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _
      ring

/-- The first nonzero gauge-fixed coefficient occurs strictly below the
pole-clearing order. -/
theorem order_lt_poleOrder
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {C : AnalyticScaledChargedOccupationPotential column charge}
    {anchor : S}
    (jet : GaugeFixedPotentialJet C anchor)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    jet.order < C.poleOrder := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  by_contra horder
  have pole_le_order : C.poleOrder ≤ jet.order :=
    Nat.le_of_not_gt horder
  let remainingOrder := jet.order - C.poleOrder
  let weightedCharge : ℝ → ℝ :=
    fun t => ∑ index, mass index * charge t index
  let weightedPair : ℝ → ℝ :=
    fun t =>
      ∑ index, mass index *
        (∑ state,
          jet.factor t state * column t index state)
  have weightedCharge_analytic :
      AnalyticAt ℝ weightedCharge 0 := by
    dsimp only [weightedCharge]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    exact analyticAt_const.mul (analytic_charge index)
  have weightedPair_analytic :
      AnalyticAt ℝ weightedPair 0 := by
    dsimp only [weightedPair]
    apply Finset.univ.analyticAt_fun_sum
    intro index _
    apply analyticAt_const.mul
    apply Finset.univ.analyticAt_fun_sum
    intro state _
    exact
      (analyticAt_pi_iff.mp jet.analytic_factor state).mul
        (analytic_column index state)
  have weightedPair_zero :
      weightedPair 0 = 0 := by
    exact balancedMass_weightedPotentialDrift_eq_zero
      (column 0) mass balance (jet.factor 0)
  have eventual_divided :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        weightedCharge t ≤
          t ^ remainingOrder * weightedPair t := by
    filter_upwards [
      jet.eventual_scaledCharge_le_factorPair
        column_zero_sum,
      self_mem_nhdsWithin] with t inequality t_pos
    have power_split :
        t ^ jet.order =
          t ^ C.poleOrder * t ^ remainingOrder := by
      dsimp only [remainingOrder]
      rw [← pow_add]
      congr 1
      omega
    have coordinate_divided :
        ∀ index,
          charge t index ≤
            t ^ remainingOrder *
              ∑ state,
                jet.factor t state * column t index state := by
      intro index
      have h := inequality index
      rw [power_split] at h
      have power_pos :
          0 < t ^ C.poleOrder :=
        pow_pos (mem_Ioi.mp t_pos) _
      have h' := h
      simp only [mul_assoc] at h'
      nlinarith
    dsimp only [weightedCharge, weightedPair]
    rw [Finset.mul_sum]
    calc
      (∑ index, mass index * charge t index) ≤
          ∑ index, mass index *
            (t ^ remainingOrder *
              ∑ state,
                jet.factor t state *
                  column t index state) := by
        apply Finset.sum_le_sum
        intro index _
        exact mul_le_mul_of_nonneg_left
          (coordinate_divided index)
          (mass_nonneg index)
      _ =
          ∑ index,
            t ^ remainingOrder *
              (mass index *
                ∑ state,
                  jet.factor t state *
                    column t index state) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
  have left_tendsto :
      Tendsto weightedCharge
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h :
        Tendsto weightedCharge
          (nhdsWithin 0 (Ioi 0))
          (nhds (weightedCharge 0)) :=
      weightedCharge_analytic.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [weightedCharge, charge_eq_one] using h
  have right_analytic :
      AnalyticAt ℝ
        (fun t => t ^ remainingOrder * weightedPair t) 0 :=
    (analyticAt_id.pow _).mul weightedPair_analytic
  have right_tendsto :
      Tendsto
        (fun t => t ^ remainingOrder * weightedPair t)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h :
        Tendsto
          (fun t => t ^ remainingOrder * weightedPair t)
          (nhdsWithin 0 (Ioi 0))
          (nhds
            ((0 : ℝ) ^ remainingOrder * weightedPair 0)) :=
      right_analytic.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [weightedPair_zero, mul_zero] using h
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  have impossible : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto
      left_tendsto right_tendsto eventual_divided
  norm_num at impossible

/-- The leading gauge-fixed coefficient pairs nonnegatively with every
endpoint column. -/
theorem leading_pair_nonneg
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {C : AnalyticScaledChargedOccupationPotential column charge}
    {anchor : S}
    (jet : GaugeFixedPotentialJet C anchor)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0))
    (index : I) :
    0 ≤
      ∑ state,
        jet.factor 0 state * column 0 index state := by
  have order_lt :
      jet.order < C.poleOrder :=
    jet.order_lt_poleOrder
      analytic_column analytic_charge
      column_zero_sum circulation
  let remainingOrder := C.poleOrder - jet.order
  have remainingOrder_pos : 0 < remainingOrder := by
    exact Nat.sub_pos_of_lt order_lt
  have eventual_divided :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ^ remainingOrder * charge t index ≤
          ∑ state,
            jet.factor t state * column t index state := by
    filter_upwards [
      jet.eventual_scaledCharge_le_factorPair
        column_zero_sum,
      self_mem_nhdsWithin] with t inequality t_pos
    have power_split :
        t ^ C.poleOrder =
          t ^ jet.order * t ^ remainingOrder := by
      dsimp only [remainingOrder]
      rw [← pow_add]
      congr 1
      omega
    have h := inequality index
    rw [power_split] at h
    have power_pos :
        0 < t ^ jet.order :=
      pow_pos (mem_Ioi.mp t_pos) _
    have h' := h
    simp only [mul_assoc] at h'
    nlinarith
  have left_analytic :
      AnalyticAt ℝ
        (fun t => t ^ remainingOrder * charge t index) 0 :=
    (analyticAt_id.pow _).mul (analytic_charge index)
  have right_analytic :
      AnalyticAt ℝ
        (fun t =>
          ∑ state,
            jet.factor t state * column t index state) 0 := by
    apply Finset.univ.analyticAt_fun_sum
    intro state _
    exact
      (analyticAt_pi_iff.mp jet.analytic_factor state).mul
        (analytic_column index state)
  have left_tendsto :
      Tendsto
        (fun t => t ^ remainingOrder * charge t index)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h :
        Tendsto
          (fun t => t ^ remainingOrder * charge t index)
          (nhdsWithin 0 (Ioi 0))
          (nhds
            ((0 : ℝ) ^ remainingOrder * charge 0 index)) :=
      left_analytic.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [zero_pow remainingOrder_pos.ne',
      zero_mul] using h
  have right_tendsto :
      Tendsto
        (fun t =>
          ∑ state,
            jet.factor t state * column t index state)
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (∑ state,
            jet.factor 0 state * column 0 index state)) :=
    right_analytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  exact le_of_tendsto_of_tendsto
    left_tendsto right_tendsto eventual_divided

/-- The supplied endpoint circulation is complementary to the first
nonzero gauge-fixed coefficient on every positive-mass column. -/
theorem exists_leading_complementary_mass
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ}
    {charge : ℝ → I → ℝ}
    {C : AnalyticScaledChargedOccupationPotential column charge}
    {anchor : S}
    (jet : GaugeFixedPotentialJet C anchor)
    (analytic_column :
      ∀ index state,
        AnalyticAt ℝ (fun t => column t index state) 0)
    (analytic_charge :
      ∀ index, AnalyticAt ℝ (fun t => charge t index) 0)
    (column_zero_sum :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ index, ∑ state, column t index state = 0)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (column 0) (charge 0)) :
    ∃ mass : I → ℝ,
      (∀ index, 0 ≤ mass index) ∧
      (∀ state,
        ∑ index, mass index * column 0 index state = 0) ∧
      (∑ index, mass index * charge 0 index = 1) ∧
      ∀ index, 0 < mass index →
        (∑ state,
          jet.factor 0 state * column 0 index state) = 0 := by
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ :=
    circulation
  refine
    ⟨mass, mass_nonneg, balance, charge_eq_one, ?_⟩
  have terms_nonneg :
      ∀ index,
        0 ≤ mass index *
          (∑ state,
            jet.factor 0 state * column 0 index state) := by
    intro index
    exact mul_nonneg (mass_nonneg index)
      (jet.leading_pair_nonneg
        analytic_column analytic_charge
        column_zero_sum
        ⟨mass, mass_nonneg, balance, charge_eq_one⟩
        index)
  have weighted_zero :
      ∑ index, mass index *
          (∑ state,
            jet.factor 0 state * column 0 index state) = 0 :=
    balancedMass_weightedPotentialDrift_eq_zero
      (column 0) mass balance (jet.factor 0)
  have each_zero :
      ∀ index,
        mass index *
          (∑ state,
            jet.factor 0 state * column 0 index state) = 0 :=
    congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg terms_nonneg).mp
        weighted_zero)
  intro index mass_pos
  exact
    (mul_eq_zero.mp (each_zero index)).resolve_left
      (ne_of_gt mass_pos)

end GaugeFixedPotentialJet

end AnalyticScaledChargedOccupationPotential

namespace GaugeComponentCounterexample

/-- The active endpoint column vanishes, while the inactive column is one. -/
def column (t : ℝ) (index : Bool) (_state : Unit) : ℝ :=
  if index then 1 else t

/-- Only the endpoint-active column carries charge. -/
def charge (_t : ℝ) (index : Bool) : ℝ :=
  if index then 0 else 1

/-- The pole-cleared dual potential is the constant gauge `1`. -/
def potential (_t : ℝ) (_state : Unit) : ℝ := 1

/-- A valid analytic scaled potential with clearing order one. -/
def scaledPotential :
    AnalyticScaledChargedOccupationPotential column charge where
  poleOrder := 1
  potential := potential
  analytic_potential := by
    rw [analyticAt_pi_iff]
    intro state
    cases state
    exact analyticAt_const
  eventual := by
    filter_upwards with t
    intro index
    cases index <;>
      simp [column, charge, potential]

/-- The endpoint uses the zero column with mass one and charge one. -/
theorem endpointCirculation :
    HasNormalizedPositiveChargedCirculation
      (column 0) (charge 0) := by
  let mass : Bool → ℝ :=
    fun index => if index then 0 else 1
  refine ⟨mass, ?_, ?_, ?_⟩
  · intro index
    cases index <;> simp [mass]
  · intro state
    cases state
    simp [mass, column]
  · simp [mass, charge]

/-- Gauge fixing removes the entire potential germ, so no first nonconstant
coefficient exists in this example. -/
theorem gaugeFixAt_eq_zero :
    gaugeFixAt () potential = 0 := by
  funext t state
  cases state
  simp [gaugeFixAt, potential]

end GaugeComponentCounterexample

end Probability
end Math
