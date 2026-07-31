/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticLinearSystem
import Math.Probability

/-!
# Pole-cleared stationary laws for analytic finite kernels

Stationarity of a finite Markov kernel is a homogeneous nonnegative linear
system, with the total mass fixed to one.  This file applies the analytic
normalized-Farkas selector to that system.

The result is deliberately local and finite-dimensional.  If normalized
stationary weights exist throughout a punctured right neighborhood, then one
fixed Cramer support selects them meromorphically: multiplication by one
power of the parameter gives an analytic nonnegative vector.  If the
normalized stationary weight is unique, this selected quotient is the
unique stationary law.

For a fixed punctured-support closed communicating class, existence and
uniqueness are the ordinary finite irreducible-chain facts.  They remain
explicit hypotheses here so that the theorem does not silently identify a
closed class, a legal game continuation, or an externally reachable child.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter Finset Set
open Math.LinearAlgebra

variable {S : Type*}

/-- The column balance matrix for stationary weights.  Rows are destination
states and columns are source states. -/
def stationaryBalance [DecidableEq S]
    (kernel : S → PMF S) : Matrix S S ℝ := by
  exact fun destination source =>
    (kernel source destination).toReal -
      if destination = source then 1 else 0

/-- Unit mass functional for normalized stationary weights. -/
def stationaryMass : S → ℝ := fun _ => 1

/-- A nonnegative, unit-mass stationary weight for a finite Markov kernel. -/
def IsNormalizedStationaryWeight [Fintype S]
    (kernel : S → PMF S) (weight : S → ℝ) : Prop :=
  (∀ state, 0 ≤ weight state) ∧
    (∀ destination,
      ∑ source, weight source *
          (kernel source destination).toReal =
        weight destination) ∧
    ∑ state, weight state = 1

/-- Multiplying the stationary balance matrix by a weight vector gives
incoming mass minus current mass. -/
theorem stationaryBalance_mulVec [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (weight : S → ℝ) (destination : S) :
    Matrix.mulVec (stationaryBalance kernel) weight destination =
      (∑ source,
        weight source * (kernel source destination).toReal) -
        weight destination := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp only [stationaryBalance]
  calc
    (∑ source,
        ((kernel source destination).toReal -
          if destination = source then 1 else 0) *
          weight source) =
        (∑ source,
          weight source * (kernel source destination).toReal) -
          ∑ source,
            (if destination = source then 1 else 0) *
              weight source := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro source _
      ring
    _ =
        (∑ source,
          weight source * (kernel source destination).toReal) -
          weight destination := by
      simp

/-- Normalized stationary weights are exactly the normalized-Farkas
certificates for the stationary balance matrix and unit mass row. -/
theorem mem_normalizedFarkasCertificateSet_stationary_iff
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (weight : S → ℝ) :
    weight ∈
        normalizedFarkasCertificateSet
          (stationaryBalance kernel) stationaryMass ↔
      IsNormalizedStationaryWeight kernel weight := by
  classical
  constructor
  · rintro ⟨hnonnegative, hequation⟩
    refine ⟨hnonnegative, ?_, ?_⟩
    · intro destination
      have hrow := congrFun hequation (Sum.inl destination)
      change
        Matrix.mulVec (stationaryBalance kernel) weight destination = 0
          at hrow
      rw [stationaryBalance_mulVec] at hrow
      exact sub_eq_zero.mp hrow
    · have hmass := congrFun hequation (Sum.inr PUnit.unit)
      change
        ∑ state, stationaryMass state * weight state = 1 at hmass
      simpa [stationaryMass] using hmass
  · rintro ⟨hnonnegative, hstationary, hmass⟩
    refine ⟨hnonnegative, ?_⟩
    funext row
    cases row with
    | inl destination =>
        change
          Matrix.mulVec (stationaryBalance kernel) weight destination = 0
        rw [stationaryBalance_mulVec]
        exact sub_eq_zero.mpr (hstationary destination)
    | inr index =>
        cases index
        change ∑ state, stationaryMass state * weight state = 1
        simpa [stationaryMass] using hmass

/-- Analytic data obtained by clearing one common endpoint pole from a
normalized stationary law. -/
structure PoleClearedAnalyticStationaryWeight [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) (x₀ : ℝ) where
  support : Finset S
  poleOrder : ℕ
  scaledWeight : ℝ → S → ℝ
  analytic_scaledWeight : AnalyticAt ℝ scaledWeight x₀
  eventually_properties :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      (∀ state, 0 ≤ scaledWeight x state) ∧
        (∀ destination,
          ∑ source,
              scaledWeight x source *
                (kernel x source destination).toReal =
            scaledWeight x destination) ∧
        (∑ state, scaledWeight x state =
          (x - x₀) ^ poleOrder) ∧
        IsNormalizedStationaryWeight (kernel x)
          (supportCramerVector
            (normalizedFarkasMatrix
              (stationaryBalance (kernel x)) stationaryMass)
            normalizedFarkasRhs support) ∧
        (x - x₀) ^ poleOrder •
            supportCramerVector
              (normalizedFarkasMatrix
                (stationaryBalance (kernel x)) stationaryMass)
              normalizedFarkasRhs support =
          scaledWeight x

namespace PoleClearedAnalyticStationaryWeight

variable [Fintype S] [DecidableEq S]
  {kernel : ℝ → S → PMF S} {x₀ : ℝ}

/-- On the punctured right neighborhood, division by the clearing power
recovers a normalized stationary law. -/
theorem eventually_normalized_quotient
    (data : PoleClearedAnalyticStationaryWeight kernel x₀) :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      IsNormalizedStationaryWeight (kernel x)
        (((x - x₀) ^ data.poleOrder)⁻¹ • data.scaledWeight x) := by
  filter_upwards [data.eventually_properties,
    self_mem_nhdsWithin] with x hx hxx₀
  have hpower :
      (x - x₀) ^ data.poleOrder ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hxx₀.ne')
  rw [← hx.2.2.2.2]
  simp [hpower, hx.2.2.2.1]

/-- If the normalized stationary law is unique, the pole-cleared selector
represents that law on one common punctured neighborhood. -/
theorem eventually_eq_unique
    (data : PoleClearedAnalyticStationaryWeight kernel x₀)
    (stationary : ℝ → S → ℝ)
    (hstationary :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        IsNormalizedStationaryWeight (kernel x) (stationary x))
    (hunique :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∀ weight,
          IsNormalizedStationaryWeight (kernel x) weight →
            weight = stationary x) :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      ((x - x₀) ^ data.poleOrder)⁻¹ • data.scaledWeight x =
        stationary x := by
  filter_upwards [data.eventually_normalized_quotient,
    hstationary, hunique] with x hx _ hxunique
  exact hxunique _ hx

/-- Equivalent pole-cleared form of `eventually_eq_unique`, avoiding
division in downstream algebra. -/
theorem eventually_scaled_eq_unique
    (data : PoleClearedAnalyticStationaryWeight kernel x₀)
    (stationary : ℝ → S → ℝ)
    (hstationary :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        IsNormalizedStationaryWeight (kernel x) (stationary x))
    (hunique :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∀ weight,
          IsNormalizedStationaryWeight (kernel x) weight →
            weight = stationary x) :
    ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
      data.scaledWeight x =
        (x - x₀) ^ data.poleOrder • stationary x := by
  filter_upwards [data.eventually_properties,
    hstationary, hunique] with x hx _ hxunique
  rw [← hxunique _ hx.2.2.2.1]
  exact hx.2.2.2.2.symm

end PoleClearedAnalyticStationaryWeight

/-- Eventual normalized stationarity for an analytic finite kernel admits a
fixed-support, pole-cleared analytic selector. -/
theorem exists_poleClearedAnalyticStationaryWeight
    [Fintype S] [DecidableEq S]
    (kernel : ℝ → S → PMF S) {x₀ : ℝ}
    (hanalytic :
      ∀ source destination,
        AnalyticAt ℝ
          (fun x => (kernel x source destination).toReal) x₀)
    (hstationary :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        ∃ weight,
          IsNormalizedStationaryWeight (kernel x) weight) :
    Nonempty (PoleClearedAnalyticStationaryWeight kernel x₀) := by
  classical
  let balance : ℝ → Matrix S S ℝ :=
    fun x => stationaryBalance (kernel x)
  let mass : ℝ → S → ℝ := fun _ => stationaryMass
  have hbalance :
      ∀ destination source,
        AnalyticAt ℝ
          (fun x => balance x destination source) x₀ := by
    intro destination source
    change
      AnalyticAt ℝ
        (fun x =>
          (kernel x source destination).toReal -
            if destination = source then 1 else 0) x₀
    exact
      (hanalytic source destination).sub analyticAt_const
  have hmass :
      ∀ state,
        AnalyticAt ℝ (fun x => mass x state) x₀ := by
    intro state
    exact analyticAt_const
  have hfeasible :
      ∀ᶠ x in nhdsWithin x₀ (Ioi x₀),
        (normalizedFarkasCertificateSet
          (balance x) (mass x)).Nonempty := by
    filter_upwards [hstationary] with x hx
    obtain ⟨weight, hweight⟩ := hx
    refine ⟨weight, ?_⟩
    simpa [balance, mass] using
      (mem_normalizedFarkasCertificateSet_stationary_iff
        (kernel x) weight).mpr hweight
  obtain ⟨support, poleOrder, scaledWeight,
      hanalyticScaled, hscaled⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      balance mass hbalance hmass hfeasible
  refine ⟨{
    support := support
    poleOrder := poleOrder
    scaledWeight := scaledWeight
    analytic_scaledWeight := hanalyticScaled
    eventually_properties := ?_
  }⟩
  filter_upwards [hscaled,
    self_mem_nhdsWithin] with x hx hxx₀
  have hnormalized :
      IsNormalizedStationaryWeight (kernel x)
        (supportCramerVector
          (normalizedFarkasMatrix
            (stationaryBalance (kernel x)) stationaryMass)
          normalizedFarkasRhs support) := by
    apply
      (mem_normalizedFarkasCertificateSet_stationary_iff
        (kernel x) _).mp
    simpa [balance, mass] using hx.2
  have hscale :
      (x - x₀) ^ poleOrder •
          supportCramerVector
            (normalizedFarkasMatrix
              (stationaryBalance (kernel x)) stationaryMass)
            normalizedFarkasRhs support =
        scaledWeight x := by
    simpa [balance, mass] using hx.1
  have hpowerNonnegative : 0 ≤ (x - x₀) ^ poleOrder := by
    exact pow_nonneg (sub_nonneg.mpr hxx₀.le) _
  have hscaledNonnegative :
      ∀ state, 0 ≤ scaledWeight x state := by
    intro state
    rw [← hscale]
    exact mul_nonneg hpowerNonnegative (hnormalized.1 state)
  have hscaledStationary :
      ∀ destination,
        ∑ source,
            scaledWeight x source *
              (kernel x source destination).toReal =
          scaledWeight x destination := by
    intro destination
    rw [← hscale]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ source,
          ((x - x₀) ^ poleOrder *
              supportCramerVector
                (normalizedFarkasMatrix
                  (stationaryBalance (kernel x)) stationaryMass)
                normalizedFarkasRhs support source) *
            (kernel x source destination).toReal) =
          (x - x₀) ^ poleOrder *
            ∑ source,
              supportCramerVector
                (normalizedFarkasMatrix
                  (stationaryBalance (kernel x)) stationaryMass)
                normalizedFarkasRhs support source *
              (kernel x source destination).toReal := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        ring
      _ =
          (x - x₀) ^ poleOrder *
            supportCramerVector
              (normalizedFarkasMatrix
                (stationaryBalance (kernel x)) stationaryMass)
              normalizedFarkasRhs support destination := by
        rw [hnormalized.2.1 destination]
  have hscaledMass :
      ∑ state, scaledWeight x state =
        (x - x₀) ^ poleOrder := by
    rw [← hscale]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hnormalized.2.2, mul_one]
  exact
    ⟨hscaledNonnegative, hscaledStationary, hscaledMass,
      hnormalized, hscale⟩

end Probability
end Math
