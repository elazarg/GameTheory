/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AnalyticCoordinateCurve

/-!
# Common ramification for coordinatewise Puiseux curves

Convergent Newton--Puiseux is naturally stated one coordinate at a time.
Curve selection needs one coupled analytic arc with one common ramification.
For a finite coordinate type, the product of the coordinate exponents
synchronizes all expansions.

This file assumes that every coordinate expansion comes from the same
selected curve. It does not assume or assert semialgebraic curve selection or
Newton--Puiseux.
-/

noncomputable section

open Filter Set Topology

namespace Math

/-- Every coordinate of `curve` becomes analytic after some positive integral
ramification, with the prescribed limiting value. All coordinates refer to
the same unramified curve. -/
def HasCoordinatewiseAnalyticRamificationAt
    {σ : Type*} (curve : ℝ → (σ → ℝ)) (x₀ : σ → ℝ) : Prop :=
  ∀ i, ∃ (q : ℕ) (gamma : ℝ → ℝ),
    0 < q ∧
      AnalyticAt ℝ gamma 0 ∧
      gamma 0 = x₀ i ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t = curve (t ^ q) i

/-- A selected positive half-curve together with coordinatewise analytic
ramifications of that same curve. -/
def HasCoordinatewiseRamifiedSelectionAt
    {σ : Type*} (A : Set (σ → ℝ))
    (coordinate : (σ → ℝ) →L[ℝ] ℝ) (x₀ : σ → ℝ) : Prop :=
  ∃ curve : ℝ → (σ → ℝ),
    HasCoordinatewiseAnalyticRamificationAt curve x₀ ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        curve t ∈ A ∧ 0 < coordinate (curve t)

private theorem tendsto_pow_nhdsGT_zero
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => t ^ d) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ)) := by
  have hfull :
      Tendsto (fun t : ℝ => t ^ d) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [Nat.ne_of_gt hd] using
      (continuousAt_pow (0 : ℝ) d).tendsto
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hfull.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact pow_pos (show (0 : ℝ) < t from ht) d

/-- Finitely many coordinatewise ramified analytic expansions synchronize to
one coupled analytic expansion. The common exponent is the product of the
coordinate exponents. -/
theorem exists_common_analytic_ramification
    {σ : Type*} [Fintype σ]
    {curve : ℝ → (σ → ℝ)} {x₀ : σ → ℝ}
    (hcurve : HasCoordinatewiseAnalyticRamificationAt curve x₀) :
    ∃ (q : ℕ) (gamma : ℝ → (σ → ℝ)),
      0 < q ∧
        AnalyticAt ℝ gamma 0 ∧
        gamma 0 = x₀ ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t = curve (t ^ q) := by
  classical
  choose exponent branch hexponent hbranch hbranch_zero hbranch_eq
    using hcurve
  let q : ℕ := ∏ i, exponent i
  let coexponent : σ → ℕ :=
    fun i => ∏ j ∈ Finset.univ.erase i, exponent j
  have hcoexponent : ∀ i, 0 < coexponent i := by
    intro i
    exact Finset.prod_pos fun j _ => hexponent j
  have hexponent_mul (i : σ) :
      exponent i * coexponent i = q := by
    exact Finset.mul_prod_erase Finset.univ exponent
      (Finset.mem_univ i)
  have hq : 0 < q := Finset.prod_pos fun i _ => hexponent i
  let gamma : ℝ → (σ → ℝ) :=
    fun t i => branch i (t ^ coexponent i)
  have hgamma : AnalyticAt ℝ gamma 0 := by
    rw [analyticAt_pi_iff]
    intro i
    apply (hbranch i).comp_of_eq (analyticAt_id.pow (coexponent i))
    simp [Nat.ne_of_gt (hcoexponent i)]
  have hgamma_zero : gamma 0 = x₀ := by
    funext i
    simp [gamma, Nat.ne_of_gt (hcoexponent i), hbranch_zero i]
  have hgamma_eq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t = curve (t ^ q) := by
    have hcoordinates :
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i,
          gamma t i = curve (t ^ q) i := by
      apply Filter.eventually_all.mpr
      intro i
      have hpull :
          ∀ᶠ t in 𝓝[>] (0 : ℝ),
            branch i (t ^ coexponent i) =
              curve ((t ^ coexponent i) ^ exponent i) i :=
        (tendsto_pow_nhdsGT_zero (hcoexponent i)).eventually
          (hbranch_eq i)
      filter_upwards [hpull] with t ht
      change branch i (t ^ coexponent i) = curve (t ^ q) i
      rw [ht, ← pow_mul, Nat.mul_comm, hexponent_mul]
    filter_upwards [hcoordinates] with t ht
    exact funext ht
  exact ⟨q, gamma, hq, hgamma, hgamma_zero, hgamma_eq⟩

/-- Coordinatewise Puiseux expansions of one selected curve produce a
positive-coordinate analytic arc in the selected set. -/
theorem HasCoordinatewiseRamifiedSelectionAt.toPositiveCoordinateAnalyticArc
    {σ : Type*} [Fintype σ]
    {A : Set (σ → ℝ)}
    {coordinate : (σ → ℝ) →L[ℝ] ℝ} {x₀ : σ → ℝ}
    (h : HasCoordinatewiseRamifiedSelectionAt A coordinate x₀)
    (hcoordinate : coordinate x₀ = 0) :
    HasPositiveCoordinateAnalyticArcAt A coordinate x₀ := by
  obtain ⟨curve, hramified, hselected⟩ := h
  obtain ⟨q, gamma, hq, hgamma, hgamma_zero, hgamma_eq⟩ :=
    exists_common_analytic_ramification hramified
  have hpow :
      Tendsto (fun t : ℝ => t ^ q) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ)) :=
    tendsto_pow_nhdsGT_zero hq
  have hselected_pow :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        curve (t ^ q) ∈ A ∧
          0 < coordinate (curve (t ^ q)) :=
    hpow.eventually hselected
  have hgood :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        gamma t ∈ A ∧ 0 < coordinate (gamma t) := by
    filter_upwards [hgamma_eq, hselected_pow] with t heq ht
    simpa [heq] using ht
  obtain ⟨eta, heta, hinterval⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  exact ⟨gamma, eta, heta, hgamma, hgamma_zero, hcoordinate,
    fun t ht => hinterval ht⟩

/-- The exact-power form consumed by analytic Bellman germs. -/
theorem HasCoordinatewiseRamifiedSelectionAt.toAnalyticPowerCurve
    {σ : Type*} [Fintype σ]
    {A : Set (σ → ℝ)}
    {coordinate : (σ → ℝ) →L[ℝ] ℝ} {x₀ : σ → ℝ}
    (h : HasCoordinatewiseRamifiedSelectionAt A coordinate x₀)
    (hcoordinate : coordinate x₀ = 0) :
    HasAnalyticPowerCurveAt A coordinate x₀ :=
  (h.toPositiveCoordinateAnalyticArc hcoordinate).toHasAnalyticPowerCurveAt

end Math
