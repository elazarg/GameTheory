/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Ramification of Weierstrass polynomials

This file formalizes the parameter change `λ = t ^ p` on polynomials over
formal power series and on iterated formal power series. Ramification is
injective, preserves the maximal ideal and distinguished polynomials, and
therefore transports Weierstrass factorizations.

`HasRamifiedPowerSeriesSplitting` is the exact formal splitting output expected
from Newton--Puiseux. Its roots are automatically centered at zero when the
input polynomial is distinguished.
-/

noncomputable section

open Polynomial

namespace Math

variable {K : Type*} [Field K]

/-- Extend the coefficient field of a polynomial over formal power series. -/
def mapPowerSeriesPolynomial
    {L : Type*} [Field L] (σ : K →+* L)
    (f : Polynomial (PowerSeries K)) :
    Polynomial (PowerSeries L) :=
  f.map (PowerSeries.map σ)

/-- Ramify the parameter of a polynomial over formal power series by
`λ = t ^ p`. -/
def ramifyPowerSeriesPolynomial
    (p : ℕ) (hp : p ≠ 0) (f : Polynomial (PowerSeries K)) :
    Polynomial (PowerSeries K) :=
  f.map (PowerSeries.expand p hp).toRingHom

/-- Ramify the parameter coefficients of an iterated formal power series,
leaving its outer value variable unchanged. -/
def ramifyIteratedPowerSeries
    (p : ℕ) (hp : p ≠ 0) (g : PowerSeries (PowerSeries K)) :
    PowerSeries (PowerSeries K) :=
  g.map (PowerSeries.expand p hp).toRingHom

theorem injective_powerSeries_expand (p : ℕ) (hp : p ≠ 0) :
    Function.Injective
      (PowerSeries.expand p hp : PowerSeries K → PowerSeries K) := by
  intro f g hfg
  ext n
  have hn := congrArg (PowerSeries.coeff (p * n)) hfg
  simpa using hn

theorem powerSeries_expand_mem_maximalIdeal_iff
    (p : ℕ) (hp : p ≠ 0) (f : PowerSeries K) :
    PowerSeries.expand p hp f ∈ IsLocalRing.maximalIdeal (PowerSeries K) ↔
      f ∈ IsLocalRing.maximalIdeal (PowerSeries K) := by
  rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker,
    RingHom.mem_ker, PowerSeries.constantCoeff_expand]

theorem powerSeries_map_mem_maximalIdeal_iff
    {L : Type*} [Field L] (σ : K →+* L) (f : PowerSeries K) :
    PowerSeries.map σ f ∈ IsLocalRing.maximalIdeal (PowerSeries L) ↔
      f ∈ IsLocalRing.maximalIdeal (PowerSeries K) := by
  rw [← PowerSeries.ker_coeff_eq_max_ideal,
    ← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, RingHom.mem_ker]
  change σ f.constantCoeff = 0 ↔ f.constantCoeff = 0
  constructor
  · intro h
    exact σ.injective (by simpa using h)
  · intro h
    simp [h]

theorem isDistinguishedAt_mapPowerSeriesPolynomial
    {L : Type*} [Field L] (σ : K →+* L)
    {f : Polynomial (PowerSeries K)}
    (H : f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K))) :
    (mapPowerSeriesPolynomial σ f).IsDistinguishedAt
      (IsLocalRing.maximalIdeal (PowerSeries L)) := by
  refine ⟨⟨?_⟩, H.monic.map _⟩
  intro n hn
  rw [mapPowerSeriesPolynomial, Polynomial.coeff_map,
    powerSeries_map_mem_maximalIdeal_iff]
  have hdegree :
      (mapPowerSeriesPolynomial σ f).natDegree = f.natDegree :=
    H.monic.natDegree_map _
  exact H.mem (by simpa [hdegree] using hn)

theorem mapPowerSeriesPolynomial_ramify
    {L : Type*} [Field L] (σ : K →+* L)
    (p : ℕ) (hp : p ≠ 0) (f : Polynomial (PowerSeries K)) :
    mapPowerSeriesPolynomial σ (ramifyPowerSeriesPolynomial p hp f) =
      ramifyPowerSeriesPolynomial p hp (mapPowerSeriesPolynomial σ f) := by
  ext n m
  simp [mapPowerSeriesPolynomial, ramifyPowerSeriesPolynomial,
    PowerSeries.map_expand]

theorem isDistinguishedAt_ramifyPowerSeriesPolynomial
    {f : Polynomial (PowerSeries K)}
    (H : f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    (p : ℕ) (hp : p ≠ 0) :
    (ramifyPowerSeriesPolynomial p hp f).IsDistinguishedAt
      (IsLocalRing.maximalIdeal (PowerSeries K)) := by
  refine ⟨⟨?_⟩, H.monic.map _⟩
  intro n hn
  rw [ramifyPowerSeriesPolynomial, Polynomial.coeff_map]
  change PowerSeries.expand p hp (f.coeff n) ∈
    IsLocalRing.maximalIdeal (PowerSeries K)
  rw [powerSeries_expand_mem_maximalIdeal_iff]
  have hdegree :
      (ramifyPowerSeriesPolynomial p hp f).natDegree = f.natDegree :=
    H.monic.natDegree_map _
  exact H.mem (by simpa [hdegree] using hn)

theorem isWeierstrassFactorization_ramify
    {g : PowerSeries (PowerSeries K)}
    {f : Polynomial (PowerSeries K)}
    {h : PowerSeries (PowerSeries K)}
    (H : g.IsWeierstrassFactorization f h)
    (p : ℕ) (hp : p ≠ 0) :
    (ramifyIteratedPowerSeries p hp g).IsWeierstrassFactorization
      (ramifyPowerSeriesPolynomial p hp f)
      (ramifyIteratedPowerSeries p hp h) := by
  refine ⟨isDistinguishedAt_ramifyPowerSeriesPolynomial
    H.isDistinguishedAt p hp, H.isUnit.map _, ?_⟩
  simp only [ramifyIteratedPowerSeries, ramifyPowerSeriesPolynomial, H.eq_mul,
    map_mul, Polynomial.polynomial_map_coe]

/-- A distinguished polynomial can only have formal roots centered at zero. -/
theorem constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    {f : Polynomial (PowerSeries K)}
    (H : f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    {s : PowerSeries K} (hs : f.IsRoot s) :
    s.constantCoeff = 0 := by
  have hpow :
      s ^ f.natDegree ∈ IsLocalRing.maximalIdeal (PowerSeries K) :=
    H.toIsWeaklyEisensteinAt.pow_natDegree_le_of_root_of_monic_mem
      hs H.monic f.natDegree le_rfl
  rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker,
    map_pow] at hpow
  by_contra hs0
  exact (pow_ne_zero _ hs0) hpow

/-- The precise formal output expected from Newton--Puiseux: after a nonzero
ramification of the parameter, the distinguished polynomial splits into
linear factors over formal power series. -/
def HasRamifiedPowerSeriesSplitting
    (f : Polynomial (PowerSeries K)) : Prop :=
  ∃ (p : ℕ) (hp : p ≠ 0)
      (roots : Fin f.natDegree → PowerSeries K),
    ramifyPowerSeriesPolynomial p hp f =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))

/-- Newton--Puiseux splitting after extending the coefficient field and
ramifying the parameter. The intended real-curve instance uses the inclusion
`ℝ →+* ℂ`. -/
def HasRamifiedPowerSeriesSplittingOver
    {L : Type*} [Field L] (σ : K →+* L)
    (f : Polynomial (PowerSeries K)) : Prop :=
  HasRamifiedPowerSeriesSplitting (mapPowerSeriesPolynomial σ f)

theorem HasRamifiedPowerSeriesSplitting.isRoot
    {f : Polynomial (PowerSeries K)}
    (H : HasRamifiedPowerSeriesSplitting f) :
    ∃ (p : ℕ) (hp : p ≠ 0)
        (roots : Fin f.natDegree → PowerSeries K),
      (∀ i, (ramifyPowerSeriesPolynomial p hp f).IsRoot (roots i)) ∧
      ramifyPowerSeriesPolynomial p hp f =
        ∏ i, (Polynomial.X - Polynomial.C (roots i)) := by
  obtain ⟨p, hp, roots, hsplit⟩ := H
  refine ⟨p, hp, roots, ?_, hsplit⟩
  intro i
  rw [Polynomial.IsRoot, hsplit, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- A Newton--Puiseux splitting witness for a distinguished polynomial consists
of centered formal branches. -/
theorem exists_centered_roots_of_hasRamifiedPowerSeriesSplitting
    {f : Polynomial (PowerSeries K)}
    (Hdist :
      f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    (Hsplit : HasRamifiedPowerSeriesSplitting f) :
    ∃ (p : ℕ) (hp : p ≠ 0)
        (roots : Fin f.natDegree → PowerSeries K),
      (∀ i,
        (ramifyPowerSeriesPolynomial p hp f).IsRoot (roots i) ∧
        (roots i).constantCoeff = 0) ∧
      ramifyPowerSeriesPolynomial p hp f =
        ∏ i, (Polynomial.X - Polynomial.C (roots i)) := by
  obtain ⟨p, hp, roots, hroots, hsplit⟩ := Hsplit.isRoot
  refine ⟨p, hp, roots, ?_, hsplit⟩
  intro i
  refine ⟨hroots i, ?_⟩
  exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    (isDistinguishedAt_ramifyPowerSeriesPolynomial Hdist p hp) (hroots i)

theorem exists_centered_roots_of_hasRamifiedPowerSeriesSplittingOver
    {L : Type*} [Field L] (σ : K →+* L)
    {f : Polynomial (PowerSeries K)}
    (Hdist :
      f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    (Hsplit : HasRamifiedPowerSeriesSplittingOver σ f) :
    ∃ (p : ℕ) (hp : p ≠ 0)
        (roots :
          Fin (mapPowerSeriesPolynomial σ f).natDegree → PowerSeries L),
      (∀ i,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial σ f)).IsRoot (roots i) ∧
        (roots i).constantCoeff = 0) ∧
      ramifyPowerSeriesPolynomial p hp (mapPowerSeriesPolynomial σ f) =
        ∏ i, (Polynomial.X - Polynomial.C (roots i)) := by
  exact exists_centered_roots_of_hasRamifiedPowerSeriesSplitting
    (isDistinguishedAt_mapPowerSeriesPolynomial σ Hdist) Hsplit

end Math
