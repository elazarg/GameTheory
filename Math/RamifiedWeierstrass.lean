/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Polynomial.Splits

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

theorem ramifyPowerSeriesPolynomial_comp
    (p : ℕ) (hp : p ≠ 0) (q : ℕ) (hq : q ≠ 0)
    (f : Polynomial (PowerSeries K)) :
    ramifyPowerSeriesPolynomial p hp
        (ramifyPowerSeriesPolynomial q hq f) =
      ramifyPowerSeriesPolynomial (p * q) (p.mul_ne_zero hp hq) f := by
  apply Polynomial.ext
  intro n
  simp only [ramifyPowerSeriesPolynomial, Polynomial.coeff_map]
  exact (PowerSeries.expand_mul p hp q hq (f.coeff n)).symm

theorem ramifyPowerSeriesPolynomial_mul
    (p : ℕ) (hp : p ≠ 0)
    (f g : Polynomial (PowerSeries K)) :
    ramifyPowerSeriesPolynomial p hp (f * g) =
      ramifyPowerSeriesPolynomial p hp f *
        ramifyPowerSeriesPolynomial p hp g := by
  simp [ramifyPowerSeriesPolynomial]

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
  ∃ (p : ℕ) (hp : p ≠ 0),
    (ramifyPowerSeriesPolynomial p hp f).Splits

/-- Newton--Puiseux splitting after extending the coefficient field and
ramifying the parameter. The intended real-curve instance uses the inclusion
`ℝ →+* ℂ`. -/
def HasRamifiedPowerSeriesSplittingOver
    {L : Type*} [Field L] (σ : K →+* L)
    (f : Polynomial (PowerSeries K)) : Prop :=
  HasRamifiedPowerSeriesSplitting (mapPowerSeriesPolynomial σ f)

theorem HasRamifiedPowerSeriesSplitting.of_splits
    {f : Polynomial (PowerSeries K)} (H : f.Splits) :
    HasRamifiedPowerSeriesSplitting f := by
  refine ⟨1, one_ne_zero, ?_⟩
  simpa [ramifyPowerSeriesPolynomial] using H

theorem HasRamifiedPowerSeriesSplitting.mul
    {f g : Polynomial (PowerSeries K)}
    (Hf : HasRamifiedPowerSeriesSplitting f)
    (Hg : HasRamifiedPowerSeriesSplitting g) :
    HasRamifiedPowerSeriesSplitting (f * g) := by
  obtain ⟨p, hp, hfsplit⟩ := Hf
  obtain ⟨q, hq, hgsplit⟩ := Hg
  refine ⟨p * q, p.mul_ne_zero hp hq, ?_⟩
  rw [ramifyPowerSeriesPolynomial_mul]
  have hfsplit' :
      (ramifyPowerSeriesPolynomial q hq
        (ramifyPowerSeriesPolynomial p hp f)).Splits :=
    hfsplit.map (PowerSeries.expand q hq).toRingHom
  have hgsplit' :
      (ramifyPowerSeriesPolynomial p hp
        (ramifyPowerSeriesPolynomial q hq g)).Splits :=
    hgsplit.map (PowerSeries.expand p hp).toRingHom
  rw [ramifyPowerSeriesPolynomial_comp] at hfsplit'
  rw [ramifyPowerSeriesPolynomial_comp] at hgsplit'
  have hfsplit'' :
      (ramifyPowerSeriesPolynomial (p * q) (p.mul_ne_zero hp hq) f).Splits := by
    simpa only [mul_comm q p] using hfsplit'
  exact hfsplit''.mul hgsplit'

theorem HasRamifiedPowerSeriesSplitting.of_ramify
    {f : Polynomial (PowerSeries K)}
    (p : ℕ) (hp : p ≠ 0)
    (H : HasRamifiedPowerSeriesSplitting
      (ramifyPowerSeriesPolynomial p hp f)) :
    HasRamifiedPowerSeriesSplitting f := by
  obtain ⟨q, hq, hsplit⟩ := H
  refine ⟨q * p, q.mul_ne_zero hq hp, ?_⟩
  rw [← ramifyPowerSeriesPolynomial_comp]
  exact hsplit

/-- The irreducible Newton--Puiseux task: every nonconstant monic polynomial
over formal power series acquires one formal root after a finite
ramification. -/
def HasRamifiedRootProperty (K : Type*) [Field K] : Prop :=
  ∀ f : Polynomial (PowerSeries K), f.Monic → 0 < f.natDegree →
    ∃ (p : ℕ) (hp : p ≠ 0) (s : PowerSeries K),
      (ramifyPowerSeriesPolynomial p hp f).IsRoot s

/-- Constructing one ramified formal root for every nonconstant monic
polynomial is sufficient for full ramified splitting. The proof repeatedly
removes the resulting linear factor and combines the finitely many
ramifications. -/
theorem hasRamifiedPowerSeriesSplitting_of_hasRamifiedRootProperty
    (Hroot : HasRamifiedRootProperty K)
    (f : Polynomial (PowerSeries K)) (hf : f.Monic) :
    HasRamifiedPowerSeriesSplitting f := by
  generalize hfn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
      by_cases hn : n = 0
      · have hf_one : f = 1 :=
          Polynomial.eq_one_of_monic_natDegree_zero hf (hfn.trans hn)
        rw [hf_one]
        exact HasRamifiedPowerSeriesSplitting.of_splits
          Polynomial.Splits.one
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        obtain ⟨p, hp, s, hs⟩ := Hroot f hf (hfn.symm ▸ hnpos)
        let F := ramifyPowerSeriesPolynomial p hp f
        let lin : Polynomial (PowerSeries K) :=
          Polynomial.X - Polynomial.C s
        let q := F /ₘ lin
        have hlin_monic : lin.Monic := by
          simpa [lin] using Polynomial.monic_X_sub_C s
        have hF_monic : F.Monic := by
          exact hf.map _
        have hfactor : lin * q = F := by
          exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hs
        have hF_ne : F ≠ 0 := hF_monic.ne_zero
        have hlin_dvd : lin ∣ F := ⟨q, hfactor.symm⟩
        have hdegree : lin.degree ≤ F.degree :=
          Polynomial.degree_le_of_dvd hlin_dvd hF_ne
        have hq_monic : q.Monic := by
          rw [Polynomial.Monic,
            Polynomial.leadingCoeff_divByMonic_of_monic hlin_monic hdegree]
          exact hF_monic
        have hF_natDegree : F.natDegree = n := by
          exact (hf.natDegree_map _).trans hfn
        have hq_natDegree : q.natDegree = n - 1 := by
          change (F /ₘ lin).natDegree = n - 1
          rw [Polynomial.natDegree_divByMonic F hlin_monic,
            hF_natDegree]
          simp [lin]
        have hq_lt : q.natDegree < n := by
          rw [hq_natDegree]
          exact Nat.sub_lt hnpos Nat.zero_lt_one
        have hq_split :
            HasRamifiedPowerSeriesSplitting q :=
          ih q.natDegree hq_lt q hq_monic rfl
        have hlin_split :
            HasRamifiedPowerSeriesSplitting lin := by
          change HasRamifiedPowerSeriesSplitting
            (Polynomial.X - Polynomial.C s)
          exact HasRamifiedPowerSeriesSplitting.of_splits
            (Polynomial.Splits.X_sub_C s)
        have hF_split :
            HasRamifiedPowerSeriesSplitting F := by
          rw [← hfactor]
          exact hlin_split.mul hq_split
        exact HasRamifiedPowerSeriesSplitting.of_ramify p hp hF_split

theorem hasRamifiedPowerSeriesSplittingOver_of_hasRamifiedRootProperty
    {L : Type*} [Field L] (σ : K →+* L)
    (Hroot : HasRamifiedRootProperty L)
    {f : Polynomial (PowerSeries K)} (hf : f.Monic) :
    HasRamifiedPowerSeriesSplittingOver σ f :=
  hasRamifiedPowerSeriesSplitting_of_hasRamifiedRootProperty Hroot
    (mapPowerSeriesPolynomial σ f) (hf.map _)

/-- A Newton--Puiseux splitting witness for a distinguished polynomial consists
of centered formal branches. -/
theorem exists_centered_roots_of_hasRamifiedPowerSeriesSplitting
    {f : Polynomial (PowerSeries K)}
    (Hdist :
      f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    (Hsplit : HasRamifiedPowerSeriesSplitting f) :
    ∃ (p : ℕ) (hp : p ≠ 0),
      (ramifyPowerSeriesPolynomial p hp f).Splits ∧
      ∀ s, (ramifyPowerSeriesPolynomial p hp f).IsRoot s →
        s.constantCoeff = 0 := by
  obtain ⟨p, hp, hsplit⟩ := Hsplit
  refine ⟨p, hp, hsplit, ?_⟩
  intro s hs
  exact constantCoeff_eq_zero_of_isRoot_of_isDistinguishedAt
    (isDistinguishedAt_ramifyPowerSeriesPolynomial Hdist p hp) hs

theorem exists_centered_roots_of_hasRamifiedPowerSeriesSplittingOver
    {L : Type*} [Field L] (σ : K →+* L)
    {f : Polynomial (PowerSeries K)}
    (Hdist :
      f.IsDistinguishedAt (IsLocalRing.maximalIdeal (PowerSeries K)))
    (Hsplit : HasRamifiedPowerSeriesSplittingOver σ f) :
    ∃ (p : ℕ) (hp : p ≠ 0),
      (ramifyPowerSeriesPolynomial p hp
        (mapPowerSeriesPolynomial σ f)).Splits ∧
      ∀ s,
        (ramifyPowerSeriesPolynomial p hp
          (mapPowerSeriesPolynomial σ f)).IsRoot s →
        s.constantCoeff = 0 := by
  exact exists_centered_roots_of_hasRamifiedPowerSeriesSplitting
    (isDistinguishedAt_mapPowerSeriesPolynomial σ Hdist) Hsplit

end Math
