/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring

/-!
# Maximizing a certificate ratio over finitely many rays

This file isolates the algebraic step used after enumerating the extreme
rays of a polyhedral certificate cone.

A certificate has a value `B` and a nonnegative mass `M`.  Every certificate
is assumed to decompose into a nonnegative linear combination of finitely
many rays, with both `B` and `M` preserved.  Rays of mass zero are harmless:
their value is nonpositive.  It follows that every positive-mass certificate
ratio `B z / M z` is bounded by, and the supremum is attained at, one of the
finitely many positive-mass rays.

The final theorem packages the additive argument used when every global ray
decomposes into playerwise certificates.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace Math
namespace LinearAlgebra

variable {Certificate Ray : Type*} [Fintype Ray]

/-- `ray` generates every certificate by a nonnegative finite combination,
and the combination preserves both certificate value and mass. -/
def HasFiniteRayDecomposition
    (ray : Ray → Certificate) (B M : Certificate → ℝ) : Prop :=
  ∀ z, ∃ a : Ray → ℝ,
    (∀ r, 0 ≤ a r) ∧
    B z = ∑ r, a r * B (ray r) ∧
    M z = ∑ r, a r * M (ray r)

/-- The set of ratios of all positive-mass certificates. -/
def positiveMassRatioSet (B M : Certificate → ℝ) : Set ℝ :=
  {q | ∃ z, 0 < M z ∧ q = B z / M z}

/-- A zero-mass/nonpositive-value hypothesis and a positive-mass ratio bound
combine into the homogeneous inequality `B z ≤ value * M z`. -/
theorem value_mul_mass_bound
    (B M : Certificate → ℝ) (value : ℝ) (z : Certificate)
    (hmass : 0 ≤ M z)
    (hzero : M z = 0 → B z ≤ 0)
    (hratio : 0 < M z → B z / M z ≤ value) :
    B z ≤ value * M z := by
  rcases hmass.eq_or_lt with hmass_zero | hmass_pos
  · rw [← hmass_zero]
    simpa using hzero hmass_zero.symm
  · exact (div_le_iff₀ hmass_pos).mp (hratio hmass_pos)

/-- Among finitely many generating rays, some positive-mass ray maximizes
the ratio of every positive-mass ray and, by the decomposition hypothesis,
the ratio of every positive-mass certificate. -/
theorem exists_maximizing_positiveMass_ray
    (ray : Ray → Certificate) (B M : Certificate → ℝ)
    (hrayMass : ∀ r, 0 ≤ M (ray r))
    (hzeroRay : ∀ r, M (ray r) = 0 → B (ray r) ≤ 0)
    (hpositiveRay : ∃ r, 0 < M (ray r))
    (hdecompose : HasFiniteRayDecomposition ray B M) :
    ∃ rMax,
      0 < M (ray rMax) ∧
      (∀ r, 0 < M (ray r) →
        B (ray r) / M (ray r) ≤
          B (ray rMax) / M (ray rMax)) ∧
      (∀ z, 0 < M z →
        B z / M z ≤ B (ray rMax) / M (ray rMax)) := by
  classical
  let positiveRays : Finset Ray :=
    Finset.univ.filter fun r => 0 < M (ray r)
  have hpositiveRays : positiveRays.Nonempty := by
    obtain ⟨r, hr⟩ := hpositiveRay
    exact ⟨r, by simp [positiveRays, hr]⟩
  obtain ⟨rMax, hrMax_mem, hrMax⟩ :=
    positiveRays.exists_max_image
      (fun r => B (ray r) / M (ray r)) hpositiveRays
  have hrMax_mass : 0 < M (ray rMax) := by
    simpa [positiveRays] using hrMax_mem
  have hrMax_ratio :
      ∀ r, 0 < M (ray r) →
        B (ray r) / M (ray r) ≤
          B (ray rMax) / M (ray rMax) := by
    intro r hr
    exact hrMax r (by simp [positiveRays, hr])
  refine ⟨rMax, hrMax_mass, hrMax_ratio, ?_⟩
  intro z hzMass
  obtain ⟨a, ha, hB, hM⟩ := hdecompose z
  have hterm :
      ∀ r,
        a r * B (ray r) ≤
          (B (ray rMax) / M (ray rMax)) *
            (a r * M (ray r)) := by
    intro r
    by_cases hrMassZero : M (ray r) = 0
    · calc
        a r * B (ray r) ≤ a r * 0 :=
          mul_le_mul_of_nonneg_left (hzeroRay r hrMassZero) (ha r)
        _ = (B (ray rMax) / M (ray rMax)) *
            (a r * M (ray r)) := by simp [hrMassZero]
    · have hrMassPos : 0 < M (ray r) :=
        lt_of_le_of_ne (hrayMass r) (Ne.symm hrMassZero)
      have hrValue :
          B (ray r) ≤
            (B (ray rMax) / M (ray rMax)) * M (ray r) :=
        (div_le_iff₀ hrMassPos).mp (hrMax_ratio r hrMassPos)
      calc
        a r * B (ray r) ≤
            a r * ((B (ray rMax) / M (ray rMax)) * M (ray r)) :=
          mul_le_mul_of_nonneg_left hrValue (ha r)
        _ = (B (ray rMax) / M (ray rMax)) *
            (a r * M (ray r)) := by ring
  apply (div_le_iff₀ hzMass).mpr
  calc
    B z = ∑ r, a r * B (ray r) := hB
    _ ≤ ∑ r, (B (ray rMax) / M (ray rMax)) *
          (a r * M (ray r)) :=
      Finset.sum_le_sum fun r _ => hterm r
    _ = (B (ray rMax) / M (ray rMax)) *
          ∑ r, a r * M (ray r) := by rw [Finset.mul_sum]
    _ = (B (ray rMax) / M (ray rMax)) * M z := by rw [hM]

/-- The supremum over all positive-mass certificates is exactly the ratio
of one positive-mass generating ray. -/
theorem exists_positiveMass_ray_sSup_eq
    (ray : Ray → Certificate) (B M : Certificate → ℝ)
    (hrayMass : ∀ r, 0 ≤ M (ray r))
    (hzeroRay : ∀ r, M (ray r) = 0 → B (ray r) ≤ 0)
    (hpositiveRay : ∃ r, 0 < M (ray r))
    (hdecompose : HasFiniteRayDecomposition ray B M) :
    ∃ rMax,
      0 < M (ray rMax) ∧
      sSup (positiveMassRatioSet B M) =
        B (ray rMax) / M (ray rMax) := by
  obtain ⟨rMax, hrMaxMass, _hrayMax, hcertificateMax⟩ :=
    exists_maximizing_positiveMass_ray
      ray B M hrayMass hzeroRay hpositiveRay hdecompose
  refine ⟨rMax, hrMaxMass, le_antisymm ?_ ?_⟩
  · apply csSup_le
    · exact ⟨B (ray rMax) / M (ray rMax),
        ray rMax, hrMaxMass, rfl⟩
    · intro q hq
      obtain ⟨z, hzMass, rfl⟩ := hq
      exact hcertificateMax z hzMass
  · apply le_csSup
    · exact ⟨B (ray rMax) / M (ray rMax), fun q hq => by
        obtain ⟨z, hzMass, rfl⟩ := hq
        exact hcertificateMax z hzMass⟩
    · exact ⟨ray rMax, hrMaxMass, rfl⟩

/-- If all positive-mass generators have already been normalized to mass
one, then one of them attains the supremum by its certificate value `B`. -/
theorem exists_normalized_ray_sSup_eq
    (ray : Ray → Certificate) (B M : Certificate → ℝ)
    (hrayMass : ∀ r, 0 ≤ M (ray r))
    (hzeroRay : ∀ r, M (ray r) = 0 → B (ray r) ≤ 0)
    (hpositiveRay : ∃ r, 0 < M (ray r))
    (hnormalized : ∀ r, 0 < M (ray r) → M (ray r) = 1)
    (hdecompose : HasFiniteRayDecomposition ray B M) :
    ∃ rMax,
      M (ray rMax) = 1 ∧
      sSup (positiveMassRatioSet B M) = B (ray rMax) := by
  obtain ⟨rMax, hrMaxMass, hrMax⟩ :=
    exists_positiveMass_ray_sSup_eq
      ray B M hrayMass hzeroRay hpositiveRay hdecompose
  have hrMaxNormalized := hnormalized rMax hrMaxMass
  refine ⟨rMax, hrMaxNormalized, ?_⟩
  simpa [hrMaxNormalized] using hrMax

variable {Player : Type*} [Fintype Player]
variable {LocalCertificate : Player → Type*}

/-- Additive playerwise decomposition gives equality of global and local
values.  The local scalar `localValue i` bounds every local certificate
ratio, including the homogeneous zero-mass case.  The reverse inequality
`localValue ≤ sSup ...` is the abstract form of embedding every playerwise
certificate into the global certificate cone. -/
theorem sSup_positiveMassRatio_eq_of_playerwise_decomposition
    (ray : Ray → Certificate) (B M : Certificate → ℝ)
    (localB localM : ∀ i, LocalCertificate i → ℝ)
    (localValue : Player → ℝ) (localMax : ℝ)
    (hrayMass : ∀ r, 0 ≤ M (ray r))
    (hzeroRay : ∀ r, M (ray r) = 0 → B (ray r) ≤ 0)
    (hpositiveRay : ∃ r, 0 < M (ray r))
    (hdecompose : HasFiniteRayDecomposition ray B M)
    (hlocalMass : ∀ i w, 0 ≤ localM i w)
    (hlocalZero :
      ∀ i w, localM i w = 0 → localB i w ≤ 0)
    (hlocalRatio :
      ∀ i w, 0 < localM i w →
        localB i w / localM i w ≤ localValue i)
    (hlocalValue_le : ∀ i, localValue i ≤ localMax)
    (hrayPlayerwise :
      ∀ r, ∃ w : ∀ i, LocalCertificate i,
        B (ray r) = ∑ i, localB i (w i) ∧
        M (ray r) = ∑ i, localM i (w i))
    (hlocal_le_global :
      localMax ≤ sSup (positiveMassRatioSet B M)) :
    sSup (positiveMassRatioSet B M) = localMax := by
  have hrayRatio_le :
      ∀ r, 0 < M (ray r) →
        B (ray r) / M (ray r) ≤ localMax := by
    intro r hrMass
    obtain ⟨w, hB, hM⟩ := hrayPlayerwise r
    apply (div_le_iff₀ hrMass).mpr
    calc
      B (ray r) = ∑ i, localB i (w i) := hB
      _ ≤ ∑ i, localValue i * localM i (w i) := by
        apply Finset.sum_le_sum
        intro i _
        exact value_mul_mass_bound
          (localB i) (localM i) (localValue i) (w i)
          (hlocalMass i (w i)) (hlocalZero i (w i))
          (hlocalRatio i (w i))
      _ ≤ ∑ i, localMax * localM i (w i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (hlocalValue_le i) (hlocalMass i (w i))
      _ = localMax * ∑ i, localM i (w i) := by
        rw [Finset.mul_sum]
      _ = localMax * M (ray r) := by rw [hM]
  obtain ⟨rMax, hrMaxMass, _hrayMax, hcertificateMax⟩ :=
    exists_maximizing_positiveMass_ray
      ray B M hrayMass hzeroRay hpositiveRay hdecompose
  apply le_antisymm
  · apply csSup_le
    · exact ⟨B (ray rMax) / M (ray rMax),
        ray rMax, hrMaxMass, rfl⟩
    · intro q hq
      obtain ⟨z, hzMass, rfl⟩ := hq
      exact (hcertificateMax z hzMass).trans
        (hrayRatio_le rMax hrMaxMass)
  · exact hlocal_le_global

end LinearAlgebra
end Math
