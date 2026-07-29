/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

/-!
# Finite graded convolution certificates

Coefficientwise identities for a finite family of products. These are the
algebraic core of the cancellation ladder obtained after a common Puiseux
ramification.

The terminal nonzero scalar coefficient forces some transition coefficient
to pair nontrivially with some centered value coefficient. The scalar
identities alone do not assert any support or rank drop.
-/

open Finset BigOperators

namespace Math

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Total-degree `k` coefficient of the finite pairing of two coefficient
families. The pair indexed by `i` and `k - i` has total degree `k`. -/
def gradedPairingCoefficient
    (transition value : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    ∑ s, transition i s * value (k - i) s

/-- Subtracting an arbitrary scalar coefficient from every state value does
not change the graded pairing when every transition coefficient has zero
total mass. -/
theorem gradedPairingCoefficient_center_invariant
    (transition value : ℕ → ι → ℝ) (center : ℕ → ℝ)
    (hmass : ∀ i, ∑ s, transition i s = 0)
    (k : ℕ) :
    gradedPairingCoefficient transition
        (fun j s => value j s - center j) k =
      gradedPairingCoefficient transition value k := by
  unfold gradedPairingCoefficient
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass i]
  simp

/-- The finite exact data supplied by a cancellation ladder up to its first
nonzero stage coefficient. -/
structure GradedCancellationCertificate (ι : Type*) [Fintype ι] where
  /-- Terminal total degree. -/
  terminalDegree : ℕ
  /-- Nonzero stage coefficient at the terminal degree. -/
  stageCoefficient : ℝ
  /-- Transition coefficients after common ramification. -/
  transition : ℕ → ι → ℝ
  /-- Centered value coefficients after common ramification. -/
  value : ℕ → ι → ℝ
  /-- Every transition coefficient has zero total mass. -/
  transition_mass_zero : ∀ i, ∑ s, transition i s = 0
  /-- All total degrees below the terminal stage degree cancel. -/
  lower_cancel :
    ∀ k, k < terminalDegree →
      gradedPairingCoefficient transition value k = 0
  /-- The terminal transition/value coefficient balances the stage term. -/
  terminal_balance :
    stageCoefficient +
      gradedPairingCoefficient transition value terminalDegree = 0
  /-- The terminal stage coefficient is genuinely present. -/
  stage_ne_zero : stageCoefficient ≠ 0

namespace GradedCancellationCertificate

/-- The terminal transition/value convolution is nonzero. -/
theorem terminal_pairing_ne_zero
    (certificate : GradedCancellationCertificate ι) :
    gradedPairingCoefficient certificate.transition certificate.value
        certificate.terminalDegree ≠ 0 := by
  intro hzero
  have hbalance := certificate.terminal_balance
  rw [hzero, add_zero] at hbalance
  exact certificate.stage_ne_zero hbalance

/-- At the terminal degree, at least one transition coefficient pairs
nontrivially with the complementary value coefficient. -/
theorem exists_transition_visible_pair
    (certificate : GradedCancellationCertificate ι) :
    ∃ i < certificate.terminalDegree + 1,
      (∑ s, certificate.transition i s *
        certificate.value (certificate.terminalDegree - i) s) ≠ 0 := by
  have hsum := certificate.terminal_pairing_ne_zero
  unfold gradedPairingCoefficient at hsum
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨i, Finset.mem_range.mp hi, hne⟩

/-- Equivalent two-degree form of terminal visibility. -/
theorem exists_transition_visible_pair_degrees
    (certificate : GradedCancellationCertificate ι) :
    ∃ i j, i + j = certificate.terminalDegree ∧
      (∑ s, certificate.transition i s * certificate.value j s) ≠ 0 := by
  obtain ⟨i, hi, hvisible⟩ := certificate.exists_transition_visible_pair
  have hle : i ≤ certificate.terminalDegree := Nat.lt_succ_iff.mp hi
  exact ⟨i, certificate.terminalDegree - i,
    Nat.add_sub_of_le hle, hvisible⟩

/-- Centering the value coefficients produces another certificate with
identical stage data and transition coefficients. -/
def center
    (certificate : GradedCancellationCertificate ι)
    (centerCoefficient : ℕ → ℝ) :
    GradedCancellationCertificate ι where
  terminalDegree := certificate.terminalDegree
  stageCoefficient := certificate.stageCoefficient
  transition := certificate.transition
  value := fun j s => certificate.value j s - centerCoefficient j
  transition_mass_zero := certificate.transition_mass_zero
  lower_cancel := by
    intro k hk
    rw [gradedPairingCoefficient_center_invariant
      certificate.transition certificate.value centerCoefficient
      certificate.transition_mass_zero]
    exact certificate.lower_cancel k hk
  terminal_balance := by
    rw [gradedPairingCoefficient_center_invariant
      certificate.transition certificate.value centerCoefficient
      certificate.transition_mass_zero]
    exact certificate.terminal_balance
  stage_ne_zero := certificate.stage_ne_zero

end GradedCancellationCertificate

/-- An exact coefficient identity, vanishing of all earlier stage
coefficients, and a nonzero terminal stage coefficient produce the finite
graded certificate. -/
def GradedCancellationCertificate.ofCoefficientIdentity
    (stage : ℕ → ℝ) (transition value : ℕ → ι → ℝ) (K : ℕ)
    (hmass : ∀ i, ∑ s, transition i s = 0)
    (hidentity : ∀ k,
      stage k + gradedPairingCoefficient transition value k = 0)
    (hbelow : ∀ k, k < K → stage k = 0)
    (hterminal : stage K ≠ 0) :
    GradedCancellationCertificate ι where
  terminalDegree := K
  stageCoefficient := stage K
  transition := transition
  value := value
  transition_mass_zero := hmass
  lower_cancel := by
    intro k hk
    have h := hidentity k
    rw [hbelow k hk, zero_add] at h
    exact h
  terminal_balance := hidentity K
  stage_ne_zero := hterminal

end

end Math
