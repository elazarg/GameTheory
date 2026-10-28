module

/-
Envelope and expected-payment consumers with signed quantities, jump
allocations, nonzero baseline charges, and atomic type laws.
-/

public import GameTheory.Analysis.SingleParameter
public import GameTheory.Tests.SingleParameter
public import GameTheory.Math.Probability.ExpectationMixture
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

noncomputable section

namespace GameTheory.Tests.SingleParameterAnalysis

open Mechanism Mechanism.SingleParameterMechanism Math.Probability MeasureTheory
open GameTheory.Tests.SingleParameter

/-- The identity allocation is signed and globally unbounded. Its envelope
integral across negative and positive reports is nonzero and negative. -/
theorem signed_envelope :
    (∫ s in (-2 : ℝ)..1, OwnAllocation quadratic.allocation () typeTwo s) = -3 / 2 := by
  have h := quadratic.utility_eq_add_integral quadratic_isDSIC () typeTwo (-2) 1
  norm_num [utility, quadratic, Profile.update_same] at h
  linarith

@[reducible]
def jump : SingleParameterMechanism Unit where
  allocation reports _ := if reports () < 1 then -1 else 3
  payment reports _ := if reports () < 1 then 3 else 7

theorem jump_isDSIC : jump.IsDSIC := by
  rw [jump.isDSIC_iff]
  intro who reports r
  cases who
  simp only [utility, Profile.update_same]
  split_ifs <;> nlinarith

def atomicTypes : PMF ℝ := mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure 0) (PMF.pure 2)

private theorem expect_atomicTypes (f : ℝ → ℝ) :
    expect atomicTypes f = (f 0 + f 2) / 2 := by
  rw [atomicTypes, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)]
  simp only [expect_pure]
  ring

theorem jump_expected_payment :
    expect atomicTypes (fun t => jump.payment (Profile.update typeTwo () t) ()) = 5 := by
  rw [expect_atomicTypes]
  norm_num [Profile.update_same]

private theorem atomicTypes_support : atomicTypes.support ⊆ Set.Icc 0 2 := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t; norm_num
  by_cases ht2 : t = 2
  · subst t; norm_num
  have hz : atomicTypes t = 0 := by
    simp [atomicTypes, mix_apply, PMF.pure_apply, ht0, ht2]
  exact False.elim (ht hz)

/-- The general identity computes a nonzero tail integral for a signed jump
allocation and a law with atoms, while retaining a nonzero baseline payment. -/
theorem atomic_tail_integral :
    (∫ s in (0 : ℝ)..2, OwnAllocation jump.allocation () typeTwo s *
      (atomicTypes.toMeasure (Set.Ici s)).toReal) = 1 := by
  have h := jump.expected_payment_eq jump_isDSIC atomicTypes () typeTwo
    (by norm_num : (0 : ℝ) ≤ 2) atomicTypes_support
  rw [jump_expected_payment, expect_atomicTypes] at h
  norm_num [OwnAllocation, Profile.update_same] at h ⊢
  linarith

@[reducible]
def opponentFee : SingleParameterMechanism Bool where
  allocation reports who := reports who
  payment reports who := (reports who) ^ 2 / 2 + reports (!who)

theorem opponentFee_isDSIC : opponentFee.IsDSIC := by
  rw [opponentFee.isDSIC_iff]
  intro who reports r
  have hne : (!who) ≠ who := by cases who <;> decide
  simp only [utility, Profile.update_same]
  change reports who * r - (r ^ 2 / 2 + Profile.update reports who r (!who)) ≤
    reports who * reports who - ((reports who) ^ 2 / 2 + reports (!who))
  rw [Profile.update_of_ne reports r hne]
  nlinarith [sq_nonneg (r - reports who)]

theorem opponentFee_payment_recovery (who : Bool) (reports : Bool → ℝ) (t : ℝ) :
    opponentFee.payment (Profile.update reports who t) who =
      opponentFee.payment (Profile.update reports who 0) who +
        t * OwnAllocation opponentFee.allocation who reports t -
        ∫ s in 0..t, OwnAllocation opponentFee.allocation who reports s := by
  simpa only [zero_mul, sub_zero] using
    opponentFee.payment_identity opponentFee_isDSIC who reports 0 t

theorem wrong_payment_identity_rejected :
    ¬ (∀ who reports t,
      zeroPayment.payment (Profile.update reports who t) who =
        zeroPayment.payment (Profile.update reports who 0) who +
          t * OwnAllocation zeroPayment.allocation who reports t -
          ∫ s in 0..t, OwnAllocation zeroPayment.allocation who reports s) := by
  intro h
  exact zeroPayment_not_isDSIC
    (zeroPayment.isDSIC_iff_monotone_payment_identity.mpr ⟨quadratic_isMonotone, h⟩)

def uniformTypes : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure uniformTypes := ⟨by simp [uniformTypes]⟩

private theorem uniform_square : (∫ t, t ^ 2 ∂uniformTypes) = 1 / 3 := by
  change (∫ t : ℝ in Set.Icc 0 1, t ^ 2) = 1 / 3
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num [integral_pow]

theorem uniform_expected_payment :
    (∫ t, quadratic.payment (Profile.update typeTwo () t) () ∂uniformTypes) = 1 / 6 := by
  change (∫ t, t ^ 2 / 2 ∂uniformTypes) = 1 / 6
  rw [integral_div, uniform_square]
  norm_num

/-- The ordinary-measure consumer uses a diffuse law without adding any
measurable-game semantics. -/
theorem uniform_tail_integral :
    (∫ s in (0 : ℝ)..1, OwnAllocation quadratic.allocation () typeTwo s *
      (uniformTypes (Set.Ici s)).toReal) = 1 / 6 := by
  have hs : ∀ᵐ t ∂uniformTypes, t ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have h := quadratic.integral_payment_eq quadratic_isDSIC uniformTypes () typeTwo
    (by norm_num : (0 : ℝ) ≤ 1) hs
  rw [uniform_expected_payment] at h
  have hv : (∫ t, t * OwnAllocation quadratic.allocation () typeTwo t ∂uniformTypes) = 1 / 3 := by
    simpa only [OwnAllocation, quadratic, Profile.update_same, pow_two] using uniform_square
  rw [hv] at h
  norm_num [OwnAllocation, Profile.update_same] at h ⊢
  linarith

/-- Arbitrary natural-number laws give bounded real type laws; no finite
support assumption is introduced by the expected-payment theorem. -/
theorem countable_expected_payment (ν : PMF ℕ) :
    let μ := ν.map (fun n : ℕ => (n : ℝ) / (n + 1))
    expect μ (fun t => quadratic.payment (Profile.update typeTwo () t) ()) =
      expect μ (fun t => t ^ 2) -
        ∫ s in (0 : ℝ)..1, OwnAllocation quadratic.allocation () typeTwo s *
          (μ.toMeasure (Set.Ici s)).toReal := by
  dsimp only
  have hs : (ν.map (fun n : ℕ => (n : ℝ) / (n + 1))).support ⊆ Set.Icc 0 1 := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨n, _, rfl⟩ := ht
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
      linarith
  have h := quadratic.expected_payment_eq quadratic_isDSIC
    (ν.map (fun n : ℕ => (n : ℝ) / (n + 1))) () typeTwo
    (by norm_num : (0 : ℝ) ≤ 1) hs
  simpa only [OwnAllocation, quadratic, Profile.update_same, zero_pow (by decide : 2 ≠ 0),
    zero_div, zero_mul, zero_add, sub_zero, pow_two] using h

end GameTheory.Tests.SingleParameterAnalysis
