/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability

/-!
# Total Variation Distance for Finite PMFs

This file promotes the positive-variation quantity from `Math.Probability` to a
compositional distance API. For probability mass functions it is the usual
half-`L¹` total variation distance.

## Main definitions

* `pmfTV` — total variation distance between finite PMFs
* `pmfTVChain` — accumulated distance through a list of intermediate laws

## Main results

* `pmfTV_eq_zero_iff` — identity of indiscernibles
* `pmfTV_symm` / `pmfTV_triangle` — symmetry and triangle inequality
* `pmfTV_map_le` — deterministic data processing
* `pmfTV_bind_le` — Markov-kernel data processing
* `pmfTV_le_chain` — finite hybrid-chain bound
-/

namespace Math
namespace Probability

/-- Total variation distance between two PMFs on a finite type. -/
noncomputable abbrev pmfTV {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) : ℝ :=
  pmfPositiveVariation μ ν

theorem pmfTV_nonneg {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    0 ≤ pmfTV μ ν :=
  pmfPositiveVariation_nonneg μ ν

theorem pmfTV_le_one {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν ≤ 1 := by
  change (∑ ω : Ω, max ((μ ω).toReal - (ν ω).toReal) 0) ≤ 1
  calc
    (∑ ω : Ω, max ((μ ω).toReal - (ν ω).toReal) 0)
        ≤ ∑ ω : Ω, (μ ω).toReal := by
          apply Finset.sum_le_sum
          intro ω _
          exact max_le
            (by
              have hν : 0 ≤ (ν ω).toReal := ENNReal.toReal_nonneg
              linarith)
            (show 0 ≤ (μ ω).toReal from ENNReal.toReal_nonneg)
    _ = 1 := pmf_toReal_sum_one μ

@[simp] theorem pmfTV_self {Ω : Type*} [Fintype Ω] (μ : PMF Ω) :
    pmfTV μ μ = 0 := by
  change pmfPositiveVariation μ μ = 0
  rw [pmfPositiveVariation_eq_half_sum_abs]
  simp

theorem pmfTV_symm {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν = pmfTV ν μ := by
  change pmfPositiveVariation μ ν = pmfPositiveVariation ν μ
  rw [pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact abs_sub_comm (μ ω).toReal (ν ω).toReal

@[simp] theorem pmfTV_eq_zero_iff {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    change pmfPositiveVariation μ ν = 0 at h
    have hsum :
        (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) = 0 := by
      have hhalf :
          (1 / 2 : ℝ) * ∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal| = 0 := by
        rw [← pmfPositiveVariation_eq_half_sum_abs]
        exact h
      nlinarith
    ext ω
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top μ ω) (PMF.apply_ne_top ν ω)).1
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => abs_nonneg ((μ x).toReal - (ν x).toReal))).mp hsum
        ω (Finset.mem_univ ω)
  · rintro rfl
    exact pmfTV_self μ

theorem pmfTV_triangle {Ω : Type*} [Fintype Ω] (μ ν ρ : PMF Ω) :
    pmfTV μ ρ ≤ pmfTV μ ν + pmfTV ν ρ := by
  change pmfPositiveVariation μ ρ ≤
    pmfPositiveVariation μ ν + pmfPositiveVariation ν ρ
  rw [pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs]
  have hsum :
      (∑ ω : Ω, |(μ ω).toReal - (ρ ω).toReal|) ≤
        (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) +
          ∑ ω : Ω, |(ν ω).toReal - (ρ ω).toReal| := by
    calc
      (∑ ω : Ω, |(μ ω).toReal - (ρ ω).toReal|)
          ≤ ∑ ω : Ω,
              (|(μ ω).toReal - (ν ω).toReal| +
                |(ν ω).toReal - (ρ ω).toReal|) := by
            apply Finset.sum_le_sum
            intro ω _
            exact abs_sub_le (μ ω).toReal (ν ω).toReal (ρ ω).toReal
      _ = (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) +
            ∑ ω : Ω, |(ν ω).toReal - (ρ ω).toReal| :=
        Finset.sum_add_distrib
  nlinarith

theorem pmfTV_map_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (μ ν : PMF α) :
    pmfTV (μ.map f) (ν.map f) ≤ pmfTV μ ν := by
  let w : β → ℝ := pmfPositiveVariationWitness (μ.map f) (ν.map f) 1
  change pmfPositiveVariation (μ.map f) (ν.map f) ≤ pmfPositiveVariation μ ν
  calc
    pmfPositiveVariation (μ.map f) (ν.map f)
        = expect (μ.map f) w - expect (ν.map f) w := by
          symm
          simpa [w] using
            expect_sub_pmfPositiveVariationWitness (μ.map f) (ν.map f) 1
    _ = expect μ (w ∘ f) - expect ν (w ∘ f) := by
      rw [expect_map, expect_map]
      rfl
    _ ≤ 1 * pmfPositiveVariation μ ν := by
      apply expect_sub_le_mul_pmfPositiveVariation
      · intro a
        exact pmfPositiveVariationWitness_nonneg
          (μ.map f) (ν.map f) zero_le_one (f a)
      · intro a
        exact pmfPositiveVariationWitness_le
          (μ.map f) (ν.map f) zero_le_one (f a)
    _ = pmfPositiveVariation μ ν := one_mul _

theorem pmfTV_bind_le {α β : Type*} [Fintype α] [Fintype β]
    (k : α → PMF β) (μ ν : PMF α) :
    pmfTV (μ.bind k) (ν.bind k) ≤ pmfTV μ ν := by
  let w : β → ℝ := pmfPositiveVariationWitness (μ.bind k) (ν.bind k) 1
  let g : α → ℝ := fun a => expect (k a) w
  change pmfPositiveVariation (μ.bind k) (ν.bind k) ≤ pmfPositiveVariation μ ν
  calc
    pmfPositiveVariation (μ.bind k) (ν.bind k)
        = expect (μ.bind k) w - expect (ν.bind k) w := by
          symm
          simpa [w] using
            expect_sub_pmfPositiveVariationWitness (μ.bind k) (ν.bind k) 1
    _ = expect μ g - expect ν g := by
      rw [expect_bind, expect_bind]
    _ ≤ 1 * pmfPositiveVariation μ ν := by
      apply expect_sub_le_mul_pmfPositiveVariation
      · intro a
        apply expect_nonneg
        intro b
        exact pmfPositiveVariationWitness_nonneg
          (μ.bind k) (ν.bind k) zero_le_one b
      · intro a
        have hle := expect_mono (k a) w (fun _ => 1) (fun b =>
          pmfPositiveVariationWitness_le
            (μ.bind k) (ν.bind k) zero_le_one b)
        simpa using hle
    _ = pmfPositiveVariation μ ν := one_mul _

/-- Sum of total-variation distances through a finite list of intermediate
laws. The empty list is the direct distance between the endpoints. -/
noncomputable def pmfTVChain {Ω : Type*} [Fintype Ω] :
    PMF Ω → List (PMF Ω) → PMF Ω → ℝ
  | μ, [], ν => pmfTV μ ν
  | μ, ρ :: rest, ν => pmfTV μ ρ + pmfTVChain ρ rest ν

@[simp] theorem pmfTVChain_nil {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTVChain μ [] ν = pmfTV μ ν := rfl

@[simp] theorem pmfTVChain_cons {Ω : Type*} [Fintype Ω]
    (μ ρ ν : PMF Ω) (rest : List (PMF Ω)) :
    pmfTVChain μ (ρ :: rest) ν = pmfTV μ ρ + pmfTVChain ρ rest ν := rfl

theorem pmfTV_le_chain {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (intermediates : List (PMF Ω)) :
    pmfTV μ ν ≤ pmfTVChain μ intermediates ν := by
  induction intermediates generalizing μ with
  | nil => exact le_rfl
  | cons ρ rest ih =>
      calc
        pmfTV μ ν ≤ pmfTV μ ρ + pmfTV ρ ν := pmfTV_triangle μ ρ ν
        _ ≤ pmfTV μ ρ + pmfTVChain ρ rest ν :=
          add_le_add (le_refl _) (ih ρ)
        _ = pmfTVChain μ (ρ :: rest) ν := rfl

theorem abs_expect_sub_le_range_mul_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (f : Ω → ℝ) {L U : ℝ}
    (hf_lower : ∀ ω, L ≤ f ω) (hf_upper : ∀ ω, f ω ≤ U) :
    |expect μ f - expect ν f| ≤ (U - L) * pmfTV μ ν := by
  have hshift (d : PMF Ω) :
      expect d (fun ω => f ω - L) = expect d f - L := by
    rw [expect_sub, expect_const]
  have hforward := expect_sub_le_mul_pmfPositiveVariation
    μ ν (fun ω => f ω - L) (U := U - L)
    (fun ω => by linarith [hf_lower ω])
    (fun ω => by linarith [hf_upper ω])
  have hreverse := expect_sub_le_mul_pmfPositiveVariation
    ν μ (fun ω => f ω - L) (U := U - L)
    (fun ω => by linarith [hf_lower ω])
    (fun ω => by linarith [hf_upper ω])
  rw [hshift μ, hshift ν] at hforward
  rw [hshift ν, hshift μ] at hreverse
  change expect ν f - L - (expect μ f - L) ≤
    (U - L) * pmfTV ν μ at hreverse
  rw [pmfTV_symm ν μ] at hreverse
  rw [abs_le]
  constructor <;> linarith

theorem abs_expect_sub_le_two_mul_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ ω, |f ω| ≤ C) :
    |expect μ f - expect ν f| ≤ (2 * C) * pmfTV μ ν := by
  have h := abs_expect_sub_le_range_mul_pmfTV μ ν f
    (L := -C) (U := C)
    (fun ω => (abs_le.mp (hf ω)).1)
    (fun ω => (abs_le.mp (hf ω)).2)
  simpa [show C - -C = 2 * C by ring] using h

end Probability
end Math
