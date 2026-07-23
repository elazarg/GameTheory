/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.QuittingGame

/-!
# Continuous obstruction for the altered-singleton quitting game

This file records the exact finite-dimensional algebra behind the continuous
absorption-path obstruction for `alteredSingletonGame`.  It is independent of
both conjectural existence/refutation statements.
-/

noncomputable section

namespace GameTheory

/-- Normalized singleton residual matrix of the altered-singleton game. -/
def alteredSingletonR : Fin 4 → Fin 4 → ℝ
  | 0 => ![0, 4, -3, 3]
  | 1 => ![-1, 0, 3, -2]
  | 2 => ![2, -2, 0, -1]
  | 3 => ![-1, -1, 3, 0]

/-- Residual vector `R m`. -/
def alteredSingletonResidual (m : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ j, alteredSingletonR i j * m j

/-- Nonnegative masses with nonnegative singleton residuals. -/
def AlteredSingletonContinuousFeasible (m : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ m i) ∧ (∀ i, 0 ≤ alteredSingletonResidual m i)

/-- Rows at which the singleton residual vanishes. -/
def alteredSingletonZeroSet (m : Fin 4 → ℝ) : Finset (Fin 4) :=
  Finset.univ.filter fun i => alteredSingletonResidual m i = 0

/-- Bit mask of the zero-residual rows. -/
def alteredSingletonZeroMask (m : Fin 4 → ℝ) : ℕ :=
  quitMask (alteredSingletonZeroSet m)

/-- Coordinate unit vector in `ℝ⁴`. -/
def fin4Unit (i : Fin 4) : Fin 4 → ℝ :=
  fun j => if j = i then 1 else 0

/-- Probability simplex in `ℝ⁴`. -/
def IsSimplex4 (alpha : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1

/-- Admissible continuous mass-removal direction on a zero face. -/
def IsAlteredSingletonTangent
    (m alpha : Fin 4 → ℝ) : Prop :=
  IsSimplex4 alpha ∧
    (∀ i, 0 < alpha i → alteredSingletonResidual m i = 0) ∧
    (∀ i, alteredSingletonResidual m i = 0 →
      alteredSingletonResidual alpha i ≤ 0)

private theorem alteredSingleton_zeroMask_formula (m : Fin 4 → ℝ) :
    alteredSingletonZeroMask m =
      (if alteredSingletonResidual m 0 = 0 then 1 else 0) +
      (if alteredSingletonResidual m 1 = 0 then 2 else 0) +
      (if alteredSingletonResidual m 2 = 0 then 4 else 0) +
      (if alteredSingletonResidual m 3 = 0 then 8 else 0) := by
  simp only [alteredSingletonZeroMask, alteredSingletonZeroSet, quitMask]
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_four]

@[simp] theorem alteredSingletonResidual_zero (m : Fin 4 → ℝ) :
    alteredSingletonResidual m 0 = 4 * m 1 - 3 * m 2 + 3 * m 3 := by
  simp [alteredSingletonResidual, alteredSingletonR, Fin.sum_univ_succ]
  ring

@[simp] theorem alteredSingletonResidual_one (m : Fin 4 → ℝ) :
    alteredSingletonResidual m 1 = -m 0 + 3 * m 2 - 2 * m 3 := by
  simp [alteredSingletonResidual, alteredSingletonR, Fin.sum_univ_succ]
  ring

@[simp] theorem alteredSingletonResidual_two (m : Fin 4 → ℝ) :
    alteredSingletonResidual m 2 = 2 * m 0 - 2 * m 1 - m 3 := by
  simp [alteredSingletonResidual, alteredSingletonR, Fin.sum_univ_succ]
  ring

@[simp] theorem alteredSingletonResidual_three (m : Fin 4 → ℝ) :
    alteredSingletonResidual m 3 = -m 0 - m 1 + 3 * m 2 := by
  simp [alteredSingletonResidual, alteredSingletonR, Fin.sum_univ_succ]
  ring

/-- Exceptional tangent on the triple zero face `{1,2,3}`. -/
def tripleExceptional : Fin 4 → ℝ := ![0, 6 / 11, 2 / 11, 3 / 11]

@[simp] theorem alteredSingletonResidual_tripleExceptional_one :
    alteredSingletonResidual tripleExceptional 1 = 0 := by
  rw [alteredSingletonResidual_one]
  norm_num [tripleExceptional, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

@[simp] theorem alteredSingletonResidual_tripleExceptional_three :
    alteredSingletonResidual tripleExceptional 3 = 0 := by
  rw [alteredSingletonResidual_three]
  norm_num [tripleExceptional, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem alteredSingletonResidual_tripleExceptional_two :
    alteredSingletonResidual tripleExceptional 2 < 0 := by
  rw [alteredSingletonResidual_two]
  norm_num [tripleExceptional, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The only feasible vector on which rows `0`, `1`, and `2` all vanish is
the zero vector. -/
theorem alteredSingleton_eq_zero_of_residual_012_eq_zero
    {m : Fin 4 → ℝ} (hm : ∀ i, 0 ≤ m i)
    (h0 : alteredSingletonResidual m 0 = 0)
    (h1 : alteredSingletonResidual m 1 = 0)
    (h2 : alteredSingletonResidual m 2 = 0) :
    m = 0 := by
  simp only [alteredSingletonResidual_zero] at h0
  simp only [alteredSingletonResidual_one] at h1
  simp only [alteredSingletonResidual_two] at h2
  funext i
  fin_cases i <;> simp <;>
    linarith [hm 0, hm 1, hm 2, hm 3]

/-- The only feasible vector on which rows `0`, `2`, and `3` all vanish is
the zero vector. -/
theorem alteredSingleton_eq_zero_of_residual_023_eq_zero
    {m : Fin 4 → ℝ} (hm : ∀ i, 0 ≤ m i)
    (h0 : alteredSingletonResidual m 0 = 0)
    (h2 : alteredSingletonResidual m 2 = 0)
    (h3 : alteredSingletonResidual m 3 = 0) :
    m = 0 := by
  simp only [alteredSingletonResidual_zero] at h0
  simp only [alteredSingletonResidual_two] at h2
  simp only [alteredSingletonResidual_three] at h3
  funext i
  fin_cases i <;> simp <;>
    linarith [hm 0, hm 1, hm 2, hm 3]

/-- Every nonzero feasible zero face is one of the four singleton faces, six
pair faces, or the two viable triple faces `{0,1,3}` and `{1,2,3}`. -/
theorem alteredSingleton_zeroMask_classification
    {m : Fin 4 → ℝ}
    (hm : AlteredSingletonContinuousFeasible m)
    (hne : m ≠ 0)
    (hz : (alteredSingletonZeroSet m).Nonempty) :
    alteredSingletonZeroMask m = 1  ∨
    alteredSingletonZeroMask m = 2  ∨
    alteredSingletonZeroMask m = 4  ∨
    alteredSingletonZeroMask m = 8  ∨
    alteredSingletonZeroMask m = 3  ∨
    alteredSingletonZeroMask m = 5  ∨
    alteredSingletonZeroMask m = 6  ∨
    alteredSingletonZeroMask m = 9  ∨
    alteredSingletonZeroMask m = 10 ∨
    alteredSingletonZeroMask m = 12 ∨
    alteredSingletonZeroMask m = 11 ∨
    alteredSingletonZeroMask m = 14 := by
  rcases hm with ⟨hm, hr⟩
  have hz' : alteredSingletonResidual m 0 = 0 ∨
      alteredSingletonResidual m 1 = 0 ∨
      alteredSingletonResidual m 2 = 0 ∨
      alteredSingletonResidual m 3 = 0 := by
    rcases hz with ⟨i, hi⟩
    simp only [alteredSingletonZeroSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    fin_cases i <;> simp_all
  rw [alteredSingleton_zeroMask_formula]
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0
  all_goals simp_all only [Fin.isValue, alteredSingletonResidual_zero, alteredSingletonResidual_one,
    alteredSingletonResidual_two, alteredSingletonResidual_three]
  all_goals
    exfalso
    apply hne
    funext i
    fin_cases i <;> simp <;>
      linarith [hm 0, hm 1, hm 2, hm 3]

private theorem alteredSingleton_zeroMask_eq_three {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 3) :
    alteredSingletonResidual m 0 = 0 ∧
    alteredSingletonResidual m 1 = 0 ∧
    alteredSingletonResidual m 2 ≠ 0 ∧
    alteredSingletonResidual m 3 ≠ 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_five {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 5) :
    alteredSingletonResidual m 0 = 0 ∧
    alteredSingletonResidual m 1 ≠ 0 ∧
    alteredSingletonResidual m 2 = 0 ∧
    alteredSingletonResidual m 3 ≠ 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_six {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 6) :
    alteredSingletonResidual m 0 ≠ 0 ∧
    alteredSingletonResidual m 1 = 0 ∧
    alteredSingletonResidual m 2 = 0 ∧
    alteredSingletonResidual m 3 ≠ 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_nine {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 9) :
    alteredSingletonResidual m 0 = 0 ∧
    alteredSingletonResidual m 1 ≠ 0 ∧
    alteredSingletonResidual m 2 ≠ 0 ∧
    alteredSingletonResidual m 3 = 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_ten {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 10) :
    alteredSingletonResidual m 0 ≠ 0 ∧
    alteredSingletonResidual m 1 = 0 ∧
    alteredSingletonResidual m 2 ≠ 0 ∧
    alteredSingletonResidual m 3 = 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_eleven {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 11) :
    alteredSingletonResidual m 0 = 0 ∧
    alteredSingletonResidual m 1 = 0 ∧
    alteredSingletonResidual m 2 ≠ 0 ∧
    alteredSingletonResidual m 3 = 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_twelve {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 12) :
    alteredSingletonResidual m 0 ≠ 0 ∧
    alteredSingletonResidual m 1 ≠ 0 ∧
    alteredSingletonResidual m 2 = 0 ∧
    alteredSingletonResidual m 3 = 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem alteredSingleton_zeroMask_eq_fourteen {m : Fin 4 → ℝ}
    (h : alteredSingletonZeroMask m = 14) :
    alteredSingletonResidual m 0 ≠ 0 ∧
    alteredSingletonResidual m 1 = 0 ∧
    alteredSingletonResidual m 2 = 0 ∧
    alteredSingletonResidual m 3 = 0 := by
  rw [alteredSingleton_zeroMask_formula] at h
  by_cases h0 : alteredSingletonResidual m 0 = 0 <;>
    by_cases h1 : alteredSingletonResidual m 1 = 0 <;>
    by_cases h2 : alteredSingletonResidual m 2 = 0 <;>
    by_cases h3 : alteredSingletonResidual m 3 = 0 <;>
    simp_all

private theorem tangent_coordinate_eq_zero
    {m alpha : Fin 4 → ℝ}
    (ha : ∀ i, 0 ≤ alpha i)
    (hsupp : ∀ i, 0 < alpha i → alteredSingletonResidual m i = 0)
    {i : Fin 4} (hi : alteredSingletonResidual m i ≠ 0) :
    alpha i = 0 := by
  apply le_antisymm
  · exact le_of_not_gt fun hpos => hi (hsupp i hpos)
  · exact ha i

/-- The only tangent on zero face `{0,1}` removes player `0`. -/
theorem alteredSingleton_tangent_zeroMask_three
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 3) :
    alpha = fin4Unit 0 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, _, hm2, hm3⟩ := alteredSingleton_zeroMask_eq_three hmask
  have ha2 := tangent_coordinate_eq_zero ha hsupp hm2
  have ha3 := tangent_coordinate_eq_zero ha hsupp hm3
  have ht0 := htangent 0 hm0
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht0
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha1 : alpha 1 = 0 := by linarith [ha 1]
  have ha0 : alpha 0 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- The only tangent on zero face `{0,2}` removes player `2`. -/
theorem alteredSingleton_tangent_zeroMask_five
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 5) :
    alpha = fin4Unit 2 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨_, hm1, hm2, hm3⟩ := alteredSingleton_zeroMask_eq_five hmask
  have ha1 := tangent_coordinate_eq_zero ha hsupp hm1
  have ha3 := tangent_coordinate_eq_zero ha hsupp hm3
  have ht2 := htangent 2 hm2
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht2
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha0 : alpha 0 = 0 := by linarith [ha 0]
  have ha2 : alpha 2 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- The only tangent on zero face `{1,2}` removes player `1`. -/
theorem alteredSingleton_tangent_zeroMask_six
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 6) :
    alpha = fin4Unit 1 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, hm1, _, hm3⟩ := alteredSingleton_zeroMask_eq_six hmask
  have ha0 := tangent_coordinate_eq_zero ha hsupp hm0
  have ha3 := tangent_coordinate_eq_zero ha hsupp hm3
  have ht1 := htangent 1 hm1
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht1
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha2 : alpha 2 = 0 := by linarith [ha 2]
  have ha1 : alpha 1 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- The only tangent on zero face `{0,3}` removes player `0`. -/
theorem alteredSingleton_tangent_zeroMask_nine
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 9) :
    alpha = fin4Unit 0 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, hm1, hm2, _⟩ := alteredSingleton_zeroMask_eq_nine hmask
  have ha1 := tangent_coordinate_eq_zero ha hsupp hm1
  have ha2 := tangent_coordinate_eq_zero ha hsupp hm2
  have ht0 := htangent 0 hm0
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht0
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha3 : alpha 3 = 0 := by linarith [ha 3]
  have ha0 : alpha 0 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- The only tangent on zero face `{2,3}` removes player `3`. -/
theorem alteredSingleton_tangent_zeroMask_twelve
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 12) :
    alpha = fin4Unit 3 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, hm1, _, hm3⟩ := alteredSingleton_zeroMask_eq_twelve hmask
  have ha0 := tangent_coordinate_eq_zero ha hsupp hm0
  have ha1 := tangent_coordinate_eq_zero ha hsupp hm1
  have ht3 := htangent 3 hm3
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht3
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha2 : alpha 2 = 0 := by linarith [ha 2]
  have ha3 : alpha 3 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- The only tangent on zero face `{0,1,3}` removes player `0`. -/
theorem alteredSingleton_tangent_zeroMask_eleven
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 11) :
    alpha = fin4Unit 0 := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, _, hm2, _⟩ := alteredSingleton_zeroMask_eq_eleven hmask
  have ha2 := tangent_coordinate_eq_zero ha hsupp hm2
  have ht0 := htangent 0 hm0
  simp [alteredSingletonResidual, alteredSingletonR,
    Fin.sum_univ_four] at ht0
  have hsum' : alpha 0 + alpha 1 + alpha 2 + alpha 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have ha1 : alpha 1 = 0 := by nlinarith [ha 1, ha 3]
  have ha3 : alpha 3 = 0 := by nlinarith [ha 1, ha 3]
  have ha0 : alpha 0 = 1 := by linarith
  funext i
  fin_cases i <;> simp [fin4Unit, ha0, ha1, ha2, ha3]

/-- A tangent on the flexible face `{1,3}` is supported on those two
coordinates. -/
theorem alteredSingleton_tangent_zeroMask_ten_support
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 10) :
    alpha 0 = 0 ∧ alpha 2 = 0 := by
  rcases hT with ⟨⟨ha, _⟩, hsupp, _⟩
  obtain ⟨hm0, _, hm2, _⟩ := alteredSingleton_zeroMask_eq_ten hmask
  exact ⟨tangent_coordinate_eq_zero ha hsupp hm0,
    tangent_coordinate_eq_zero ha hsupp hm2⟩

/-- An interior mixture on `{1,3}` releases both zero rows immediately. -/
theorem alteredSingleton_tangent_zeroMask_ten_interior_releases
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 10)
    (ha1 : 0 < alpha 1) (ha3 : 0 < alpha 3) :
    alteredSingletonResidual alpha 1 < 0 ∧
    alteredSingletonResidual alpha 3 < 0 := by
  obtain ⟨ha0, ha2⟩ := alteredSingleton_tangent_zeroMask_ten_support hT hmask
  constructor <;>
    simp [alteredSingletonResidual, alteredSingletonR,
      Fin.sum_univ_four, ha0, ha2] <;>
    linarith

/-- Every tangent on the triple face `{1,2,3}` lies in the triangle spanned
by its two endpoint controls and `tripleExceptional`. -/
theorem alteredSingleton_tangent_zeroMask_fourteen_convexHull
    {m alpha : Fin 4 → ℝ}
    (hT : IsAlteredSingletonTangent m alpha)
    (hmask : alteredSingletonZeroMask m = 14) :
    ∃ l1 l3 lt : ℝ,
      0 ≤ l1 ∧ 0 ≤ l3 ∧ 0 ≤ lt ∧
      l1 + l3 + lt = 1 ∧
      alpha = l1 • fin4Unit 1 + l3 • fin4Unit 3 +
        lt • tripleExceptional := by
  rcases hT with ⟨⟨ha, hsum⟩, hsupp, htangent⟩
  obtain ⟨hm0, hm1, _, hm3⟩ := alteredSingleton_zeroMask_eq_fourteen hmask
  have ha0 := tangent_coordinate_eq_zero ha hsupp hm0
  have ht1 := htangent 1 hm1
  have ht3 := htangent 3 hm3
  simp only [alteredSingletonResidual_one, alteredSingletonResidual_three,
    ha0, neg_zero, zero_add] at ht1 ht3
  rw [Fin.sum_univ_four] at hsum
  refine ⟨alpha 1 - 3 * alpha 2,
    alpha 3 - (3 / 2) * alpha 2,
    (11 / 2) * alpha 2, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith [ha 2]
  · linarith
  · funext i
    fin_cases i <;> simp [fin4Unit, tripleExceptional, ha0] <;> ring

/-- Under the weak nonnegativity hypothesis from the continuous calculation,
the return map cannot lie above the repetition threshold. -/
theorem cycle_0210_return_le
    {b d : ℝ} (hd : 0 ≤ d) (_hlo : d / 2 ≤ b) (hhi : b ≤ 2 * d) :
    b / 4 - d / 8 ≤ d / 2 := by
  nlinarith

/-- The return map of a nondegenerate completed `0 → 2 → 1 → 0`
cycle exits the region in which that cycle can repeat.  Strict positivity of
`d` is necessary: with `b = d = 0`, the weak hypotheses hold but the requested
strict inequality becomes `0 < 0`. -/
theorem cycle_0210_cannot_repeat
    {b d : ℝ} (hd : 0 < d) (_hlo : d / 2 ≤ b) (hhi : b ≤ 2 * d) :
    b / 4 - d / 8 < d / 2 := by
  nlinarith

/-- A nonzero `0 → 2 → 3 → 0` cycle is algebraically impossible. -/
theorem cycle_0230_impossible
    {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hfirst : 2 * d ≤ b) (hreturn : 4 * b ≤ d) :
    b = 0 ∧ d = 0 := by
  constructor <;> nlinarith

end GameTheory
