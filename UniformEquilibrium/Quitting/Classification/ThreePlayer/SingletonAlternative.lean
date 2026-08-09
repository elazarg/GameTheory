/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Three-coordinate singleton alternative

This is a finite, semantic-free alternative for a three-coordinate singleton
source packet. The input is a zero-diagonal excess matrix `M` and a feasible
probability `μ`. The output is either a complementary probability or one of
the two strict directed three-cycles.

The singleton-payoff adapter at the end is the interface used by the
strategic compilers; the finite classification itself does not mention
quitting-game strategies.
-/

noncomputable section

namespace GameTheory

abbrev ThreePlayer := Fin 3

/-! ## Packets and certificates -/

def threeMixed (M : ThreePlayer → ThreePlayer → ℝ)
    (μ : ThreePlayer → ℝ) (i : ThreePlayer) : ℝ :=
  ∑ j, M i j * μ j

structure ThreeProbability (μ : ThreePlayer → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ μ i
  total : ∑ i, μ i = 1

structure ThreeComplementaryProbability
    (M : ThreePlayer → ThreePlayer → ℝ) where
  mass : ThreePlayer → ℝ
  probability : ThreeProbability mass
  feasible : ∀ i, 0 ≤ threeMixed M mass i
  complementary : ∀ i, mass i * threeMixed M mass i = 0
  active_diagonal : ∀ i, 0 < mass i → M i i = 0

structure ThreeRightStrictCycle
    (M : ThreePlayer → ThreePlayer → ℝ) where
  p : ℝ
  q : ℝ
  r : ℝ
  s : ℝ
  t : ℝ
  u : ℝ
  hp : 0 < p
  hq : 0 < q
  hr : 0 < r
  hs : 0 < s
  ht : 0 < t
  hu : 0 < u
  h01 : M 0 1 = -p
  h02 : M 0 2 = q
  h10 : M 1 0 = s
  h12 : M 1 2 = -r
  h20 : M 2 0 = -t
  h21 : M 2 1 = u
  determinant : 0 < q * s * u - p * r * t
  diagonal : ∀ i, M i i = 0

structure ThreeLeftStrictCycle
    (M : ThreePlayer → ThreePlayer → ℝ) where
  p : ℝ
  q : ℝ
  r : ℝ
  s : ℝ
  t : ℝ
  u : ℝ
  hp : 0 < p
  hq : 0 < q
  hr : 0 < r
  hs : 0 < s
  ht : 0 < t
  hu : 0 < u
  h01 : M 0 1 = p
  h02 : M 0 2 = -q
  h10 : M 1 0 = -s
  h12 : M 1 2 = r
  h20 : M 2 0 = t
  h21 : M 2 1 = -u
  determinant : 0 < p * r * t - q * s * u
  diagonal : ∀ i, M i i = 0

inductive ThreeSingletonAlternative
    (M : ThreePlayer → ThreePlayer → ℝ) : Type
  | complementary (certificate : ThreeComplementaryProbability M)
  | right (certificate : ThreeRightStrictCycle M)
  | left (certificate : ThreeLeftStrictCycle M)

lemma threeMixed_explicit (M : ThreePlayer → ThreePlayer → ℝ)
    (μ : ThreePlayer → ℝ) (i : ThreePlayer) :
    threeMixed M μ i = M i 0 * μ 0 + M i 1 * μ 1 + M i 2 * μ 2 := by
  simp [threeMixed, Fin.sum_univ_succ, add_assoc]

lemma pure_probability (j : ThreePlayer) :
    ThreeProbability (fun i => if i = j then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · intro i
    split_ifs <;> norm_num
  · simp

noncomputable def pure_complementary
    (M : ThreePlayer → ThreePlayer → ℝ)
    (j : ThreePlayer) (hdiag : M j j = 0)
    (hcolumn : ∀ i, 0 ≤ M i j) :
    ThreeComplementaryProbability M := by
  let e : ThreePlayer → ℝ := fun i => if i = j then 1 else 0
  refine ⟨e, pure_probability j, ?_, ?_, ?_⟩
  · intro i
    rw [threeMixed]
    simp only [e]
    classical
    rw [Finset.sum_eq_single j]
    · simpa [hdiag] using hcolumn i
    · intro b hb hbj
      simp [hbj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro i
    by_cases hij : i = j
    · subst i
      simp [threeMixed, e, hdiag]
    · simp [e, hij]
  · intro i hi
    have hij : i = j := by
      by_contra hne
      simp [e, hne] at hi
    subst i
    exact hdiag

/-! ## The two small supports -/

private lemma fin3_eq_of_three_distinct
    (i j k l : ThreePlayer) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    i = j ∨ i = k ∨ i = l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

lemma pure_of_two_zeros
    (M : ThreePlayer → ThreePlayer → ℝ)
    (μ : ThreePlayer → ℝ) (hμ : ThreeProbability μ)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hactive : ∀ i, 0 < μ i → M i i = 0)
    {j k : ThreePlayer} (hjk : j ≠ k)
    (hj : μ j = 0) (hk : μ k = 0) :
    Nonempty (ThreeComplementaryProbability M) := by
  classical
  have hsum := hμ.total
  have hleft : ∃ l : ThreePlayer, l ≠ j ∧ l ≠ k := by
    fin_cases j <;> fin_cases k
    · contradiction
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · contradiction
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · contradiction
  rcases hleft with ⟨l, hlj, hlk⟩
  have hl : μ l = 1 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [Fin.sum_univ_succ]
  have hdiag_l : M l l = 0 := hactive l (by linarith)
  have hcolumn : ∀ i, 0 ≤ M i l := by
    intro i
    have hi := hfeas i
    rw [threeMixed_explicit] at hi
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all
  exact ⟨pure_complementary M l hdiag_l hcolumn⟩

lemma pure_of_two_support
    (M : ThreePlayer → ThreePlayer → ℝ)
    (μ : ThreePlayer → ℝ) (_hμ : ThreeProbability μ)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hactive : ∀ i, 0 < μ i → M i i = 0)
    {j k l : ThreePlayer} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hj : 0 < μ j) (hk : 0 < μ k) (hl : μ l = 0) :
    Nonempty (ThreeComplementaryProbability M) := by
  classical
  have hdiag_j : M j j = 0 := hactive j hj
  have hdiag_k : M k k = 0 := hactive k hk
  have hkj := hfeas k
  have hjj := hfeas j
  rw [threeMixed_explicit] at hkj hjj
  have hcross_kj : 0 ≤ M k j := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all
  have hcross_jk : 0 ≤ M j k := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all
  have hrest := hfeas l
  rw [threeMixed_explicit] at hrest
  by_cases hlj : 0 ≤ M l j
  · have hcolumn : ∀ i, 0 ≤ M i j := by
      intro i
      rcases fin3_eq_of_three_distinct i j k l hjk hjl hkl with
        rfl | rfl | rfl
      · exact hdiag_j.ge
      · exact hcross_kj
      · exact hlj
    exact ⟨pure_complementary M j hdiag_j hcolumn⟩
  · have hlk : 0 ≤ M l k := by
      by_contra hn
      push Not at hn
      fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp_all <;> nlinarith
    have hcolumn : ∀ i, 0 ≤ M i k := by
      intro i
      rcases fin3_eq_of_three_distinct i j k l hjk hjl hkl with
        rfl | rfl | rfl
      · exact hcross_jk
      · exact hdiag_k.ge
      · exact hlk
    exact ⟨pure_complementary M k hdiag_k hcolumn⟩

/-! ## Sign extraction in the full-support case -/

lemma column_has_negative
    (M : ThreePlayer → ThreePlayer → ℝ)
    (hnoColumn : ¬ ∃ j, ∀ i, 0 ≤ M i j) :
    ∀ j, ∃ i, M i j < 0 := by
  intro j
  by_contra hn
  push Not at hn
  exact hnoColumn ⟨j, hn⟩

lemma row_has_positive
    (M : ThreePlayer → ThreePlayer → ℝ)
    (hdiag : ∀ i, M i i = 0)
    (μ : ThreePlayer → ℝ) (_hμ : ThreeProbability μ)
    (hμpos : ∀ i, 0 < μ i)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hcolneg : ∀ j, ∃ i, M i j < 0) :
    ∀ i, ∃ j, j ≠ i ∧ 0 < M i j := by
  intro i
  fin_cases i
  · by_contra hn
    push Not at hn
    have h01 : M 0 1 ≤ 0 := hn 1 (by decide)
    have h02 : M 0 2 ≤ 0 := hn 2 (by decide)
    have hz01 : M 0 1 = 0 := by
      have h0 := hfeas 0
      rw [threeMixed_explicit] at h0
      simp [hdiag] at h0
      nlinarith [h0, hμpos 1, hμpos 2]
    have hz02 : M 0 2 = 0 := by
      have h0 := hfeas 0
      rw [threeMixed_explicit] at h0
      simp [hdiag] at h0
      nlinarith [h0, hμpos 1, hμpos 2]
    rcases hcolneg 1 with ⟨k, hk⟩
    rcases hcolneg 2 with ⟨l, hl⟩
    rcases hcolneg 0 with ⟨m, hm⟩
    fin_cases k <;> fin_cases l <;> fin_cases m <;>
      simp_all
    all_goals
      have h1 := hfeas 1
      have h2 := hfeas 2
      rw [threeMixed_explicit] at h1 h2
      simp [hdiag] at h1 h2
      nlinarith [h1, h2, hμpos 0, hμpos 1, hμpos 2]
  · by_contra hn
    push Not at hn
    have h10 : M 1 0 ≤ 0 := hn 0 (by decide)
    have h12 : M 1 2 ≤ 0 := hn 2 (by decide)
    have hz10 : M 1 0 = 0 := by
      have h1 := hfeas 1
      rw [threeMixed_explicit] at h1
      simp [hdiag] at h1
      nlinarith [h1, hμpos 0, hμpos 2]
    have hz12 : M 1 2 = 0 := by
      have h1 := hfeas 1
      rw [threeMixed_explicit] at h1
      simp [hdiag] at h1
      nlinarith [h1, hμpos 0, hμpos 2]
    rcases hcolneg 0 with ⟨k, hk⟩
    rcases hcolneg 2 with ⟨l, hl⟩
    rcases hcolneg 1 with ⟨m, hm⟩
    fin_cases k <;> fin_cases l <;> fin_cases m <;>
      simp_all
    all_goals
      have h0 := hfeas 0
      have h2 := hfeas 2
      rw [threeMixed_explicit] at h0 h2
      simp [hdiag] at h0 h2
      nlinarith [h0, h2, hμpos 0, hμpos 1, hμpos 2]
  · by_contra hn
    push Not at hn
    have h20 : M 2 0 ≤ 0 := hn 0 (by decide)
    have h21 : M 2 1 ≤ 0 := hn 1 (by decide)
    have hz20 : M 2 0 = 0 := by
      have h2 := hfeas 2
      rw [threeMixed_explicit] at h2
      simp [hdiag] at h2
      nlinarith [h2, hμpos 0, hμpos 1]
    have hz21 : M 2 1 = 0 := by
      have h2 := hfeas 2
      rw [threeMixed_explicit] at h2
      simp [hdiag] at h2
      nlinarith [h2, hμpos 0, hμpos 1]
    rcases hcolneg 0 with ⟨k, hk⟩
    rcases hcolneg 1 with ⟨l, hl⟩
    rcases hcolneg 2 with ⟨m, hm⟩
    fin_cases k <;> fin_cases l <;> fin_cases m <;>
      simp_all
    all_goals
      have h0 := hfeas 0
      have h1 := hfeas 1
      rw [threeMixed_explicit] at h0 h1
      simp [hdiag] at h0 h1
      nlinarith [h0, h1, hμpos 0, hμpos 1, hμpos 2]

lemma triple_product_lt
    {a b c d e f : ℝ}
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (_hf : 0 < f)
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    (hstrict : a < b ∨ c < d ∨ e < f) :
    a * c * e < b * d * f := by
  rcases hstrict with hab' | hcd' | hef'
  · calc
      a * c * e < b * c * e := by
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hab' hc) he
      _ ≤ b * d * e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcd (le_of_lt hb)) (le_of_lt he)
      _ ≤ b * d * f := by
        exact mul_le_mul_of_nonneg_left hef
          (mul_nonneg (le_of_lt hb) (le_of_lt hd))
  · calc
      a * c * e ≤ b * c * e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hab (le_of_lt hc)) (le_of_lt he)
      _ < b * d * e := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hcd' hb) he
      _ ≤ b * d * f := by
        exact mul_le_mul_of_nonneg_left hef
          (mul_nonneg (le_of_lt hb) (le_of_lt hd))
  · calc
      a * c * e ≤ b * c * e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hab (le_of_lt hc)) (le_of_lt he)
      _ ≤ b * d * e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcd (le_of_lt hb)) (le_of_lt he)
      _ < b * d * f := by
        exact mul_lt_mul_of_pos_left hef'
          (mul_pos hb hd)

private lemma right_strict_cycle_of_orientation
    (M : ThreePlayer → ThreePlayer → ℝ)
    (hdiag : ∀ i, M i i = 0)
    (μ : ThreePlayer → ℝ)
    (hμpos : ∀ i, 0 < μ i)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hrowpos : ∀ i, ∃ j, j ≠ i ∧ 0 < M i j)
    (hi0 : M 2 0 < 0) (hi1 : M 0 1 < 0) (hi2 : M 1 2 < 0)
    (hcomp : ¬∀ i, threeMixed M μ i = 0) :
    Nonempty (ThreeRightStrictCycle M) := by
  classical
  have h02 : 0 < M 0 2 := by
    rcases hrowpos 0 with ⟨j0, hj0, hj0p⟩
    fin_cases j0
    · simp_all
    · exact (lt_asymm hi1 hj0p).elim
    · exact hj0p
  have h10 : 0 < M 1 0 := by
    rcases hrowpos 1 with ⟨j1, hj1, hj1p⟩
    fin_cases j1
    · exact hj1p
    · simp_all
    · exact (lt_asymm hi2 hj1p).elim
  have h21 : 0 < M 2 1 := by
    rcases hrowpos 2 with ⟨j2, hj2, hj2p⟩
    fin_cases j2
    · exact (lt_asymm hi0 hj2p).elim
    · exact hj2p
    · simp_all
  refine ⟨⟨-M 0 1, M 0 2, -M 1 2, M 1 0, -M 2 0, M 2 1,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by ring, rfl, rfl, by ring, by ring, rfl, ?_, hdiag⟩⟩
  have h0 := hfeas 0
  have h1 := hfeas 1
  have h2 := hfeas 2
  rw [threeMixed_explicit] at h0 h1 h2
  rw [hdiag 0] at h0
  rw [hdiag 1] at h1
  rw [hdiag 2] at h2
  simp only [zero_mul, zero_add, add_zero] at h0 h1 h2
  have h0' : (-M 0 1) * μ 1 ≤ M 0 2 * μ 2 := by nlinarith [h0]
  have h1' : (-M 1 2) * μ 2 ≤ M 1 0 * μ 0 := by nlinarith [h1]
  have h2' : (-M 2 0) * μ 0 ≤ M 2 1 * μ 1 := by nlinarith [h2]
  have hA : 0 < (-M 0 1) * μ 1 := mul_pos (by linarith) (hμpos 1)
  have hB : 0 < M 0 2 * μ 2 := mul_pos h02 (hμpos 2)
  have hC : 0 < (-M 1 2) * μ 2 := mul_pos (by linarith) (hμpos 2)
  have hD : 0 < M 1 0 * μ 0 := mul_pos h10 (hμpos 0)
  have hE : 0 < (-M 2 0) * μ 0 := mul_pos (by linarith) (hμpos 0)
  have hF : 0 < M 2 1 * μ 1 := mul_pos h21 (hμpos 1)
  have hcases :
      (-M 0 1) * μ 1 < M 0 2 * μ 2 ∨
        (-M 1 2) * μ 2 < M 1 0 * μ 0 ∨
          (-M 2 0) * μ 0 < M 2 1 * μ 1 := by
    by_contra hz
    push Not at hz
    apply hcomp
    intro i
    fin_cases i <;> simp [threeMixed_explicit, hdiag] <;>
      nlinarith [h0, h1, h2, hz.1, hz.2.1, hz.2.2]
  have hprod := triple_product_lt hA hB hC hD hE hF h0' h1' h2' hcases
  ring_nf at hprod
  nlinarith [hprod, mul_pos (mul_pos (hμpos 0) (hμpos 1)) (hμpos 2)]

private lemma left_strict_cycle_of_orientation
    (M : ThreePlayer → ThreePlayer → ℝ)
    (hdiag : ∀ i, M i i = 0)
    (μ : ThreePlayer → ℝ)
    (hμpos : ∀ i, 0 < μ i)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hrowpos : ∀ i, ∃ j, j ≠ i ∧ 0 < M i j)
    (hi0 : M 1 0 < 0) (hi1 : M 2 1 < 0) (hi2 : M 0 2 < 0)
    (hcomp : ¬∀ i, threeMixed M μ i = 0) :
    Nonempty (ThreeLeftStrictCycle M) := by
  classical
  have h01 : 0 < M 0 1 := by
    rcases hrowpos 0 with ⟨j0, hj0, hj0p⟩
    fin_cases j0
    · simp_all
    · exact hj0p
    · exact (lt_asymm hi2 hj0p).elim
  have h12 : 0 < M 1 2 := by
    rcases hrowpos 1 with ⟨j1, hj1, hj1p⟩
    fin_cases j1
    · exact (lt_asymm hi0 hj1p).elim
    · simp_all
    · exact hj1p
  have h20 : 0 < M 2 0 := by
    rcases hrowpos 2 with ⟨j2, hj2, hj2p⟩
    fin_cases j2
    · exact hj2p
    · exact (lt_asymm hi1 hj2p).elim
    · simp_all
  refine ⟨⟨M 0 1, -M 0 2, M 1 2, -M 1 0, M 2 0, -M 2 1,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, rfl, by ring, by ring, rfl, rfl, by ring, ?_, hdiag⟩⟩
  have h0 := hfeas 0
  have h1 := hfeas 1
  have h2 := hfeas 2
  rw [threeMixed_explicit] at h0 h1 h2
  rw [hdiag 0] at h0
  rw [hdiag 1] at h1
  rw [hdiag 2] at h2
  simp only [zero_mul, zero_add, add_zero] at h0 h1 h2
  have h0' : (-M 0 2) * μ 2 ≤ M 0 1 * μ 1 := by nlinarith [h0]
  have h1' : (-M 1 0) * μ 0 ≤ M 1 2 * μ 2 := by nlinarith [h1]
  have h2' : (-M 2 1) * μ 1 ≤ M 2 0 * μ 0 := by nlinarith [h2]
  have hA : 0 < (-M 0 2) * μ 2 := mul_pos (by linarith) (hμpos 2)
  have hB : 0 < M 0 1 * μ 1 := mul_pos h01 (hμpos 1)
  have hC : 0 < (-M 1 0) * μ 0 := mul_pos (by linarith) (hμpos 0)
  have hD : 0 < M 1 2 * μ 2 := mul_pos h12 (hμpos 2)
  have hE : 0 < (-M 2 1) * μ 1 := mul_pos (by linarith) (hμpos 1)
  have hF : 0 < M 2 0 * μ 0 := mul_pos h20 (hμpos 0)
  have hcases :
      (-M 0 2) * μ 2 < M 0 1 * μ 1 ∨
        (-M 1 0) * μ 0 < M 1 2 * μ 2 ∨
          (-M 2 1) * μ 1 < M 2 0 * μ 0 := by
    by_contra hz
    push Not at hz
    apply hcomp
    intro i
    fin_cases i <;> simp [threeMixed_explicit, hdiag] <;>
      nlinarith [h0, h1, h2, hz.1, hz.2.1, hz.2.2]
  have hprod := triple_product_lt hA hB hC hD hE hF h0' h1' h2' hcases
  ring_nf at hprod
  nlinarith [hprod, mul_pos (mul_pos (hμpos 0) (hμpos 1)) (hμpos 2)]

/-- With full source support, feasibility and zero diagonal force either a
complementary probability or one of the two strict directed sign cycles. -/
lemma full_support_sign_cycle
    (M : ThreePlayer → ThreePlayer → ℝ)
    (hdiag : ∀ i, M i i = 0)
    (μ : ThreePlayer → ℝ) (hμ : ThreeProbability μ)
    (hμpos : ∀ i, 0 < μ i)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hnoColumn : ¬ ∃ j, ∀ i, 0 ≤ M i j) :
    Nonempty (ThreeComplementaryProbability M) ∨
      Nonempty (ThreeRightStrictCycle M) ∨ Nonempty (ThreeLeftStrictCycle M) := by
  classical
  by_cases hcomp : ∀ i, threeMixed M μ i = 0
  · exact Or.inl ⟨⟨μ, hμ,
      hfeas, (fun i => by simp [hcomp i]), fun i _ => hdiag i⟩⟩
  have hcolneg := column_has_negative M hnoColumn
  have hrowpos := row_has_positive M hdiag μ hμ hμpos hfeas hcolneg
  have hc0 : M 2 0 < 0 ∨ M 1 0 < 0 := by
    rcases hcolneg 0 with ⟨i, hi⟩
    fin_cases i <;> simp_all
  have hc1 : M 0 1 < 0 ∨ M 2 1 < 0 := by
    rcases hcolneg 1 with ⟨i, hi⟩
    fin_cases i <;> simp_all
  have hc2 : M 1 2 < 0 ∨ M 0 2 < 0 := by
    rcases hcolneg 2 with ⟨i, hi⟩
    fin_cases i <;> simp_all
  have hnotrow0 : ¬(M 0 1 < 0 ∧ M 0 2 < 0) := by
    rintro ⟨h01, h02⟩
    rcases hrowpos 0 with ⟨j, hne, hj⟩
    fin_cases j <;> simp_all <;> linarith
  have hnotrow1 : ¬(M 1 0 < 0 ∧ M 1 2 < 0) := by
    rintro ⟨h10, h12⟩
    rcases hrowpos 1 with ⟨j, hne, hj⟩
    fin_cases j <;> simp_all <;> linarith
  have hnotrow2 : ¬(M 2 0 < 0 ∧ M 2 1 < 0) := by
    rintro ⟨h20, h21⟩
    rcases hrowpos 2 with ⟨j, hne, hj⟩
    fin_cases j <;> simp_all <;> linarith
  rcases hc0 with hi0 | hi0 <;>
    rcases hc1 with hi1 | hi1 <;>
    rcases hc2 with hi2 | hi2
  all_goals try { exact (hnotrow0 ⟨hi1, hi2⟩).elim }
  all_goals try { exact (hnotrow1 ⟨hi0, hi2⟩).elim }
  all_goals try { exact (hnotrow2 ⟨hi0, hi1⟩).elim }
  · exact Or.inr (Or.inl
      (right_strict_cycle_of_orientation
        M hdiag μ hμpos hfeas hrowpos hi0 hi1 hi2 hcomp))
  · exact Or.inr (Or.inr
      (left_strict_cycle_of_orientation
        M hdiag μ hμpos hfeas hrowpos hi0 hi1 hi2 hcomp))

/-! ## Main source-packet alternative -/

/-- Every feasible three-coordinate source with an active zero diagonal has a
complementary probability or one of the two strict directed cycle
certificates. Degenerate supports are absorbed by the complementary branch. -/
noncomputable def three_singleton_source_alternative
    (M : ThreePlayer → ThreePlayer → ℝ)
    (μ : ThreePlayer → ℝ) (hμ : ThreeProbability μ)
    (hfeas : ∀ i, 0 ≤ threeMixed M μ i)
    (hactive : ∀ i, 0 < μ i → M i i = 0) :
    ThreeSingletonAlternative M := by
  classical
  by_cases h0 : μ 0 = 0
  · by_cases h1 : μ 1 = 0
    · exact .complementary
        (Classical.choice (pure_of_two_zeros M μ hμ hfeas hactive
          (j := 0) (k := 1) (by decide) h0 h1))
    · by_cases h2 : μ 2 = 0
      · exact .complementary
          (Classical.choice (pure_of_two_zeros M μ hμ hfeas hactive
            (j := 0) (k := 2) (by decide) h0 h2))
      · exact .complementary (Classical.choice (pure_of_two_support M μ hμ hfeas hactive
            (j := 1) (k := 2) (l := 0)
            (by decide) (by decide) (by decide)
            (by exact lt_of_le_of_ne (hμ.nonneg 1) (Ne.symm h1))
            (by exact lt_of_le_of_ne (hμ.nonneg 2) (Ne.symm h2)) h0))
  · by_cases h1 : μ 1 = 0
    · by_cases h2 : μ 2 = 0
      · exact .complementary
          (Classical.choice (pure_of_two_zeros M μ hμ hfeas hactive
            (j := 1) (k := 2) (by decide) h1 h2))
      · exact .complementary (Classical.choice (pure_of_two_support M μ hμ hfeas hactive
            (j := 0) (k := 2) (l := 1)
            (by decide) (by decide) (by decide)
            (by exact lt_of_le_of_ne (hμ.nonneg 0) (Ne.symm h0))
            (by exact lt_of_le_of_ne (hμ.nonneg 2) (Ne.symm h2)) h1))
    · by_cases h2 : μ 2 = 0
      · exact .complementary (Classical.choice (pure_of_two_support M μ hμ hfeas hactive
            (j := 0) (k := 1) (l := 2)
            (by decide) (by decide) (by decide)
            (by exact lt_of_le_of_ne (hμ.nonneg 0) (Ne.symm h0))
            (by exact lt_of_le_of_ne (hμ.nonneg 1) (Ne.symm h1)) h2))
      · have hμpos : ∀ i, 0 < μ i := by
          intro i
          fin_cases i
          · exact lt_of_le_of_ne (hμ.nonneg 0) (Ne.symm h0)
          · exact lt_of_le_of_ne (hμ.nonneg 1) (Ne.symm h1)
          · exact lt_of_le_of_ne (hμ.nonneg 2) (Ne.symm h2)
        have hdiag : ∀ i, M i i = 0 := fun i => hactive i (hμpos i)
        by_cases hcolumn : ∃ j, ∀ i, 0 ≤ M i j
        · let j : ThreePlayer := Classical.choose hcolumn
          have hj : ∀ i, 0 ≤ M i j := Classical.choose_spec hcolumn
          exact .complementary (pure_complementary M j (hdiag j) hj)
        · have hsign := full_support_sign_cycle M hdiag μ hμ hμpos hfeas hcolumn
          by_cases hc : Nonempty (ThreeComplementaryProbability M)
          · exact .complementary (Classical.choice hc)
          by_cases hr : Nonempty (ThreeRightStrictCycle M)
          · exact .right (Classical.choice hr)
          · have hl : Nonempty (ThreeLeftStrictCycle M) := by
              rcases hsign with hc' | hr' | hl'
              · exact (hc hc').elim
              · exact (hr hr').elim
              · exact hl'
            exact .left (Classical.choice hl)

/-! ## Singleton-payoff-facing adapter -/

def singletonExcess
    (a : ThreePlayer → ThreePlayer → ℝ) (target : ThreePlayer → ℝ) :
    ThreePlayer → ThreePlayer → ℝ :=
  fun i j => a j i - target i

def singletonMixed
    (a : ThreePlayer → ThreePlayer → ℝ) (ν : ThreePlayer → ℝ)
    (i : ThreePlayer) : ℝ :=
  ∑ j, ν j * a j i

structure SingletonComplementarySourceCertificate
    (a : ThreePlayer → ThreePlayer → ℝ)
    (target : ThreePlayer → ℝ) where
  mass : ThreePlayer → ℝ
  probability : ThreeProbability mass
  mixed_ge_target : ∀ i, target i ≤ singletonMixed a mass i
  active_pins : ∀ i, 0 < mass i → singletonMixed a mass i = a i i

noncomputable def complementary_of_excess_certificate
    (a : ThreePlayer → ThreePlayer → ℝ)
    (target : ThreePlayer → ℝ)
    (c : ThreeComplementaryProbability (singletonExcess a target)) :
    SingletonComplementarySourceCertificate a target := by
  refine ⟨c.mass, c.probability, ?_, ?_⟩
  · intro i
    have hi := c.feasible i
    unfold threeMixed singletonExcess at hi
    have hsum :
        ∑ j, (a j i - target i) * c.mass j =
          singletonMixed a c.mass i - target i := by
      calc
        _ = ∑ j, (c.mass j * a j i - target i * c.mass j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = singletonMixed a c.mass i - target i := by
          simp only [singletonMixed]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          rw [c.probability.total]
          ring
    rw [hsum] at hi
    linarith
  · intro i hi
    have hz := c.complementary i
    have hzero : threeMixed (singletonExcess a target) c.mass i = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt hi)
    unfold threeMixed singletonExcess at hzero
    have hsum :
        ∑ j, (a j i - target i) * c.mass j =
          singletonMixed a c.mass i - target i := by
      calc
        _ = ∑ j, (c.mass j * a j i - target i * c.mass j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = singletonMixed a c.mass i - target i := by
          simp only [singletonMixed]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          rw [c.probability.total]
          ring
    rw [hsum] at hzero
    have hdiag := c.active_diagonal i hi
    unfold singletonExcess at hdiag
    linarith

end GameTheory
