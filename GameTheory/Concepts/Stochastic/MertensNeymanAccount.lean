/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive

/-!
# The stochastic account update for uniform zero-sum strategies

This file isolates the three-point account update used by published
Mertens–Neyman-style uniform-value constructions. Given a multiplicative
step `γ > 1`, current account `s`, floor `M`, and payoff/value gap `y`, the
next account is `γs`, `s`, or `γ⁻¹s`.

The upward and downward probabilities are calibrated so that the expected
account increment is exactly `y` away from the floor. At the floor,
downward motion is suppressed; the resulting error is bounded by one when
`-1 ≤ y`. The scale conditions make explicit a prerequisite that informal
descriptions can hide: the account must be large enough for these formulas
to define probabilities.

This is the algebraic kernel behind the account telescope. It does not
assert the discounted-value variation estimate or the floor-occupation
bound needed for a complete securing strategy.

The formulation follows Section 4 of Hansen, Ibsen-Jensen, and Neyman,
*Stochastic Games with Limited Public Memory*.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Math.Probability

/-- The three possible multiplicative account moves. -/
inductive AccountMove
  | up
  | stay
  | down
  deriving DecidableEq, Fintype

/-- Probability of moving from `s` to `γs`. -/
def upProbability (γ s y : ℝ) : ℝ :=
  max y 0 / (s * (γ - 1))

/-- Probability of moving from `s` to `γ⁻¹s`. Downward motion is suppressed
at the account floor. -/
def downProbability (γ M s y : ℝ) : ℝ :=
  if M < s then min y 0 / (s * (γ⁻¹ - 1)) else 0

/-- Probability of leaving the account unchanged. -/
def stayProbability (γ M s y : ℝ) : ℝ :=
  1 - upProbability γ s y - downProbability γ M s y

/-- Expected one-step account increment under the up/stay/down weights. -/
def expectedChange (γ M s y : ℝ) : ℝ :=
  upProbability γ s y * (γ * s - s) +
    downProbability γ M s y * (γ⁻¹ * s - s)

/-- Sufficient scale conditions for the three account-update weights to be
probabilities for every gap in `[-1, 2]`. -/
def IsValidScale (γ s : ℝ) : Prop :=
  1 < γ ∧ 0 < s ∧
    2 ≤ s * (γ - 1) ∧
    1 ≤ s * (1 - γ⁻¹)

/-- For `γ = 1 + ε/9`, the explicit floor condition `18/ε ≤ s`
implies both probability-normalization scale bounds. -/
theorem isValidScale_one_add_epsilon_div_nine
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 18 / ε ≤ s) :
    IsValidScale (1 + ε / 9) s := by
  have hse : 18 ≤ s * ε := (div_le_iff₀ hε).mp hs
  have hs0 : 0 < s := by nlinarith
  have hden : 0 < 9 + ε := by linarith
  refine ⟨by linarith, hs0, ?_, ?_⟩
  · norm_num
    nlinarith
  · have hinv :
        1 - (1 + ε / 9)⁻¹ = ε / (9 + ε) := by
      field_simp
      ring
    rw [hinv]
    rw [← mul_div_assoc]
    rw [le_div_iff₀ hden]
    nlinarith

theorem IsValidScale.gamma_ne_one {γ s : ℝ} (h : IsValidScale γ s) :
    γ ≠ 1 :=
  ne_of_gt h.1

theorem IsValidScale.s_ne_zero {γ s : ℝ} (h : IsValidScale γ s) :
    s ≠ 0 :=
  ne_of_gt h.2.1

theorem IsValidScale.upDenom_pos {γ s : ℝ} (h : IsValidScale γ s) :
    0 < s * (γ - 1) :=
  mul_pos h.2.1 (sub_pos.mpr h.1)

theorem IsValidScale.inv_sub_one_neg {γ s : ℝ} (h : IsValidScale γ s) :
    γ⁻¹ - 1 < 0 := by
  have hγ0 : 0 < γ := lt_trans zero_lt_one h.1
  exact sub_neg.mpr ((inv_lt_one₀ hγ0).2 h.1)

theorem IsValidScale.downDenom_neg {γ s : ℝ} (h : IsValidScale γ s) :
    s * (γ⁻¹ - 1) < 0 :=
  mul_neg_of_pos_of_neg h.2.1 h.inv_sub_one_neg

theorem upProbability_nonneg {γ s y : ℝ} (h : IsValidScale γ s) :
    0 ≤ upProbability γ s y := by
  exact div_nonneg (le_max_right _ _) h.upDenom_pos.le

theorem downProbability_nonneg {γ M s y : ℝ} (h : IsValidScale γ s) :
    0 ≤ downProbability γ M s y := by
  unfold downProbability
  split_ifs
  · exact div_nonneg_of_nonpos (min_le_right _ _) h.downDenom_neg.le
  · exact le_rfl

theorem up_add_down_le_one
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    upProbability γ s y + downProbability γ M s y ≤ 1 := by
  by_cases hy : 0 ≤ y
  · have hup : upProbability γ s y ≤ 1 := by
      unfold upProbability
      rw [max_eq_left hy, div_le_one h.upDenom_pos]
      exact hyUpper.trans h.2.2.1
    simpa [downProbability, min_eq_right hy] using hup
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hup : upProbability γ s y = 0 := by
      simp [upProbability, max_eq_right hy']
    rw [hup, zero_add]
    unfold downProbability
    split_ifs
    · rw [min_eq_left hy', div_le_one_of_neg h.downDenom_neg]
      have hdenom :
          s * (γ⁻¹ - 1) = -(s * (1 - γ⁻¹)) := by ring
      rw [hdenom]
      linarith [h.2.2.2]
    · exact zero_le_one

theorem stayProbability_nonneg
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    0 ≤ stayProbability γ M s y := by
  unfold stayProbability
  linarith [up_add_down_le_one (M := M) h hyLower hyUpper]

theorem probabilities_sum (γ M s y : ℝ) :
    upProbability γ s y + stayProbability γ M s y +
      downProbability γ M s y = 1 := by
  unfold stayProbability
  ring

/-- Real weight assigned to an account move. -/
def moveProbability (γ M s y : ℝ) : AccountMove → ℝ
  | .up => upProbability γ s y
  | .stay => stayProbability γ M s y
  | .down => downProbability γ M s y

theorem moveProbability_nonneg
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) (move : AccountMove) :
    0 ≤ moveProbability γ M s y move := by
  cases move with
  | up => exact upProbability_nonneg h
  | stay => exact stayProbability_nonneg h hyLower hyUpper
  | down => exact downProbability_nonneg h

@[simp] theorem sum_moveProbability (γ M s y : ℝ) :
    ∑ move, moveProbability γ M s y move = 1 := by
  classical
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simpa [moveProbability, add_assoc] using probabilities_sum γ M s y

/-- The account update as an actual probability mass function. -/
def updatePMF
    (γ M s y : ℝ) (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) : PMF AccountMove :=
  PMF.ofFintype
    (fun move => ENNReal.ofReal (moveProbability γ M s y move))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun move _ => moveProbability_nonneg h hyLower hyUpper move)]
      simp)

@[simp] theorem updatePMF_apply_toReal
    (γ M s y : ℝ) (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) (move : AccountMove) :
    ((updatePMF γ M s y h hyLower hyUpper) move).toReal =
      moveProbability γ M s y move := by
  rw [updatePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (moveProbability_nonneg h hyLower hyUpper move)]

/-- Account level after a three-point move. -/
def nextAccount (γ s : ℝ) : AccountMove → ℝ
  | .up => γ * s
  | .stay => s
  | .down => γ⁻¹ * s

/-- The expectation of the PMF update agrees with `expectedChange`. -/
theorem expect_nextAccount_sub
    {γ M s y : ℝ} (h : IsValidScale γ s) (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
        (fun move => nextAccount γ s move - s) =
      expectedChange γ M s y := by
  classical
  rw [expect_eq_sum]
  rw [show (Finset.univ : Finset AccountMove) =
      {.up, .stay, .down} by decide]
  simp [moveProbability, nextAccount, expectedChange]

/-- Away from the floor, the expected account increment equals the
payoff/value gap exactly. -/
theorem expectedChange_eq_of_floor_lt
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M < s) :
    expectedChange γ M s y = y := by
  have hup :
      γ * s - s = s * (γ - 1) := by ring
  have hdown :
      γ⁻¹ * s - s = s * (γ⁻¹ - 1) := by ring
  unfold expectedChange upProbability downProbability
  rw [if_pos hMs, hup, hdown,
    div_mul_cancel₀ _ h.upDenom_pos.ne',
    div_mul_cancel₀ _ h.downDenom_neg.ne]
  linarith [max_add_min y 0]

/-- At the floor, the expected account increment is the positive part of
the payoff/value gap. -/
theorem expectedChange_eq_of_le_floor
    {γ M s y : ℝ} (h : IsValidScale γ s) (hsM : s ≤ M) :
    expectedChange γ M s y = max y 0 := by
  have hup :
      γ * s - s = s * (γ - 1) := by ring
  unfold expectedChange upProbability downProbability
  rw [if_neg (not_lt.mpr hsM), hup, zero_mul, add_zero,
    div_mul_cancel₀ _ h.upDenom_pos.ne']

/-- The update law's floor correction. With `M ≤ s`, expected account
growth minus the floor indicator is bounded above by the gap `y`. This is
the one-step inequality that telescopes in the uniform-payoff proof. -/
theorem expectedChange_sub_floorIndicator_le
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s)
    (hyLower : -1 ≤ y) :
    expectedChange γ M s y - (if s = M then 1 else 0) ≤ y := by
  by_cases hstrict : M < s
  · rw [expectedChange_eq_of_floor_lt h hstrict, if_neg (ne_of_gt hstrict)]
    linarith
  · have hsM : s = M := le_antisymm (not_lt.mp hstrict) hMs
    rw [expectedChange_eq_of_le_floor h (not_lt.mp hstrict), if_pos hsM]
    by_cases hy : 0 ≤ y
    · rw [max_eq_left hy]
      linarith
    · rw [max_eq_right (le_of_not_ge hy)]
      simpa using hyLower

/-- PMF form of the floor-corrected account inequality. -/
theorem expect_nextAccount_sub_floorIndicator_le
    {γ M s y : ℝ} (h : IsValidScale γ s) (hMs : M ≤ s)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 2) :
    expect (updatePMF γ M s y h hyLower hyUpper)
          (fun move => nextAccount γ s move - s) -
        (if s = M then 1 else 0) ≤ y := by
  rw [expect_nextAccount_sub h hyLower hyUpper]
  exact expectedChange_sub_floorIndicator_le h hMs hyLower

/-- The published one-step payoff estimate. The account gap is formed using
the old discounted value. If switching to the next discounted value loses
at most `ε * lam / 16`, with `lam ≤ 1`, the stage payoff minus the switched
value covers the account drift, the floor correction, and a `9ε/16` error.
-/
theorem payoff_sub_switchedValue_ge
    {γ M s ε lam payoff oldValue newValue : ℝ}
    (h : IsValidScale γ s) (hMs : M ≤ s)
    (hε : 0 ≤ ε) (hlam1 : lam ≤ 1)
    (hyLower : -1 ≤ payoff - oldValue + ε / 2)
    (hyUpper : payoff - oldValue + ε / 2 ≤ 2)
    (hswitch : -ε * lam / 16 ≤ oldValue - newValue) :
    -9 * ε / 16 +
          expect
            (updatePMF γ M s (payoff - oldValue + ε / 2) h
              hyLower hyUpper)
            (fun move => nextAccount γ s move - s) -
          (if s = M then 1 else 0) ≤
        payoff - newValue := by
  have haccount :=
    expect_nextAccount_sub_floorIndicator_le h hMs hyLower hyUpper
  have h_eps_lam : ε * lam ≤ ε := by
    exact mul_le_of_le_one_right hε hlam1
  nlinarith

/-- Finite-horizon telescope for the account-process payoff inequality.
This is the deterministic expectation-level form of the summation step: a
one-step `9ε/16` loss accumulates linearly, account increments telescope,
and floor corrections remain as an occupation sum. -/
theorem sum_payoff_ge_of_account_steps
    (ε : ℝ) (payoff nextValue account floorLoss : ℕ → ℝ)
    (hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) - floorLoss t ≤
        payoff t - nextValue t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, nextValue t) -
          (T : ℝ) * (9 * ε / 16) +
          (account T - account 0) -
          ∑ t ∈ Finset.range T, floorLoss t ≤
        ∑ t ∈ Finset.range T, payoff t := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      push_cast
      linarith [hstep T]

/-- Cesàro conclusion of the account telescope. If the average switched
value loses at most `ε/8`, floor occupation costs at most `ε/8`, and the
expected account has not fallen below its initial level, then the average
payoff is at least the target minus `ε`. -/
theorem average_payoff_ge_target_sub_epsilon_of_account_bounds
    {ε target : ℝ} (hε : 0 ≤ ε)
    (payoff nextValue account floorLoss : ℕ → ℝ)
    (hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) - floorLoss t ≤
        payoff t - nextValue t)
    {T : ℕ} (hT : 0 < T)
    (haccount : account 0 ≤ account T)
    (hvalue :
      target - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t)
    (hfloor :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8) :
    target - ε ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, payoff t := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum :=
    sum_payoff_ge_of_account_steps ε payoff nextValue account floorLoss
      hstep T
  have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
  have hscaled' :
      (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, nextValue t) -
            9 * ε / 16 +
            (T : ℝ)⁻¹ * (account T - account 0) -
            (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, floorLoss t) ≤
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, payoff t := by
    calc
      _ = (T : ℝ)⁻¹ *
          ((∑ t ∈ Finset.range T, nextValue t) -
            (T : ℝ) * (9 * ε / 16) +
            (account T - account 0) -
            ∑ t ∈ Finset.range T, floorLoss t) := by
              rw [inv_eq_one_div]
              field_simp
      _ ≤ _ := hscaled
  have haccountScaled :
      0 ≤ (T : ℝ)⁻¹ * (account T - account 0) :=
    mul_nonneg (inv_nonneg.mpr hTreal.le) (sub_nonneg.mpr haccount)
  nlinarith

end MertensNeymanAccount
end StochasticGame
end GameTheory
