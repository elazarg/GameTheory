/-
# EXP-108: a concrete alternating-block sequence

This file attempts to discharge the endpoint hypotheses of
`fair_two_point_order_limits`.  The block endpoints grow by squaring, so the
last completed block dominates the prefix at every endpoint.  The least-block
index is deliberately exposed: its interval characterization is the finite
arithmetic checkpoint needed before the liminf/limsup filter argument.
-/

import GameTheory.Experimental.PostArchitecture.AsymptoticPayoffSeparation

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture

/-- Rapidly growing block endpoints. -/
def blockEndpoint : ℕ → ℕ
  | 0 => 2
  | k + 1 => blockEndpoint k ^ 2

theorem blockEndpoint_two_le (k : ℕ) : 2 ≤ blockEndpoint k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [blockEndpoint]
      nlinarith

theorem blockEndpoint_strictMono (k : ℕ) :
    blockEndpoint k < blockEndpoint (k + 1) := by
  simp only [blockEndpoint]
  have hk := blockEndpoint_two_le k
  nlinarith

theorem blockEndpoint_succ_le (k : ℕ) :
    blockEndpoint k + 1 ≤ blockEndpoint (k + 1) := by
  exact Nat.succ_le_of_lt (blockEndpoint_strictMono k)

theorem blockEndpoint_mono {i j : ℕ} (hij : i ≤ j) :
    blockEndpoint i ≤ blockEndpoint j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
      exact le_trans ih (Nat.le_of_lt (blockEndpoint_strictMono j))

theorem blockEndpoint_ge (k : ℕ) : k + 2 ≤ blockEndpoint k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstep := blockEndpoint_succ_le k
      omega

theorem exists_block_endpoint (n : ℕ) :
    ∃ k, n < blockEndpoint (k + 1) := by
  refine ⟨n, ?_⟩
  have hge := blockEndpoint_ge n
  have hstep := blockEndpoint_strictMono n
  omega

/-- The least block whose right endpoint is past `n`. -/
def blockIndex (n : ℕ) : ℕ :=
  Nat.find (exists_block_endpoint n)

theorem blockIndex_spec (n : ℕ) :
    n < blockEndpoint (blockIndex n + 1) := by
  exact Nat.find_spec (exists_block_endpoint n)

theorem blockIndex_le_of_lt_endpoint {n k : ℕ}
    (h : n < blockEndpoint (k + 1)) : blockIndex n ≤ k := by
  exact Nat.find_min' (exists_block_endpoint n) h

/-- Alternating Boolean stage payoff, using the least enclosing block. -/
def alternatingBlockStage (n : ℕ) : ℝ :=
  if blockIndex n % 2 = 0 then 0 else 1

theorem alternatingBlockStage_nonneg (n : ℕ) :
    0 ≤ alternatingBlockStage n := by
  unfold alternatingBlockStage
  split <;> norm_num

theorem alternatingBlockStage_le_one (n : ℕ) :
    alternatingBlockStage n ≤ 1 := by
  unfold alternatingBlockStage
  split <;> norm_num

theorem alternatingBlockStage_on_block {k n : ℕ}
    (hlo : blockEndpoint k ≤ n)
    (hhi : n < blockEndpoint (k + 1)) :
    alternatingBlockStage n = if k % 2 = 0 then 0 else 1 := by
  have hle : blockIndex n ≤ k :=
    blockIndex_le_of_lt_endpoint hhi
  have hnot : ¬ blockIndex n < k := by
    intro hlt
    have hlt' : blockIndex n + 1 ≤ k := by omega
    have hmono : blockEndpoint (blockIndex n + 1) ≤ blockEndpoint k :=
      blockEndpoint_mono hlt'
    have hspec := blockIndex_spec n
    omega
  have heq : blockIndex n = k := by omega
  unfold alternatingBlockStage
  rw [heq]

theorem alternatingBlockStage_sum_Ico (k : ℕ) :
    ∑ i ∈ Finset.Ico (blockEndpoint k) (blockEndpoint (k + 1)),
        alternatingBlockStage i =
      if k % 2 = 0 then 0 else
        ((blockEndpoint (k + 1) - blockEndpoint k : ℕ) : ℝ) := by
  by_cases hk : k % 2 = 0
  · simp only [if_pos hk]
    apply Finset.sum_eq_zero
    intro i hi
    rw [alternatingBlockStage_on_block
      (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2]
    simp [hk]
  · simp only [if_neg hk]
    calc
      (∑ i ∈ Finset.Ico (blockEndpoint k) (blockEndpoint (k + 1)),
          alternatingBlockStage i) =
          ∑ i ∈ Finset.Ico (blockEndpoint k) (blockEndpoint (k + 1)),
            (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [alternatingBlockStage_on_block
                (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2]
              simp [hk]
      _ = ((blockEndpoint (k + 1) - blockEndpoint k : ℕ) : ℝ) := by
        simp [Nat.card_Ico]

theorem alternatingBlockStage_sum_range_le (n : ℕ) :
    ∑ i ∈ Finset.range n, alternatingBlockStage i ≤ (n : ℝ) := by
  calc
    (∑ i ∈ Finset.range n, alternatingBlockStage i) ≤
        ∑ i ∈ Finset.range n, (1 : ℝ) := by
          exact Finset.sum_le_sum fun i hi => alternatingBlockStage_le_one i
    _ = (n : ℝ) := by simp

theorem alternatingBlockStage_sum_endpoint_even {k : ℕ}
    (hk : k % 2 = 0) :
    ∑ i ∈ Finset.range (blockEndpoint (k + 1)), alternatingBlockStage i ≤
      (blockEndpoint k : ℝ) := by
  have hle : blockEndpoint k ≤ blockEndpoint (k + 1) :=
    (blockEndpoint_strictMono k).le
  have hdecomp := Finset.sum_range_add_sum_Ico alternatingBlockStage hle
  rw [← hdecomp, alternatingBlockStage_sum_Ico, if_pos hk]
  have hprefix := alternatingBlockStage_sum_range_le (blockEndpoint k)
  norm_num at hprefix ⊢
  linarith

theorem alternatingBlockStage_sum_endpoint_odd {k : ℕ}
    (hk : k % 2 ≠ 0) :
    (blockEndpoint (k + 1) : ℝ) - blockEndpoint k ≤
      ∑ i ∈ Finset.range (blockEndpoint (k + 1)), alternatingBlockStage i := by
  have hle : blockEndpoint k ≤ blockEndpoint (k + 1) :=
    (blockEndpoint_strictMono k).le
  have hdecomp := Finset.sum_range_add_sum_Ico alternatingBlockStage hle
  rw [← hdecomp, alternatingBlockStage_sum_Ico, if_neg hk]
  rw [Nat.cast_sub hle]
  have hprefix : 0 ≤
      ∑ i ∈ Finset.range (blockEndpoint k), alternatingBlockStage i := by
    exact Finset.sum_nonneg fun i hi => alternatingBlockStage_nonneg i
  norm_num at hprefix ⊢
  linarith

theorem alternatingCesaro_endpoint_even {k : ℕ} (hk : k % 2 = 0) :
    cesaroAverage alternatingBlockStage (blockEndpoint (k + 1) - 1) ≤
      (blockEndpoint k : ℝ) / blockEndpoint (k + 1) := by
  unfold cesaroAverage
  have hpos : 0 < blockEndpoint (k + 1) :=
    Nat.zero_lt_of_lt (blockEndpoint_strictMono k)
  have hone : 1 ≤ blockEndpoint (k + 1) := by
    omega
  have hidx : blockEndpoint (k + 1) - 1 + 1 = blockEndpoint (k + 1) :=
    Nat.sub_add_cancel hone
  rw [hidx]
  have hsum := alternatingBlockStage_sum_endpoint_even hk
  have hden : 0 ≤ ((blockEndpoint (k + 1) : ℕ) : ℝ)⁻¹ := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hden
  simpa [div_eq_mul_inv, Nat.cast_add, mul_comm] using hmul

theorem alternatingCesaro_endpoint_odd {k : ℕ} (hk : k % 2 ≠ 0) :
    1 - (blockEndpoint k : ℝ) / blockEndpoint (k + 1) ≤
      cesaroAverage alternatingBlockStage (blockEndpoint (k + 1) - 1) := by
  unfold cesaroAverage
  have hposNat : 0 < blockEndpoint (k + 1) :=
    Nat.zero_lt_of_lt (blockEndpoint_strictMono k)
  have hone : 1 ≤ blockEndpoint (k + 1) := by
    omega
  have hidx : blockEndpoint (k + 1) - 1 + 1 = blockEndpoint (k + 1) :=
    Nat.sub_add_cancel hone
  rw [hidx]
  have hsum := alternatingBlockStage_sum_endpoint_odd hk
  have hden : 0 ≤ ((blockEndpoint (k + 1) : ℕ) : ℝ)⁻¹ := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hden
  have hpos : (0 : ℝ) < blockEndpoint (k + 1) := by
    exact_mod_cast (Nat.zero_lt_of_lt (blockEndpoint_strictMono k))
  rw [show (1 : ℝ) - (blockEndpoint k : ℝ) /
      blockEndpoint (k + 1) =
        ((blockEndpoint (k + 1) : ℝ) - blockEndpoint k) *
          ((blockEndpoint (k + 1) : ℝ)⁻¹) by
        field_simp]
  simpa [mul_comm] using hmul

theorem alternatingCesaro_bounded (n : ℕ) :
    0 ≤ cesaroAverage alternatingBlockStage n ∧
      cesaroAverage alternatingBlockStage n ≤ 1 := by
  unfold cesaroAverage
  have hsum_nonneg : 0 ≤
      ∑ i ∈ Finset.range (n + 1), alternatingBlockStage i := by
    exact Finset.sum_nonneg fun i hi => alternatingBlockStage_nonneg i
  have hsum_le := alternatingBlockStage_sum_range_le (n + 1)
  have hden : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  constructor
  · exact mul_nonneg hden hsum_nonneg
  · have hmul := mul_le_mul_of_nonneg_left hsum_le hden
    have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      ((n + 1 : ℕ) : ℝ)⁻¹ *
          ∑ i ∈ Finset.range (n + 1), alternatingBlockStage i ≤
          ((n + 1 : ℕ) : ℝ)⁻¹ * (n + 1 : ℝ) := by
            simpa using hmul
      _ = 1 := by
        rw [Nat.cast_add]
        field_simp [hpos.ne']
        norm_num

/-
The remaining bridge is a filter argument: the even and odd endpoint
subsequences must be shown cofinal in `atTop`, and their endpoint bounds must
be combined with the global bounds to identify the corresponding `liminf` and
`limsup`.  The finite endpoint estimates above do not by themselves prove
those filter statements.
-/

end GameTheory.Experimental.PostArchitecture
