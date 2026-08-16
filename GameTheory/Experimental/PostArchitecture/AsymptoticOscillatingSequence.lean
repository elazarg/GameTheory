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
open scoped Topology
open Filter
open GameTheory.Math.Probability

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

def evenEndpoint (k : ℕ) : ℕ := blockEndpoint (2 * k + 1) - 1

def oddEndpoint (k : ℕ) : ℕ := blockEndpoint (2 * k + 2) - 1

theorem evenEndpoint_ge (k : ℕ) : k ≤ evenEndpoint k := by
  unfold evenEndpoint
  have h := blockEndpoint_ge (2 * k + 1)
  omega

theorem oddEndpoint_ge (k : ℕ) : k ≤ oddEndpoint k := by
  unfold oddEndpoint
  have h := blockEndpoint_ge (2 * k + 2)
  omega

theorem tendsto_evenEndpoint :
    Tendsto evenEndpoint atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall evenEndpoint_ge) tendsto_id

theorem tendsto_oddEndpoint :
    Tendsto oddEndpoint atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall oddEndpoint_ge) tendsto_id

theorem tendsto_blockEndpoint_ratio :
    Tendsto (fun k => (blockEndpoint k : ℝ) /
      blockEndpoint (k + 1)) atTop (𝓝 0) := by
  have hendpoint : Tendsto blockEndpoint atTop atTop :=
    tendsto_atTop_mono' atTop (f₁ := id) (f₂ := blockEndpoint)
      (Eventually.of_forall (fun k : ℕ => by
        dsimp
        have h := blockEndpoint_ge k
        omega)) tendsto_id
  have hinv : Tendsto (fun k => (1 : ℝ) / blockEndpoint k)
      atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (C := (1 : ℝ)) |>.comp hendpoint
  apply hinv.congr'
  filter_upwards with k
  simp only [blockEndpoint, Nat.cast_pow]
  have hpos : (0 : ℝ) < blockEndpoint k := by
    have h : 0 < blockEndpoint k := by
      have h' := blockEndpoint_two_le k
      omega
    exact_mod_cast h
  field_simp

theorem tendsto_evenEndpoint_cesaro :
    Tendsto (fun k => cesaroAverage alternatingBlockStage (evenEndpoint k))
      atTop (𝓝 0) := by
  have hratio := tendsto_blockEndpoint_ratio
  have hupper : ∀ k, cesaroAverage alternatingBlockStage (evenEndpoint k) ≤
      (blockEndpoint (2 * k : ℕ) : ℝ) /
        blockEndpoint (2 * k + 1) := by
    intro k
    unfold evenEndpoint
    simpa [evenEndpoint] using
      (alternatingCesaro_endpoint_even (k := 2 * k) (by omega))
  have hupper_tendsto : Tendsto (fun k =>
      (blockEndpoint (2 * k : ℕ) : ℝ) / blockEndpoint (2 * k + 1))
      atTop (𝓝 0) := by
    convert hratio.comp (tendsto_atTop_mono' atTop
      (f₁ := id) (f₂ := fun k : ℕ => 2 * k)
      (Eventually.of_forall (fun k : ℕ => by dsimp; omega)) tendsto_id) using 1
    funext k
    congr 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper_tendsto
    (fun k => (alternatingCesaro_bounded (evenEndpoint k)).1)
    hupper

theorem tendsto_oddEndpoint_cesaro :
    Tendsto (fun k => cesaroAverage alternatingBlockStage (oddEndpoint k))
      atTop (𝓝 1) := by
  have hratio := tendsto_blockEndpoint_ratio
  have hlower : ∀ k, 1 - (blockEndpoint (2 * k + 1 : ℕ) : ℝ) /
        blockEndpoint (2 * k + 2) ≤
      cesaroAverage alternatingBlockStage (oddEndpoint k) := by
    intro k
    unfold oddEndpoint
    simpa [oddEndpoint] using
      (alternatingCesaro_endpoint_odd (k := 2 * k + 1) (by omega))
  have hratio_tendsto : Tendsto (fun k =>
      (blockEndpoint (2 * k + 1 : ℕ) : ℝ) /
        blockEndpoint (2 * k + 2)) atTop (𝓝 0) := by
    convert hratio.comp (tendsto_atTop_mono' atTop
      (f₁ := id) (f₂ := fun k : ℕ => 2 * k + 1)
      (Eventually.of_forall (fun k : ℕ => by dsimp; omega)) tendsto_id) using 1
    funext k
    congr 2
  have hlower_tendsto : Tendsto (fun k => 1 -
      (blockEndpoint (2 * k + 1 : ℕ) : ℝ) /
      blockEndpoint (2 * k + 2)) atTop (𝓝 1) :=
    by simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        hratio_tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower_tendsto tendsto_const_nhds hlower
    (fun k => (alternatingCesaro_bounded (oddEndpoint k)).2)

theorem cesaroAverage_alternating_liminf_limsup :
    Filter.liminf (fun n => cesaroAverage alternatingBlockStage n) atTop = 0 ∧
    Filter.limsup (fun n => cesaroAverage alternatingBlockStage n) atTop = 1 := by
  let u : ℕ → ℝ := fun n => cesaroAverage alternatingBlockStage n
  have hlow : ∀ n, 0 ≤ u n := fun n => (alternatingCesaro_bounded n).1
  have hhigh : ∀ n, u n ≤ 1 := fun n => (alternatingCesaro_bounded n).2
  have hzero : MapClusterPt 0 atTop u := by
    apply MapClusterPt.of_comp tendsto_evenEndpoint
    simpa [u, Function.comp_def] using tendsto_evenEndpoint_cesaro.mapClusterPt
  have hone : MapClusterPt 1 atTop u := by
    apply MapClusterPt.of_comp tendsto_oddEndpoint
    simpa [u, Function.comp_def] using tendsto_oddEndpoint_cesaro.mapClusterPt
  have hlow' : (0 : ℝ) ≤ Filter.liminf u atTop :=
    le_liminf_of_le
      (isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hhigh))
      (Eventually.of_forall hlow)
  have hhigh' : Filter.limsup u atTop ≤ (1 : ℝ) :=
    limsup_le_of_le
      (isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall hlow))
      (Eventually.of_forall hhigh)
  have hliminf_le : Filter.liminf u atTop ≤ (0 : ℝ) :=
    hzero.liminf_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall hlow))
  have hlimsup_ge : (1 : ℝ) ≤ Filter.limsup u atTop :=
    hone.le_limsup (isBoundedUnder_of_eventually_le
      (Eventually.of_forall hhigh))
  exact ⟨le_antisymm hliminf_le hlow', le_antisymm hhigh' hlimsup_ge⟩

theorem cesaroAverage_complement_alternating_liminf_limsup :
    Filter.liminf (fun n => cesaroAverage
      (complementSequence alternatingBlockStage) n) atTop = 0 ∧
    Filter.limsup (fun n => cesaroAverage
      (complementSequence alternatingBlockStage) n) atTop = 1 := by
  have hlow : ∀ n, 0 ≤ cesaroAverage
      (complementSequence alternatingBlockStage) n := by
    intro n
    rw [cesaroAverage_complement]
    linarith [(alternatingCesaro_bounded n).2]
  have hhigh : ∀ n, cesaroAverage
      (complementSequence alternatingBlockStage) n ≤ 1 := by
    intro n
    rw [cesaroAverage_complement]
    linarith [(alternatingCesaro_bounded n).1]
  have hzero : Tendsto (fun k => cesaroAverage
      (complementSequence alternatingBlockStage) (evenEndpoint k)) atTop (𝓝 1) := by
    rw [show (fun k => cesaroAverage
      (complementSequence alternatingBlockStage) (evenEndpoint k)) =
      (fun k => 1 - cesaroAverage alternatingBlockStage (evenEndpoint k)) by
        funext k; rw [cesaroAverage_complement]]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        tendsto_evenEndpoint_cesaro
  have hone : Tendsto (fun k => cesaroAverage
      (complementSequence alternatingBlockStage) (oddEndpoint k)) atTop (𝓝 0) := by
    rw [show (fun k => cesaroAverage
      (complementSequence alternatingBlockStage) (oddEndpoint k)) =
      (fun k => 1 - cesaroAverage alternatingBlockStage (oddEndpoint k)) by
        funext k; rw [cesaroAverage_complement]]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        tendsto_oddEndpoint_cesaro
  let u : ℕ → ℝ := fun n => cesaroAverage
    (complementSequence alternatingBlockStage) n
  have hzero' : MapClusterPt 0 atTop u := by
    apply MapClusterPt.of_comp tendsto_oddEndpoint
    simpa [u, Function.comp_def] using hone.mapClusterPt
  have hone' : MapClusterPt 1 atTop u := by
    apply MapClusterPt.of_comp tendsto_evenEndpoint
    simpa [u, Function.comp_def] using hzero.mapClusterPt
  have hlow' : (0 : ℝ) ≤ Filter.liminf u atTop :=
    le_liminf_of_le
      (isCoboundedUnder_ge_of_eventually_le atTop (Eventually.of_forall hhigh))
      (Eventually.of_forall hlow)
  have hhigh' : Filter.limsup u atTop ≤ (1 : ℝ) :=
    limsup_le_of_le
      (isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall hlow))
      (Eventually.of_forall hhigh)
  have hliminf_le : Filter.liminf u atTop ≤ (0 : ℝ) :=
    hzero'.liminf_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall hlow))
  have hlimsup_ge : (1 : ℝ) ≤ Filter.limsup u atTop :=
    hone'.le_limsup (isBoundedUnder_of_eventually_le
      (Eventually.of_forall hhigh))
  exact ⟨le_antisymm hliminf_le hlow', le_antisymm hhigh' hlimsup_ge⟩

theorem alternatingBlockStage_separates_asymptotic_payoffs :
    FinDist.expect (fairTwoPointLaw alternatingBlockStage)
        (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop) = 0 ∧
    (∀ n, FinDist.expect (fairTwoPointLaw alternatingBlockStage)
      (fun path => cesaroAverage path n) = (1 / 2 : ℝ)) ∧
    Tendsto (fun n => FinDist.expect (fairTwoPointLaw alternatingBlockStage)
      (fun path => cesaroAverage path n)) atTop (𝓝 (1 / 2 : ℝ)) ∧
    FinDist.expect (fairTwoPointLaw alternatingBlockStage)
        (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop) = 1 ∧
    FinDist.expect (fairTwoPointLaw alternatingBlockStage)
        (fun path => Filter.liminf (fun n => cesaroAverage path n) atTop) ≠
      (1 / 2 : ℝ) ∧
    FinDist.expect (fairTwoPointLaw alternatingBlockStage)
        (fun path => Filter.limsup (fun n => cesaroAverage path n) atTop) ≠
      (1 / 2 : ℝ) := by
  exact fair_two_point_order_limits alternatingBlockStage
    cesaroAverage_alternating_liminf_limsup.1
    cesaroAverage_alternating_liminf_limsup.2
    cesaroAverage_complement_alternating_liminf_limsup.1
    cesaroAverage_complement_alternating_liminf_limsup.2

end GameTheory.Experimental.PostArchitecture
