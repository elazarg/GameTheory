/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge

/-!
# Zero-retention ideal singleton blocks on the semantic carrier

The positive-retention mesh in `IdealSingletonCarrierBridge` realizes every
ideal singleton block with retention in `(0,1]`.  This file closes the endpoint
at retention zero by taking a second, explicit limit through retentions
`1/(n+1)`.  Thus reset blocks, as well as contracting blocks, are honest points
of the attainable terminal-semantic carrier.
-/

noncomputable section

open Filter

namespace GameTheory
namespace IdealSingletonCarrierBridge

open IdealSingletonBlockApproximation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The ideal singleton semantic pair depends continuously on its retention
parameter. -/
theorem continuous_idealSingletonSemanticPair_retention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (pair : QuittingTerminalSemanticPair ι) :
    Continuous (fun α => idealSingletonSemanticPair reward owner α pair) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro who
    exact (continuous_id.mul continuous_const).add
      ((continuous_const.sub continuous_id).mul continuous_const)
  · apply continuous_pi
    intro who
    by_cases hwho : who = owner
    · subst who
      simp only [idealSingletonClearance, if_pos]
      fun_prop
    · simp only [idealSingletonClearance, if_neg hwho]
      fun_prop

/-- Retentions `1/(n+1)` approach the reset endpoint through `(0,1]`. -/
theorem tendsto_idealSingletonSemanticPair_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (pair : QuittingTerminalSemanticPair ι) :
    Tendsto (fun n : ℕ => idealSingletonSemanticPair reward owner
        (1 / ((n : ℝ) + 1)) pair)
      atTop (nhds (idealSingletonSemanticPair reward owner 0 pair)) := by
  exact (continuous_idealSingletonSemanticPair_retention reward owner pair).continuousAt
    |>.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A genuine subdivision of a positive coarse hazard into a positive number
of microstages has strictly positive micro-hazard. -/
theorem quittingMeshHazard_pos
    {p : ℝ} {m : ℕ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hm : 0 < m) :
    0 < quittingMeshHazard p m := by
  unfold quittingMeshHazard
  have hpow : (1 - p) ^ ((m : ℝ)⁻¹ : ℝ) < 1 :=
    Real.rpow_lt_one (sub_nonneg.mpr hp1) (by linarith)
      (inv_pos.mpr (Nat.cast_pos.mpr hm))
  linarith

/-- A single diagonal sequence of genuine finite positive-hazard prefixes
converges to the zero-retention reset.  The outer retention is
`1/(n+2)`, and the selected inner mesh is fine enough to have error below
`1/(n+1)`. -/
theorem exists_diffuseSingletonPrefix_diagonal_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    ∃ meshIndex : ℕ → ℕ,
      Tendsto (fun n : ℕ =>
          diffuseSingletonPrefix reward owner (1 / ((n : ℝ) + 2))
            (by positivity) (by
              apply (div_le_one (by positivity)).2
              linarith only
                [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
            (meshIndex n) pair)
        atTop (nhds (idealSingletonSemanticPair reward owner 0 pair)) ∧
      ∀ n : ℕ, 0 < quittingMeshHazard (1 - 1 / ((n : ℝ) + 2))
        (meshIndex n + 1) := by
  let α : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hα0 : ∀ n : ℕ, 0 < α n := by
    intro n
    dsimp [α]
    positivity
  have hα1 : ∀ n : ℕ, α n ≤ 1 := by
    intro n
    dsimp [α]
    rw [div_le_one (by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hαlt : ∀ n : ℕ, α n < 1 := by
    intro n
    dsimp [α]
    rw [div_lt_one (by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hαtendsto : Tendsto α atTop (nhds 0) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    have heq : α =
        (fun n : ℕ => 1 / ((n : ℝ) + 1)) ∘ (fun n : ℕ => n + 1) := by
      funext n
      dsimp [α, Function.comp]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [heq]
    exact hshift
  have hmesh : ∀ n : ℕ, Tendsto (fun k =>
      diffuseSingletonPrefix reward owner (α n) (hα0 n) (hα1 n) k pair)
      atTop (nhds (idealSingletonSemanticPair reward owner (α n) pair)) := by
    intro n
    exact tendsto_diffuseSingletonPrefix reward pair owner (α n)
      (hα0 n) (hα1 n) hclearance
  have hclose : ∀ n : ℕ, ∃ N, ∀ k, N ≤ k →
      dist (diffuseSingletonPrefix reward owner (α n)
          (hα0 n) (hα1 n) k pair)
        (idealSingletonSemanticPair reward owner (α n) pair) <
          1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.tendsto_atTop.1 (hmesh n) (1 / ((n : ℝ) + 1)) (by positivity)
  choose meshIndex hmeshIndex using hclose
  refine ⟨meshIndex, ?_, ?_⟩
  · have herror : Tendsto (fun n : ℕ =>
        dist (diffuseSingletonPrefix reward owner (α n)
            (hα0 n) (hα1 n) (meshIndex n) pair)
          (idealSingletonSemanticPair reward owner (α n) pair))
        atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact dist_nonneg
      · intro n
        exact (hmeshIndex n (meshIndex n) le_rfl).le
      · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hideal : Tendsto (fun n : ℕ =>
        idealSingletonSemanticPair reward owner (α n) pair)
        atTop (nhds (idealSingletonSemanticPair reward owner 0 pair)) :=
      (continuous_idealSingletonSemanticPair_retention reward owner pair).continuousAt
        |>.tendsto.comp hαtendsto
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero
    · intro n
      exact dist_nonneg
    · intro n
      exact dist_triangle _
        (idealSingletonSemanticPair reward owner (α n) pair) _
    · have hidealDist : Tendsto (fun n : ℕ => dist
          (idealSingletonSemanticPair reward owner (α n) pair)
          (idealSingletonSemanticPair reward owner 0 pair))
          atTop (nhds 0) := by
        simpa using hideal.dist
          (tendsto_const_nhds : Tendsto
            (fun _ : ℕ => idealSingletonSemanticPair reward owner 0 pair)
            atTop (nhds (idealSingletonSemanticPair reward owner 0 pair)))
      simpa [α] using herror.add hidealDist
  · intro n
    exact quittingMeshHazard_pos (by linarith [hαlt n]) (by linarith [hα0 n])
      (Nat.succ_pos (meshIndex n))

/-- The zero-retention ideal singleton reset preserves the actual compact
semantic carrier.  It is a limit of positive-retention ideal blocks, each of
which is itself a limit of explicit positive-hazard finite prefixes. -/
theorem idealSingletonSemanticPair_zero_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    idealSingletonSemanticPair reward owner 0 pair ∈
      quittingTerminalSemanticCarrier reward := by
  obtain ⟨meshIndex, hdiagonal, _hhazard⟩ :=
    exists_diffuseSingletonPrefix_diagonal_tendsto_zero
      reward pair owner hclearance
  apply isClosed_closure.mem_of_tendsto hdiagonal
  exact Eventually.of_forall fun n : ℕ => by
    unfold diffuseSingletonPrefix
    dsimp only
    exact repeatedSingletonPrefix_mem_carrier reward owner _ _ _
      (meshIndex n + 1) pair hB hreward hpair

end IdealSingletonCarrierBridge
end GameTheory
