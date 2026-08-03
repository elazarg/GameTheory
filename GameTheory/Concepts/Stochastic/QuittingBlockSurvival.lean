/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingExceptionalTailLimits
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Uniform block contraction for nonperiodic quitting paths

This file contains the scalar survival package needed by graph-directed
quitting constructions.  No periodicity is assumed.  If every aligned block
of `K` stages contracts each player's opponent-survival clock by at most the
same `rho < 1`, then aligned multi-block survival is bounded by powers of
`rho`, every arbitrary-start tail tends to zero, and the expected opponent
live time from every aligned boundary is at most `K / (1-rho)`.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Uniform playerwise opponent contraction on every aligned `K`-block. -/
def IsQuittingOpponentBlockContraction
    (roots : ℕ → ι → PMF Bool) (K : ℕ) (rho : ℝ) : Prop :=
  ∀ block who,
    quittingOpponentSurvivalWeight roots who (block * K) K ≤ rho

/-- Every finite opponent-survival product is at most one. -/
theorem quittingOpponentSurvivalWeight_le_one
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start fuel ≤ 1 := by
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [show fuel + 1 = fuel.succ by omega,
        quittingOpponentSurvivalWeight_succ]
      exact mul_le_one₀ ih
        (quittingStationaryContinueMass_nonneg
          (Function.update (roots (start + fuel)) who (PMF.pure false)))
        (quittingStationaryContinueMass_le_one
          (Function.update (roots (start + fuel)) who (PMF.pure false)))

/-- Starting at any aligned boundary, survival through `turns` whole blocks
is at most `rho^turns`. -/
theorem quittingOpponentSurvivalWeight_aligned_mul_le_pow
    (roots : ℕ → ι → PMF Bool) {rho : ℝ}
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (firstBlock : ℕ) (who : ι) :
    ∀ turns,
      quittingOpponentSurvivalWeight roots who (firstBlock * K)
          (turns * K) ≤
        rho ^ turns := by
  intro turns
  induction turns with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ turns ih =>
      rw [Nat.succ_mul, quittingOpponentSurvivalWeight_add]
      have hnext := hblock (firstBlock + turns) who
      have hstart : firstBlock * K + turns * K =
          (firstBlock + turns) * K := by ring
      rw [hstart]
      calc
        quittingOpponentSurvivalWeight roots who (firstBlock * K)
              (turns * K) *
            quittingOpponentSurvivalWeight roots who
              ((firstBlock + turns) * K) K ≤
            rho ^ turns * rho := by
              exact mul_le_mul ih hnext
                (quittingOpponentSurvivalWeight_nonneg roots who
                  ((firstBlock + turns) * K) K)
                (pow_nonneg hrho0 turns)
        _ = rho ^ turns.succ := (pow_succ rho turns).symm

/-- Survival at any offset inside an aligned block is bounded by the power
at the beginning of that block. -/
theorem quittingOpponentSurvivalWeight_aligned_add_le_pow
    (roots : ℕ → ι → PMF Bool) {rho : ℝ}
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (firstBlock turns offset : ℕ) (who : ι) :
    quittingOpponentSurvivalWeight roots who (firstBlock * K)
        (turns * K + offset) ≤
      rho ^ turns := by
  have hmono := antitone_quittingOpponentSurvivalWeight
    roots who (firstBlock * K)
  exact (hmono (Nat.le_add_right (turns * K) offset)).trans
    (quittingOpponentSurvivalWeight_aligned_mul_le_pow
      roots hblock hrho0 firstBlock who turns)

/-- Aligned block contraction forces every arbitrary-start opponent-survival
tail to vanish.  At most one partial block is traversed before the aligned
geometric estimate applies. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_of_blockContraction
    (roots : ℕ → ι → PMF Bool) {rho : ℝ}
    (hK : 0 < K)
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (who : ι) (start : ℕ) :
    Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0) := by
  let firstBlock := start / K + 1
  let boundary := firstBlock * K
  let wait := boundary - start
  have hstartBoundary : start ≤ boundary := by
    dsimp only [boundary, firstBlock]
    rw [Nat.add_mul, one_mul]
    exact (Nat.lt_div_mul_add hK).le
  have hstartWait : start + wait = boundary := by
    dsimp only [wait]
    omega
  have hsubBound : ∀ turns,
      quittingOpponentSurvivalWeight roots who start
          (wait + turns * K) ≤
        rho ^ turns := by
    intro turns
    rw [quittingOpponentSurvivalWeight_add, hstartWait]
    calc
      quittingOpponentSurvivalWeight roots who start wait *
            quittingOpponentSurvivalWeight roots who boundary
              (turns * K) ≤
          1 * rho ^ turns := by
            exact mul_le_mul
              (quittingOpponentSurvivalWeight_le_one roots who start wait)
              (by
                dsimp only [boundary]
                exact quittingOpponentSurvivalWeight_aligned_mul_le_pow
                  roots hblock hrho0 firstBlock who turns)
              (quittingOpponentSurvivalWeight_nonneg roots who boundary
                (turns * K)) zero_le_one
      _ = rho ^ turns := one_mul _
  have hpow : Tendsto (fun turns : ℕ ↦ rho ^ turns)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1
  have hsub : Tendsto (fun turns : ℕ ↦
      quittingOpponentSurvivalWeight roots who start
        (wait + turns * K)) atTop (nhds 0) := by
    apply squeeze_zero
    · intro turns
      exact quittingOpponentSurvivalWeight_nonneg roots who start _
    · exact hsubBound
    · exact hpow
  rw [Metric.tendsto_atTop] at hsub ⊢
  intro epsilon hepsilon
  obtain ⟨turns, hturns⟩ := hsub epsilon hepsilon
  refine ⟨wait + turns * K, ?_⟩
  intro fuel hfuel
  have hmono := antitone_quittingOpponentSurvivalWeight roots who start hfuel
  have hclose := hturns turns le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg roots who start _)]
      at hclose ⊢
  exact hmono.trans_lt hclose

/-- Every finite prefix of the opponent-live clock from an aligned boundary
has mass at most `K/(1-rho)`. -/
theorem sum_quittingOpponentSurvivalWeight_aligned_le
    (roots : ℕ → ι → PMF Bool) {rho : ℝ}
    (hK : 0 < K)
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (firstBlock : ℕ) (who : ι) (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        quittingOpponentSurvivalWeight roots who (firstBlock * K) time) ≤
      (K : ℝ) / (1 - rho) := by
  have hwhole : ∀ turns : ℕ,
      (∑ time ∈ Finset.range (turns * K),
          quittingOpponentSurvivalWeight roots who
            (firstBlock * K) time) ≤
        (K : ℝ) * ∑ turn ∈ Finset.range turns, rho ^ turn := by
    intro turns
    induction turns with
    | zero => simp
    | succ turns ih =>
        have honeBlock :
            (∑ offset ∈ Finset.range K,
                quittingOpponentSurvivalWeight roots who
                  (firstBlock * K) (turns * K + offset)) ≤
              (K : ℝ) * rho ^ turns := by
          calc
            (∑ offset ∈ Finset.range K,
                quittingOpponentSurvivalWeight roots who
                  (firstBlock * K) (turns * K + offset)) ≤
                ∑ _offset ∈ Finset.range K, rho ^ turns := by
                  apply Finset.sum_le_sum
                  intro offset _
                  exact quittingOpponentSurvivalWeight_aligned_add_le_pow
                    roots hblock hrho0 firstBlock turns offset who
            _ = (K : ℝ) * rho ^ turns := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Nat.succ_mul, Finset.sum_range_add,
          Finset.sum_range_succ]
        calc
          (∑ x ∈ Finset.range (turns * K),
              quittingOpponentSurvivalWeight roots who
                (firstBlock * K) x) +
              ∑ x ∈ Finset.range K,
                quittingOpponentSurvivalWeight roots who
                  (firstBlock * K) (turns * K + x) ≤
            (K : ℝ) * ∑ x ∈ Finset.range turns, rho ^ x +
              (K : ℝ) * rho ^ turns := add_le_add ih honeBlock
          _ = (K : ℝ) *
              ((∑ x ∈ Finset.range turns, rho ^ x) +
                rho ^ turns) := by ring
  let turns := horizon / K + 1
  have hhorizonTurns : horizon ≤ turns * K := by
    dsimp only [turns]
    rw [Nat.add_mul, one_mul]
    exact (Nat.lt_div_mul_add hK).le
  have hprefixMono :
      (∑ time ∈ Finset.range horizon,
          quittingOpponentSurvivalWeight roots who
            (firstBlock * K) time) ≤
        ∑ time ∈ Finset.range (turns * K),
          quittingOpponentSurvivalWeight roots who
            (firstBlock * K) time := by
    calc
      (∑ time ∈ Finset.range horizon,
          quittingOpponentSurvivalWeight roots who
            (firstBlock * K) time) ≤
        (∑ time ∈ Finset.range horizon,
            quittingOpponentSurvivalWeight roots who
              (firstBlock * K) time) +
          ∑ time ∈ Finset.Ico horizon (turns * K),
            quittingOpponentSurvivalWeight roots who
              (firstBlock * K) time := by
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun time _ ↦
            quittingOpponentSurvivalWeight_nonneg roots who
              (firstBlock * K) time)
      _ = ∑ time ∈ Finset.range (turns * K),
          quittingOpponentSurvivalWeight roots who
            (firstBlock * K) time :=
        Finset.sum_range_add_sum_Ico _ hhorizonTurns
  have hgeometric :
      (∑ turn ∈ Finset.range turns, rho ^ turn) ≤ (1 - rho)⁻¹ := by
    have hpartial :=
      (summable_geometric_of_lt_one hrho0 hrho1).sum_le_tsum
        (Finset.range turns) (fun turn _ ↦ pow_nonneg hrho0 turn)
    simpa only [tsum_geometric_of_lt_one hrho0 hrho1] using hpartial
  calc
    (∑ time ∈ Finset.range horizon,
        quittingOpponentSurvivalWeight roots who
          (firstBlock * K) time) ≤
      ∑ time ∈ Finset.range (turns * K),
        quittingOpponentSurvivalWeight roots who
          (firstBlock * K) time := hprefixMono
    _ ≤ (K : ℝ) * ∑ turn ∈ Finset.range turns, rho ^ turn :=
      hwhole turns
    _ ≤ (K : ℝ) * (1 - rho)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeometric (Nat.cast_nonneg K)
    _ = (K : ℝ) / (1 - rho) := by ring

/-- Expected opponent-live time from an aligned block boundary. -/
def quittingExpectedOpponentLiveTime
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  ∑' time, quittingOpponentSurvivalWeight roots who start time

/-- The infinite expected opponent-live time obeys the same geometric block
bound as every finite prefix. -/
theorem quittingExpectedOpponentLiveTime_aligned_le
    (roots : ℕ → ι → PMF Bool) {rho : ℝ}
    (hK : 0 < K)
    (hblock : IsQuittingOpponentBlockContraction roots K rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (firstBlock : ℕ) (who : ι) :
    quittingExpectedOpponentLiveTime roots who (firstBlock * K) ≤
      (K : ℝ) / (1 - rho) := by
  unfold quittingExpectedOpponentLiveTime
  exact Real.tsum_le_of_sum_range_le
    (fun time ↦ quittingOpponentSurvivalWeight_nonneg
      roots who (firstBlock * K) time)
    (sum_quittingOpponentSurvivalWeight_aligned_le
      roots hK hblock hrho0 hrho1 firstBlock who)

end GameTheory
