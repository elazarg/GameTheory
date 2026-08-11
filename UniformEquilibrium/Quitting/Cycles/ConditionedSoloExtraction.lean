/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling

/-!
# Solo extraction from a summable conditioned deleted clock

Fix one player `owner` in a tail conditioned on eventual absorption.  If the
conditioned clock obtained by deleting `owner` is summable, then absorption by
an opponent has only summable total mass.  Every payoff coordinate therefore
tracks the payoff vector generated when `owner` quits alone.

The key point is vector-valued.  The existing singleton anchor is stated for
the selected player's own payoff coordinate.  Applying it to a projected
reward table gives the same estimate for every payoff recipient:

`|A_t(j) - q_t r_{\{owner\}}(j)| ≤ 2 M b_owner(t)`.

After division by the remaining eventual-absorption probability, the exact
conditioned Bellman recursion yields

`d_t(j) ≤ 2 M β_owner(t) + c_t d_{t+1}(j)`.

Finite iteration leaves a terminal error multiplied by the conditioned
continuation product.  Completeness of that product kills the terminal term,
while summability of `β_owner` makes its tail sum vanish.  Thus the whole
conditioned payoff vector converges to `owner`'s solo payoff vector.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## A deterministic finite-iteration lemma -/

/-- Iterate a scalar affine upper recurrence.  The unweighted charge sum is
valid because every coefficient lies in `[0,1]`; the terminal error retains
the exact product of continuation coefficients. -/
theorem value_le_sum_charge_add_product_tail
    (value charge coefficient : ℕ → ℝ)
    (hcharge : ∀ time, 0 ≤ charge time)
    (hcoefficientNonneg : ∀ time, 0 ≤ coefficient time)
    (hcoefficientOne : ∀ time, coefficient time ≤ 1)
    (hstep : ∀ time,
      value time ≤ charge time + coefficient time * value (time + 1))
    (start fuel : ℕ) :
    value start ≤
      (∑ offset ∈ Finset.range fuel, charge (start + offset)) +
        (∏ offset ∈ Finset.range fuel, coefficient (start + offset)) *
          value (start + fuel) := by
  have hproductNonneg : ∀ horizon,
      0 ≤ ∏ offset ∈ Finset.range horizon,
        coefficient (start + offset) := by
    intro horizon
    exact Finset.prod_nonneg fun offset _ ↦
      hcoefficientNonneg (start + offset)
  have hproductOne : ∀ horizon,
      (∏ offset ∈ Finset.range horizon,
        coefficient (start + offset)) ≤ 1 := by
    intro horizon
    induction horizon with
    | zero => simp
    | succ horizon ih =>
        rw [Finset.prod_range_succ]
        calc
          (∏ offset ∈ Finset.range horizon,
                coefficient (start + offset)) *
              coefficient (start + horizon) ≤
            (∏ offset ∈ Finset.range horizon,
                coefficient (start + offset)) * 1 :=
              mul_le_mul_of_nonneg_left
                (hcoefficientOne (start + horizon))
                (hproductNonneg horizon)
          _ = ∏ offset ∈ Finset.range horizon,
                coefficient (start + offset) := by ring
          _ ≤ 1 := ih
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      let prefixWeight := ∏ offset ∈ Finset.range fuel,
        coefficient (start + offset)
      let nextCharge := charge (start + fuel)
      let nextCoefficient := coefficient (start + fuel)
      have hprefix0 : 0 ≤ prefixWeight := by
        simpa only [prefixWeight] using hproductNonneg fuel
      have hprefix1 : prefixWeight ≤ 1 := by
        simpa only [prefixWeight] using hproductOne fuel
      have hscaledStep :
          prefixWeight * value (start + fuel) ≤
            prefixWeight * nextCharge +
              prefixWeight * nextCoefficient * value (start + fuel + 1) := by
        calc
          prefixWeight * value (start + fuel) ≤
              prefixWeight *
                (charge (start + fuel) +
                  coefficient (start + fuel) * value (start + fuel + 1)) :=
            mul_le_mul_of_nonneg_left (hstep (start + fuel)) hprefix0
          _ = prefixWeight * nextCharge +
              prefixWeight * nextCoefficient * value (start + fuel + 1) := by
            dsimp only [nextCharge, nextCoefficient]
            ring
      have hscaledCharge : prefixWeight * nextCharge ≤ nextCharge := by
        calc
          prefixWeight * nextCharge ≤ 1 * nextCharge :=
            mul_le_mul_of_nonneg_right hprefix1
              (hcharge (start + fuel))
          _ = nextCharge := one_mul _
      calc
        value start ≤
            (∑ offset ∈ Finset.range fuel, charge (start + offset)) +
              prefixWeight * value (start + fuel) := by
          simpa only [prefixWeight] using ih
        _ ≤ (∑ offset ∈ Finset.range fuel, charge (start + offset)) +
              (prefixWeight * nextCharge +
                prefixWeight * nextCoefficient * value (start + fuel + 1)) := by
          gcongr
        _ ≤ (∑ offset ∈ Finset.range fuel, charge (start + offset)) +
              (nextCharge +
                prefixWeight * nextCoefficient * value (start + fuel + 1)) := by
          gcongr
        _ = (∑ offset ∈ Finset.range (fuel + 1),
              charge (start + offset)) +
              (∏ offset ∈ Finset.range (fuel + 1),
                coefficient (start + offset)) *
                value (start + (fuel + 1)) := by
          dsimp only [prefixWeight, nextCharge, nextCoefficient]
          rw [Finset.sum_range_succ, Finset.prod_range_succ]
          simp only [Nat.add_assoc]
          ring

/-! ## Vector-valued singleton anchoring -/

/-- The one-stage absorbing contribution is anchored at one selected owner's
singleton outcome in every payoff coordinate, not only in the owner's own
coordinate. -/
theorem abs_quittingRootAbsorbingContribution_sub_absorption_mul_solo_le
    (root : ι → PMF Bool) (owner recipient : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingRootAbsorbingContribution reward root recipient -
        quittingRootAbsorptionMass root *
          reward (quittingSingletonTerminal owner) recipient| ≤
      2 * M * quittingRootOpponentAbsorptionMass root owner := by
  classical
  let projectedReward :
      {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun terminal _ ↦ reward terminal recipient
  have hprojected : ∀ terminal player,
      |projectedReward terminal player| ≤ M := by
    intro terminal player
    simpa only [projectedReward] using hreward terminal recipient
  have hanchor :=
    abs_quittingRootAbsorbingContribution_sub_absorption_mul_singleton_le
      (reward := projectedReward) root owner hM hprojected
  simpa [projectedReward, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff, quittingRootPayoff] using hanchor

/-! ## The conditioned solo recurrence -/

omit [DecidableEq ι] in
/-- The conditioned Bellman recursion in a division-safe form that does not
require positive one-stage absorption.  Rows with zero current absorption are
pure continuation rows. -/
theorem quittingTailConditionedValue_eq_absorbingContribution_div_add
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ) (recipient : ι)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingTailConditionedValue roots value boundary time recipient =
      quittingRootAbsorbingContribution reward (roots time) recipient /
          quittingTailEventualAbsorption roots time +
        quittingTailConditionedContinuationWeight roots time *
          quittingTailConditionedValue roots value boundary
            (time + 1) recipient := by
  have hstep := congrFun (hpolicy time) recipient
  rw [quittingRootSuccessorPayoff_apply_eq_affine] at hstep
  have hsurvival :=
    quittingJointSurvivalLimit_eq_continue_mul_succ roots time
  unfold quittingTailConditionedValue
    quittingTailConditionedContinuationWeight
  rw [hstep, hsurvival]
  field_simp [hcurrent.ne', hnext.ne']
  ring

/-- One conditioned Bellman step contracts the error from `owner`'s full solo
payoff vector, up to the owner-deleted absorption charge. -/
theorem abs_quittingTailConditionedValue_sub_singleton_le_step
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ) (owner recipient : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    |quittingTailConditionedValue roots value boundary time recipient -
        reward (quittingSingletonTerminal owner) recipient| ≤
      2 * M * quittingTailConditionedOpponentWeight roots time owner +
        quittingTailConditionedContinuationWeight roots time *
          |quittingTailConditionedValue roots value boundary
              (time + 1) recipient -
            reward (quittingSingletonTerminal owner) recipient| := by
  let eventual := quittingTailEventualAbsorption roots time
  let absorption := quittingRootAbsorptionMass (roots time)
  let rawOpponent := quittingRootOpponentAbsorptionMass (roots time) owner
  let alpha := absorption / eventual
  let beta := rawOpponent / eventual
  let continuation := quittingTailConditionedContinuationWeight roots time
  let absorbing :=
    quittingRootAbsorbingContribution reward (roots time) recipient
  let current :=
    quittingTailConditionedValue roots value boundary time recipient
  let next :=
    quittingTailConditionedValue roots value boundary (time + 1) recipient
  let solo := reward (quittingSingletonTerminal owner) recipient
  have hrec :=
    quittingTailConditionedValue_eq_absorbingContribution_div_add
      roots value boundary hpolicy time recipient hcurrent hnext
  change current = absorbing / eventual + continuation * next at hrec
  have hanchor :=
    abs_quittingRootAbsorbingContribution_sub_absorption_mul_solo_le
      (reward := reward) (roots time) owner recipient hM hreward
  change |absorbing - absorption * solo| ≤
    2 * M * rawOpponent at hanchor
  have hscaled :
      |absorbing / eventual - alpha * solo| ≤ 2 * M * beta := by
    have hrearrange :
        absorbing / eventual - alpha * solo =
          (absorbing - absorption * solo) / eventual := by
      dsimp only [alpha]
      field_simp [hcurrent.ne']
    rw [hrearrange, abs_div, abs_of_pos hcurrent]
    calc
      |absorbing - absorption * solo| / eventual ≤
          (2 * M * rawOpponent) / eventual :=
        div_le_div_of_nonneg_right hanchor hcurrent.le
      _ = 2 * M * beta := by
        dsimp only [beta]
        ring
  have hcontinuation0 : 0 ≤ continuation := by
    have h := quittingTailConditionedContinuationWeight_nonneg roots time
      (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1
      hcurrent
    simpa only [continuation] using h
  have hweights :=
    quittingTailConditionedWeights_add roots time hcurrent
  change alpha + continuation = 1 at hweights
  have hidentity :
      current - solo =
        (absorbing / eventual - alpha * solo) +
          continuation * (next - solo) := by
    rw [hrec]
    linear_combination solo * hweights
  change |current - solo| ≤
    2 * M * beta + continuation * |next - solo|
  rw [hidentity]
  calc
    |(absorbing / eventual - alpha * solo) +
        continuation * (next - solo)| ≤
      |absorbing / eventual - alpha * solo| +
        |continuation * (next - solo)| := abs_add_le _ _
    _ = |absorbing / eventual - alpha * solo| +
        continuation * |next - solo| := by
      rw [abs_mul, abs_of_nonneg hcontinuation0]
    _ ≤ 2 * M * beta + continuation * |next - solo| :=
      add_le_add hscaled (le_refl _)

/-! ## Tail bound and convergence -/

/-- A summable owner-deleted conditioned clock gives an explicit tail-sum
bound for every coordinate's distance from the owner's solo payoff vector. -/
theorem abs_quittingTailConditionedValue_sub_singleton_le_tsum
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (owner : ι)
    (hclock : Summable (fun time ↦
      quittingTailConditionedOpponentWeight roots time owner))
    (start : ℕ) (recipient : ι) :
    |quittingTailConditionedValue roots value boundary start recipient -
        reward (quittingSingletonTerminal owner) recipient| ≤
      2 * M * ∑' offset : ℕ,
        quittingTailConditionedOpponentWeight roots (start + offset) owner := by
  let beta : ℕ → ℝ := fun time ↦
    quittingTailConditionedOpponentWeight roots time owner
  let distance : ℕ → ℝ := fun time ↦
    |quittingTailConditionedValue roots value boundary time recipient -
      reward (quittingSingletonTerminal owner) recipient|
  let charge : ℕ → ℝ := fun time ↦ 2 * M * beta time
  let coefficient : ℕ → ℝ := fun time ↦
    quittingTailConditionedContinuationWeight roots time
  have hbetaSummable : Summable beta := by
    simpa only [beta] using hclock
  have hbetaNonneg : ∀ time, 0 ≤ beta time := by
    intro time
    have hraw :
        0 ≤ quittingRootOpponentAbsorptionMass (roots time) owner := by
      unfold quittingRootOpponentAbsorptionMass
      exact quittingRootAbsorptionMass_nonneg _
    dsimp only [beta]
    unfold quittingTailConditionedOpponentWeight
    exact div_nonneg hraw (hpositive time).le
  have hchargeNonneg : ∀ time, 0 ≤ charge time := by
    intro time
    dsimp only [charge]
    exact mul_nonneg (mul_nonneg (by norm_num) hM) (hbetaNonneg time)
  have hcoefficientNonneg : ∀ time, 0 ≤ coefficient time := by
    intro time
    have hunit :=
      (quittingTailConditionedWeights_mem_unitInterval roots time
        (quittingTailEventualAbsorption_mem_unitInterval
          roots (time + 1)).1
        (hpositive time)).2
    simpa only [coefficient] using hunit.1
  have hcoefficientOne : ∀ time, coefficient time ≤ 1 := by
    intro time
    have hunit :=
      (quittingTailConditionedWeights_mem_unitInterval roots time
        (quittingTailEventualAbsorption_mem_unitInterval
          roots (time + 1)).1
        (hpositive time)).2
    simpa only [coefficient] using hunit.2
  have hstep : ∀ time,
      distance time ≤ charge time + coefficient time * distance (time + 1) := by
    intro time
    simpa only [distance, charge, coefficient, beta] using
      (abs_quittingTailConditionedValue_sub_singleton_le_step
        (reward := reward) roots value boundary hpolicy time owner recipient
          hM hreward (hpositive time) (hpositive (time + 1)))
  have hbetaSuffix : Summable (fun offset ↦ beta (start + offset)) := by
    have hshift : Summable (fun offset ↦ beta (offset + start)) :=
      (summable_nat_add_iff start).2 hbetaSummable
    simpa [Nat.add_comm] using hshift
  have hproductLimit : Tendsto (fun fuel ↦
      ∏ offset ∈ Finset.range fuel,
        coefficient (start + offset)) atTop (nhds 0) := by
    simpa only [coefficient] using
      (tendsto_prod_quittingTailConditionedContinuationWeight_zero
        roots start hpositive heventualZero)
  have hbound : ∀ fuel,
      distance start ≤
        2 * M * (∑' offset : ℕ, beta (start + offset)) +
          2 * M * (∏ offset ∈ Finset.range fuel,
            coefficient (start + offset)) := by
    intro fuel
    have hiterate := value_le_sum_charge_add_product_tail
      distance charge coefficient hchargeNonneg hcoefficientNonneg
        hcoefficientOne hstep start fuel
    have hfiniteBeta :
        (∑ offset ∈ Finset.range fuel, beta (start + offset)) ≤
          ∑' offset : ℕ, beta (start + offset) :=
      hbetaSuffix.sum_le_tsum (Finset.range fuel) fun offset _ ↦
        hbetaNonneg (start + offset)
    have hfiniteCharge :
        (∑ offset ∈ Finset.range fuel, charge (start + offset)) ≤
          2 * M * ∑' offset : ℕ, beta (start + offset) := by
      calc
        (∑ offset ∈ Finset.range fuel, charge (start + offset)) =
            2 * M *
              (∑ offset ∈ Finset.range fuel, beta (start + offset)) := by
          dsimp only [charge]
          rw [Finset.mul_sum]
        _ ≤ 2 * M * ∑' offset : ℕ, beta (start + offset) :=
          mul_le_mul_of_nonneg_left hfiniteBeta
            (mul_nonneg (by norm_num) hM)
    have hproduct0 :
        0 ≤ ∏ offset ∈ Finset.range fuel,
          coefficient (start + offset) :=
      Finset.prod_nonneg fun offset _ ↦ hcoefficientNonneg (start + offset)
    have htailDistance : distance (start + fuel) ≤ 2 * M := by
      dsimp only [distance]
      calc
        |quittingTailConditionedValue roots value boundary
              (start + fuel) recipient -
            reward (quittingSingletonTerminal owner) recipient| ≤
          |quittingTailConditionedValue roots value boundary
              (start + fuel) recipient| +
            |reward (quittingSingletonTerminal owner) recipient| :=
          abs_sub _ _
        _ ≤ M + M :=
          add_le_add (hconditionedBound (start + fuel) recipient)
            (hreward (quittingSingletonTerminal owner) recipient)
        _ = 2 * M := by ring
    have hterminal :
        (∏ offset ∈ Finset.range fuel,
              coefficient (start + offset)) * distance (start + fuel) ≤
          (∏ offset ∈ Finset.range fuel,
              coefficient (start + offset)) * (2 * M) :=
      mul_le_mul_of_nonneg_left htailDistance hproduct0
    calc
      distance start ≤
          (∑ offset ∈ Finset.range fuel, charge (start + offset)) +
            (∏ offset ∈ Finset.range fuel,
              coefficient (start + offset)) * distance (start + fuel) :=
        hiterate
      _ ≤ 2 * M * (∑' offset : ℕ, beta (start + offset)) +
            (∏ offset ∈ Finset.range fuel,
              coefficient (start + offset)) * (2 * M) :=
        add_le_add hfiniteCharge hterminal
      _ = 2 * M * (∑' offset : ℕ, beta (start + offset)) +
            2 * M * (∏ offset ∈ Finset.range fuel,
              coefficient (start + offset)) := by ring
  have hupperLimit : Tendsto (fun fuel ↦
      2 * M * (∑' offset : ℕ, beta (start + offset)) +
        2 * M * (∏ offset ∈ Finset.range fuel,
          coefficient (start + offset))) atTop
      (nhds (2 * M * ∑' offset : ℕ, beta (start + offset))) := by
    have hscaled := hproductLimit.const_mul (2 * M)
    simpa using tendsto_const_nhds.add hscaled
  have hfinal := ge_of_tendsto' hupperLimit hbound
  simpa only [distance, beta] using hfinal

/-- **Summable deleted-clock solo extraction.**  If the conditioned clock
with `owner` deleted is summable, every coordinate of the conditioned payoff
converges to the payoff generated when `owner` quits alone. -/
theorem tendsto_quittingTailConditionedValue_solo_of_summableOpponentWeight
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤ M)
    (owner : ι)
    (hclock : Summable (fun time ↦
      quittingTailConditionedOpponentWeight roots time owner)) :
    ∀ recipient,
      Tendsto (fun time ↦
        quittingTailConditionedValue roots value boundary time recipient)
        atTop
        (nhds (reward (quittingSingletonTerminal owner) recipient)) := by
  intro recipient
  let beta : ℕ → ℝ := fun time ↦
    quittingTailConditionedOpponentWeight roots time owner
  have hbetaSummable : Summable beta := by
    simpa only [beta] using hclock
  have hbetaNonneg : ∀ time, 0 ≤ beta time := by
    intro time
    have hraw :
        0 ≤ quittingRootOpponentAbsorptionMass (roots time) owner := by
      unfold quittingRootOpponentAbsorptionMass
      exact quittingRootAbsorptionMass_nonneg _
    dsimp only [beta]
    unfold quittingTailConditionedOpponentWeight
    exact div_nonneg hraw (hpositive time).le
  have htail : Tendsto (fun time ↦
      ∑' offset : ℕ, beta (time + offset)) atTop (nhds 0) := by
    have htail' : Tendsto (fun time ↦
        ∑' offset : ℕ, beta (offset + time)) atTop (nhds 0) :=
      tendsto_sum_nat_add beta
    simpa [Nat.add_comm] using htail'
  have hmajor : Tendsto (fun time ↦
      2 * M * ∑' offset : ℕ, beta (time + offset))
      atTop (nhds 0) := by
    simpa using htail.const_mul (2 * M)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hmajor) ε hε
  refine ⟨threshold, fun time htime ↦ ?_⟩
  rw [Real.dist_eq]
  have hpointwise :=
    abs_quittingTailConditionedValue_sub_singleton_le_tsum
      (reward := reward) roots value boundary hpolicy hM hreward hpositive
        heventualZero hconditionedBound owner hclock time recipient
  exact lt_of_le_of_lt hpointwise <| by
    have hclose := hthreshold time htime
    have htail0 : 0 ≤ ∑' offset : ℕ, beta (time + offset) :=
      tsum_nonneg fun offset ↦ hbetaNonneg (time + offset)
    have hbound0 :
        0 ≤ 2 * M * ∑' offset : ℕ, beta (time + offset) :=
      mul_nonneg (mul_nonneg (by norm_num) hM) htail0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbound0] at hclose
    simpa only [beta] using hclose

end GameTheory
