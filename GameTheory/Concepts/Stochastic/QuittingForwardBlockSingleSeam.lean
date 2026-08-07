/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingleSeamProjectiveLasso

/-!
# Reversing an exact forward Bellman block into a single-seam lasso

Let a forward orbit obey

`V_(t+1) = F(root_t, V_t)`.

A chronological quitting cycle reads a finite interval backwards.  For a
block of length `n+1` starting at `start`, phase `p : Fin (n+1)` carries

```text
root_p  = root_(start + p.rev),
value_p = V_(start + p.rev + 1).
```

Every phase except `Fin.last n` then satisfies the chronological Bellman
equation exactly.  The last phase uses `V_(start+n+1)` instead of `V_start` as
its wrapped continuation, so its policy residual is the single affine seam

```text
continueMass(root_start) * (V_start - V_(start+n+1)).
```

All hypotheses in this file are local to the displayed finite interval.  A
producer may extend its arrays arbitrarily outside the prefix; no Bellman,
support, or rationality statement is requested there.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The roots of a forward interval, read in chronological reverse order. -/
def quittingReversedForwardCycle
    (roots : ℕ → ι → PMF Bool) (start n : ℕ) :
    Fin (n + 1) → ι → PMF Bool :=
  fun phase => roots (start + phase.rev)

/-- The entering values of the reversed chronological interval. -/
def quittingReversedForwardValue
    (forward : ℕ → Payoff ι) (start n : ℕ) :
    Fin (n + 1) → Payoff ι :=
  fun phase => forward (start + phase.rev + 1)

omit [DecidableEq ι] in
/-- The aggregate absorption of the reversed cycle is exactly the survival
product over the original forward interval.  Reversal changes neither the
finite product nor its absorption deficit. -/
theorem quittingCyclicWeightedAbsorption_reversedForwardCycle
    (roots : ℕ → ι → PMF Bool) (start n : ℕ) :
    quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle roots start n) =
      1 - ∏ offset ∈ Finset.range (n + 1),
        (1 - quittingRootAbsorptionMass (roots (start + offset))) := by
  classical
  let charge : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (roots time)
  let factor : Fin (n + 1) → ℝ := fun phase =>
    1 - charge (start + phase)
  have hcontinue : ∀ phase : Fin (n + 1),
      quittingStationaryContinueMass (roots (start + phase.rev)) =
        factor phase.rev := by
    intro phase
    dsimp only [factor, charge]
    unfold quittingRootAbsorptionMass
    ring
  unfold quittingCyclicWeightedAbsorption
    quittingReversedForwardCycle
  simp_rw [hcontinue]
  have hrev :
      (∏ phase : Fin (n + 1), factor phase.rev) =
        ∏ phase : Fin (n + 1), factor phase := by
    simpa using (Equiv.prod_comp Fin.revPerm factor)
  rw [hrev, Finset.prod_range]
  rfl

omit [DecidableEq ι] in
/-- Away from the last phase, rotating forward once and then reversing lowers
the underlying forward index by one. -/
theorem finRotate_rev_add_one_eq_rev_of_ne_last
    {n : ℕ} (phase : Fin (n + 1)) (hphase : phase ≠ Fin.last n) :
    ((finRotate (n + 1) phase).rev : ℕ) + 1 = phase.rev := by
  have hlt : phase.val < n := Fin.val_lt_last hphase
  rw [finRotate_of_lt hlt]
  simp only [Fin.val_rev]
  omega

omit [DecidableEq ι] in
/-- Every nonclosing phase of a reversed exact forward block has zero cyclic
policy residual. -/
theorem quittingCyclicPolicyResidual_reversedForward_eq_zero_of_ne_last
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (forward : ℕ → Payoff ι)
    (start n : ℕ)
    (hpolicy : ∀ time,
      start ≤ time → time < start + n + 1 →
      forward (time + 1) = quittingRootSuccessorPayoff reward
        (forward time) (roots time))
    (phase : Fin (n + 1)) (who : ι)
    (hphase : phase ≠ Fin.last n) :
    quittingCyclicPolicyResidual reward
        (quittingReversedForwardCycle roots start n)
        (quittingReversedForwardValue forward start n)
        phase who = 0 := by
  have hrev := finRotate_rev_add_one_eq_rev_of_ne_last phase hphase
  have htailIndex :
      start + ((finRotate (n + 1) phase).rev : ℕ) + 1 =
        start + (phase.rev : ℕ) := by
    omega
  have htime0 : start ≤ start + (phase.rev : ℕ) := by omega
  have htime1 : start + (phase.rev : ℕ) < start + n + 1 := by
    have hlt := phase.rev.isLt
    omega
  have hcurrent := congrFun
    (hpolicy (start + (phase.rev : ℕ)) htime0 htime1) who
  unfold quittingCyclicPolicyResidual
    quittingReversedForwardCycle quittingReversedForwardValue
  rw [htailIndex]
  rw [show start + (phase.rev : ℕ) + 1 =
      (start + (phase.rev : ℕ)) + 1 by omega, hcurrent]
  simp

omit [DecidableEq ι] in
/-- The closing residual of a reversed forward block is bounded by its endpoint
seam. -/
theorem abs_quittingCyclicPolicyResidual_reversedForward_last_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (forward : ℕ → Payoff ι)
    (start n : ℕ)
    (hpolicy : ∀ time,
      start ≤ time → time < start + n + 1 →
      forward (time + 1) = quittingRootSuccessorPayoff reward
        (forward time) (roots time))
    (seam : ℝ)
    (hclose : ∀ who,
      |forward start who - forward (start + n + 1) who| ≤ seam)
    (who : ι) :
    |quittingCyclicPolicyResidual reward
        (quittingReversedForwardCycle roots start n)
        (quittingReversedForwardValue forward start n)
        (Fin.last n) who| ≤ seam := by
  have hstep := congrFun
    (hpolicy start (by omega) (by omega)) who
  have hresidual :
      quittingCyclicPolicyResidual reward
          (quittingReversedForwardCycle roots start n)
          (quittingReversedForwardValue forward start n)
          (Fin.last n) who =
        quittingStationaryContinueMass (roots start) *
          (forward start who - forward (start + n + 1) who) := by
    unfold quittingCyclicPolicyResidual
      quittingReversedForwardCycle quittingReversedForwardValue
    simp only [Fin.val_rev, Fin.val_last, finRotate_last, Fin.val_zero]
    rw [show start + (n + 1 - (n + 1)) + 1 = start + 1 by omega,
      show start + (n + 1 - (0 + 1)) + 1 = start + n + 1 by omega,
      show start + 1 = start + 1 by rfl, hstep]
    have hrootIndex : start + (n + 1 - (n + 1)) = start := by
      omega
    rw [hrootIndex, quittingRootSuccessorPayoff_sub_eq_continueMass_mul]
  rw [hresidual, abs_mul,
    abs_of_nonneg (quittingStationaryContinueMass_nonneg (roots start))]
  calc
    quittingStationaryContinueMass (roots start) *
        |forward start who - forward (start + n + 1) who| ≤
      1 * |forward start who - forward (start + n + 1) who| :=
        mul_le_mul_of_nonneg_right
          (quittingStationaryContinueMass_le_one (roots start))
          (abs_nonneg _)
    _ ≤ seam := by simpa using hclose who

/-- Support-local optimality transfers to the reversed cycle.  Only the
closing phase pays the endpoint-closeness error; all other phases are exact
reindexings and are weakened from `supportError` to
`supportError + seamError`. -/
theorem isQuittingRootSupportApproxNash_reversedForward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (forward : ℕ → Payoff ι)
    (start n : ℕ) {supportError seamError : ℝ}
    (hseamError : 0 ≤ seamError)
    (hsupport : ∀ time,
      start ≤ time → time < start + n + 1 →
      IsQuittingRootSupportApproxNash reward
        (forward time) supportError (roots time))
    (hclose : ∀ who,
      |forward (start + n + 1) who - forward start who| ≤ seamError)
    (phase : Fin (n + 1)) :
    IsQuittingRootSupportApproxNash reward
      (quittingReversedForwardValue forward start n
        (finRotate (n + 1) phase))
      (supportError + seamError)
      (quittingReversedForwardCycle roots start n phase) := by
  by_cases hphase : phase = Fin.last n
  · subst phase
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (roots start) (forward start) (forward (start + n + 1))
      (δ := supportError) (η := seamError)
      (hsupport start (by omega) (by omega)) hclose
    simpa [quittingReversedForwardCycle,
      quittingReversedForwardValue, Fin.val_rev, finRotate_last] using htransfer
  · have hrev := finRotate_rev_add_one_eq_rev_of_ne_last phase hphase
    have htailIndex :
        start + ((finRotate (n + 1) phase).rev : ℕ) + 1 =
          start + (phase.rev : ℕ) := by
      omega
    have htime0 : start ≤ start + (phase.rev : ℕ) := by omega
    have htime1 : start + (phase.rev : ℕ) < start + n + 1 := by
      have hlt := phase.rev.isLt
      omega
    have htransfer := isQuittingRootSupportApproxNash_of_tail_close
      reward (roots (start + (phase.rev : ℕ)))
        (forward (start + (phase.rev : ℕ)))
        (forward (start + (phase.rev : ℕ)))
      (δ := supportError) (η := seamError)
      (hsupport (start + (phase.rev : ℕ)) htime0 htime1)
      (fun who => by simp [hseamError])
    unfold quittingReversedForwardCycle quittingReversedForwardValue
    rw [htailIndex]
    exact htransfer

/-- **Forward block to single-seam lasso.**

The block is read backwards, its nonclosing phases are exact, and endpoint
closeness pays the sole seam and support-transfer error.  Every assumption is
restricted to the finite interval consumed by the block. -/
def quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (forward : ℕ → Payoff ι)
    (start n : ℕ) {supportError seamError : ℝ}
    (hsupportError : 0 ≤ supportError) (hseamError : 0 ≤ seamError)
    (hpolicy : ∀ time,
      start ≤ time → time < start + n + 1 →
      forward (time + 1) = quittingRootSuccessorPayoff reward
        (forward time) (roots time))
    (hsupport : ∀ time,
      start ≤ time → time < start + n + 1 →
      IsQuittingRootSupportApproxNash reward
        (forward time) supportError (roots time))
    (hclose : ∀ who,
      |forward start who - forward (start + n + 1) who| ≤ seamError)
    (hclosingRatio : seamError ≤
      (supportError + seamError) *
        quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle roots start n))
    (hrational : ∀ target time,
      start < time → time ≤ start + n + 1 →
      quittingPunishmentValue reward target -
          (supportError + seamError) ≤ forward time target)
    (absorbingPhase : Fin (n + 1))
    (habsorbing : 0 < quittingRootAbsorptionMass
      (quittingReversedForwardCycle roots start n absorbingPhase)) :
    QuittingFiniteSingleSeamProjectiveLasso reward (n + 1)
      (supportError + seamError) where
  cycle := quittingReversedForwardCycle roots start n
  value := quittingReversedForwardValue forward start n
  closing := Fin.last n
  error_nonneg := add_nonneg hsupportError hseamError
  exact_away := by
    intro phase who hphase
    exact quittingCyclicPolicyResidual_reversedForward_eq_zero_of_ne_last
      reward roots forward start n hpolicy phase who hphase
  closing_bound := by
    intro who
    exact (abs_quittingCyclicPolicyResidual_reversedForward_last_le
      reward roots forward start n hpolicy seamError hclose who).trans
        hclosingRatio
  support := by
    intro phase
    exact isQuittingRootSupportApproxNash_reversedForward
      reward roots forward start n hseamError hsupport
        (fun who => by
          rw [abs_sub_comm]
          exact hclose who) phase
  rational := by
    intro target phase
    have hlt := phase.rev.isLt
    exact hrational target (start + (phase.rev : ℕ) + 1)
      (by omega) (by omega)
  absorbingPhase := absorbingPhase
  absorbing := habsorbing

end GameTheory
