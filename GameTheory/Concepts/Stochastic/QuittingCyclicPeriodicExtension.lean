/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclePinnedDebt

/-!
# Periodic extension of an anchored chain by its cyclic continuation block

`QuittingCyclePinnedDebt` defines `quittingCyclePinnedDynamicDebt`, the exact
backward Bellman debt of an anchored chain graded against a *realized*
terminal continuation, and records that its general nonnegativity was not
proved there.  The obstruction was an interface one:
`quittingFiniteDynamicDebt_nonneg` consumes `IsQuittingLivePrescribedValue`,
a `∀ time` condition, whereas `quittingFiniteNashBellmanPathValue` and
`quittingFiniteNashBellmanPathRoots` pad beyond the cutoff with `0` and
all-Continue -- a padding coherent only for the zero boundary.

This file removes the obstruction by supplying the extension that docstring
asked for.  Given an anchored chain of length `cutoff` and a cyclic
continuation block of period `period + 1`, the *periodic extension* runs the
chain on `[0, cutoff)` and then repeats the block forever.

## Index convention

`QuittingFiniteNashBellmanPath ι n = Fin (n + 1) → QuittingNashBellmanPoint ι`
and the point at index `k` carries the value *entering* stage `k` together
with the root *played at* stage `k`.  Edge `stage : Fin n` therefore relates
`path (Fin.castSucc stage)` (entering stage `stage`) to `path (Fin.succ stage)`
(entering stage `stage + 1`), and the root of stage `stage` is stored in
`path (Fin.castSucc stage)`.

The extension follows the same convention:

* `quittingCyclicPeriodicValue cutoff path period block time` is the value
  *entering* time `time`;
* `quittingCyclicPeriodicRoots cutoff path period block time` is the root
  *played at* time `time`;
* for `time < cutoff` both read `path ⟨time, _⟩`, matching
  `quittingFiniteNashBellmanPathValue` (defined for `time < cutoff + 1`) and
  `quittingFiniteNashBellmanPathRoots` (defined for `time < cutoff`);
* for `cutoff ≤ time` both read
  `block (Fin.castSucc ⟨(time - cutoff) % (period + 1), _⟩)`.

The two conventions therefore agree on exactly the windows demanded by
`quittingFiniteDynamicDebt_congr`: roots on `[start, start + fuel)` and values
on `[start, start + fuel]`, which for `start + fuel = cutoff` are `[0, cutoff)`
and `[0, cutoff]`.  At `time = cutoff` the extension reads `(block 0).1`,
which equals the chain's anchor `(path (Fin.last cutoff)).1` precisely because
the block reproduces `terminal` at its origin.

## Where self-reproduction is consumed

Two gluing identities drive everything:

* `hjoin : (block 0).1 = (path (Fin.last cutoff)).1` -- the seam at the
  cutoff;
* `hcycle : (block 0).1 = (block (Fin.last (period + 1))).1` -- the seam at
  each wrap of the block.

Both follow from `IsQuittingCyclicContinuationBlock` together with anchoring,
and `hcycle` is *exactly* the block's self-reproduction clause
`(block 0).1 = terminal` combined with its terminal anchoring.  Without it the
extension breaks at every wrap: `quittingCyclicPeriodicValue_succ_of_le` would
be false.

## What absorption is and is not used for

The absorption clause of `IsQuittingCyclicContinuationBlock` is **not** used
anywhere in this file, and the lemmas below are deliberately stated without
it.  This is not a weakening of the fence.  Absorption is what makes the
realized continuation a *function of the block* rather than a free parameter
(`quittingCyclicContinuation_value_eq_of_absorbing_period_one`), and it is the
reason the cycle-pinned family is not vacuous; but the periodic extension is a
statement about the exactness grammar alone, so it does not need it, and
saying so is more informative than carrying an unused hypothesis.  The final
nonnegativity theorems are nevertheless stated against
`IsQuittingCyclicContinuation` and `quittingCyclePinnedChainSet`, which do
carry the fence.

## Second half of the file: general-period uniqueness

`QuittingCyclePinnedDebt` proves that an absorbing self-reproducing row
determines its continuation only at period one.  The second half of this file
removes that restriction: `quittingRootSequenceBackwardPayoff` composes the
block's backward steps, `quittingRootSequenceBackwardPayoff_sub` shows the
composed map is affine with linear part `∏ k, quittingStationaryContinueMass`,
and `quittingCyclicContinuation_unique_of_absorbing` concludes that two cyclic
continuation blocks playing the same rows certify the same terminal vector.
That is the statement making the realized continuation a *function of the
rows*, which is the whole reason absorption is part of the definition.  Here
absorption *is* used, through
`prod_quittingStationaryContinueMass_lt_one_of_absorbing`.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The periodic block stage -/

/-- The block stage played at extended time `time`.  It is read only for
`cutoff ≤ time`, where it is `(time - cutoff) % (period + 1)`. -/
def quittingCyclicPeriodicStage (cutoff period time : ℕ) : Fin (period + 1) :=
  ⟨(time - cutoff) % (period + 1), Nat.mod_lt _ (Nat.succ_pos period)⟩

@[simp] theorem quittingCyclicPeriodicStage_self (cutoff period : ℕ) :
    quittingCyclicPeriodicStage cutoff period cutoff = 0 := by
  apply Fin.ext
  simp [quittingCyclicPeriodicStage]

/-- Advancing the extended clock advances the block stage cyclically. -/
theorem quittingCyclicPeriodicStage_succ_val (cutoff period time : ℕ)
    (htime : cutoff ≤ time) :
    (quittingCyclicPeriodicStage cutoff period (time + 1)).val =
      ((quittingCyclicPeriodicStage cutoff period time).val + 1) % (period + 1) := by
  have hsub : time + 1 - cutoff = time - cutoff + 1 := by omega
  simp only [quittingCyclicPeriodicStage, hsub]
  rw [Nat.mod_add_mod]

/-! ## The periodic extension of an anchored chain -/

/-- The value *entering* extended time `time`: the chain's displayed value
before the cutoff, and the block's displayed value at the corresponding cyclic
stage from the cutoff on. -/
def quittingCyclicPeriodicValue
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (time : ℕ) : Payoff ι :=
  if htime : time < cutoff then (path ⟨time, Nat.lt_succ_of_lt htime⟩).1
  else (block (Fin.castSucc (quittingCyclicPeriodicStage cutoff period time))).1

/-- The root *played at* extended time `time`, on the same convention as
`quittingCyclicPeriodicValue`. -/
def quittingCyclicPeriodicRoots
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (time : ℕ) : ι → PMF Bool :=
  if htime : time < cutoff then
    quittingRootOfSimplex (path ⟨time, Nat.lt_succ_of_lt htime⟩).2
  else
    quittingRootOfSimplex
      (block (Fin.castSucc (quittingCyclicPeriodicStage cutoff period time))).2

section PeriodicExtension

variable (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
  (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))

omit [DecidableEq ι] in
theorem quittingCyclicPeriodicValue_of_lt (time : ℕ) (htime : time < cutoff) :
    quittingCyclicPeriodicValue cutoff path period block time =
      (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 :=
  dif_pos htime

omit [DecidableEq ι] in
theorem quittingCyclicPeriodicValue_of_le (time : ℕ) (htime : cutoff ≤ time) :
    quittingCyclicPeriodicValue cutoff path period block time =
      (block (Fin.castSucc (quittingCyclicPeriodicStage cutoff period time))).1 :=
  dif_neg (not_lt.mpr htime)

omit [DecidableEq ι] in
theorem quittingCyclicPeriodicRoots_of_lt (time : ℕ) (htime : time < cutoff) :
    quittingCyclicPeriodicRoots cutoff path period block time =
      quittingRootOfSimplex (path ⟨time, Nat.lt_succ_of_lt htime⟩).2 :=
  dif_pos htime

omit [DecidableEq ι] in
theorem quittingCyclicPeriodicRoots_of_le (time : ℕ) (htime : cutoff ≤ time) :
    quittingCyclicPeriodicRoots cutoff path period block time =
      quittingRootOfSimplex
        (block (Fin.castSucc (quittingCyclicPeriodicStage cutoff period time))).2 :=
  dif_neg (not_lt.mpr htime)

omit [DecidableEq ι] in
/-- At the seam the extension displays the block's origin value. -/
theorem quittingCyclicPeriodicValue_at_cutoff :
    quittingCyclicPeriodicValue cutoff path period block cutoff = (block 0).1 := by
  have hidx : Fin.castSucc (quittingCyclicPeriodicStage cutoff period cutoff) =
      (0 : Fin (period + 2)) := by
    apply Fin.ext
    simp [quittingCyclicPeriodicStage]
  rw [quittingCyclicPeriodicValue_of_le cutoff path period block cutoff le_rfl, hidx]

/-! ### The two seams -/

omit [DecidableEq ι] in
/-- **The wrap seam.**  From the cutoff on, the extension's next value is the
block's next displayed value, the block being read cyclically.  This is where
the block's self-reproduction is consumed: at the last block stage the
successor index wraps to `0`, and `hcycle` identifies the block's origin value
with its terminal value. -/
theorem quittingCyclicPeriodicValue_succ_of_le
    (hcycle : (block 0).1 = (block (Fin.last (period + 1))).1)
    (time : ℕ) (htime : cutoff ≤ time) :
    quittingCyclicPeriodicValue cutoff path period block (time + 1) =
      (block (Fin.succ (quittingCyclicPeriodicStage cutoff period time))).1 := by
  rw [quittingCyclicPeriodicValue_of_le cutoff path period block (time + 1) (by omega)]
  have hjlt : (quittingCyclicPeriodicStage cutoff period time).val < period + 1 :=
    (quittingCyclicPeriodicStage cutoff period time).isLt
  have hval := quittingCyclicPeriodicStage_succ_val cutoff period time htime
  by_cases hcase : (quittingCyclicPeriodicStage cutoff period time).val + 1 < period + 1
  · have hidx : Fin.castSucc (quittingCyclicPeriodicStage cutoff period (time + 1)) =
        Fin.succ (quittingCyclicPeriodicStage cutoff period time) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ, hval, Nat.mod_eq_of_lt hcase]
    rw [hidx]
  · have hjeq : (quittingCyclicPeriodicStage cutoff period time).val + 1 = period + 1 := by
      omega
    have hidx : Fin.castSucc (quittingCyclicPeriodicStage cutoff period (time + 1)) =
        (0 : Fin (period + 2)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_zero, hval, hjeq, Nat.mod_self]
    have hidx' : Fin.succ (quittingCyclicPeriodicStage cutoff period time) =
        Fin.last (period + 1) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last, hjeq]
    rw [hidx, hidx', hcycle]

omit [DecidableEq ι] in
/-- **The cutoff seam.**  Before the cutoff the extension's next value is the
chain's next displayed value; at the last pre-cutoff stage this uses `hjoin`,
that is, that the block's origin value is the chain's anchor. -/
theorem quittingCyclicPeriodicValue_succ_of_lt
    (hjoin : (block 0).1 = (path (Fin.last cutoff)).1)
    (time : ℕ) (htime : time < cutoff) :
    quittingCyclicPeriodicValue cutoff path period block (time + 1) =
      (path ⟨time + 1, Nat.succ_lt_succ htime⟩).1 := by
  by_cases hnext : time + 1 < cutoff
  · rw [quittingCyclicPeriodicValue_of_lt cutoff path period block (time + 1) hnext]
  · have hcut : cutoff = time + 1 := by omega
    subst hcut
    have hlast : (Fin.last (time + 1)) =
        (⟨time + 1, Nat.lt_succ_self (time + 1)⟩ : Fin (time + 2)) := rfl
    rw [quittingCyclicPeriodicValue_at_cutoff (time + 1) path period block, hjoin, hlast]

/-! ## The extension is an exact prescribed value at every time -/

/-- **The periodic extension solves the backward Bellman recursion globally.**
Before the cutoff this is the chain's own edge relation; from the cutoff on it
is the block's, read cyclically.  Only the two gluing identities are used;
absorption is not. -/
theorem quittingCyclicPeriodicValue_eq_successor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpathEdges : ∀ stage : Fin cutoff, IsQuittingNashBellmanEdge reward
      (path (Fin.castSucc stage)) (path (Fin.succ stage)))
    (hblockEdges : ∀ stage : Fin (period + 1), IsQuittingNashBellmanEdge reward
      (block (Fin.castSucc stage)) (block (Fin.succ stage)))
    (hjoin : (block 0).1 = (path (Fin.last cutoff)).1)
    (hcycle : (block 0).1 = (block (Fin.last (period + 1))).1)
    (time : ℕ) :
    quittingCyclicPeriodicValue cutoff path period block time =
      quittingRootSuccessorPayoff reward
        (quittingCyclicPeriodicValue cutoff path period block (time + 1))
        (quittingCyclicPeriodicRoots cutoff path period block time) := by
  by_cases htime : time < cutoff
  · rw [quittingCyclicPeriodicValue_of_lt cutoff path period block time htime,
      quittingCyclicPeriodicRoots_of_lt cutoff path period block time htime,
      quittingCyclicPeriodicValue_succ_of_lt cutoff path period block hjoin time htime]
    exact (hpathEdges ⟨time, htime⟩).1
  · have hle : cutoff ≤ time := not_lt.mp htime
    rw [quittingCyclicPeriodicValue_of_le cutoff path period block time hle,
      quittingCyclicPeriodicRoots_of_le cutoff path period block time hle,
      quittingCyclicPeriodicValue_succ_of_le cutoff path period block hcycle time hle]
    exact (hblockEdges (quittingCyclicPeriodicStage cutoff period time)).1

/-- **The scalar form: `IsQuittingLivePrescribedValue` holds globally.**  This
is the hypothesis `quittingFiniteDynamicDebt_nonneg` needs, and the whole
point of the periodic extension. -/
theorem isQuittingLivePrescribedValue_quittingCyclicPeriodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpathEdges : ∀ stage : Fin cutoff, IsQuittingNashBellmanEdge reward
      (path (Fin.castSucc stage)) (path (Fin.succ stage)))
    (hblockEdges : ∀ stage : Fin (period + 1), IsQuittingNashBellmanEdge reward
      (block (Fin.castSucc stage)) (block (Fin.succ stage)))
    (hjoin : (block 0).1 = (path (Fin.last cutoff)).1)
    (hcycle : (block 0).1 = (block (Fin.last (period + 1))).1)
    (who : ι) :
    IsQuittingLivePrescribedValue reward
      (quittingCyclicPeriodicRoots cutoff path period block) who
      (fun time ↦ quittingCyclicPeriodicValue cutoff path period block time who) := by
  intro time
  have hvec := congrFun (quittingCyclicPeriodicValue_eq_successor cutoff path period
    block reward hpathEdges hblockEdges hjoin hcycle time) who
  refine hvec.trans ?_
  exact quittingRootExpectedPayoff_continuation_congr reward
    (quittingCyclicPeriodicValue cutoff path period block (time + 1))
    (fun _ ↦ quittingCyclicPeriodicValue cutoff path period block (time + 1) who)
    (quittingCyclicPeriodicRoots cutoff path period block time) who rfl

/-! ## Agreement with the original chain on the debt window -/

omit [DecidableEq ι] in
/-- Before the cutoff the extension plays the chain's own roots. -/
theorem quittingCyclicPeriodicRoots_eq_pathRoots (time : ℕ) (htime : time < cutoff) :
    quittingCyclicPeriodicRoots cutoff path period block time =
      quittingFiniteNashBellmanPathRoots cutoff path time := by
  rw [quittingCyclicPeriodicRoots_of_lt cutoff path period block time htime]
  unfold quittingFiniteNashBellmanPathRoots
  rw [dif_pos htime]

omit [DecidableEq ι] in
/-- The extension agrees with the padded chain value on the closed window
`[0, cutoff]`.  At `cutoff` this is the cutoff seam; beyond it the two
genuinely differ, the padding being `0` and the extension being the block. -/
theorem quittingCyclicPeriodicValue_eq_pathValue
    (hjoin : (block 0).1 = (path (Fin.last cutoff)).1)
    (time : ℕ) (htime : time ≤ cutoff) :
    quittingCyclicPeriodicValue cutoff path period block time =
      quittingFiniteNashBellmanPathValue cutoff path time := by
  rcases lt_or_eq_of_le htime with hlt | heq
  · rw [quittingCyclicPeriodicValue_of_lt cutoff path period block time hlt]
    unfold quittingFiniteNashBellmanPathValue
    rw [dif_pos (Nat.lt_succ_of_lt hlt)]
  · subst heq
    have hlast : (Fin.last time) =
        (⟨time, Nat.lt_succ_self time⟩ : Fin (time + 1)) := rfl
    rw [quittingCyclicPeriodicValue_at_cutoff time path period block, hjoin, hlast]
    unfold quittingFiniteNashBellmanPathValue
    rw [dif_pos (Nat.lt_succ_self time)]

/-! ## Nonnegativity of the cycle-pinned dynamic debt -/

/-- The cycle-pinned dynamic debt is computed by the periodic extension.  The
debt recursion reads roots on `[time, cutoff)` and values on `[time, cutoff]`,
exactly the windows on which the extension and the padded chain agree. -/
theorem quittingCyclePinnedDynamicDebt_eq_periodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (hjoin : (block 0).1 = (path (Fin.last cutoff)).1)
    (who : ι) (time : ℕ) (htime : time ≤ cutoff) :
    quittingCyclePinnedDynamicDebt reward terminal cutoff path who time =
      quittingFiniteDynamicDebt reward
        (quittingCyclicPeriodicRoots cutoff path period block) who
        (fun liveTime ↦
          quittingCyclicPeriodicValue cutoff path period block liveTime who)
        (quittingTerminalContinuationMismatch reward terminal who)
        time (cutoff - time) := by
  rw [quittingCyclePinnedDynamicDebt]
  refine quittingFiniteDynamicDebt_congr reward _ _ who _ _ _ time (cutoff - time)
    (fun liveTime _ hlt ↦ ?_) (fun liveTime _ hle ↦ ?_)
  · exact (quittingCyclicPeriodicRoots_eq_pathRoots cutoff path period block
      liveTime (by omega)).symm
  · exact congrFun (quittingCyclicPeriodicValue_eq_pathValue cutoff path period block
      hjoin liveTime (by omega)).symm who

/-- **General nonnegativity of the cycle-pinned dynamic debt.**  Every chain
anchored at a self-consistent cyclic continuation has nonnegative exact
backward Bellman debt at every time.  This closes the gap recorded in the
module docstring of `QuittingCyclePinnedDebt`. -/
theorem quittingCyclePinnedDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (hterminal : IsQuittingCyclicContinuation reward terminal)
    (hpath : path ∈ quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (who : ι) (time : ℕ) :
    0 ≤ quittingCyclePinnedDynamicDebt reward terminal cutoff path who time := by
  obtain ⟨blockPeriod, blockPath, hblockMem, horigin, -⟩ := hterminal
  have hjoin : (blockPath 0).1 = (path (Fin.last cutoff)).1 := by
    rw [horigin, hpath.2.1]
  have hcycle : (blockPath 0).1 = (blockPath (Fin.last (blockPeriod + 1))).1 := by
    rw [horigin, hblockMem.2.1]
  by_cases htime : time ≤ cutoff
  · rw [quittingCyclePinnedDynamicDebt_eq_periodic cutoff path blockPeriod blockPath
      reward terminal hjoin who time htime]
    exact quittingFiniteDynamicDebt_nonneg reward _ who _
      (isQuittingLivePrescribedValue_quittingCyclicPeriodic cutoff path blockPeriod
        blockPath reward hpath.2.2 hblockMem.2.2 hjoin hcycle who)
      (quittingTerminalContinuationMismatch_nonneg reward terminal who)
      time (cutoff - time)
  · rw [quittingCyclePinnedDynamicDebt, show cutoff - time = 0 by omega,
      quittingFiniteDynamicDebt_zero]
    exact quittingTerminalContinuationMismatch_nonneg reward terminal who

/-- Pair form: every member of `quittingCyclePinnedChainSet` has nonnegative
cycle-pinned dynamic debt at every time. -/
theorem quittingCyclePinnedDynamicDebt_nonneg_of_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : Payoff ι × QuittingFiniteNashBellmanPath ι cutoff)
    (hpair : pair ∈ quittingCyclePinnedChainSet reward cutoff)
    (who : ι) (time : ℕ) :
    0 ≤ quittingCyclePinnedDynamicDebt reward pair.1 cutoff pair.2 who time :=
  quittingCyclePinnedDynamicDebt_nonneg cutoff pair.2 reward pair.1 hpair.1 hpair.2
    who time

end PeriodicExtension

/-! ## General-period uniqueness of the realized continuation

`quittingCyclicContinuation_unique_of_absorbing_period_one` shows that a
single absorbing self-reproducing row determines its continuation.  The
statements below remove the restriction to period one: what a cyclic
continuation block certifies is a *function of its rows*, not a free
parameter, at every period.

The mechanism is the one already isolated in
`quittingRootSuccessorPayoff_sub`: a single exact backward step is affine in
the continuation with scalar linear part `quittingStationaryContinueMass`.
Composing `L` steps multiplies the linear parts, so the block map is affine
with linear part `∏ k, quittingStationaryContinueMass (roots k)`, and
absorption at a single stage makes that product `< 1`.
-/

/-- Backward composition of exact Bellman steps along a root sequence.
`quittingRootSequenceBackwardPayoff reward roots continuation start steps` is
the value *entering* time `start` after running `steps` exact backward steps
with the roots played at `start, …, start + steps - 1` and then using
`continuation`.  This is the chain convention: the root of stage `k` is
`roots k`, and the result is the value entering the first stage. -/
def quittingRootSequenceBackwardPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (continuation : Payoff ι) : ℕ → ℕ → Payoff ι
  | _, 0 => continuation
  | start, steps + 1 =>
      quittingRootSuccessorPayoff reward
        (quittingRootSequenceBackwardPayoff reward roots continuation
          (start + 1) steps)
        (roots start)

omit [DecidableEq ι] in
@[simp] theorem quittingRootSequenceBackwardPayoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (continuation : Payoff ι) (start : ℕ) :
    quittingRootSequenceBackwardPayoff reward roots continuation start 0 =
      continuation := rfl

omit [DecidableEq ι] in
theorem quittingRootSequenceBackwardPayoff_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (continuation : Payoff ι) (start steps : ℕ) :
    quittingRootSequenceBackwardPayoff reward roots continuation start
        (steps + 1) =
      quittingRootSuccessorPayoff reward
        (quittingRootSequenceBackwardPayoff reward roots continuation
          (start + 1) steps)
        (roots start) := rfl

omit [DecidableEq ι] in
/-- **The block map is affine with linear part the product of the stage
masses.**  This is the `Fin`-indexed composition of
`quittingRootSuccessorPayoff_sub`. -/
theorem quittingRootSequenceBackwardPayoff_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (continuation continuation' : Payoff ι)
    (who : ι) (start steps : ℕ) :
    quittingRootSequenceBackwardPayoff reward roots continuation start steps who -
        quittingRootSequenceBackwardPayoff reward roots continuation' start
          steps who =
      (∏ k ∈ Finset.range steps,
          quittingStationaryContinueMass (roots (start + k))) *
        (continuation who - continuation' who) := by
  induction steps generalizing start with
  | zero => simp
  | succ steps ih =>
      have hprod : (∏ k ∈ Finset.range (steps + 1),
            quittingStationaryContinueMass (roots (start + k))) =
          quittingStationaryContinueMass (roots start) *
            ∏ k ∈ Finset.range steps,
              quittingStationaryContinueMass (roots (start + 1 + k)) := by
        have hshift : (∏ k ∈ Finset.range steps,
              quittingStationaryContinueMass (roots (start + (k + 1)))) =
            ∏ k ∈ Finset.range steps,
              quittingStationaryContinueMass (roots (start + 1 + k)) :=
          Finset.prod_congr rfl (fun k _ ↦ by
            rw [show start + (k + 1) = start + 1 + k by omega])
        rw [Finset.prod_range_succ', hshift, Nat.add_zero]
        exact mul_comm _ _
      rw [quittingRootSequenceBackwardPayoff_succ,
        quittingRootSequenceBackwardPayoff_succ,
        quittingRootSuccessorPayoff_sub, ih (start + 1), hprod, mul_assoc]

omit [DecidableEq ι] in
/-- **Strict contraction from a single absorbing stage.**  All stage masses
lie in `[0, 1]`, so one stage with positive absorption mass already forces the
product over the block to be strictly below one. -/
theorem prod_quittingStationaryContinueMass_lt_one_of_absorbing
    (roots : ℕ → ι → PMF Bool) (steps stage : ℕ) (hstage : stage < steps)
    (habsorb : 0 < quittingRootAbsorptionMass (roots stage)) :
    (∏ k ∈ Finset.range steps, quittingStationaryContinueMass (roots k)) < 1 := by
  have hmem : stage ∈ Finset.range steps := Finset.mem_range.mpr hstage
  have hsplit := Finset.mul_prod_erase (Finset.range steps)
    (fun k ↦ quittingStationaryContinueMass (roots k)) hmem
  have hle : (∏ k ∈ (Finset.range steps).erase stage,
      quittingStationaryContinueMass (roots k)) ≤ 1 :=
    Finset.prod_le_one (fun i _ ↦ quittingStationaryContinueMass_nonneg (roots i))
      (fun i _ ↦ quittingStationaryContinueMass_le_one (roots i))
  have hnonneg : 0 ≤ quittingStationaryContinueMass (roots stage) :=
    quittingStationaryContinueMass_nonneg (roots stage)
  have hlt : quittingStationaryContinueMass (roots stage) < 1 := by
    rw [quittingRootAbsorptionMass] at habsorb; linarith
  calc (∏ k ∈ Finset.range steps, quittingStationaryContinueMass (roots k)) =
      quittingStationaryContinueMass (roots stage) *
        ∏ k ∈ (Finset.range steps).erase stage,
          quittingStationaryContinueMass (roots k) := hsplit.symm
    _ ≤ quittingStationaryContinueMass (roots stage) * 1 :=
        mul_le_mul_of_nonneg_left hle hnonneg
    _ = quittingStationaryContinueMass (roots stage) := mul_one _
    _ < 1 := hlt

omit [DecidableEq ι] in
/-- **General-period uniqueness of the fixed continuation.**  A root sequence
whose block mass product is strictly below one fixes at most one continuation
vector.  At `steps = 1` this is
`quittingCyclicContinuation_unique_of_absorbing_period_one`. -/
theorem quittingRootSequence_fixedContinuation_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (steps : ℕ)
    (terminal terminal' : Payoff ι)
    (hfixed : terminal =
      quittingRootSequenceBackwardPayoff reward roots terminal 0 steps)
    (hfixed' : terminal' =
      quittingRootSequenceBackwardPayoff reward roots terminal' 0 steps)
    (hcontract : (∏ k ∈ Finset.range steps,
      quittingStationaryContinueMass (roots k)) < 1) :
    terminal = terminal' := by
  funext who
  have hsub := quittingRootSequenceBackwardPayoff_sub reward roots terminal
    terminal' who 0 steps
  rw [← congrFun hfixed who, ← congrFun hfixed' who] at hsub
  simp only [Nat.zero_add] at hsub
  nlinarith [hsub]

omit [DecidableEq ι] in
/-- **Specialization check.**  At `steps = 1` the general uniqueness statement
is exactly `quittingCyclicContinuation_unique_of_absorbing_period_one`, so the
generalization is genuine and not a differently shaped claim. -/
theorem quittingRootSequence_fixedContinuation_unique_period_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal terminal' : Payoff ι) (root : ι → PMF Bool)
    (hfixed : terminal = quittingRootSuccessorPayoff reward terminal root)
    (hfixed' : terminal' = quittingRootSuccessorPayoff reward terminal' root)
    (habsorb : 0 < quittingRootAbsorptionMass root) :
    terminal = terminal' := by
  refine quittingRootSequence_fixedContinuation_unique reward (fun _ ↦ root) 1
    terminal terminal' hfixed hfixed' ?_
  rw [Finset.prod_range_one]
  rw [quittingRootAbsorptionMass] at habsorb
  linarith

/-- An anchored exact chain is the backward composition of its own roots over
the remaining horizon, terminated at its anchor. -/
theorem quittingFiniteAnchoredChain_value_eq_backwardPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (steps : ℕ) :
    ∀ time, time + steps = cutoff →
      quittingFiniteNashBellmanPathValue cutoff path time =
        quittingRootSequenceBackwardPayoff reward
          (quittingFiniteNashBellmanPathRoots cutoff path) terminal time steps := by
  induction steps with
  | zero =>
      intro time hsum
      have hcut : cutoff = time := by omega
      subst hcut
      rw [quittingRootSequenceBackwardPayoff_zero]
      unfold quittingFiniteNashBellmanPathValue
      rw [dif_pos (Nat.lt_succ_self cutoff)]
      exact hpath.2.1
  | succ steps ih =>
      intro time hsum
      have htime : time < cutoff := by omega
      rw [quittingRootSequenceBackwardPayoff_succ, ← ih (time + 1) (by omega)]
      exact quittingFiniteNashBellmanPathValue_eq_successor_of_edges reward cutoff
        path hpath.2.2 time htime

/-- A cyclic continuation block exhibits its terminal vector as a fixed point
of the block's backward map.  Absorption is not used here. -/
theorem quittingCyclicContinuationBlock_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    terminal = quittingRootSequenceBackwardPayoff reward
      (quittingFiniteNashBellmanPathRoots (period + 1) block) terminal 0
      (period + 1) := by
  have hstep := quittingFiniteAnchoredChain_value_eq_backwardPayoff reward terminal
    (period + 1) block hblock.1 (period + 1) 0 (by omega)
  rw [← hstep]
  unfold quittingFiniteNashBellmanPathValue
  rw [dif_pos (Nat.succ_pos (period + 1))]
  exact hblock.2.1.symm

/-- **The realized continuation is a function of the block's rows.**  Two
cyclic continuation blocks of the same period playing the same rows at every
stage certify the same terminal vector.  This is the general-period form of
`quittingCyclicContinuation_unique_of_absorbing_period_one`, and it is what
the absorption fence buys.  Absorption enters only through the strict
inequality `∏ k, quittingStationaryContinueMass (roots k) < 1`; at product one
the argument gives nothing, and it cannot: the all-Continue block of
`quittingAllContinueBlock_forced` has product one and its map is the identity,
so it fixes every vector. -/
theorem quittingCyclicContinuation_unique_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal terminal' : Payoff ι) (period : ℕ)
    (block block' : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block)
    (hblock' : IsQuittingCyclicContinuationBlock reward terminal' (period + 1) block')
    (hrows : ∀ stage : Fin (period + 1),
      quittingRootOfSimplex (block (Fin.castSucc stage)).2 =
        quittingRootOfSimplex (block' (Fin.castSucc stage)).2) :
    terminal = terminal' := by
  have hsame : quittingFiniteNashBellmanPathRoots (period + 1) block =
      quittingFiniteNashBellmanPathRoots (period + 1) block' := by
    funext time
    unfold quittingFiniteNashBellmanPathRoots
    by_cases htime : time < period + 1
    · rw [dif_pos htime, dif_pos htime]
      exact hrows ⟨time, htime⟩
    · rw [dif_neg htime, dif_neg htime]
  obtain ⟨stage, habsorb⟩ := hblock.2.2
  have hstageRoot : quittingFiniteNashBellmanPathRoots (period + 1) block stage.val =
      quittingRootOfSimplex (block (Fin.castSucc stage)).2 := by
    unfold quittingFiniteNashBellmanPathRoots
    rw [dif_pos stage.isLt]
    rfl
  have hcontract := prod_quittingStationaryContinueMass_lt_one_of_absorbing
    (quittingFiniteNashBellmanPathRoots (period + 1) block) (period + 1) stage.val
    stage.isLt (by rw [hstageRoot]; exact habsorb)
  refine quittingRootSequence_fixedContinuation_unique reward
    (quittingFiniteNashBellmanPathRoots (period + 1) block) (period + 1)
    terminal terminal' (quittingCyclicContinuationBlock_fixed reward terminal period
      block hblock) ?_ hcontract
  rw [hsame]
  exact quittingCyclicContinuationBlock_fixed reward terminal' period block' hblock'

end GameTheory
