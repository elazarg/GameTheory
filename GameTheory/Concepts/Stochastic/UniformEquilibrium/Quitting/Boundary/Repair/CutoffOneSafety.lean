/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtChains
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Exact safety at cutoff one in quitting games

A one-stage zero-boundary Nash root has a completely explicit exact dynamic
debt.  For player `who`, let `V` be the prescribed payoff at the root, `Q`
the pure-Quit endpoint, and `C⁺` the pure-Continue endpoint when survival
beyond the root is capped by the positive singleton option.  The cutoff-one
debt is

`max Q C⁺ - V`.

Exact root Nash already gives `Q ≤ V`.  Hence vanishing cutoff-one debt is
equivalent to the single semialgebraic safety inequality `C⁺ ≤ V`.  The
definitions below use the actual finite dynamic-debt recursion consumed by
the all-Continue-tail compiler; the displayed formula is not an unrelated
scalar surrogate.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supplied root at time zero, followed by all-Continue forever. -/
def quittingCutoffOneRoots (root : ι → PMF Bool) : ℕ → ι → PMF Bool
  | 0 => root
  | _ + 1 => quittingAllContinueRoot

/-- The zero-boundary value sequence attached to one supplied root. -/
def quittingCutoffOneValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : ℕ → Payoff ι
  | 0 => quittingRootSuccessorPayoff reward (0 : Payoff ι) root
  | _ + 1 => 0

/-- Player `who`'s Continue endpoint when surviving the root exposes the
singleton-or-Never terminal option. -/
def quittingCutoffOnePositiveContinuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootContinuePayoff reward
    (quittingPositiveSingletonDebtCap reward) root who

/-- The literal exact dynamic debt of the one-root zero-boundary chain. -/
def quittingCutoffOneDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingFiniteDynamicDebt reward (quittingCutoffOneRoots root) who
    (fun time => quittingCutoffOneValue reward root time who)
    (quittingPositiveSingletonDebtCap reward who) 0 1

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingCutoffOneRoots_zero
    (root : ι → PMF Bool) :
    quittingCutoffOneRoots root 0 = root := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingCutoffOneRoots_succ
    (root : ι → PMF Bool) (time : ℕ) :
    quittingCutoffOneRoots root (time + 1) =
      (quittingAllContinueRoot : ι → PMF Bool) := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingCutoffOneValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingCutoffOneValue reward root 0 =
      quittingRootSuccessorPayoff reward (0 : Payoff ι) root := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingCutoffOneValue_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingCutoffOneValue reward root (time + 1) = 0 := rfl

omit [DecidableEq ι] in
/-- The one-root value sequence is genuine policy evaluation, including its
all-Continue zero suffix. -/
theorem isQuittingLivePrescribedValue_cutoffOne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    IsQuittingLivePrescribedValue reward (quittingCutoffOneRoots root) who
      (fun time => quittingCutoffOneValue reward root time who) := by
  intro time
  cases time with
  | zero => rfl
  | succ time =>
      change (0 : ℝ) = quittingRootSuccessorPayoff reward
        (0 : Payoff ι) quittingAllContinueRoot who
      exact (congrFun
        (quittingRootSuccessorPayoff_allContinueRoot_eq
          reward (0 : Payoff ι)) who).symm

/-- Cutoff-one exact debt is nonnegative because the displayed value sequence
is actual policy evaluation and the terminal singleton cap is nonnegative. -/
theorem quittingCutoffOneDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingCutoffOneDynamicDebt reward root who := by
  exact quittingFiniteDynamicDebt_nonneg reward
    (quittingCutoffOneRoots root) who
    (fun time => quittingCutoffOneValue reward root time who)
    (isQuittingLivePrescribedValue_cutoffOne reward root who)
    (le_max_left _ _) 0 1

/-- **Exact cutoff-one debt equation.** -/
theorem quittingCutoffOneDynamicDebt_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingCutoffOneDynamicDebt reward root who =
      max
          (quittingRootQuitPayoff reward (0 : Payoff ι) root who)
          (quittingCutoffOnePositiveContinuePayoff reward root who) -
        quittingRootSuccessorPayoff reward (0 : Payoff ι) root who := by
  rw [quittingCutoffOneDynamicDebt, quittingFiniteDynamicDebt_succ]
  simp only [quittingFiniteDynamicDebt_zero,
    quittingCutoffOneValue_succ, Pi.zero_apply, zero_add]
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (quittingCutoffOneRoots root) who (0 : Payoff ι) 0,
    ← quittingRootContinuePayoff_eq_fixedOpponents
      reward (quittingCutoffOneRoots root) who
        (quittingPositiveSingletonDebtCap reward) 0]
  rfl

/-- Exact Nash at the zero-tail root makes the pure-Quit endpoint safe. -/
theorem quittingRootQuitPayoff_le_successor_of_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingRootQuitPayoff reward (0 : Payoff ι) root who ≤
      quittingRootSuccessorPayoff reward (0 : Payoff ι) root who := by
  simpa [quittingRootQuitPayoff, quittingRootSuccessorPayoff] using
    hnash who (PMF.pure true)

/-- **Exact cutoff-one safety equivalence.**  At a zero-tail exact Nash root,
the dynamic debt vanishes exactly when the positive-boundary Continue
endpoint lies below the prescribed root payoff. -/
theorem quittingCutoffOneDynamicDebt_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingCutoffOneDynamicDebt reward root who = 0 ↔
      quittingCutoffOnePositiveContinuePayoff reward root who ≤
        quittingRootSuccessorPayoff reward (0 : Payoff ι) root who := by
  let quitValue := quittingRootQuitPayoff reward (0 : Payoff ι) root who
  let continueValue := quittingCutoffOnePositiveContinuePayoff reward root who
  let prescribed :=
    quittingRootSuccessorPayoff reward (0 : Payoff ι) root who
  have hquit : quitValue ≤ prescribed :=
    quittingRootQuitPayoff_le_successor_of_isZeroNash
      reward root who hnash
  have hnonneg : 0 ≤ quittingCutoffOneDynamicDebt reward root who :=
    quittingCutoffOneDynamicDebt_nonneg reward root who
  rw [quittingCutoffOneDynamicDebt_eq] at hnonneg
  rw [quittingCutoffOneDynamicDebt_eq]
  change max quitValue continueValue - prescribed = 0 ↔
    continueValue ≤ prescribed
  constructor
  · intro hzero
    have hmax : max quitValue continueValue = prescribed :=
      sub_eq_zero.mp hzero
    exact (le_max_right quitValue continueValue).trans_eq hmax
  · intro hcontinue
    have hupper : max quitValue continueValue ≤ prescribed :=
      max_le hquit hcontinue
    change 0 ≤ max quitValue continueValue - prescribed at hnonneg
    linarith

/-- Simultaneous cutoff-one safety is equivalent to zero exact debt in every
player coordinate. -/
theorem all_quittingCutoffOneDynamicDebt_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    (∀ who, quittingCutoffOneDynamicDebt reward root who = 0) ↔
      ∀ who, quittingCutoffOnePositiveContinuePayoff reward root who ≤
        quittingRootSuccessorPayoff reward (0 : Payoff ι) root who := by
  constructor <;> intro h who
  · exact (quittingCutoffOneDynamicDebt_eq_zero_iff
      reward root who hnash).1 (h who)
  · exact (quittingCutoffOneDynamicDebt_eq_zero_iff
      reward root who hnash).2 (h who)

/-- The path-level exact-D coordinate at cutoff one has the same explicit
`max Q C⁺ - V` formula. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_cutoff_one_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : QuittingFiniteNashBellmanPath ι 1)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward 1)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward 1 path who 0 =
      max
          (quittingRootQuitPayoff reward (0 : Payoff ι)
            (quittingFiniteNashBellmanPathRoots 1 path 0) who)
          (quittingCutoffOnePositiveContinuePayoff reward
            (quittingFiniteNashBellmanPathRoots 1 path 0) who) -
        quittingRootSuccessorPayoff reward (0 : Payoff ι)
          (quittingFiniteNashBellmanPathRoots 1 path 0) who := by
  have hterminal :=
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward 1 path hpath
  have hpolicy :=
    quittingFiniteNashBellmanPathValue_eq_successor
      reward 1 path hpath 0 (by omega)
  rw [hterminal] at hpolicy
  rw [quittingFiniteNashBellmanPathDynamicDebt,
    quittingFiniteDynamicDebt_succ]
  simp only [quittingFiniteDynamicDebt_zero, hterminal, Pi.zero_apply,
    zero_add]
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (quittingFiniteNashBellmanPathRoots 1 path) who
        (0 : Payoff ι) 0,
    ← quittingRootContinuePayoff_eq_fixedOpponents
      reward (quittingFiniteNashBellmanPathRoots 1 path) who
        (quittingPositiveSingletonDebtCap reward) 0,
    hpolicy]
  rfl

/-- The specialized cutoff-one wrapper is definitionally faithful to the
general path exact-D coordinate on every admissible one-edge chain. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_cutoff_one_eq_cutoffOne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : QuittingFiniteNashBellmanPath ι 1)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward 1)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward 1 path who 0 =
      quittingCutoffOneDynamicDebt reward
        (quittingFiniteNashBellmanPathRoots 1 path 0) who := by
  rw [quittingFiniteNashBellmanPathDynamicDebt_cutoff_one_eq
      reward path hpath who,
    quittingCutoffOneDynamicDebt_eq]

/-- Every zero-debt cutoff-one Nash--Bellman certificate is exactly a safe
zero-tail Nash root, and conversely. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_cutoff_one_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : QuittingFiniteNashBellmanPath ι 1)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward 1)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward 1 path who 0 = 0 ↔
      quittingCutoffOnePositiveContinuePayoff reward
          (quittingFiniteNashBellmanPathRoots 1 path 0) who ≤
        quittingRootSuccessorPayoff reward (0 : Payoff ι)
          (quittingFiniteNashBellmanPathRoots 1 path 0) who := by
  rw [quittingFiniteNashBellmanPathDynamicDebt_cutoff_one_eq_cutoffOne
    reward path hpath who]
  have hnash := quittingFiniteNashBellmanPathRoots_isZeroNash
    reward 1 path hpath 0 (by omega)
  have hterminal :=
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward 1 path hpath
  simp only [Nat.zero_add] at hnash
  rw [hterminal] at hnash
  exact quittingCutoffOneDynamicDebt_eq_zero_iff reward
    (quittingFiniteNashBellmanPathRoots 1 path 0) who hnash

omit [Fintype ι] [DecidableEq ι] in
/-- From time one onward, the cutoff-one schedule is all-Continue. -/
theorem quittingCutoffOneRoots_eq_allContinue_of_one_le
    (root : ι → PMF Bool) (time : ℕ) (htime : 1 ≤ time) :
    quittingCutoffOneRoots root time =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  cases time with
  | zero => omega
  | succ time => rfl

omit [DecidableEq ι] in
/-- The cutoff-one value is zero at its terminal time. -/
theorem quittingCutoffOneValue_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingCutoffOneValue reward root 1 = 0 := rfl

omit [DecidableEq ι] in
/-- The only pre-terminal value equation of the cutoff-one schedule. -/
theorem quittingCutoffOneValue_eq_successor_of_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (time : ℕ) (htime : time < 1) :
    quittingCutoffOneValue reward root time =
      quittingRootSuccessorPayoff reward
        (quittingCutoffOneValue reward root (time + 1))
        (quittingCutoffOneRoots root time) := by
  have hzero : time = 0 := Nat.lt_one_iff.mp htime
  subst time
  rfl

omit [DecidableEq ι] in
/-- The one-root/all-Continue profile delivers the prescribed zero-tail root
payoff exactly. -/
theorem quittingTerminalPayoff_cutoffOneRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingTerminalPayoff reward
        (quittingInfinitePathProfile reward (quittingCutoffOneRoots root)) =
      quittingRootSuccessorPayoff reward (0 : Payoff ι) root := by
  classical
  rw [quittingTerminalPayoff_finiteExactChainProfile reward
    (quittingCutoffOneRoots root) (quittingCutoffOneValue reward root) 1
    (quittingCutoffOneRoots_eq_allContinue_of_one_le root)
    (quittingCutoffOneValue_one reward root)
    (quittingCutoffOneValue_eq_successor_of_lt_one reward root)]
  rfl

/-- A safe zero-tail exact Nash root, followed by Never, is an exact terminal
Nash profile. -/
theorem cutoffOneProfile_isZeroAsymptoticNash_of_safe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root)
    (hsafe : ∀ who,
      quittingCutoffOnePositiveContinuePayoff reward root who ≤
        quittingRootSuccessorPayoff reward (0 : Payoff ι) root who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingInfinitePathProfile reward (quittingCutoffOneRoots root)) := by
  apply finiteChainProfile_isεAsymptoticNash_of_dynamicDebt
    reward (quittingCutoffOneRoots root) (quittingCutoffOneValue reward root)
      1 0
    (quittingCutoffOneRoots_eq_allContinue_of_one_le root)
    (quittingCutoffOneValue_one reward root)
    (quittingCutoffOneValue_eq_successor_of_lt_one reward root)
  intro who
  change quittingCutoffOneDynamicDebt reward root who ≤ 0
  rw [(quittingCutoffOneDynamicDebt_eq_zero_iff
    reward root who hnash).2 (hsafe who)]

/-- **Cutoff-one uniform-existence theorem.**  One zero-tail exact Nash root
satisfying the playerwise semialgebraic safety inequalities makes its own
prescribed payoff vector a uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_cutoffOneSafeRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root)
    (hsafe : ∀ who,
      quittingCutoffOnePositiveContinuePayoff reward root who ≤
        quittingRootSuccessorPayoff reward (0 : Payoff ι) root who) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingRootSuccessorPayoff reward (0 : Payoff ι) root) := by
  have hterminal :=
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward
      (quittingInfinitePathProfile reward (quittingCutoffOneRoots root))
      (cutoffOneProfile_isZeroAsymptoticNash_of_safe
        reward root hnash hsafe)
  rwa [quittingTerminalPayoff_cutoffOneRoots reward root] at hterminal

end GameTheory
