/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtOptimizer
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Root.SuccessorCertificate
import GameTheory.Concepts.Stochastic.Models.Quitting.SimpleBranches
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Debt.Dynamic.DebtAugmentedEdge
import Math.PMFProduct.Bool

/-!
# The survival-times-terminal dynamic-debt bound is not tight

`quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on`
(`FiniteDynamicDebtChains.lean`) proves

`quittingFiniteDynamicDebt reward roots who prescribed terminalDebt start fuel ≤
  quittingOpponentSurvivalWeight roots who start fuel * terminalDebt`

whenever `prescribed` is a genuine live prescribed value and every local
residual vanishes on the examined window.  This is an **upper** bound only,
and this file records that no reverse inequality holds: there is no constant
`κ > 0` with

`κ * (quittingOpponentSurvivalWeight roots who start fuel * terminalDebt) ≤
  quittingFiniteDynamicDebt reward roots who prescribed terminalDebt start fuel`

in general.

## Mechanism

`quittingFiniteDynamicDebt` is a backward Bellman recursion built from a
`max` between a "stop now" alternative and a "continue, carrying the
transported debt forward" alternative.  A `max` can only ever *truncate*: it
never amplifies.  Once the stopping alternative's clean value already meets
or exceeds what continuing (plus whatever debt has accumulated downstream)
would deliver, the `max` selects the stopping branch outright and the
transported debt is discharged to nothing, no matter how large the surviving
terminal debt is.  There is no mechanism that could make the debt *exceed*
its survival-weighted cap, but there is nothing preventing it from being
annihilated far below that cap either.

## The witness

Two players over `Bool`.  Player `false` (`who`) is the tracked debt owner:
its prescribed policy quits for certain at the one examined stage.  Player
`true` (the opponent) continues for certain at every stage, so the opponent
survival weight is exactly `1` on every window.  The reward table gives the
solo-quitter `false` a terminal payoff of `1` and every other terminal
configuration `0`.

At the examined stage, `false`'s prescribed value already equals the pure
quit payoff `1`; the alternative of continuing (with the transported
terminal debt `terminalDebt = 1` added in) reaches exactly `1` as well, so
the `max` still selects `1` and no residual debt survives.  The dynamic debt
is exactly `0`, while the survival-weighted terminal debt is `1 · 1 = 1`.

## Deviation from the naively transcribed witness

A tempting simplification -- both players stay in these same pure actions
*forever*, not just at the examined stage -- does **not** work: it forces
the prescribed value to be constant and forces the "stop" and "continue"
branches to coincide identically (a bare tie, not a strict gap), so a
positive transported debt is *never* discharged and instead propagates
backward completely unchanged.  See `not_stationary_forever_witness` below
for the literal Lean confirmation.  The fix used here keeps the opponent's
"always continue" behavior exactly as stated (so the survival weight is
genuinely `1` on every window, not just the examined one), but lets the
debt owner's own prescribed policy return to `0` immediately after the
examined stage, which is enough to open a strict gap at that one stage
without disturbing the survival-weight computation at all.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingDynamicDebtSurvivalBoundNotTight

/-! We use `false` for the tracked debt owner and `true` for the opponent,
who continues with certainty at every stage. -/

/-- The reward table: the debt owner's solo terminal is `1`; every other
terminal configuration, including every payoff of the opponent, is `0`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun player =>
    if player then 0 else if false ∈ quitters.1 ∧ true ∉ quitters.1 then 1 else 0

/-- The root played at the one examined stage: the debt owner quits for
certain, the opponent continues for certain. -/
def rootQuit : Bool → PMF Bool :=
  fun player => if player then PMF.pure false else PMF.pure true

/-- The product-root family: the examined stage uses `rootQuit`, and every
later stage is all-Continue.  The opponent continues with certainty at
*every* stage, so its survival weight is `1` on every window. -/
def roots : ℕ → Bool → PMF Bool
  | 0 => rootQuit
  | _ + 1 => quittingAllContinueRoot

/-- The debt owner's prescribed bookkeeping value: `1` at the examined
stage, `0` from the next stage onward. -/
def prescribed : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 0

/-- The terminal debt fed into the recursion: the debt owner's positive
singleton cap, shown below to equal `1`. -/
def terminalDebt : ℝ := quittingPositiveSingletonDebtCap reward false

/-- The opponent's `rootQuit` marginal is a sure continue. -/
@[simp] theorem rootQuit_true : rootQuit true = PMF.pure false := rfl

/-- The debt owner's `rootQuit` marginal is a sure quit. -/
@[simp] theorem rootQuit_false : rootQuit false = PMF.pure true := rfl

/-- The examined stage uses `rootQuit`. -/
@[simp] theorem roots_zero : roots 0 = rootQuit := rfl

/-- Every later stage is all-Continue. -/
theorem roots_succ (t : ℕ) : roots (t + 1) = quittingAllContinueRoot := rfl

/-- The prescribed value at the examined stage is `1`. -/
@[simp] theorem prescribed_zero : prescribed 0 = 1 := rfl

/-- The prescribed value at every later stage is `0`. -/
@[simp] theorem prescribed_succ (t : ℕ) : prescribed (t + 1) = 0 := rfl

/-- The debt owner's solo-quit singleton terminal reward is `1`. -/
@[simp] theorem reward_singletonFalse :
    reward (quittingSingletonTerminal false) false = 1 := by
  simp [reward, quittingSingletonTerminal]

/-- The terminal debt fed into the recursion is `1`. -/
@[simp] theorem terminalDebt_eq_one : terminalDebt = 1 := by
  unfold terminalDebt quittingPositiveSingletonDebtCap
  rw [reward_singletonFalse]
  norm_num

/-! ## Root endpoint formulas, valid against any opponent marginal -/

/-- The debt owner's pure-Quit endpoint is exactly the opponent's Continue
probability: a solo quit only pays `1` when the opponent does not also
quit. -/
theorem false_quitPayoff (tail : Payoff Bool) (selectedRoot : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail selectedRoot false =
      (selectedRoot true false).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, quittingQuitters]

/-- The debt owner's pure-Continue endpoint is the opponent's Continue
probability times the declared tail: the owner only reaches the tail when
the opponent also does not quit. -/
theorem false_continuePayoff (tail : Payoff Bool) (selectedRoot : Bool → PMF Bool) :
    quittingRootContinuePayoff reward tail selectedRoot false =
      (selectedRoot true false).toReal * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, quittingQuitters]

/-- Against `rootQuit`, the pure-Quit endpoint is `1`: the opponent
continues with certainty there. -/
theorem quittingRootQuitPayoff_rootQuit (tail : Payoff Bool) :
    quittingRootQuitPayoff reward tail rootQuit false = 1 := by
  rw [false_quitPayoff]
  simp

/-- Against `rootQuit`, the pure-Continue endpoint is exactly the tail. -/
theorem quittingRootContinuePayoff_rootQuit (tail : Payoff Bool) :
    quittingRootContinuePayoff reward tail rootQuit false = tail false := by
  rw [false_continuePayoff]
  simp

/-! ## Opponent behavior: continues with certainty at every stage -/

/-- The opponent's marginal is `continue` at every stage, at both the
examined stage and every later one. -/
theorem roots_true (time : ℕ) : roots time true = PMF.pure false := by
  cases time with
  | zero => rfl
  | succ t => rfl

/-- Fixed-opponent Continue mass, generic in the underlying root family. -/
theorem fixedOpponentsContinueMass_eq (rootsFamily : ℕ → Bool → PMF Bool) (time : ℕ) :
    quittingFixedOpponentsContinueMass rootsFamily false time =
      (rootsFamily time true false).toReal := by
  unfold quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  simp [pmfPi_apply, quittingAllContinueAction]

/-- The opponent's certain-continue behavior makes the fixed-opponent
Continue mass exactly `1` at every stage.  Consequently the opponent
survival weight is `1` on every window (see `opponentSurvivalWeight_eq_one`
below), matching the intended witness's opponent behavior exactly. -/
@[simp] theorem fixedOpponentsContinueMass_eq_one (time : ℕ) :
    quittingFixedOpponentsContinueMass roots false time = 1 := by
  rw [fixedOpponentsContinueMass_eq, roots_true]
  simp

/-- The debt owner's opponent-only survival weight is `1` on every window
starting at time `0`: the opponent never quits. -/
theorem opponentSurvivalWeight_eq_one (fuel : ℕ) :
    quittingOpponentSurvivalWeight roots false 0 fuel = 1 := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset _
  exact fixedOpponentsContinueMass_eq_one (0 + offset)

/-! ## The debt owner's prescribed value is a genuine live prescribed value -/

/-- `prescribed` genuinely solves the live prescribed-value recursion along
`roots`: at the examined stage it equals the pure quit payoff (since the
owner's own marginal there is a certain quit), and at every later stage the
recursion trivially preserves the constant value `0`, since the all-Continue
root there sends any tail straight through. -/
theorem isQuittingLivePrescribedValue :
    IsQuittingLivePrescribedValue reward roots false prescribed := by
  intro time
  cases time with
  | zero =>
      change prescribed 0 =
        quittingRootSuccessorPayoff reward (fun _ ↦ prescribed 1) rootQuit false
      rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_rootQuit]
      simp [prescribed, rootQuit]
  | succ t =>
      change prescribed (t + 1) = quittingRootSuccessorPayoff reward
        (fun _ ↦ prescribed (t + 1 + 1)) quittingAllContinueRoot false
      rw [congrFun (quittingRootSuccessorPayoff_allContinueRoot_eq reward
        (fun _ ↦ prescribed (t + 1 + 1))) false]
      simp

/-! ## The residual vanishes at the examined stage -/

/-- The fixed-opponent Quit value at the examined stage is `1`. -/
theorem fixedOpponentsQuitValue_zero :
    quittingFixedOpponentsQuitValue reward roots false 0 = 1 := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward roots false
    (0 : Payoff Bool) 0, roots_zero, quittingRootQuitPayoff_rootQuit]

/-- The fixed-opponent immediate Continue reward at the examined stage is
`0`: with the opponent already forced to continue, the all-continue action
carries no immediate absorbing reward. -/
theorem fixedOpponentsContinueReward_zero :
    quittingFixedOpponentsContinueReward reward roots false 0 = 0 := by
  have h := quittingRootContinuePayoff_eq_fixedOpponents reward roots false
    (0 : Payoff Bool) 0
  rw [roots_zero, quittingRootContinuePayoff_rootQuit] at h
  simp only [Pi.zero_apply, mul_zero, add_zero] at h
  exact h.symm

/-- The prescribed local residual vanishes at the examined stage: the
Bellman maximum there already equals the prescribed value `1`. -/
theorem residual_zero_at_zero :
    quittingPrescribedOneStepResidual reward roots false prescribed 0 = 0 := by
  unfold quittingPrescribedOneStepResidual quittingLiveBellmanValue
  rw [fixedOpponentsQuitValue_zero, fixedOpponentsContinueReward_zero,
    fixedOpponentsContinueMass_eq_one]
  rw [show prescribed (0 + 1) = 0 from prescribed_succ 0]
  rw [show (0 : ℝ) + 1 * 0 = 0 by ring, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

/-! ## The actual dynamic debt is `0` -/

/-- The one-step exact dynamic debt at the examined stage is exactly `0`:
the transported terminal debt is annihilated outright by the `max`, since
the stopping branch already ties the continuing-with-debt branch. -/
theorem dynamicDebt_zero_one :
    quittingFiniteDynamicDebt reward roots false prescribed terminalDebt 0 1 = 0 := by
  change quittingFiniteDynamicDebt reward roots false prescribed terminalDebt 0 (0 + 1) = 0
  rw [quittingFiniteDynamicDebt_succ_eq_endpoints, quittingFiniteDynamicDebt_zero, roots_zero]
  simp only [quittingRootQuitPayoff_rootQuit, quittingRootContinuePayoff_rootQuit,
    fixedOpponentsContinueMass_eq_one, terminalDebt_eq_one,
    show prescribed (0 + 1) = 0 from prescribed_succ 0, prescribed_zero]
  rw [show (0 : ℝ) + 1 * 1 = 1 by ring, max_self]
  norm_num

/-! ## The witness genuinely lies inside the landed bound's scope -/

/-- The landed theorem's hypotheses all hold for this witness: `prescribed`
is a genuine live prescribed value, the terminal debt is nonnegative, and
the residual vanishes throughout the one-stage window `bound = 1`. -/
theorem satisfies_landed_bound :
    ∀ start fuel, start + fuel ≤ 1 →
      quittingFiniteDynamicDebt reward roots false prescribed terminalDebt
          start fuel ≤
        quittingOpponentSurvivalWeight roots false start fuel * terminalDebt :=
  quittingFiniteDynamicDebt_le_survival_mul_terminalDebt_on reward roots false
    prescribed isQuittingLivePrescribedValue
    (terminalDebt_eq_one ▸ (by norm_num : (0 : ℝ) ≤ 1)) 1
    (fun time htime ↦ by
      have : time = 0 := by omega
      subst this
      exact residual_zero_at_zero)

/-! ## Headline: the bound is not tight -/

/-- **The survival-times-terminal bound is one-sided.**  At this witness the
dynamic debt is exactly `0` while the survival-weighted terminal debt is
exactly `1`.  In particular the debt is strictly below the landed bound's
right side, even though the witness satisfies every one of the bound's
hypotheses (`satisfies_landed_bound`). -/
theorem dynamicDebt_lt_survival_mul_terminalDebt :
    quittingFiniteDynamicDebt reward roots false prescribed terminalDebt 0 1 <
      quittingOpponentSurvivalWeight roots false 0 1 * terminalDebt := by
  rw [dynamicDebt_zero_one, opponentSurvivalWeight_eq_one, terminalDebt_eq_one]
  norm_num

/-- **No positive multiple of the survival-weighted terminal debt
lower-bounds the dynamic debt.**  The `max` in the debt recursion can only
truncate a transported terminal debt, never amplify it, so there is no
constant `κ > 0` making `κ * (survival * terminalDebt)` a universal lower
bound on the dynamic debt: this witness already has dynamic debt `0` while
its survival-weighted terminal debt is the strictly positive value `1`. -/
theorem not_exists_pos_const_le_dynamicDebt :
    ¬ ∃ κ : ℝ, 0 < κ ∧
      ∀ start fuel,
        κ * (quittingOpponentSurvivalWeight roots false start fuel * terminalDebt) ≤
          quittingFiniteDynamicDebt reward roots false prescribed terminalDebt
            start fuel := by
  rintro ⟨κ, hκ, hle⟩
  have h := hle 0 1
  rw [dynamicDebt_zero_one, opponentSurvivalWeight_eq_one, terminalDebt_eq_one] at h
  nlinarith

/-! ## Confirmation that a literally-stationary witness does not work -/

/-- If instead the debt owner quit with certainty at *every* stage (not
just the examined one, as the naive de-gamed transcription suggested), the
prescribed value would be forced constant at `1` and the stopping branch
would exactly tie the continuing branch at every stage.  A tie never
discharges a positive transported debt against a Continue mass of `1`: it
transports it forward completely unchanged.  This confirms the literal
"quits forever" witness does **not** produce truncation; the fix used above
keeps the opponent's "always continue" behavior but returns the owner's own
prescribed policy to `0` immediately after the one examined stage. -/
theorem not_stationary_forever_witness :
    quittingFiniteDynamicDebt reward (fun _ ↦ rootQuit) false (fun _ ↦ (1 : ℝ))
        terminalDebt 0 1 = terminalDebt := by
  change quittingFiniteDynamicDebt reward (fun _ ↦ rootQuit) false (fun _ ↦ (1 : ℝ))
      terminalDebt 0 (0 + 1) = terminalDebt
  rw [quittingFiniteDynamicDebt_succ_eq_endpoints, quittingFiniteDynamicDebt_zero,
    quittingRootQuitPayoff_rootQuit, quittingRootContinuePayoff_rootQuit,
    fixedOpponentsContinueMass_eq (fun _ ↦ rootQuit), terminalDebt_eq_one]
  have hopp : (rootQuit true false).toReal = 1 := by simp [rootQuit]
  change max (1 : ℝ) (1 + (rootQuit true false).toReal * 1) - 1 = 1
  rw [hopp, max_eq_right (by norm_num : (1 : ℝ) ≤ 1 + 1 * 1)]
  norm_num

end QuittingDynamicDebtSurvivalBoundNotTight

end GameTheory
