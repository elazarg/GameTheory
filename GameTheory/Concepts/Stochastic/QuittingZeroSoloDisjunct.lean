/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAdmissibleCycleTerminalEquilibrium
import GameTheory.Concepts.Stochastic.QuittingOwnerSoloCertification

/-!
# The zero-solo disjunct of the finite-quitting reduction

Write `Λ_i = max {0, r_i({i})}` for the solo-quit anchor of coordinate `i`
(`quittingPositiveSingletonDebtCap`).  A weight is **zero-solo** when `Λ = 0`,
i.e. when `r_i({i}) ≤ 0` at every coordinate.

On that class the whole program collapses to one profile.  Under all-continue
nobody ever absorbs, so the profile's terminal payoff is the zero vector.  A
unilateral deviation by `i` faces permanently silent opponents, so the only
absorbing event it can create is the singleton `{i}`, worth `r_i({i}) ≤ 0`;
never absorbing is worth `0`.  So all-continue is an *exact* terminal Nash
profile, and the exact terminal-to-uniform consumer delivers the zero vector
as a uniform-equilibrium payoff.

The absorbing-cycle route cannot reach these weights: absorption is exactly
what a zero-solo equilibrium refuses to do, and there are zero-solo weights
admitting no admissible absorbing cycle at all.  That is why the reduction is
stated below as a *disjunction*: a weight is covered either by this file's
zero-solo branch or by the cycle branch of
`QuittingAdmissibleCycleTerminalEquilibrium`.  Whether the second disjunct
holds on every weight with some `r_i({i}) > 0` is open; the disjunction as
stated here is a theorem.

## What is reused

Everything about the all-continue profile is already in `QuittingSimpleBranches`
(`quittingAlwaysContinueProfile`, its zero terminal payoff, and the exact
`ε`-Nash test `isεAsymptoticNash_quittingAlwaysContinue_iff`), and the exact
terminal-to-uniform step is `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`
of `QuittingOwnerSoloCertification`.  Nothing here rebuilds them.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The zero-solo class -/

/-- A weight is **zero-solo** when every coordinate's solo-quitting reward is
nonpositive, i.e. when the solo-quit anchor `Λ` vanishes identically. -/
def IsQuittingZeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ who : ι, reward (quittingSingletonTerminal who) who ≤ 0

omit [Fintype ι] [DecidableEq ι] in
/-- Zero-solo is literally `Λ = 0` for the repository's solo-quit anchor
`quittingPositiveSingletonDebtCap reward who = max {0, r_who({who})}`. -/
theorem isQuittingZeroSolo_iff_positiveSingletonDebtCap_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingZeroSolo reward ↔
      ∀ who : ι, quittingPositiveSingletonDebtCap reward who = 0 := by
  constructor
  · intro hzero who
    exact max_eq_left (hzero who)
  · intro hcap who
    have hle : reward (quittingSingletonTerminal who) who ≤
        quittingPositiveSingletonDebtCap reward who :=
      le_max_right _ _
    rw [hcap who] at hle
    exact hle

/-! ## All-continue is an exact equilibrium there -/

/-- On a zero-solo weight the all-continue profile is an **exact** terminal
Nash profile: no deviation against permanently silent opponents beats `0`. -/
theorem isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo reward) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward) :=
  (isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl).mpr hzero

/-- Conversely, an exact terminal Nash all-continue profile forces the weight
to be zero-solo.  So the zero-solo class is exactly the class on which this
file's construction works. -/
theorem isQuittingZeroSolo_of_isZeroAsymptoticNash_quittingAlwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward)) :
    IsQuittingZeroSolo reward :=
  (isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl).mp hnash

/-- The zero-solo class is exactly the class where all-continue is an exact
terminal equilibrium. -/
theorem isZeroAsymptoticNash_quittingAlwaysContinue_iff_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingAlwaysContinueProfile reward) ↔
      IsQuittingZeroSolo reward :=
  isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl

/-! ## The disjunct itself -/

/-- **The zero-solo disjunct.**  A zero-solo quitting game has the zero vector
as a uniform-equilibrium payoff, realized by all-continue.

`HEADLINE` — the unconditional half of the finite-quitting reduction: the
branch on which no equilibrium absorbs, hence the branch the absorbing-cycle
carrier of `QuittingAdmissibleCycleTerminalEquilibrium` provably cannot reach.
It covers only weights with `r_i({i}) ≤ 0` at *every* coordinate, and says
nothing about weights with some `r_i({i}) > 0`; the hypothesis is not
removable, since by
`isQuittingZeroSolo_of_isZeroAsymptoticNash_quittingAlwaysContinue` a single
coordinate with `r_i({i}) > 0` already destroys the all-continue profile's
exact optimality. -/
theorem quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) := by
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (quittingAlwaysContinueProfile reward)
    (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero)
  have hpayoff : quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) = (0 : Payoff ι) :=
    funext fun who ↦ quittingTerminalPayoff_quittingAlwaysContinue reward who
  rwa [hpayoff] at huniform

/-- Existential form of the zero-solo disjunct, matching the shape of the
cycle branch. -/
theorem exists_uniformEquilibriumPayoff_of_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  ⟨0, quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzero⟩

/-! ## The disjunctive reduction

The second disjunct, packaged as a `Prop` on the weight alone so that the two
branches can be stated side by side.
-/

/-- A weight **admits an admissible absorbing cycle** when some finite exact
Nash--Bellman block of positive length reproduces its own value at its origin,
absorbs at some stage, and has vanishing deviation mismatch at every
coordinate. -/
def HasAdmissibleAbsorbingQuittingCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)),
    IsQuittingCyclicContinuationBlock reward terminal (period + 1) block ∧
      IsQuittingCycleAdmissible reward
        (quittingCyclicContinuationBlockCycle period block)

/-- **The finite-quitting reduction, disjunctive form.**  A weight which is
either zero-solo or admits an admissible absorbing cycle has a uniform
equilibrium payoff.

`HEADLINE` — the current shape of the whole finite-quitting reduction in one
statement: the zero-solo branch is this file, the cycle branch is
`exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock`.
What it does **not** cover is the completeness of the disjunction itself: that
*every* weight satisfies one of the two disjuncts is open, and is exactly the
remaining obligation of the program.  In particular this theorem is not an
unconditional existence result. -/
theorem exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbranch : IsQuittingZeroSolo reward ∨
      HasAdmissibleAbsorbingQuittingCycle reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hbranch with hzero | ⟨terminal, period, block, hblock, hadmissible⟩
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · exact exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock
      reward terminal period block hblock hadmissible

/-! ## The counterexample weight is in the zero-solo branch

The two-player table `r({1}) = (0, -1)`, `r({2}) = (1, -1)`, `r({1,2}) = (0,0)`
admits no admissible absorbing cycle (hand-checked, not formalized), which
refutes the unqualified reduction.  It is zero-solo — `r_1({1}) = 0` and
`r_2({2}) = -1` — so the disjunction survives it.  The instance below records
only the machine-checkable half: that this weight lands in the zero-solo
branch and therefore has a uniform equilibrium payoff.
-/

namespace QuittingZeroSoloDisjunct

/-- The counterexample weight of `TheCarrierNeedsTheZeroSoloDisjunct`, with
`false` for player one and `true` for player two. -/
def carrierReward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who =>
    if S.1 = {false} then (if who then -1 else 0)
    else if S.1 = {true} then (if who then -1 else 1)
    else 0

@[simp] theorem carrierReward_singleton_false :
    carrierReward (quittingSingletonTerminal false) false = 0 := by
  simp [carrierReward, quittingSingletonTerminal]

@[simp] theorem carrierReward_singleton_true :
    carrierReward (quittingSingletonTerminal true) true = -1 := by
  have hne : ({true} : Finset Bool) ≠ {false} := by decide
  simp [carrierReward, quittingSingletonTerminal, hne]

/-- The counterexample weight is zero-solo. -/
theorem isQuittingZeroSolo_carrierReward : IsQuittingZeroSolo carrierReward := by
  intro who
  cases who with
  | false => simp
  | true => norm_num

/-- Hence it has the zero vector as a uniform-equilibrium payoff, realized by
all-continue — even though it admits no admissible absorbing cycle. -/
theorem isUniformEquilibriumPayoff_zero_carrierReward :
    (quittingGame carrierReward).IsUniformEquilibriumPayoff none
      (0 : Payoff Bool) :=
  quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo carrierReward
    isQuittingZeroSolo_carrierReward

end QuittingZeroSoloDisjunct

end GameTheory
