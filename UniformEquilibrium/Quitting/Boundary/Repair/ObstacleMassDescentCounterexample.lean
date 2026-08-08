/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Debt.Dynamic.ExactDynamicDebtVanishingCounterexample

/-!
# The unilateral stopping obstacle is not a function of accumulated mass

This is the minimal two-player, two-row regression from the marked-absorption-
cylinder design.  It is a permanent fence, not a step toward a repair:
**the unilateral quit-at-`t` stopping obstacle does not descend to
accumulated absorption mass.**  Two rows can carry the same accumulated mass
and different obstacle values.

## Why the naive descent argument fails

The tempting argument runs: a stretch that has absorbed no mass has every
preceding row's continue mass equal to `1`, so `τ` is locally constant, so
"nothing changed" and the obstacle should be too.  This is true but
irrelevant.  `τ(t) = 1 - ∏_{u < t} c(p_u)` is the mass absorbed **strictly
before** stage `t`.  Two times with `τ(t) = τ(t')` only constrain the *rows
before* `t` and `t'` to have contributed no mass; the row the obstacle
actually reads *at* `t` (respectively at `t'`) is unconstrained by that
equality.  A zero-mass stretch does force its own rows to be trivial -- that
much is true -- but it says nothing about the row immediately following the
stretch, which is exactly where the two counterexample times differ.

## The counterexample

Player `false` (`1`) has reward `r_1({1}) = 0` and `r_1({1,2}) = 1`, so with
opponent-only survival `S_{-1}` and quit-at-`t` obstacle `Q_1`,

`Q_1(p,t) = S_{-1}(t) · p_{t,2}`

where `p_{t,2}` is player two's row-`t` quit probability.  The two-row table

`p_0 = (0,0)`, `p_1 = (0,1)`

has `τ(0) = τ(1) = 0` (row `0` absorbs nothing), yet `Q_1(p,0) = 0` while
`Q_1(p,1) = 1`.  No function of accumulated mass alone can match both values.

## Scope

The failure is not confined to zero rows or to this particular reward: the
universal descent property "the obstacle is a function of accumulated mass,
for every array" holds only in the degenerate case `r_i(K) = 0` for every
`K ∋ i`, in which the obstacle itself is identically zero.

This module does **not** refute the enriched-absorption-path route.  It
refutes only the statement of the obstacle as a function of accumulated mass.
The repair recorded in the design document is to carry the obstacle as a
closed completed hypograph of the full chronological trace `t ↦ (τ(t), Q_i(t))`,
retaining the zero-mass stages where this counterexample lives, rather than
collapsing it to a function of `τ` alone.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingObstacleMassDescentCounterexample

/-! We use `false` for player one, the owner of the tracked obstacle, and
`true` for player two. -/

/-- The reward table with `r_1({1}) = 0` and `r_1({1,2}) = 1`.  Player two's
component is never consulted below, so it is fixed at `0`. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who => if who then 0 else if true ∈ quitters.1 then 1 else 0

/-- Row `1` of the table: player one surely continues (`p_{1,1} = 0`) and
player two surely quits (`p_{1,2} = 1`). -/
def row1 : Bool → PMF Bool :=
  fun who => if who then PMF.pure true else PMF.pure false

/-- The two-row table `p_0 = (0,0)`, `p_1 = (0,1)` from the design record,
extended past index `1` by repeating row `1`.  Only rows `0` and `1` are read
below; the extension exists solely so `rows` is a total `ℕ`-indexed family. -/
def rows : ℕ → Bool → PMF Bool
  | 0 => quittingAllContinueRoot
  | _ + 1 => row1

/-- Accumulated absorption mass strictly before stage `t`,
`τ(t) = 1 - ∏_{u < t} c(p_u)`, reusing the repo's one-stage continue mass
`quittingStationaryContinueMass`. -/
def accumulatedMass (t : ℕ) : ℝ :=
  1 - ∏ u ∈ Finset.range t, quittingStationaryContinueMass (rows u)

/-- Player one's quit-at-`t` obstacle value `Q_1(p,t) = S_{-1}(t) · (one-stage
quit contribution at `t`)`, reusing the repo's opponent-only survival
`quittingOpponentSurvivalWeight` and one-stage fixed-opponents quit value
`quittingFixedOpponentsQuitValue`. -/
def obstacleValue (t : ℕ) : ℝ :=
  quittingOpponentSurvivalWeight rows false 0 t *
    quittingFixedOpponentsQuitValue reward rows false t

/-- Player two's row-`1` marginal is a sure quit. -/
@[simp] theorem row1_true : row1 true = PMF.pure true := rfl

/-- Player one's row-`1` marginal is a sure continue. -/
@[simp] theorem row1_false : row1 false = PMF.pure false := rfl

/-- Row `0` is the all-continue root. -/
@[simp] theorem rows_zero : rows 0 = quittingAllContinueRoot := rfl

/-- Row `1` is `row1`. -/
@[simp] theorem rows_one : rows 1 = row1 := rfl

/-! ## Accumulated mass: `τ(0) = τ(1) = 0` -/

/-- The all-continue root's all-continue mass is exactly one; row zero is
this root. -/
theorem stationaryContinueMass_allContinueRoot :
    quittingStationaryContinueMass (quittingAllContinueRoot : Bool → PMF Bool) =
      1 := by
  simp [quittingStationaryContinueMass, quittingAllContinueRoot,
    quittingAllContinueAction, pmfPi_apply]

/-- No mass has absorbed before stage `0`: the empty product. -/
theorem accumulatedMass_zero : accumulatedMass 0 = 0 := by
  simp [accumulatedMass]

/-- No mass has absorbed before stage `1` either: row `0` alone absorbs
nothing. -/
theorem accumulatedMass_one : accumulatedMass 1 = 0 := by
  simp [accumulatedMass, stationaryContinueMass_allContinueRoot]

/-- The two rows carry the same accumulated mass. -/
theorem accumulatedMass_zero_eq_one :
    accumulatedMass 0 = accumulatedMass 1 := by
  rw [accumulatedMass_zero, accumulatedMass_one]

/-! ## The quit-at-`t` obstacle: `Q_1(p,0) = 0 ≠ 1 = Q_1(p,1)` -/

/-- Player one's pure-Quit endpoint against opponent marginal `selectedRoot`
is exactly that marginal's own quit probability: quitting always delivers
`r_1({1}) = 0` unless the opponent also quits, delivering `r_1({1,2}) = 1`. -/
theorem quittingRootQuitPayoff_eq (tail : Payoff Bool)
    (selectedRoot : Bool → PMF Bool) :
    quittingRootQuitPayoff reward tail selectedRoot false =
      (selectedRoot true true).toReal := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward]

/-- Player one's one-stage quit contribution against fixed opponents at row
`t` is exactly that row's opponent quit probability. -/
theorem quittingFixedOpponentsQuitValue_eq (time : ℕ) :
    quittingFixedOpponentsQuitValue reward rows false time =
      (rows time true true).toReal := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward rows false
    (0 : Payoff Bool) time, quittingRootQuitPayoff_eq]

/-- Row zero's opponent surely continues: the quit-at-`0` bracket vanishes. -/
theorem quittingFixedOpponentsQuitValue_zero :
    quittingFixedOpponentsQuitValue reward rows false 0 = 0 := by
  rw [quittingFixedOpponentsQuitValue_eq]
  simp [quittingAllContinueRoot]

/-- Row one's opponent surely quits: the quit-at-`1` bracket is one. -/
theorem quittingFixedOpponentsQuitValue_one :
    quittingFixedOpponentsQuitValue reward rows false 1 = 1 := by
  rw [quittingFixedOpponentsQuitValue_eq]
  simp

/-- No stages precede `0`: opponent survival to `0` is trivially one. -/
theorem opponentSurvivalWeight_zero :
    quittingOpponentSurvivalWeight rows false 0 0 = 1 := by
  simp [quittingOpponentSurvivalWeight]

/-- Row zero's opponent surely continues: opponent survival to `1` is also
one. -/
theorem opponentSurvivalWeight_one :
    quittingOpponentSurvivalWeight rows false 0 1 = 1 := by
  unfold quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  simp [quittingStationaryContinueMass, quittingAllContinueRoot,
    quittingAllContinueAction, pmfPi_apply]

/-- Player one's quit-at-`0` obstacle value is `0`. -/
theorem obstacleValue_zero : obstacleValue 0 = 0 := by
  simp [obstacleValue, opponentSurvivalWeight_zero,
    quittingFixedOpponentsQuitValue_zero]

/-- Player one's quit-at-`1` obstacle value is `1`. -/
theorem obstacleValue_one : obstacleValue 1 = 1 := by
  simp [obstacleValue, opponentSurvivalWeight_one,
    quittingFixedOpponentsQuitValue_one]

/-- The two rows carry different obstacle values. -/
theorem obstacleValue_zero_ne_one : obstacleValue 0 ≠ obstacleValue 1 := by
  rw [obstacleValue_zero, obstacleValue_one]
  norm_num

/-! ## The headline fence -/

/-- **The unilateral stopping obstacle is not a function of accumulated
mass.**  Stages `0` and `1` carry equal accumulated mass and unequal
obstacle values, so no scalar function of accumulated mass alone can
reproduce the obstacle at every stage.  This is the permanent counterexample
to the tempting "descent lemma"; the enriched-absorption-path route must
instead carry the obstacle as a completed hypograph of the full
`t ↦ (τ(t), Q_1(p,t))` trace, retaining zero-mass stages. -/
theorem not_exists_obstacle_as_function_of_accumulatedMass :
    ¬ ∃ f : ℝ → ℝ, ∀ t, f (accumulatedMass t) = obstacleValue t := by
  rintro ⟨f, hf⟩
  have h0 := hf 0
  have h1 := hf 1
  rw [accumulatedMass_zero, obstacleValue_zero] at h0
  rw [accumulatedMass_one, obstacleValue_one] at h1
  rw [h0] at h1
  norm_num at h1

end QuittingObstacleMassDescentCounterexample

end GameTheory
