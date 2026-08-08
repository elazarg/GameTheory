/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.CycleIsolatedCoordinate

/-!
# The candidate hard weight's isolated-negative cycle

A solver reports an explicit two-player weight family, parametrized by
`0 < α < 1`, and claims that *every* complementary sequence for it has
deviation gain bounded below by `α`.  This file checks the reported cycle
and its gain -- the concrete part of that claim -- against the repository's
own quitting-game machinery.  The universally quantified floor over *every*
complementary sequence is **not** attempted here; see the closing remarks.

## The weight

Player `1` is encoded as `false`, player `2` as `true`.  `reward` is
`r({1}) = (-α, 1)`, `r({2}) = (-1, 1)`, `r({1,2}) = (-α, 0)`.  Coordinate
`2`'s own solo reward `r_2({2}) = 1 > 0` (`soloReward_true_true`) is the
fact the wider argument uses to force total absorption; nothing below needs
it, since this file only checks one already-complementary candidate cycle,
not the universal floor.

## The cycle

For every rate `0 < p < 1`, the stationary row at which player `1` quits
with probability `p` and player `2` never quits (`root`) is a length-one
absorbing exact (`ε = 0`) cyclic continuation block (`isCyclicContinuationBlock`)
-- i.e. a **complementary** cycle in the repository's sense, `p` and `1 - p`
are exact best responses at both coordinates simultaneously -- and it
isolates coordinate `1` (`isIsolated`): coordinate `2` is silent at every
phase.

Its value at coordinate `1` is exactly the solo reward `r_1({1}) = -α`
(`quittingCyclicContinuationBlock_value_eq_soloReward_of_isolated`, not
restated here), and its anchored companion mismatch there is *exactly* `α`
(`mismatch_eq_alpha`) -- confirming both reported numbers.  In particular the
boundary-option supremum really is `max {0, -α} = 0`: the isolated companion
map is `w ↦ max {r_1({1}), w}` (`quittingRootCompanionMap_of_isolated`), so
the anchored orbit from `Λ_1 = max {0, r_1({1})}` never moves, and `Λ_1 = 0`
here (`soloQuitCap`) because `r_1({1}) = -α < 0`.  The deviation supremum is
contributed entirely by the "never activate coordinate `1`" option, matching
the reported route exactly; no finite-time deviation contributes anything
beyond what the fixed point already selects.

## What this file does not cover

`mismatch_eq_alpha` is a statement about **one** cycle for this weight, the
one the solver exhibited.  It is not a statement about every complementary
sequence for this weight, and complementarity (exact best response,
packaged here as `IsQuittingCyclicContinuationBlock`) is the only class the
claimed floor `∀ complementary sequence, max_i gain_i ≥ α` quantifies over;
a strategy profile with small deviation gain that is *not* complementary is
outside the floor's scope and outside this file's scope too.  Two further
steps are needed to reach the floor, neither of which is attempted here:

1. **Total absorption.**  That `r_2({2}) = 1 > 0` forces every complementary
   sequence (not just this cyclic one) to absorb with probability one, hence
   forces coordinate `2` silent at every time.  No lemma in the repository
   derives absorption *from* optimality plus a positive solo reward; the
   existing absorbing-cycle machinery always takes absorption at some stage
   as a hypothesis, not a conclusion.
2. **The floor itself**, universally quantified over arbitrary (not
   necessarily periodic) complementary sequences.  The repository's
   Bellman-exactness predicate for an infinite sequence,
   `IsQuittingLivePrescribedValue` (`QuittingBellmanTelescope.lean`), is
   stated for one coordinate against one root sequence, not jointly for
   every player at once; no repository definition currently packages "every
   coordinate is exactly best-responding at every time, no periodicity
   assumed" as a single `Prop` the way `IsQuittingCyclicContinuationBlock`
   does for finite periodic blocks.

Reaching the floor therefore needs both a new joint infinite-horizon
complementarity predicate and a new absorption theorem; neither is a
routine consequence of what already exists.
-/

noncomputable section

namespace GameTheory

namespace QuittingCandidateHardWeightCycle

/-- The candidate hard weight: `r({1}) = (-α, 1)`, `r({2}) = (-1, 1)`,
`r({1,2}) = (-α, 0)`, with player `1` encoded as `false` and player `2` as
`true`. -/
def reward (α : ℝ) : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S who =>
    if S.1 = {false} then (if who then (1 : ℝ) else -α)
    else if S.1 = {true} then (if who then (1 : ℝ) else -1)
    else (if who then (0 : ℝ) else -α)

/-- Player `1`'s payoff when `1` quits alone is `-α`. -/
@[simp] theorem soloReward_false_false (α : ℝ) :
    reward α (quittingSingletonTerminal false) false = -α := by
  simp [reward, quittingSingletonTerminal]

/-- Player `2`'s payoff when `1` quits alone is `1`. -/
@[simp] theorem soloReward_false_true (α : ℝ) :
    reward α (quittingSingletonTerminal false) true = 1 := by
  simp [reward, quittingSingletonTerminal]

/-- Player `1`'s payoff when `2` quits alone is `-1`. -/
@[simp] theorem soloReward_true_false (α : ℝ) :
    reward α (quittingSingletonTerminal true) false = -1 := by
  have hne : ({true} : Finset Bool) ≠ {false} := by decide
  simp [reward, quittingSingletonTerminal, hne]

/-- Player `2`'s payoff when `2` quits alone is `1`, the load-bearing entry
the wider (unformalized) argument uses to force total absorption. -/
@[simp] theorem soloReward_true_true (α : ℝ) :
    reward α (quittingSingletonTerminal true) true = 1 := by
  have hne : ({true} : Finset Bool) ≠ {false} := by decide
  simp [reward, quittingSingletonTerminal, hne]

/-- Player `2`'s payoff at the collision coalition `{1,2}` is `0`. -/
@[simp] theorem collisionReward_false_true (α : ℝ) :
    quittingSingletonCollisionReward (reward α) false true = 0 := by
  have h1 : ({false, true} : Finset Bool) ≠ {false} := by decide
  have h2 : ({false, true} : Finset Bool) ≠ {true} := by decide
  simp [quittingSingletonCollisionReward, reward, h1, h2]

/-- The owner `false` (player `1`) quits at rate `p`; player `2` continues
surely, which is exactly isolation of player `1`. -/
def root (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Bool → PMF Bool :=
  quittingSoloStationaryRoot false (quittingHazardCoin p hp0 hp1)

/-- The cyclic value: the realized terminal payoff when player `1` alone
quits. -/
def value (α : ℝ) : Payoff Bool := quittingSoloReward (reward α) false

/-- Coordinate `1`'s cyclic value is `r_1({1}) = -α`. -/
@[simp] theorem value_false (α : ℝ) : value α false = -α := soloReward_false_false α

/-- Coordinate `2`'s cyclic value is `r_2({1}) = 1`. -/
@[simp] theorem value_true (α : ℝ) : value α true = 1 := soloReward_false_true α

/-- The row reproduces its own value, at every rate `p`. -/
theorem value_eq_successor (α p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    value α = quittingRootSuccessorPayoff (reward α) (value α) (root p hp0 hp1) :=
  (quittingRootSuccessorPayoff_soloStationaryRoot_self (reward α) false
    (quittingHazardCoin p hp0 hp1)).symm

/-- **The row is exactly (`ε = 0`) endpoint Nash**, at every rate `p`: player
`1` is exactly indifferent (the generic solo-quitter fact), and player `2`
has no incentive to join the exit since `(1 - p) * r_2({2}) + p * r_2({1,2})
= 1 - p ≤ 1 = r_2({1})`. -/
theorem isEndpointNash (α p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsεQuittingRootEndpointNash (reward α) (value α) 0 (root p hp0 hp1) := by
  refine isεQuittingRootEndpointNash_soloStationaryRoot (reward α) false
    (quittingHazardCoin p hp0 hp1) ?_
  intro other hother
  cases other with
  | false => exact absurd rfl hother
  | true =>
      change (quittingHazardCoin p hp0 hp1 false).toReal *
            reward α (quittingSingletonTerminal true) true +
          (quittingHazardCoin p hp0 hp1 true).toReal *
            quittingSingletonCollisionReward (reward α) false true ≤
          reward α (quittingSingletonTerminal false) true
      rw [soloReward_true_true, collisionReward_false_true, soloReward_false_true,
        quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]
      linarith

/-- The row absorbs at rate `p`. -/
theorem absorptionMass_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 < quittingRootAbsorptionMass (root p hp0.le hp1) := by
  rw [root, quittingRootAbsorptionMass_soloStationaryRoot,
    quittingHazardCoin_true_toReal]
  exact hp0

/-- The cyclic value is within the canonical reward bound. -/
theorem abs_value_le (α : ℝ) : ∀ who, |value α who| ≤ quittingRewardBound (reward α) :=
  fun who ↦ abs_reward_le_quittingRewardBound (reward α) (quittingSingletonTerminal false) who

/-- **The candidate cycle is complementary.**  For every rate `0 < p < 1` the
row is an absorbing exact cyclic continuation block of length one -- the
repository's notion of a complementary absorbing cycle. -/
theorem isCyclicContinuationBlock (α p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuittingCyclicContinuationBlock (reward α) (value α) 1
      (quittingRowBlock (value α) (root p hp0.le hp1.le)) :=
  quittingRowBlock_isQuittingCyclicContinuationBlock (reward α) (value α)
    (root p hp0.le hp1.le) (abs_value_le α) (value_eq_successor α p hp0.le hp1.le)
    (isEndpointNash α p hp0.le hp1.le) (absorptionMass_pos p hp0 hp1.le)

/-- **The cycle is isolated-negative at coordinate `1`.**  Player `2` is
silent at the row's only phase. -/
theorem isIsolated (α p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots 1
        (quittingRowBlock (value α) (root p hp0.le hp1.le))) false 1 := by
  intro time htime
  have htime0 : time = 0 := by omega
  subst htime0
  rw [quittingFiniteNashBellmanPathRoots_of_lt 1 _ 0 (by omega),
    quittingRootOfSimplex_quittingRowBlock]
  exact (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot (root p hp0.le hp1.le)
    false).mpr ⟨quittingHazardCoin p hp0.le hp1.le, rfl⟩

/-- The solo-quit anchor at coordinate `1` is `Λ_1 = max {0, -α} = 0`. -/
@[simp] theorem soloQuitCap (α : ℝ) (hα0 : 0 < α) :
    quittingPositiveSingletonDebtCap (reward α) false = 0 := by
  rw [quittingSoloQuitAnchor_eq, soloReward_false_false]
  exact max_eq_left (by linarith)

/-- The anchored companion orbit at coordinate `1` is constant, hence
converges to its own starting point `Λ_1`. -/
theorem tendsto_iterate_soloQuitAnchor (α p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite (reward α)
          (quittingFiniteNashBellmanPathRoots 1
            (quittingRowBlock (value α) (root p hp0.le hp1.le))) false 0 1)^[N]
          (quittingPositiveSingletonDebtCap (reward α) false))
      Filter.atTop (nhds (quittingPositiveSingletonDebtCap (reward α) false)) :=
  tendsto_iterate_soloQuitAnchor_of_isolated (reward α) _ false 1 (isIsolated α p hp0 hp1)

/-- **The cycle's mismatch is exactly `α`, confirming the reported value.**
This is `Λ_1 - r_1({1}) = 0 - (-α) = α`, so the deviation supremum against
this cycle is exactly the "never activate coordinate `1`" boundary option
`max {0, -α} = 0`, and no finite-time deviation contributes more. -/
theorem mismatch_eq_alpha (α p : ℝ) (hα0 : 0 < α) (hp0 : 0 < p) (hp1 : p < 1) :
    quittingPositiveSingletonDebtCap (reward α) false - value α false = α := by
  rw [quittingCyclicContinuationBlock_mismatch_eq_of_isolated (reward α) (value α) 1
    (quittingRowBlock (value α) (root p hp0.le hp1.le))
    (isCyclicContinuationBlock α p hp0 hp1) (isIsolated α p hp0 hp1)
    (quittingPositiveSingletonDebtCap (reward α) false)
    (tendsto_iterate_soloQuitAnchor α p hp0 hp1),
    soloReward_false_false, neg_neg]
  exact max_eq_right hα0.le

end QuittingCandidateHardWeightCycle

end GameTheory
