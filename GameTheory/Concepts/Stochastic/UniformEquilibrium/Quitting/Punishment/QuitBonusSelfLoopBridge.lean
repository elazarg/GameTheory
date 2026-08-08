/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.WeightedRowMotionSeparation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.BoundedSurgeryDescentCounterexample
import Math.ChargedPathBudgetCounterexamples

/-!
# The repo's canonical one-stage operator reproduces the quit-bonus self-loop

`Math.ChargedPathBudget.QuitBonus` proves, over the explicit two-coordinate
table `wFirst a = (a, 0)`, `wSecond = (1, -1)`, `wBoth = (0, 1)` indexed by
`Fin 2` and a hand-rolled `oneStageUpdate`, that the row `x = (1/2, 0)` fixes
the value vector `v = (a, 0)` exactly, giving a positive-charge self-loop and
hence no bounded potential.

The same reward table already lives in the repo as
`QuittingBoundedSurgeryDescentCounterexample.reward`, indexed by `Bool`
(`false` the first player, `true` the second), and the repo's canonical
one-stage operator on such a table is `oneStageNext`
(`WeightedRowMotionSeparation.lean`), built from `sigmaValue`, `excludedValue`,
`gammaValue` (`QuittingCyclicWeightRowDichotomy.lean`) through the coalition
reward `weightOfReward` (`QuittingHazardRowBridge.lean`). This file shows the
canonical operator reproduces the same fixed point on the repo's own table,
and draws the same no-bounded-potential conclusion for the resulting charged
relation.

## Contents

* `row`, `val`: the calibrating row and value vector, indexed by `Bool` to
  match `QuittingBoundedSurgeryDescentCounterexample.reward`.
* `oneStageNext_eq`: a generic reduction, for any `Bool`-indexed coalition
  weight `r` and any row/continuation pair, of `oneStageNext r x rest i` to
  an explicit four-term sum over the three nonempty coalitions of `Bool` and
  the continuation — the `Bool`-indexed counterpart of
  `QuitBonus.oneStageUpdate_eq_coalitionSum`, obtained by expanding the
  powerset sums inside `sigmaValue` and `excludedValue` at a singleton
  index-complement.
* `oneStageNext_reward_fixed`: **the wiring theorem.** The canonical operator,
  applied to `weightOfReward (reward a)` at the row `row`, fixes `val a`
  exactly, matching `QuitBonus.oneStageUpdate_fixed` pointwise.
* `val_eq_quitBonus_val`, `row_eq_quitBonus_row`: the calibrating data here is
  literally `QuitBonus`'s own data, reindexed by the `Bool ≃ Fin 2`
  relabelling `finOfBool` that sends the first player to coordinate `0` and
  the second to coordinate `1`.
* `relation`, `no_boundedPotential`: the charged relation of the repo-operator
  self-loop on this table has no bounded potential, by the same
  positive-charge-self-loop argument `QuitBonus.no_boundedPotential` uses,
  applied here to the repo's own operator and reward table.
-/

noncomputable section

namespace GameTheory

namespace QuittingQuitBonusSelfLoopBridge

open QuittingBoundedSurgeryDescentCounterexample (reward)

/-! ## The calibrating row and value vector, indexed by `Bool` -/

/-- The calibrating row on `reward`: the first player (`false`) quits with
probability one half, the second player (`true`) never quits. -/
def row : Bool → ℝ := fun i => if i then 0 else 1 / 2

/-- The calibrating value vector: `false ↦ a`, `true ↦ 0`. -/
def val (a : ℝ) : Bool → ℝ := fun i => if i then 0 else a

/-! ## The generic coalition-sum reduction of `oneStageNext` over `Bool` -/

private theorem univ_erase_eq (i : Bool) : (Finset.univ.erase i : Finset Bool) = {!i} := by
  cases i <;> decide

private theorem sum_powerset_singleton {α : Type*} (a : α) (f : Finset α → ℝ) :
    ∑ J ∈ ({a} : Finset α).powerset, f J = f ∅ + f {a} := by
  classical
  have h : ({a} : Finset α) = insert a ∅ := by simp
  rw [h, Finset.sum_powerset_insert (Finset.notMem_empty a)]
  simp

private theorem sum_powerset_erase_empty_singleton {α : Type*} [DecidableEq α] (a : α)
    (f : Finset α → ℝ) :
    ∑ J ∈ ({a} : Finset α).powerset.erase ∅, f J = f {a} := by
  have hmem : (∅ : Finset α) ∈ ({a} : Finset α).powerset := Finset.empty_mem_powerset _
  have hsplit := Finset.add_sum_erase _ f hmem
  rw [sum_powerset_singleton a f] at hsplit
  linarith [hsplit]

private theorem sigmaValue_eq (r : Finset Bool → Bool → ℝ) (x : Bool → ℝ) (i : Bool) :
    sigmaValue r x i = (1 - x (!i)) * r {i} i + x (!i) * r {i, !i} i := by
  unfold sigmaValue
  rw [univ_erase_eq, sum_powerset_singleton]
  simp

private theorem excludedValue_eq (r : Finset Bool → Bool → ℝ) (x : Bool → ℝ) (i : Bool) :
    excludedValue r x i = x (!i) * r {!i} i := by
  unfold excludedValue
  rw [univ_erase_eq, sum_powerset_erase_empty_singleton]
  simp

private theorem continueMassExcl_eq (x : Bool → ℝ) (i : Bool) :
    continueMassExcl x i = 1 - x (!i) := by
  unfold continueMassExcl
  rw [univ_erase_eq]
  simp

private theorem gammaValue_eq (r : Finset Bool → Bool → ℝ) (x : Bool → ℝ) (i : Bool) (next : ℝ) :
    gammaValue r x i next = x (!i) * r {!i} i + (1 - x (!i)) * next := by
  unfold gammaValue
  rw [excludedValue_eq, continueMassExcl_eq]

/-- **The `Bool`-indexed coalition-sum reduction of `oneStageNext`.** The exact
counterpart of `QuitBonus.oneStageUpdate_eq_coalitionSum`, obtained here by
expanding the powerset sums defining `sigmaValue` and `excludedValue`, since
`Bool` has exactly two elements and every index-complement is a singleton. -/
theorem oneStageNext_eq (r : Finset Bool → Bool → ℝ) (x rest : Bool → ℝ) (i : Bool) :
    oneStageNext r x rest i =
      x i * (1 - x (!i)) * r {i} i + x i * x (!i) * r {i, !i} i
        + (1 - x i) * x (!i) * r {!i} i + (1 - x i) * (1 - x (!i)) * rest i := by
  unfold oneStageNext oneStageMixPayoff
  rw [sigmaValue_eq, gammaValue_eq]
  ring

/-! ## The wiring theorem -/

/-- **The repo-operator self-loop.** At the calibrating row, the repo's
canonical one-stage operator `oneStageNext`, applied to the coalition weight
`weightOfReward (reward a)`, fixes the calibrating value vector exactly, at
every coordinate. -/
theorem oneStageNext_reward_fixed (a : ℝ) (i : Bool) :
    oneStageNext (weightOfReward (reward a)) row (val a) i = val a i := by
  rw [oneStageNext_eq]
  cases i
  · simp [row, val, weightOfReward, reward]
    ring
  · simp [row, val, weightOfReward, reward]

/-- The self-loop as a single function equality. -/
theorem oneStageNext_reward_isSelfLoop (a : ℝ) :
    oneStageNext (weightOfReward (reward a)) row (val a) = val a := by
  funext i
  exact oneStageNext_reward_fixed a i

/-! ## Identification with `QuitBonus`'s own calibrating data -/

/-- The relabelling sending the first player (`false`) to coordinate `0` and
the second player (`true`) to coordinate `1`, matching the indexing of
`Math.ChargedPathBudget.QuitBonus`. -/
def finOfBool : Bool → Fin 2 := fun b => if b then 1 else 0

/-- The calibrating value vector here is exactly `QuitBonus.val`, reindexed. -/
theorem val_eq_quitBonus_val (a : ℝ) (i : Bool) :
    val a i = Math.ChargedPathBudget.QuitBonus.val a (finOfBool i) := by
  cases i <;> simp [val, finOfBool, Math.ChargedPathBudget.QuitBonus.val]

/-- The calibrating row here is exactly `QuitBonus.row`, reindexed. -/
theorem row_eq_quitBonus_row (i : Bool) :
    row i = Math.ChargedPathBudget.QuitBonus.row (finOfBool i) := by
  cases i <;> simp [row, finOfBool, Math.ChargedPathBudget.QuitBonus.row]

/-! ## No bounded potential for the repo-operator relation -/

/-- Quitting charge of the calibrating row: the probability that somebody
quits, matching `QuitBonus.quitCharge` at the same numeric value. -/
def quitCharge : ℝ := 1 - Math.PMFProduct.continueMass row

@[simp] theorem continueMass_row : Math.PMFProduct.continueMass row = 1 / 2 := by
  simp [Math.PMFProduct.continueMass, row]
  norm_num

@[simp] theorem quitCharge_eq : quitCharge = 1 / 2 := by
  rw [quitCharge, continueMass_row]; norm_num

theorem quitCharge_pos : 0 < quitCharge := by rw [quitCharge_eq]; norm_num

/-- The charged relation attached to the repo-operator calibration on
`reward`: a self-loop at the fixed value vector `val a`, carrying the row's
quitting charge. By `val_eq_quitBonus_val`, `row_eq_quitBonus_row` and
`quitCharge_eq` (which matches `QuitBonus.quitCharge_row`), this is the same
edge as `QuitBonus.relation a`, reindexed by `finOfBool`. -/
def relation (a : ℝ) : Math.ChargedPathBudget.ChargedRelation (Bool → ℝ) Unit where
  src _ := val a
  tgt _ := val a
  charge _ := quitCharge
  charge_nonneg _ := quitCharge_pos.le

@[simp] theorem relation_charge (a : ℝ) (u : Unit) : (relation a).charge u = 1 / 2 := by
  have h : (relation a).charge u = quitCharge := rfl
  rw [h, quitCharge_eq]

/-- The repo-operator calibration is an exact positive-charge self-loop, so
its budget is infinite — the same conclusion as `QuitBonus.not_hasFiniteBudget`,
now for the repo's own reward table and canonical one-stage operator. -/
theorem not_hasFiniteBudget (a : ℝ) : ¬ (relation a).HasFiniteBudget := by
  refine (relation a).not_hasFiniteBudget_of_positive_selfLoop () rfl ?_
  rw [relation_charge]
  norm_num

/-- **No bounded potential for the repo-operator relation on this table.**
The repo's canonical `oneStageNext` operator, applied to
`weightOfReward (reward a)`, realizes exactly the same positive-charge
self-loop as `QuitBonus.relation a` (up to the `Bool ≃ Fin 2` relabelling
`finOfBool`), so no bounded potential of any kind exists for it either. -/
theorem no_boundedPotential (a : ℝ) :
    ¬ ∃ Φ : (Bool → ℝ) → ℝ, (relation a).IsBoundedPotential Φ := by
  rw [← (relation a).hasFiniteBudget_iff_exists_boundedPotential]
  exact not_hasFiniteBudget a

end QuittingQuitBonusSelfLoopBridge

end GameTheory
