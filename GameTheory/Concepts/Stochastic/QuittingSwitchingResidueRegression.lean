/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# A three-player switching-residue regression table

This file machine-checks a concrete rational three-player reward table and
two general scalar lemmas, entirely by arithmetic: no stochastic-game
dynamics, roots, or profiles are used anywhere below.

Players are encoded as `Player := Fin 3`, with the coordinates `0, 1, 2`
denoting players `1, 2, 3` of the source table.  Coalitions are `Finset
Player`.  `reward S i` is player `i`'s payoff once exactly the members of `S`
have quit; the convention `reward ∅ i = 0` is built into the definition.  The
seven nonempty-coalition rows are

* `{1} ↦ (1, 2/5, 2/5)`, `{2} ↦ (0, 0, 1)`, `{3} ↦ (0, 0, 1)`,
* `{1,2} ↦ (1, 1, 0)`, `{1,3} ↦ (1, 0, 0)`, `{2,3} ↦ (2, 1, 0)`,
* `{1,2,3} ↦ (0, 0, 1)`.

## What is proved

* `q_one_eq_one`, `q_one_pos`: player one's solo reward is `1 > 0`
  (not a "zero-solo" table).
* `d12_eq`, `d13_eq`, `max_d12_d13_ge`, `d12_le_zero`, `d13_le_zero`:
  player one's owner-switching residual against each opponent, at rate
  `h`, is `d12(h) = h - 2/5` and `d13(h) = 3/5 - h`.  Their sum is the
  constant `1/5`, so their max is always at least `1/10`; neither residual
  is `≤ 0` on the whole interval `(0,1]` (each vanishes at one interior
  point), so no single opponent blocks player one at every switching rate.
* `d21_eq_one`, `d31_eq_one`: players two and three are blocked by player
  one at *every* switching rate, the residual being the constant `1`.
* `SureExitFails` and `sureExitFails_1` .. `sureExitFails_123`: every one of
  the seven nonempty coalitions fails the sure-exit inequality system --
  some member has a strict incentive to leave, or some outsider has a
  strict incentive to join.
* `OwnerOptimal`, `SpectatorNoJoin`, `ownerOptimalForcesDeltaOne`,
  `ownerOptimalForcesDeltaZero`, `diff12` .. `diff32`, and
  `collisionRepairFails12` .. `collisionRepairFails32`: for every ordered
  (owner, blocker) pair, the fixed-collision-rate repair mechanism --
  owner endpoint optimality plus spectator no-join, at a shared rate
  `δ ∈ [0,1]` -- is infeasible.  The owner endpoint difference forces `δ`
  to the boundary (`1` when the difference is positive, `0` when negative);
  at that forced boundary the repair fails, either because the resulting
  sure pair already fails its own sure-exit system (the positive-difference
  pairs, reusing `SureExitFails`) or because the spectator's own no-join
  inequality fails outright (the negative-difference pairs).
* `collisionRate_ge_of_balance_nonneg`, `not_balance_nonneg_of_gain_nonpos`,
  `fixedGap_ge_half`: two general scalar lemmas, independent of the table
  above.  The first pair bounds the collision rate forced by a nonnegative
  balance between a fixed loss and a fixed gain, and rules out a nonnegative
  balance altogether once the gain is nonpositive (away from the degenerate
  endpoint `δ = 1`).  The second shows a sufficiently small collision rate
  cannot erode a fixed positive gap below half its value.

Every result here is original to this development; none of it is quoted or
adapted from a specific published source.
-/

noncomputable section

namespace GameTheory

namespace QuittingSwitchingResidueRegression

/-- Players, encoded as `Fin 3` with `0, 1, 2` denoting players `1, 2, 3` of
the source table. -/
abbrev Player := Fin 3

/-- The reward table, extended by the convention `reward ∅ = 0`.  The seven
nonempty-coalition rows, in player order `1, 2, 3` (i.e. Lean indices
`0, 1, 2`), are `{1} ↦ (1,2/5,2/5)`, `{2} ↦ (0,0,1)`, `{3} ↦ (0,0,1)`,
`{1,2} ↦ (1,1,0)`, `{1,3} ↦ (1,0,0)`, `{2,3} ↦ (2,1,0)`,
`{1,2,3} ↦ (0,0,1)`. -/
def reward (S : Finset Player) (who : Player) : ℝ :=
  if (0 : Player) ∈ S then
    if (1 : Player) ∈ S then
      if (2 : Player) ∈ S then ![(0 : ℝ), 0, 1] who
      else ![(1 : ℝ), 1, 0] who
    else
      if (2 : Player) ∈ S then ![(1 : ℝ), 0, 0] who
      else ![(1 : ℝ), 2 / 5, 2 / 5] who
  else
    if (1 : Player) ∈ S then
      if (2 : Player) ∈ S then ![(2 : ℝ), 1, 0] who
      else ![(0 : ℝ), 0, 1] who
    else
      if (2 : Player) ∈ S then ![(0 : ℝ), 0, 1] who
      else 0

@[simp] theorem reward_singleton1 : reward {0} = ![(1 : ℝ), 2 / 5, 2 / 5] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_singleton2 : reward {1} = ![(0 : ℝ), 0, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_singleton3 : reward {2} = ![(0 : ℝ), 0, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair12 : reward {0, 1} = ![(1 : ℝ), 1, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair13 : reward {0, 2} = ![(1 : ℝ), 0, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair23 : reward {1, 2} = ![(2 : ℝ), 1, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_grand : reward {0, 1, 2} = ![(0 : ℝ), 0, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_empty : reward (∅ : Finset Player) = ![(0 : ℝ), 0, 0] := by
  funext who; fin_cases who <;> simp [reward]

/-! ## (a) Not zero-solo -/

/-- `q i` is player `i`'s solo reward `reward {i} i`. -/
def q (i : Player) : ℝ := reward {i} i

theorem q_one_eq_one : q 0 = 1 := by simp [q]

/-- (a) Not zero-solo: player one's solo reward is `1`, strictly positive. -/
theorem q_one_pos : 0 < q 0 := by rw [q_one_eq_one]; norm_num

/-! ## (b) Owner one is switching-blocked with no universal blocker -/

/-- `d i j h` is owner `i`'s switching residual against opponent `j` at
switching rate `h`: `(1 - h) * q j + h * reward {i, j} j - reward {i} j`. -/
def d (i j : Player) (h : ℝ) : ℝ :=
  (1 - h) * q j + h * reward ({i, j} : Finset Player) j - reward {i} j

theorem d12_eq (h : ℝ) : d 0 1 h = h - 2 / 5 := by
  simp [d, q, reward]

theorem d13_eq (h : ℝ) : d 0 2 h = 3 / 5 - h := by
  simp [d, q, reward]; ring

/-- The two residuals sum to the constant `1/5`, so their maximum is always
at least `1/10`; this holds for every `h`, in particular for every
`h ∈ (0, 1]`. -/
theorem max_d12_d13_ge (h : ℝ) : (1 : ℝ) / 10 ≤ max (d 0 1 h) (d 0 2 h) := by
  rw [d12_eq, d13_eq]
  rcases le_total (h - 2 / 5) (3 / 5 - h) with hc | hc
  · rw [max_eq_right hc]; linarith
  · rw [max_eq_left hc]; linarith

/-- Player two alone does not block owner one at every rate: the residual
vanishes at `h = 2/5`. -/
theorem d12_le_zero : d 0 1 (2 / 5) ≤ 0 := by rw [d12_eq]; norm_num

/-- Player three alone does not block owner one at every rate: the residual
vanishes at `h = 3/5`. -/
theorem d13_le_zero : d 0 2 (3 / 5) ≤ 0 := by rw [d13_eq]; norm_num

/-! ## (c) Owners two and three are universally blocked by player one -/

theorem d21_eq_one (h : ℝ) : d 1 0 h = 1 := by
  simp [d, q, reward]

theorem d31_eq_one (h : ℝ) : d 2 0 h = 1 := by
  simp [d, q, reward]

/-! ## (d) Every sure set fails the sure-exit inequality system -/

/-- The sure-exit inequality system for a coalition `S`: either some member
has a strict incentive to leave (`reward (∅) = 0` in the singleton case, via
the built-in convention on `reward`), or some outsider has a strict
incentive to join. -/
def SureExitFails (S : Finset Player) : Prop :=
  (∃ i ∈ S, reward S i < reward (S.erase i) i) ∨
    (∃ j ∉ S, reward S j < reward (insert j S) j)

/-- `{1}`: player two joins, `2/5 < 1`. -/
theorem sureExitFails_1 : SureExitFails ({0} : Finset Player) := by
  refine Or.inr ⟨1, by decide, ?_⟩
  simp [reward]; norm_num

/-- `{2}`: player one joins, `0 < 1`. -/
theorem sureExitFails_2 : SureExitFails ({1} : Finset Player) := by
  refine Or.inr ⟨0, by decide, ?_⟩
  simp [reward]

/-- `{3}`: player one joins, `0 < 1`. -/
theorem sureExitFails_3 : SureExitFails ({2} : Finset Player) := by
  refine Or.inr ⟨0, by decide, ?_⟩
  simp [reward]

/-- `{1,2}`: player three joins, `0 < 1`. -/
theorem sureExitFails_12 : SureExitFails ({0, 1} : Finset Player) := by
  refine Or.inr ⟨2, by decide, ?_⟩
  simp [reward]

/-- `{1,3}`: player three leaves, `0 < 2/5`. -/
theorem sureExitFails_13 : SureExitFails ({0, 2} : Finset Player) := by
  refine Or.inl ⟨2, by decide, ?_⟩
  simp [reward]

/-- `{2,3}`: player three leaves, `0 < 1`. -/
theorem sureExitFails_23 : SureExitFails ({1, 2} : Finset Player) := by
  refine Or.inl ⟨2, by decide, ?_⟩
  simp [reward]

/-- `{1,2,3}`: player one leaves, `0 < 2`. -/
theorem sureExitFails_123 : SureExitFails ({0, 1, 2} : Finset Player) := by
  refine Or.inl ⟨0, by decide, ?_⟩
  simp [reward]

/-! ## (e) Every fixed sure-blocker collision repair fails -/

/-- The owner endpoint difference against blocker `j`:
`reward {i,j} i - reward {j} i`. -/
def ownerEndpointDiff (i j : Player) : ℝ :=
  reward ({i, j} : Finset Player) i - reward {j} i

theorem diff12 : ownerEndpointDiff 0 1 = 1 := by simp [ownerEndpointDiff, reward]
theorem diff13 : ownerEndpointDiff 0 2 = 1 := by simp [ownerEndpointDiff, reward]
theorem diff21 : ownerEndpointDiff 1 0 = 3 / 5 := by
  simp [ownerEndpointDiff, reward]; norm_num
theorem diff23 : ownerEndpointDiff 1 2 = 1 := by simp [ownerEndpointDiff, reward]
theorem diff31 : ownerEndpointDiff 2 0 = -(2 / 5) := by simp [ownerEndpointDiff, reward]
theorem diff32 : ownerEndpointDiff 2 1 = -1 := by simp [ownerEndpointDiff, reward]

/-- Owner `i`'s endpoint optimality at collision rate `δ` against blocker
`j`: the `δ`-mixture of the two endpoint rewards equals their max. -/
def OwnerOptimal (i j : Player) (δ : ℝ) : Prop :=
  (1 - δ) * reward {j} i + δ * reward ({i, j} : Finset Player) i =
    max (reward {j} i) (reward ({i, j} : Finset Player) i)

/-- Spectator `k`'s no-join condition at collision rate `δ`, for owner `i`
and blocker `j`: joining the coalition is not strictly better than staying
out, at the same mixture rate `δ`. -/
def SpectatorNoJoin (i j k : Player) (δ : ℝ) : Prop :=
  (1 - δ) * reward ({j, k} : Finset Player) k + δ * reward ({i, j, k} : Finset Player) k ≤
    (1 - δ) * reward {j} k + δ * reward ({i, j} : Finset Player) k

/-- A strictly positive owner endpoint gap forces the collision rate to `1`:
the mixture can only reach the (strictly larger) `δ = 1` endpoint value. -/
theorem ownerOptimalForcesDeltaOne {a b δ : ℝ} (hpos : 0 < b - a)
    (hopt : (1 - δ) * a + δ * b = max a b) : δ = 1 := by
  rw [max_eq_right (by linarith : a ≤ b)] at hopt
  have hz : (δ - 1) * (b - a) = 0 := by linear_combination hopt
  rcases mul_eq_zero.mp hz with h | h
  · linarith
  · linarith

/-- A strictly negative owner endpoint gap forces the collision rate to `0`:
the mixture can only reach the (strictly larger) `δ = 0` endpoint value. -/
theorem ownerOptimalForcesDeltaZero {a b δ : ℝ} (hneg : b - a < 0)
    (hopt : (1 - δ) * a + δ * b = max a b) : δ = 0 := by
  rw [max_eq_left (by linarith : b ≤ a)] at hopt
  have hz : δ * (b - a) = 0 := by linear_combination hopt
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · linarith

/-- `(owner 1, blocker 2)`: forced to `δ = 1`, where the resulting sure pair
`{1,2}` already fails its own sure-exit system. -/
theorem collisionRepairFails12 (δ : ℝ) (hopt : OwnerOptimal 0 1 δ) :
    δ = 1 ∧ SureExitFails ({0, 1} : Finset Player) := by
  have hpos : (0 : ℝ) < reward ({0, 1} : Finset Player) 0 - reward ({1} : Finset Player) 0 := by
    simp [reward]
  exact ⟨ownerOptimalForcesDeltaOne hpos hopt, sureExitFails_12⟩

/-- `(owner 1, blocker 3)`: forced to `δ = 1`, where the resulting sure pair
`{1,3}` already fails its own sure-exit system. -/
theorem collisionRepairFails13 (δ : ℝ) (hopt : OwnerOptimal 0 2 δ) :
    δ = 1 ∧ SureExitFails ({0, 2} : Finset Player) := by
  have hpos : (0 : ℝ) < reward ({0, 2} : Finset Player) 0 - reward ({2} : Finset Player) 0 := by
    simp [reward]
  exact ⟨ownerOptimalForcesDeltaOne hpos hopt, sureExitFails_13⟩

/-- `(owner 2, blocker 1)`: forced to `δ = 1`, where the resulting sure pair
`{1,2}` already fails its own sure-exit system. -/
theorem collisionRepairFails21 (δ : ℝ) (hopt : OwnerOptimal 1 0 δ) :
    δ = 1 ∧ SureExitFails ({0, 1} : Finset Player) := by
  have hpos : (0 : ℝ) < reward ({1, 0} : Finset Player) 1 - reward ({0} : Finset Player) 1 := by
    simp [reward]; norm_num
  exact ⟨ownerOptimalForcesDeltaOne hpos hopt, sureExitFails_12⟩

/-- `(owner 2, blocker 3)`: forced to `δ = 1`, where the resulting sure pair
`{2,3}` already fails its own sure-exit system. -/
theorem collisionRepairFails23 (δ : ℝ) (hopt : OwnerOptimal 1 2 δ) :
    δ = 1 ∧ SureExitFails ({1, 2} : Finset Player) := by
  have hpos : (0 : ℝ) < reward ({1, 2} : Finset Player) 1 - reward ({2} : Finset Player) 1 := by
    simp [reward]
  exact ⟨ownerOptimalForcesDeltaOne hpos hopt, sureExitFails_23⟩

/-- `(owner 3, blocker 1)`: forced to `δ = 0`, where spectator two's own
no-join inequality fails outright: `reward {1,2} 2 = 1 > 2/5 = reward {1} 2`. -/
theorem collisionRepairFails31 (δ : ℝ) :
    ¬ (OwnerOptimal 2 0 δ ∧ SpectatorNoJoin 2 0 1 δ) := by
  rintro ⟨hopt, hno⟩
  have hneg : reward ({2, 0} : Finset Player) 2 - reward ({0} : Finset Player) 2 < 0 := by
    simp [reward]
  have hδ : δ = 0 := ownerOptimalForcesDeltaZero hneg hopt
  subst hδ
  simp [SpectatorNoJoin, reward] at hno
  norm_num at hno

/-- `(owner 3, blocker 2)`: forced to `δ = 0`, where spectator one's own
no-join inequality fails outright: `reward {1,2} 1 = 1 > 0 = reward {2} 1`. -/
theorem collisionRepairFails32 (δ : ℝ) :
    ¬ (OwnerOptimal 2 1 δ ∧ SpectatorNoJoin 2 1 0 δ) := by
  rintro ⟨hopt, hno⟩
  have hneg : reward ({2, 1} : Finset Player) 2 - reward ({1} : Finset Player) 2 < 0 := by
    simp [reward]
  have hδ : δ = 0 := ownerOptimalForcesDeltaZero hneg hopt
  subst hδ
  simp [SpectatorNoJoin, reward] at hno
  norm_num at hno

/-! ## Object 2: two general scalar lemmas (not table-specific) -/

/-- (f) Collision-rate forcing: a nonnegative balance between a fixed loss
`γ > 0` and a fixed gain `p > 0` forces the collision rate at least the
loss-share `γ / (γ + p)`. -/
theorem collisionRate_ge_of_balance_nonneg {γ p δ : ℝ} (hγ : 0 < γ) (hp : 0 < p)
    (hbalance : 0 ≤ (1 - δ) * (-γ) + δ * p) : γ / (γ + p) ≤ δ := by
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < γ + p)]
  nlinarith

/-- (f) The degenerate companion: once the gain is nonpositive, the balance
cannot be nonnegative at any collision rate strictly below one (`δ = 1`
with `p = 0` is the excluded boundary case, where the balance is exactly
zero). -/
theorem not_balance_nonneg_of_gain_nonpos {γ p δ : ℝ} (hγ : 0 < γ) (hp : p ≤ 0)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ¬ 0 ≤ (1 - δ) * (-γ) + δ * p := by
  intro hbalance
  nlinarith [mul_nonneg hδ0 (neg_nonneg.mpr hp), mul_pos hγ (sub_pos.mpr hδ1)]

/-- (g) Fixed-gap bound: a sufficiently small collision rate cannot erode a
fixed positive gap `γ` below half its value, against an arbitrary
nonnegative erosion coefficient `M` (the case `M = 0` is handled directly:
no erosion occurs regardless of `δ`). -/
theorem fixedGap_ge_half {γ M δ : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (_hδ0 : 0 ≤ δ)
    (hδ : δ ≤ γ / (8 * M)) : γ / 2 ≤ γ - 4 * M * δ := by
  rcases hM.eq_or_lt with hM0 | hMpos
  · subst hM0
    simp
    linarith
  · rw [le_div_iff₀ (by linarith : (0 : ℝ) < 8 * M)] at hδ
    nlinarith

end QuittingSwitchingResidueRegression

end GameTheory
