/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCollisionRepairCharacterization
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformPayoffSelection

/-!
# The three-player local-mechanism residue is nonempty

This file closes the local-mechanism residue question by an explicit rational
one-parameter family.  For `L > 18/5`, the table `reward L` escapes all four
local mechanisms used by the three-player branch classification:

* every solo-owner rate is blocked (`K1`);
* every nonempty sure exit set fails (`K2`);
* every ordered one-owner/sure-blocker collision repair fails (`K3`), in the
  actual semantic `QuittingCollisionRepairWorks` predicate and therefore
  independently of how the exact punishment floor is computed;
* every interior two-owner/one-sure-blocker root fails (`K4`).  For blocker
  `1` the two mixer indifferences force rates `(1/2, 1/3)`, and the blocker's
  quit-minus-continue residual is exactly `(18 - 5L)/90`; the other two
  blocker choices force one mixer to the boundary.

Nevertheless the same table has an exact absorbing stationary equilibrium:
players `0` and `2` quit surely and player `1` quits with probability `2/7`.
Its terminal payoff is `(5/7, L, 2/7)`.  Thus the residue is genuinely
nonempty, and it is absorbed by the omitted **double-sure mixer** cell, already
covered by the general sure-set/owner engine.

The concrete rational witness is `L = 4`.
-/

noncomputable section

namespace GameTheory
namespace QuittingLocalMechanismResidueWitness

open StochasticGame Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

/-- The three players. -/
abbrev Player := Fin 3

/-- The parametric reward table, extended by zero at the empty set.

Rows, in player order `0,1,2`, are

* `{0}       ↦ (1, 2/5, 2/5)`;
* `{1}       ↦ (0, 0, 1)`;
* `{2}       ↦ (0, 0, 1)`;
* `{0,1}     ↦ (1, 1, 0)`;
* `{0,2}     ↦ (1, L, 0)`;
* `{1,2}     ↦ (2, 1, 0)`;
* `{0,1,2}   ↦ (0, L, 1)`.
-/
def reward (L : ℝ) (S : Finset Player) (who : Player) : ℝ :=
  if (0 : Player) ∈ S then
    if (1 : Player) ∈ S then
      if (2 : Player) ∈ S then ![(0 : ℝ), L, 1] who
      else ![(1 : ℝ), 1, 0] who
    else
      if (2 : Player) ∈ S then ![(1 : ℝ), L, 0] who
      else ![(1 : ℝ), 2 / 5, 2 / 5] who
  else
    if (1 : Player) ∈ S then
      if (2 : Player) ∈ S then ![(2 : ℝ), 1, 0] who
      else ![(0 : ℝ), 0, 1] who
    else
      if (2 : Player) ∈ S then ![(0 : ℝ), 0, 1] who
      else 0

@[simp] theorem reward_singleton0 (L : ℝ) :
    reward L {0} = ![(1 : ℝ), 2 / 5, 2 / 5] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_singleton1 (L : ℝ) :
    reward L {1} = ![(0 : ℝ), 0, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_singleton2 (L : ℝ) :
    reward L {2} = ![(0 : ℝ), 0, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair01 (L : ℝ) :
    reward L {0, 1} = ![(1 : ℝ), 1, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair02 (L : ℝ) :
    reward L {0, 2} = ![(1 : ℝ), L, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_pair12 (L : ℝ) :
    reward L {1, 2} = ![(2 : ℝ), 1, 0] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_grand (L : ℝ) :
    reward L {0, 1, 2} = ![(0 : ℝ), L, 1] := by
  funext who; fin_cases who <;> simp [reward]

@[simp] theorem reward_empty (L : ℝ) :
    reward L (∅ : Finset Player) = ![(0 : ℝ), 0, 0] := by
  funext who; fin_cases who <;> simp [reward]

/-- The genuine quitting-game reward obtained by restricting `reward L` to
nonempty coalitions. -/
def gameReward (L : ℝ) : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S ↦ reward L S.1

/-- The game-layer extended reward agrees with the arithmetic table, including
at the empty set. -/
theorem quittingSetReward_gameReward (L : ℝ) (S : Finset Player) :
    quittingSetReward (gameReward L) S = reward L S := by
  funext who
  by_cases hS : S.Nonempty
  · simp [quittingSetReward_of_nonempty (gameReward L) hS, gameReward]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, quittingSetReward_empty,
      reward]

/-! ## K1: every owner rate is blocked -/

/-- Own solo payoff. -/
def solo (L : ℝ) (who : Player) : ℝ := reward L {who} who

/-- The joining residual of `blocker` against solo owner `owner` at rate `p`. -/
def switchingResidual (L : ℝ) (owner blocker : Player) (p : ℝ) : ℝ :=
  (1 - p) * solo L blocker +
    p * reward L ({owner, blocker} : Finset Player) blocker -
      reward L {owner} blocker

@[simp] theorem switchingResidual_01 (L p : ℝ) :
    switchingResidual L 0 1 p = p - 2 / 5 := by
  simp [switchingResidual, solo, reward]

@[simp] theorem switchingResidual_02 (L p : ℝ) :
    switchingResidual L 0 2 p = 3 / 5 - p := by
  simp [switchingResidual, solo, reward]
  ring

@[simp] theorem switchingResidual_10 (L p : ℝ) :
    switchingResidual L 1 0 p = 1 := by
  simp [switchingResidual, solo, reward]

@[simp] theorem switchingResidual_12 (L p : ℝ) :
    switchingResidual L 1 2 p = -p := by
  simp [switchingResidual, solo, reward]

@[simp] theorem switchingResidual_20 (L p : ℝ) :
    switchingResidual L 2 0 p = 1 := by
  simp [switchingResidual, solo, reward]

@[simp] theorem switchingResidual_21 (L p : ℝ) :
    switchingResidual L 2 1 p = p := by
  simp [switchingResidual, solo, reward]

/-- Every owner/rate pair in `(0,1]` has a strict joining blocker.  Owner `0`
is covered by the switching pair `1,2`; owners `1,2` have universal blocker
`0`. -/
def EveryOwnerRateBlocked (L : ℝ) : Prop :=
  ∀ owner p, 0 < p → p ≤ 1 →
    ∃ blocker, blocker ≠ owner ∧ 0 < switchingResidual L owner blocker p

theorem everyOwnerRateBlocked (L : ℝ) : EveryOwnerRateBlocked L := by
  intro owner p hp _hp1
  fin_cases owner
  · by_cases h : p ≤ 2 / 5
    · refine ⟨2, by decide, ?_⟩
      rw [switchingResidual_02]
      linarith
    · refine ⟨1, by decide, ?_⟩
      rw [switchingResidual_01]
      linarith
  · refine ⟨0, by decide, ?_⟩
    rw [switchingResidual_10]
    norm_num
  · refine ⟨0, by decide, ?_⟩
    rw [switchingResidual_20]
    norm_num

/-! ## K2: every sure exit set fails -/

/-- The strict negation of the sure-exit inequalities at `S`. -/
def SureExitFails (L : ℝ) (S : Finset Player) : Prop :=
  (∃ i ∈ S, reward L S i < reward L (S.erase i) i) ∨
    (∃ j ∉ S, reward L S j < reward L (insert j S) j)

theorem sureExitFails_0 (L : ℝ) : SureExitFails L ({0} : Finset Player) := by
  refine Or.inr ⟨1, by decide, ?_⟩
  simp [reward]
  norm_num

theorem sureExitFails_1 (L : ℝ) : SureExitFails L ({1} : Finset Player) := by
  refine Or.inr ⟨0, by decide, ?_⟩
  simp [reward]

theorem sureExitFails_2 (L : ℝ) : SureExitFails L ({2} : Finset Player) := by
  refine Or.inr ⟨0, by decide, ?_⟩
  simp [reward]

theorem sureExitFails_01 (L : ℝ) : SureExitFails L ({0, 1} : Finset Player) := by
  refine Or.inr ⟨2, by decide, ?_⟩
  simp [reward]

theorem sureExitFails_02 (L : ℝ) : SureExitFails L ({0, 2} : Finset Player) := by
  refine Or.inl ⟨2, by decide, ?_⟩
  simp [reward]

theorem sureExitFails_12 (L : ℝ) : SureExitFails L ({1, 2} : Finset Player) := by
  refine Or.inl ⟨2, by decide, ?_⟩
  simp [reward]

theorem sureExitFails_012 (L : ℝ) :
    SureExitFails L ({0, 1, 2} : Finset Player) := by
  refine Or.inl ⟨0, by decide, ?_⟩
  simp [reward]

private theorem nonempty_fin3_cases (S : Finset Player) (hS : S.Nonempty) :
    S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
  by_cases h0 : 0 ∈ S
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; right
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
  · by_cases h1 : 1 ∈ S
    · by_cases h2 : 2 ∈ S
      · right; right; right; right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
    · by_cases h2 : 2 ∈ S
      · right; right; left
        ext who
        fin_cases who <;> simp [h0, h1, h2]
      · obtain ⟨who, hwho⟩ := hS
        fin_cases who <;> simp_all

/-- Arithmetic sure-exit failure implies failure of the game-layer predicate. -/
theorem not_isQuittingSureExitSet_of_sureExitFails
    (L : ℝ) {S : Finset Player} (h : SureExitFails L S) :
    ¬ IsQuittingSureExitSet (gameReward L) S := by
  rintro ⟨hmember, houtsider⟩
  rcases h with ⟨i, hi, hlt⟩ | ⟨j, hj, hlt⟩
  · exact absurd (hmember i hi) (by
      rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
      exact not_le.mpr hlt)
  · exact absurd (houtsider j hj) (by
      rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
      exact not_le.mpr hlt)

/-- No nonempty coalition is a sure exit set. -/
def NoSureExitSet (L : ℝ) : Prop :=
  ∀ S : Finset Player, S.Nonempty → ¬ IsQuittingSureExitSet (gameReward L) S

theorem noSureExitSet (L : ℝ) : NoSureExitSet L := by
  intro S hS
  rcases nonempty_fin3_cases S hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_0 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_1 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_2 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_01 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_02 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_12 L)
  · exact not_isQuittingSureExitSet_of_sureExitFails L (sureExitFails_012 L)

/-! ## K3: all ordered collision repairs fail semantically -/

private theorem collision_owner_gain_01 (L : ℝ) :
    quittingSetReward (gameReward L) ({1} : Finset Player) 0 <
      quittingSetReward (gameReward L) ({0, 1} : Finset Player) 0 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]

private theorem collision_owner_gain_02 (L : ℝ) :
    quittingSetReward (gameReward L) ({2} : Finset Player) 0 <
      quittingSetReward (gameReward L) ({0, 2} : Finset Player) 0 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]

private theorem collision_owner_gain_10 (L : ℝ) :
    quittingSetReward (gameReward L) ({0} : Finset Player) 1 <
      quittingSetReward (gameReward L) ({1, 0} : Finset Player) 1 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]
  norm_num

private theorem collision_owner_gain_12 (L : ℝ) :
    quittingSetReward (gameReward L) ({2} : Finset Player) 1 <
      quittingSetReward (gameReward L) ({1, 2} : Finset Player) 1 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]

private theorem collision_owner_loss_20 (L : ℝ) :
    quittingSetReward (gameReward L) ({2, 0} : Finset Player) 2 <
      quittingSetReward (gameReward L) ({0} : Finset Player) 2 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]
  norm_num

private theorem collision_owner_loss_21 (L : ℝ) :
    quittingSetReward (gameReward L) ({2, 1} : Finset Player) 2 <
      quittingSetReward (gameReward L) ({1} : Finset Player) 2 := by
  rw [quittingSetReward_gameReward, quittingSetReward_gameReward]
  simp [reward]

/-- `(owner, blocker) = (0,1)`: owner optimality forces rate `1`, where
spectator `2` strictly joins. -/
theorem noCollisionRepair_01 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 0 1 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 1 :=
    eq_one_of_quittingCollisionOwnerOptimal_of_lt h1
      (collision_owner_gain_01 L) hconditions.1
  have hspectator := hconditions.2.1 2 (by decide) (by decide)
  rw [hr] at hspectator
  unfold QuittingCollisionSpectatorNoJoin at hspectator
  rw [quittingCollisionRepairValue_apply] at hspectator
  simp only [quittingSetReward_gameReward] at hspectator
  norm_num [reward] at hspectator

/-- `(owner, blocker) = (0,2)`: owner optimality forces rate `1`, where the
blocker's leave deviation gives `2/5 > 0`. -/
theorem noCollisionRepair_02 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 0 2 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 1 :=
    eq_one_of_quittingCollisionOwnerOptimal_of_lt h1
      (collision_owner_gain_02 L) hconditions.1
  have hbalance := hconditions.2.2
  rw [hr] at hbalance
  unfold QuittingCollisionBlockerBalance at hbalance
  rw [quittingCollisionRepairValue_apply] at hbalance
  simp only [quittingSetReward_gameReward] at hbalance
  norm_num [reward] at hbalance

/-- `(owner, blocker) = (1,0)`: owner optimality forces rate `1`, where
spectator `2` strictly joins. -/
theorem noCollisionRepair_10 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 1 0 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 1 :=
    eq_one_of_quittingCollisionOwnerOptimal_of_lt h1
      (collision_owner_gain_10 L) hconditions.1
  have hspectator := hconditions.2.1 2 (by decide) (by decide)
  rw [hr] at hspectator
  unfold QuittingCollisionSpectatorNoJoin at hspectator
  rw [quittingCollisionRepairValue_apply] at hspectator
  simp only [quittingSetReward_gameReward] at hspectator
  norm_num [reward] at hspectator

/-- `(owner, blocker) = (1,2)`: owner optimality forces rate `1`, where the
blocker's leave deviation gives `1 > 0`. -/
theorem noCollisionRepair_12 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 1 2 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 1 :=
    eq_one_of_quittingCollisionOwnerOptimal_of_lt h1
      (collision_owner_gain_12 L) hconditions.1
  have hbalance := hconditions.2.2
  rw [hr] at hbalance
  unfold QuittingCollisionBlockerBalance at hbalance
  rw [quittingCollisionRepairValue_apply] at hbalance
  simp only [quittingSetReward_gameReward] at hbalance
  norm_num [reward] at hbalance

/-- `(owner, blocker) = (2,0)`: owner optimality forces rate `0`, where
spectator `1` strictly joins. -/
theorem noCollisionRepair_20 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 2 0 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 0 :=
    eq_zero_of_quittingCollisionOwnerOptimal_of_lt h0
      (collision_owner_loss_20 L) hconditions.1
  have hspectator := hconditions.2.1 1 (by decide) (by decide)
  rw [hr] at hspectator
  unfold QuittingCollisionSpectatorNoJoin at hspectator
  rw [quittingCollisionRepairValue_apply] at hspectator
  simp only [quittingSetReward_gameReward] at hspectator
  norm_num [reward] at hspectator

/-- `(owner, blocker) = (2,1)`: owner optimality forces rate `0`, where
spectator `0` strictly joins. -/
theorem noCollisionRepair_21 (L rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks (gameReward L) 2 1 rate h0 h1 := by
  intro hworks
  have hconditions :=
    (quittingCollisionRepairWorks_iff (gameReward L) (by decide) h0 h1).mp hworks
  have hr : rate = 0 :=
    eq_zero_of_quittingCollisionOwnerOptimal_of_lt h0
      (collision_owner_loss_21 L) hconditions.1
  have hspectator := hconditions.2.1 0 (by decide) (by decide)
  rw [hr] at hspectator
  unfold QuittingCollisionSpectatorNoJoin at hspectator
  rw [quittingCollisionRepairValue_apply] at hspectator
  simp only [quittingSetReward_gameReward] at hspectator
  norm_num [reward] at hspectator

/-- All six ordered sure-blocker collision mechanisms fail. -/
def NoCollisionRepair (L : ℝ) : Prop :=
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 0 1 rate h0 h1) ∧
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 0 2 rate h0 h1) ∧
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 1 0 rate h0 h1) ∧
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 1 2 rate h0 h1) ∧
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 2 0 rate h0 h1) ∧
  (∀ rate h0 h1,
      ¬ QuittingCollisionRepairWorks (gameReward L) 2 1 rate h0 h1)

theorem noCollisionRepair (L : ℝ) : NoCollisionRepair L := by
  exact ⟨noCollisionRepair_01 L, noCollisionRepair_02 L,
    noCollisionRepair_10 L, noCollisionRepair_12 L,
    noCollisionRepair_20 L, noCollisionRepair_21 L⟩

/-! ## K4: every interior two-owner root fails -/

/-- One mixer's quit-minus-continue difference when `blocker` quits surely and
the other mixer quits at `otherRate`. -/
def twoOwnerMixerDifference (L : ℝ)
    (mixer blocker other : Player) (otherRate : ℝ) : ℝ :=
  ((1 - otherRate) * reward L ({mixer, blocker} : Finset Player) mixer +
      otherRate * reward L ({mixer, blocker, other} : Finset Player) mixer) -
    ((1 - otherRate) * reward L ({blocker} : Finset Player) mixer +
      otherRate * reward L ({blocker, other} : Finset Player) mixer)

/-- The blocker's prescribed quit payoff under the two mixer rates. -/
def twoOwnerBlockerQuitValue (L : ℝ)
    (mixer blocker other : Player) (mixerRate otherRate : ℝ) : ℝ :=
  (1 - mixerRate) * (1 - otherRate) * reward L {blocker} blocker +
    mixerRate * (1 - otherRate) *
      reward L ({mixer, blocker} : Finset Player) blocker +
    (1 - mixerRate) * otherRate *
      reward L ({other, blocker} : Finset Player) blocker +
    mixerRate * otherRate *
      reward L ({mixer, blocker, other} : Finset Player) blocker

/-- The blocker's one-stage absorbing reward after deviating to Continue. -/
def twoOwnerBlockerContinueReward (L : ℝ)
    (mixer blocker other : Player) (mixerRate otherRate : ℝ) : ℝ :=
  mixerRate * (1 - otherRate) * reward L {mixer} blocker +
    (1 - mixerRate) * otherRate * reward L {other} blocker +
    mixerRate * otherRate * reward L ({mixer, other} : Finset Player) blocker

/-- An interior two-owner/one-sure-blocker stationary root.  The predicate is
weaker than the full `K4` mechanism because it omits all floor constraints;
therefore proving its failure proves failure of `K4` a fortiori. -/
def TwoOwnerRootCandidate (L : ℝ)
    (mixer blocker other : Player) (mixerRate otherRate : ℝ) : Prop :=
  0 < mixerRate ∧ mixerRate < 1 ∧
    0 < otherRate ∧ otherRate < 1 ∧
    twoOwnerMixerDifference L mixer blocker other otherRate = 0 ∧
    twoOwnerMixerDifference L other blocker mixer mixerRate = 0 ∧
    twoOwnerBlockerContinueReward L mixer blocker other mixerRate otherRate +
        (1 - mixerRate) * (1 - otherRate) *
          twoOwnerBlockerQuitValue L mixer blocker other mixerRate otherRate ≤
      twoOwnerBlockerQuitValue L mixer blocker other mixerRate otherRate

/-- With blocker `0`, mixer `1`'s indifference forces mixer `2` to quit surely. -/
theorem noTwoOwnerRoot_blocker0 (L : ℝ) :
    ¬ ∃ a b, TwoOwnerRootCandidate L 1 0 2 a b := by
  rintro ⟨a, b, _ha0, _ha1, _hb0, hb1, hmix, _hother, _hblocker⟩
  have hb : b = 1 := by
    simp [twoOwnerMixerDifference, reward] at hmix
    linarith
  linarith

/-- With blocker `2`, mixer `1`'s indifference forces mixer `0` to quit surely. -/
theorem noTwoOwnerRoot_blocker2 (L : ℝ) :
    ¬ ∃ a b, TwoOwnerRootCandidate L 0 2 1 a b := by
  rintro ⟨a, b, _ha0, ha1, _hb0, _hb1, _hmix, hother, _hblocker⟩
  have ha : a = 1 := by
    simp [twoOwnerMixerDifference, reward] at hother
    linarith
  linarith

/-- With blocker `1`, the two indifferences force rates `(1/2,1/3)`.  At those
rates the blocker's quit-minus-continue residual is `(18 - 5L)/90`, so it is
strictly negative exactly when `L > 18/5`. -/
theorem noTwoOwnerRoot_blocker1 {L : ℝ} (hL : 18 / 5 < L) :
    ¬ ∃ a b, TwoOwnerRootCandidate L 0 1 2 a b := by
  rintro ⟨a, b, _ha0, _ha1, _hb0, _hb1, hmix, hother, hblocker⟩
  have hb : b = 1 / 3 := by
    simp [twoOwnerMixerDifference, reward] at hmix
    linarith
  have ha : a = 1 / 2 := by
    simp [twoOwnerMixerDifference, reward] at hother
    linarith
  rw [ha, hb] at hblocker
  norm_num [twoOwnerBlockerContinueReward, twoOwnerBlockerQuitValue, reward]
    at hblocker
  nlinarith

/-- All three choices of the sure blocker fail. -/
def NoTwoOwnerRoot (L : ℝ) : Prop :=
  (¬ ∃ a b, TwoOwnerRootCandidate L 1 0 2 a b) ∧
  (¬ ∃ a b, TwoOwnerRootCandidate L 0 1 2 a b) ∧
  (¬ ∃ a b, TwoOwnerRootCandidate L 0 2 1 a b)

theorem noTwoOwnerRoot {L : ℝ} (hL : 18 / 5 < L) : NoTwoOwnerRoot L :=
  ⟨noTwoOwnerRoot_blocker0 L, noTwoOwnerRoot_blocker1 hL,
    noTwoOwnerRoot_blocker2 L⟩

/-! ## The local residue and its absorber -/

/-- The exact conjunction of the four local exclusions used here. -/
def IsLocalMechanismResidue (L : ℝ) : Prop :=
  EveryOwnerRateBlocked L ∧ NoSureExitSet L ∧
    NoCollisionRepair L ∧ NoTwoOwnerRoot L

/-- **The local residue is nonempty.**  Every member of the family with
`L > 18/5` satisfies all four exclusions. -/
theorem isLocalMechanismResidue {L : ℝ} (hL : 18 / 5 < L) :
    IsLocalMechanismResidue L :=
  ⟨everyOwnerRateBlocked L, noSureExitSet L, noCollisionRepair L,
    noTwoOwnerRoot hL⟩

/-- The concrete rational residue witness. -/
theorem isLocalMechanismResidue_four : IsLocalMechanismResidue 4 := by
  apply isLocalMechanismResidue
  norm_num

private theorem twoSevenths_nonneg : (0 : ℝ) ≤ 2 / 7 := by norm_num
private theorem twoSevenths_le_one : (2 / 7 : ℝ) ≤ 1 := by norm_num
private theorem twoSevenths_pos : (0 : ℝ) < 2 / 7 := by norm_num
private theorem doubleSure_nonempty : ({0, 2} : Finset Player).Nonempty := by decide
private theorem mixer_not_mem_doubleSure : (1 : Player) ∉ ({0, 2} : Finset Player) := by
  decide

/-- The omitted local mechanism: players `0,2` quit surely and player `1`
mixes at rate `2/7`. -/
def doubleSureMixerRoot : Player → PMF Bool :=
  quittingSureSetOwnerRoot ({0, 2} : Finset Player) 1 (2 / 7)
    twoSevenths_nonneg twoSevenths_le_one

/-- The corresponding stationary behavior profile. -/
def doubleSureMixerProfile (L : ℝ) :
    (quittingGame (gameReward L)).BehaviorProfile :=
  quittingStationaryProfile (gameReward L) doubleSureMixerRoot

/-- The exact on-path payoff of the double-sure mixer. -/
def doubleSureMixerValue (L : ℝ) : Payoff Player := ![(5 / 7 : ℝ), L, 2 / 7]

/-- The stationary profile's terminal payoff is `(5/7,L,2/7)`. -/
theorem terminalPayoff_doubleSureMixerProfile (L : ℝ) :
    quittingTerminalPayoff (gameReward L) (doubleSureMixerProfile L) =
      doubleSureMixerValue L := by
  funext who
  rw [doubleSureMixerProfile, doubleSureMixerRoot,
    terminalPayoff_sureSetOwnerRoot (gameReward L) doubleSure_nonempty
      mixer_not_mem_doubleSure (2 / 7) twoSevenths_nonneg twoSevenths_le_one who]
  fin_cases who <;>
    norm_num [doubleSureMixerValue, quittingSureSetOwnerValue,
      quittingSetReward_gameReward, reward]

/-- **Exact absorber.**  The double-sure mixer is a terminal `0`-Nash
profile against every behavioral unilateral deviation, for every real `L`. -/
theorem isExactTerminalNash_doubleSureMixerProfile (L : ℝ) :
    (quittingGame (gameReward L)).IsεAsymptoticNash
      (quittingTerminalPayoff (gameReward L)) 0
      (doubleSureMixerProfile L) := by
  rw [doubleSureMixerProfile, doubleSureMixerRoot]
  refine isεAsymptoticNash_sureSetOwnerRoot_of_exactCap_le
    (gameReward L) doubleSure_nonempty mixer_not_mem_doubleSure
      (2 / 7) twoSevenths_nonneg twoSevenths_le_one twoSevenths_pos 0 ?_
  intro who
  fin_cases who <;>
    norm_num [quittingSureSetOwnerExactCap, quittingSureSetOwnerValue,
      quittingSetReward_gameReward, reward]

/-- The concrete residue witness therefore has a uniform-equilibrium payoff.
The same exact terminal Nash profile supplies every positive error. -/
theorem exists_uniformEquilibriumPayoff_four :
    ∃ payoff : Payoff Player,
      (quittingGame (gameReward 4)).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  refine ⟨doubleSureMixerProfile 4, ?_⟩
  exact (isExactTerminalNash_doubleSureMixerProfile 4).mono hε.le

end QuittingLocalMechanismResidueWitness
end GameTheory
