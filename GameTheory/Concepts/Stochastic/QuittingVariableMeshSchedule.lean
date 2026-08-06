/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingletonStationaryRoot
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Accuracy-indexed variable subdivision schedules

A fixed subdivision count cannot make

`1 - (1 - p_t)^(1/m)`

uniformly small along a nonperiodic path when the coarse masses `p_t` may
approach one.  The correct construction chooses one finite subdivision count
for each coarse arc.  This file contains the scalar choice and a deterministic
clock which flattens the resulting variable-length blocks into ordinary game
time.
-/

noncomputable section

namespace GameTheory

open Math

/-! ## Adaptive subdivision length -/

/-- A finite subdivision count chosen above the logarithmic intensity divided
by the requested micro-hazard scale. -/
def quittingAdaptiveMeshLength (p delta : ℝ) : ℕ :=
  Classical.choose (exists_nat_gt (quittingMeshIntensity p / delta))

/-- The defining Archimedean inequality for the adaptive length. -/
theorem quittingAdaptiveMeshLength_spec (p delta : ℝ) :
    quittingMeshIntensity p / delta <
      (quittingAdaptiveMeshLength p delta : ℝ) :=
  Classical.choose_spec (exists_nat_gt (quittingMeshIntensity p / delta))

/-- For a genuine coarse hazard and a positive target scale, the selected
subdivision count is positive. -/
theorem quittingAdaptiveMeshLength_pos
    {p delta : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hdelta : 0 < delta) :
    0 < quittingAdaptiveMeshLength p delta := by
  have hintensity : 0 ≤ quittingMeshIntensity p :=
    quittingMeshIntensity_nonneg hp0 hp1.le
  have hquotient : 0 ≤ quittingMeshIntensity p / delta :=
    div_nonneg hintensity hdelta.le
  have hcast : 0 < (quittingAdaptiveMeshLength p delta : ℝ) :=
    lt_of_le_of_lt hquotient (quittingAdaptiveMeshLength_spec p delta)
  exact_mod_cast hcast

/-- Adaptive subdivision makes every resulting micro-hazard strictly smaller
than the requested scale, even when the coarse hazards approach one. -/
theorem quittingMeshHazard_adaptive_lt
    {p delta : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hdelta : 0 < delta) :
    quittingMeshHazard p (quittingAdaptiveMeshLength p delta) < delta := by
  let m := quittingAdaptiveMeshLength p delta
  have hmNat : 0 < m :=
    quittingAdaptiveMeshLength_pos hp0 hp1 hdelta
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hspec : quittingMeshIntensity p / delta < (m : ℝ) := by
    simpa only [m] using quittingAdaptiveMeshLength_spec p delta
  have hintensity : quittingMeshIntensity p < (m : ℝ) * delta :=
    (div_lt_iff₀ hdelta).mp hspec
  have hdiv : quittingMeshIntensity p / (m : ℝ) < delta :=
    (div_lt_iff₀ hm).mpr (by simpa [mul_comm] using hintensity)
  exact (quittingMeshHazard_le_intensity_div hp1).trans_lt hdiv

/-! ## Flattening variable-length blocks -/

/-- The cumulative game-time boundary before coarse block `block`. -/
def quittingVariableMeshBoundary (length : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | block + 1 => quittingVariableMeshBoundary length block + length block

@[simp] theorem quittingVariableMeshBoundary_zero (length : ℕ → ℕ) :
    quittingVariableMeshBoundary length 0 = 0 := rfl

@[simp] theorem quittingVariableMeshBoundary_succ
    (length : ℕ → ℕ) (block : ℕ) :
    quittingVariableMeshBoundary length (block + 1) =
      quittingVariableMeshBoundary length block + length block := rfl

/-- At flattened game time `time`, record the current coarse block and the
microstage offset inside that block. -/
def quittingVariableMeshState (length : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | time + 1 =>
      let current := quittingVariableMeshState length time
      if current.2 + 1 < length current.1 then
        (current.1, current.2 + 1)
      else
        (current.1 + 1, 0)

@[simp] theorem quittingVariableMeshState_zero (length : ℕ → ℕ) :
    quittingVariableMeshState length 0 = (0, 0) := rfl

/-- One clock step either advances inside the current block or enters the next
block at offset zero. -/
theorem quittingVariableMeshState_succ
    (length : ℕ → ℕ) (time : ℕ) :
    quittingVariableMeshState length (time + 1) =
      let current := quittingVariableMeshState length time
      if current.2 + 1 < length current.1 then
        (current.1, current.2 + 1)
      else
        (current.1 + 1, 0) := rfl

/-- Under positive block lengths, the clock offset is always a valid offset in
its current block. -/
theorem quittingVariableMeshState_offset_lt
    (length : ℕ → ℕ) (hlength : ∀ block, 0 < length block) :
    ∀ time,
      (quittingVariableMeshState length time).2 <
        length (quittingVariableMeshState length time).1 := by
  intro time
  induction time with
  | zero => simpa using hlength 0
  | succ time _ih =>
      rw [quittingVariableMeshState_succ]
      split_ifs with hinside
      · simpa using hinside
      · simpa using hlength
          ((quittingVariableMeshState length time).1 + 1)

/-- Starting at offset zero of one block, every strict in-block offset is
reached at the corresponding later game time. -/
theorem quittingVariableMeshState_add_offset_of_eq
    (length : ℕ → ℕ) (hlength : ∀ block, 0 < length block)
    {start block : ℕ}
    (hstart : quittingVariableMeshState length start = (block, 0)) :
    ∀ {offset : ℕ}, offset < length block →
      quittingVariableMeshState length (start + offset) = (block, offset) := by
  intro offset hoffset
  induction offset with
  | zero => simpa using hstart
  | succ offset ih =>
      have hoffsetPrev : offset < length block :=
        lt_trans (Nat.lt_succ_self offset) hoffset
      have hprev := ih hoffsetPrev
      rw [show start + (offset + 1) = start + offset + 1 by omega,
        quittingVariableMeshState_succ, hprev]
      simp only [Prod.snd, Prod.fst]
      rw [if_pos hoffset]

/-- A positive block closes exactly at offset `length block` and enters the
next block at offset zero. -/
theorem quittingVariableMeshState_add_length_of_eq
    (length : ℕ → ℕ) (hlength : ∀ block, 0 < length block)
    {start block : ℕ}
    (hstart : quittingVariableMeshState length start = (block, 0)) :
    quittingVariableMeshState length (start + length block) =
      (block + 1, 0) := by
  have hpred : length block - 1 < length block :=
    Nat.sub_lt (hlength block) (by omega)
  have hprev := quittingVariableMeshState_add_offset_of_eq
    length hlength hstart hpred
  have htime : start + length block =
      start + (length block - 1) + 1 := by omega
  rw [htime, quittingVariableMeshState_succ, hprev]
  simp only [Prod.snd, Prod.fst]
  rw [if_neg (by omega)]

/-- Every cumulative boundary is the start of its advertised coarse block. -/
theorem quittingVariableMeshState_boundary
    (length : ℕ → ℕ) (hlength : ∀ block, 0 < length block) :
    ∀ block,
      quittingVariableMeshState length
          (quittingVariableMeshBoundary length block) =
        (block, 0) := by
  intro block
  induction block with
  | zero => rfl
  | succ block ih =>
      simpa only [quittingVariableMeshBoundary_succ] using
        quittingVariableMeshState_add_length_of_eq length hlength ih

/-- Boundary-plus-offset coordinates agree with the flattened clock. -/
theorem quittingVariableMeshState_boundary_add
    (length : ℕ → ℕ) (hlength : ∀ block, 0 < length block)
    (block offset : ℕ) (hoffset : offset < length block) :
    quittingVariableMeshState length
        (quittingVariableMeshBoundary length block + offset) =
      (block, offset) :=
  quittingVariableMeshState_add_offset_of_eq length hlength
    (quittingVariableMeshState_boundary length hlength block) hoffset

end GameTheory
