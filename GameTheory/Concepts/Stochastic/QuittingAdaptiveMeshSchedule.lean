/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingletonFlowMesh
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Variable-length mesh schedules

A nonperiodic singleton-flow path may contain coarse hazards arbitrarily close
to one, so no fixed subdivision count makes every micro-hazard small.  The
correct construction assigns a finite positive subdivision count to each
coarse stage and then flattens the resulting variable-length blocks into one
ordinary natural-time path.

This file isolates the arithmetic of that flattening.  The state at a microtime
is a pair `(block, offset)`.  Positive block lengths ensure that the recursion
visits exactly

`(0,0), ..., (0,m₀-1), (1,0), ..., (1,m₁-1), ...`.
-/

noncomputable section

namespace GameTheory

open Math

/-- Starting microtime of a variable-length block. -/
def quittingVariableBlockPrefix (count : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | block + 1 => quittingVariableBlockPrefix count block + count block

@[simp] theorem quittingVariableBlockPrefix_zero
    (count : ℕ → ℕ) :
    quittingVariableBlockPrefix count 0 = 0 := rfl

@[simp] theorem quittingVariableBlockPrefix_succ
    (count : ℕ → ℕ) (block : ℕ) :
    quittingVariableBlockPrefix count (block + 1) =
      quittingVariableBlockPrefix count block + count block := rfl

/-- Block and offset occupied at a microtime. -/
def quittingVariableBlockState (count : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | time + 1 =>
      let here := quittingVariableBlockState count time
      if here.2 + 1 < count here.1 then
        (here.1, here.2 + 1)
      else
        (here.1 + 1, 0)

@[simp] theorem quittingVariableBlockState_zero
    (count : ℕ → ℕ) :
    quittingVariableBlockState count 0 = (0, 0) := rfl

/-- The recursive offset always lies inside its current positive-length
block. -/
theorem quittingVariableBlockState_offset_lt
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block) :
    ∀ time,
      (quittingVariableBlockState count time).2 <
        count (quittingVariableBlockState count time).1 := by
  intro time
  induction time with
  | zero =>
      simpa [quittingVariableBlockState] using hcount 0
  | succ time ih =>
      by_cases hstep :
          (quittingVariableBlockState count time).2 + 1 <
            count (quittingVariableBlockState count time).1
      · simp [quittingVariableBlockState, hstep]
      · simpa [quittingVariableBlockState, hstep] using
          hcount ((quittingVariableBlockState count time).1 + 1)

/-- Microtime is exactly block prefix plus the current offset. -/
theorem quittingVariableBlockState_time_eq
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block) :
    ∀ time,
      time = quittingVariableBlockPrefix count
          (quittingVariableBlockState count time).1 +
        (quittingVariableBlockState count time).2 := by
  intro time
  induction time with
  | zero => simp [quittingVariableBlockState, quittingVariableBlockPrefix]
  | succ time ih =>
      have hoffset :=
        quittingVariableBlockState_offset_lt count hcount time
      by_cases hstep :
          (quittingVariableBlockState count time).2 + 1 <
            count (quittingVariableBlockState count time).1
      · simp only [quittingVariableBlockState, hstep, ↓reduceIte,
          Prod.fst, Prod.snd]
        omega
      · have hend :
            (quittingVariableBlockState count time).2 + 1 =
              count (quittingVariableBlockState count time).1 := by
          omega
        simp only [quittingVariableBlockState, hstep, ↓reduceIte,
          Prod.fst, Prod.snd, quittingVariableBlockPrefix_succ]
        omega

/-- Starting from the first offset of a block, the recursion stays in that
block at every smaller offset. -/
theorem quittingVariableBlockState_add_offset
    (count : ℕ → ℕ) (start block : ℕ)
    (hstart : quittingVariableBlockState count start = (block, 0)) :
    ∀ offset, offset < count block →
      quittingVariableBlockState count (start + offset) = (block, offset) := by
  intro offset
  induction offset with
  | zero =>
      intro _
      simpa using hstart
  | succ offset ih =>
      intro hoffset
      have hprev : offset < count block := by omega
      have hstate := ih hprev
      rw [show start + offset.succ = start + offset + 1 by omega,
        quittingVariableBlockState, hstate]
      simp only [Prod.fst, Prod.snd, if_pos hoffset]

/-- After exactly the positive length of a block, the recursion enters the
next block at offset zero. -/
theorem quittingVariableBlockState_add_count
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block)
    (start block : ℕ)
    (hstart : quittingVariableBlockState count start = (block, 0)) :
    quittingVariableBlockState count (start + count block) =
      (block + 1, 0) := by
  obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (hcount block))
  rw [hlast]
  have hstate := quittingVariableBlockState_add_offset
    count start block hstart last (Nat.lt_succ_self last)
  rw [show start + (last + 1) = start + last + 1 by omega,
    quittingVariableBlockState, hstate]
  simp

/-- Every block prefix is visited at offset zero. -/
@[simp] theorem quittingVariableBlockState_prefix
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block) :
    ∀ block,
      quittingVariableBlockState count
        (quittingVariableBlockPrefix count block) = (block, 0) := by
  intro block
  induction block with
  | zero => simp
  | succ block ih =>
      rw [quittingVariableBlockPrefix_succ]
      exact quittingVariableBlockState_add_count count hcount
        (quittingVariableBlockPrefix count block) block ih

/-- Explicit state inside a variable-length block. -/
theorem quittingVariableBlockState_prefix_add
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block)
    (block offset : ℕ) (hoffset : offset < count block) :
    quittingVariableBlockState count
        (quittingVariableBlockPrefix count block + offset) =
      (block, offset) :=
  quittingVariableBlockState_add_offset count
    (quittingVariableBlockPrefix count block) block
    (quittingVariableBlockState_prefix count hcount block)
    offset hoffset

/-- Duration occupied by a consecutive family of variable-length blocks. -/
def quittingVariableBlockDuration
    (count : ℕ → ℕ) (start fuel : ℕ) : ℕ :=
  quittingVariableBlockPrefix count (start + fuel) -
    quittingVariableBlockPrefix count start

/-- A later block prefix lies after an earlier prefix. -/
theorem quittingVariableBlockPrefix_le_add
    (count : ℕ → ℕ) (start fuel : ℕ) :
    quittingVariableBlockPrefix count start ≤
      quittingVariableBlockPrefix count (start + fuel) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [show start + fuel.succ = start + fuel + 1 by omega,
        quittingVariableBlockPrefix_succ]
      exact ih.trans (Nat.le_add_right _ _)

/-- Prefix plus the duration of a block interval is its endpoint. -/
theorem quittingVariableBlockPrefix_add_duration
    (count : ℕ → ℕ) (start fuel : ℕ) :
    quittingVariableBlockPrefix count start +
        quittingVariableBlockDuration count start fuel =
      quittingVariableBlockPrefix count (start + fuel) := by
  unfold quittingVariableBlockDuration
  exact Nat.add_sub_of_le
    (quittingVariableBlockPrefix_le_add count start fuel)

@[simp] theorem quittingVariableBlockDuration_zero
    (count : ℕ → ℕ) (start : ℕ) :
    quittingVariableBlockDuration count start 0 = 0 := by
  simp [quittingVariableBlockDuration]

/-- Appending one variable-length block appends exactly its count to the
elapsed duration. -/
theorem quittingVariableBlockDuration_succ
    (count : ℕ → ℕ) (start fuel : ℕ) :
    quittingVariableBlockDuration count start (fuel + 1) =
      quittingVariableBlockDuration count start fuel + count (start + fuel) := by
  unfold quittingVariableBlockDuration
  rw [show start + (fuel + 1) = start + fuel + 1 by omega,
    quittingVariableBlockPrefix_succ]
  have hle := quittingVariableBlockPrefix_le_add count start fuel
  omega

/-- A positive subdivision count can make one logarithmic mesh hazard smaller
than any prescribed positive cap, even when the coarse hazard is arbitrarily
close to one. -/
theorem exists_quittingMeshCount_hazard_le
    {p cap : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hcap : 0 < cap) :
    ∃ count : ℕ, 0 < count ∧ quittingMeshHazard p count ≤ cap := by
  have hintensity0 : 0 ≤ quittingMeshIntensity p :=
    quittingMeshIntensity_nonneg hp0 hp1.le
  obtain ⟨count, hcountLarge⟩ :=
    exists_nat_gt (quittingMeshIntensity p / cap)
  have hcountReal : 0 < (count : ℝ) := by
    exact (div_nonneg hintensity0 hcap.le).trans_lt hcountLarge
  have hintensityDiv :
      quittingMeshIntensity p / (count : ℝ) ≤ cap := by
    apply (div_le_iff₀ hcountReal).2
    have hmul : quittingMeshIntensity p < (count : ℝ) * cap :=
      (div_lt_iff₀ hcap).1 hcountLarge
    linarith
  refine ⟨count, ?_,
    (quittingMeshHazard_le_intensity_div hp1).trans hintensityDiv⟩
  exact_mod_cast hcountReal

end GameTheory
