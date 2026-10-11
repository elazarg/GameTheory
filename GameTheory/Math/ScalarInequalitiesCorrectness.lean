/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Math.ScalarInequalities
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Real correctness of rational scalar inference

The executable candidate satisfies the table whenever any nonnegative real
solution does. Consequently inference is sound, complete and returns the least
nonnegative feasible scalar, even among real solutions. Negative slopes need
no extra premise: lowering a feasible scalar preserves their upper bounds.
-/

namespace GameTheory.Math.ScalarInequalities
variable {Index : Type*}

/-- The candidate is nonnegative, including for an empty table. -/
theorem candidate_nonnegative (rows : Finset Index) (gain slope : Index → ℚ) :
    0 ≤ candidate rows gain slope :=
  Finset.le_max' _ 0 (Finset.mem_insert_self ..)

/-- Each positive slope's required ratio is at most the candidate. -/
theorem ratio_le_candidate (rows : Finset Index) (gain slope : Index → ℚ)
    {index : Index} (member : index ∈ rows) (positive : 0 < slope index) :
    gain index / slope index ≤ candidate rows gain slope := by
  have bound : (if 0 < slope index then gain index / slope index else 0) ≤ candidate rows gain
    slope :=
    Finset.le_max' _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem (fun entry => if 0 < slope entry then gain entry / slope entry else
      0) member))
  simpa only [ite_eq_left positive] using bound

/-- Every nonnegative feasible real scalar is at least the rational candidate. -/
theorem candidate_le (rows : Finset Index) (gain slope : Index → ℚ)
    {scalar : ℝ} (nonnegative : 0 ≤ scalar)
    (feasible : ∀ index ∈ rows, (gain index : ℝ) ≤ (slope index : ℝ) * scalar) :
    (candidate rows gain slope : ℝ) ≤ scalar := by
  have member := Finset.max'_mem
    (insert 0 (rows.image (fun index => if 0 < slope index then gain index / slope index else 0)))
    (Finset.insert_nonempty ..)
  change candidate rows gain slope ∈ _ at member
  rcases Finset.mem_insert.mp member with zero | member
  · simpa only [zero, Rat.cast_zero] using nonnegative
  · obtain ⟨index, inRows, equal⟩ := Finset.mem_image.mp member
    rw [← equal]
    by_cases positive : 0 < slope index
    · rw [ite_eq_left positive, Rat.cast_div]
      have positiveReal : (0 : ℝ) < (slope index : ℝ) := by exact_mod_cast positive
      exact (div_le_iff₀ positiveReal).mpr ((feasible index inRows).trans_eq (mul_comm ..))
    · simpa only [ite_eq_right positive, Rat.cast_zero] using nonnegative

/-- If any nonnegative real solution exists, the candidate satisfies every row.
Negative slopes reverse the comparison, so reducing to the candidate preserves their upper bounds.
  -/
theorem candidate_feasible (rows : Finset Index) (gain slope : Index → ℚ)
    {scalar : ℝ} (nonnegative : 0 ≤ scalar)
    (feasible : ∀ index ∈ rows, (gain index : ℝ) ≤ (slope index : ℝ) * scalar) :
    ∀ index ∈ rows, gain index ≤ slope index * candidate rows gain slope := by
  intro index member
  by_cases positive : 0 < slope index
  · exact ((div_le_iff₀ positive).mp (ratio_le_candidate rows gain slope member positive)).trans_eq
      (mul_comm ..)
  · have nonpositive : (slope index : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt positive
    have bound := (feasible index member).trans
      (mul_le_mul_of_nonpos_left (candidate_le rows gain slope nonnegative feasible) nonpositive)
    exact_mod_cast bound

/-- Every returned rational scalar is nonnegative and feasible over the reals. -/
theorem inferred_sound (rows : Finset Index) (gain slope : Index → ℚ)
    {scalar : ℚ} (inferred : infer rows gain slope = some scalar) :
    0 ≤ scalar ∧ ∀ index ∈ rows, (gain index : ℝ) ≤ (slope index : ℝ) * scalar := by
  unfold infer at inferred
  split at inferred
  next feasible =>
    cases Option.some.inj inferred
    refine ⟨candidate_nonnegative .., ?_⟩
    intro index member
    exact_mod_cast feasible index member
  next => contradiction

/-- Successful inference returns the least nonnegative feasible scalar, even among reals. -/
theorem inferred_minimal (rows : Finset Index) (gain slope : Index → ℚ)
    {scalar : ℚ} (inferred : infer rows gain slope = some scalar)
    {other : ℝ} (nonnegative : 0 ≤ other)
    (feasible : ∀ index ∈ rows, (gain index : ℝ) ≤ (slope index : ℝ) * other) :
    (scalar : ℝ) ≤ other := by
  unfold infer at inferred
  split at inferred
  next =>
    cases Option.some.inj inferred
    exact candidate_le rows gain slope nonnegative feasible
  next => contradiction

/-- Rejection is equivalent to the absence of any nonnegative real solution. -/
theorem infer_eq_none_iff (rows : Finset Index) (gain slope : Index → ℚ) :
    infer rows gain slope = none ↔
      ¬ ∃ scalar : ℝ, 0 ≤ scalar ∧ ∀ index ∈ rows,
        (gain index : ℝ) ≤ (slope index : ℝ) * scalar := by
  constructor
  · intro rejected
    rintro ⟨scalar, nonnegative, feasible⟩
    have candidateSafe := candidate_feasible rows gain slope nonnegative feasible
    unfold infer at rejected
    rw [ite_eq_left candidateSafe] at rejected
    exact Option.some_ne_none _ rejected
  · intro impossible
    unfold infer
    split
    next feasible =>
      exact False.elim (impossible ⟨candidate rows gain slope,
        by exact_mod_cast candidate_nonnegative rows gain slope,
        fun index member => by exact_mod_cast feasible index member⟩)
    next => rfl

/-- Feasibility for every sufficiently large scalar forces a nonnegative slope. -/
theorem slope_nonneg_of_eventually_feasible (gain slope cutoff : ℝ)
    (feasible : ∀ scalar, cutoff ≤ scalar → gain ≤ slope * scalar) : 0 ≤ slope := by
  by_contra negative
  have negative : slope < 0 := lt_of_not_ge negative
  have bound := feasible (max cutoff ((gain - 1) / slope)) (le_max_left ..)
  have upper := mul_le_mul_of_nonpos_left
    (le_max_right cutoff ((gain - 1) / slope)) negative.le
  have cancel : slope * ((gain - 1) / slope) = gain - 1 := by
    field_simp [ne_of_lt negative]
  rw [cancel] at upper
  linarith

/-- A finite real table is feasible at every sufficiently large nonnegative scalar
exactly when every slope is nonnegative and zero-slope rows have no positive gain.
The ambient row carrier may be infinite. -/
theorem exists_eventually_feasible_iff (rows : Finset Index) (gain slope : Index → ℝ) :
    (∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ scalar, cutoff ≤ scalar → ∀ index ∈ rows,
      gain index ≤ slope index * scalar) ↔
      ∀ index ∈ rows, 0 ≤ slope index ∧ (slope index = 0 → gain index ≤ 0) := by
  classical
  constructor
  · rintro ⟨cutoff, _, feasible⟩ index member
    refine ⟨slope_nonneg_of_eventually_feasible _ _ cutoff
      (fun scalar large => feasible scalar large index member), ?_⟩
    intro zero
    have atCutoff := feasible cutoff le_rfl index member
    simpa only [zero, zero_mul] using atCutoff
  · intro condition
    let amount (index : Index) := max 0 (gain index / slope index)
    let cutoff := ∑ index ∈ rows, amount index
    have nonnegative (index : Index) : 0 ≤ amount index := le_max_left ..
    refine ⟨cutoff, Finset.sum_nonneg (fun index _ => nonnegative index), ?_⟩
    intro scalar large index member
    by_cases zero : slope index = 0
    · simpa only [zero, zero_mul] using (condition index member).2 zero
    · have positive : 0 < slope index := lt_of_le_of_ne (condition index member).1 (Ne.symm zero)
      have bound : gain index / slope index ≤ scalar :=
        (le_max_right _ _).trans
          ((Finset.single_le_sum (fun entry _ => nonnegative entry) member).trans large)
      exact (div_le_iff₀ positive).mp bound |>.trans_eq (mul_comm _ _)

end GameTheory.Math.ScalarInequalities
