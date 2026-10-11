import GameTheory.Math.ScalarInequalitiesCorrectness
namespace GameTheory.Tests.ScalarInequalities
open GameTheory.Math.ScalarInequalities

theorem empty_table : infer (∅ : Finset Bool) (fun _ => 17) (fun _ => -1) = some 0 := by norm_num
  [infer, candidate]

theorem fractional_lower_and_upper :
    infer ({false, true} : Finset Bool) (fun i => if i then -2 else 3)
      (fun i => if i then -1 else 2) = some (3 / 2) := by norm_num [infer, candidate]

theorem incompatible_signed_rows :
    infer ({false, true} : Finset Bool) (fun i => if i then -1 else 3)
      (fun i => if i then -1 else 2) = none := by norm_num [infer, candidate]

theorem profitable_constant_row :
    infer ({false} : Finset Bool) (fun _ => 1) (fun _ => 0) = none := by norm_num [infer, candidate]

theorem negative_only_zero_suffices :
    infer ({false} : Finset Bool) (fun _ => -2) (fun _ => -1) = some 0 := by norm_num [infer,
      candidate]

/-- A lower bound exceeding an upper bound excludes every nonnegative real solution. -/
theorem signed_rows_have_no_real_solution :
    ¬ ∃ scalar : ℝ, 0 ≤ scalar ∧ ∀ i ∈ ({false, true} : Finset Bool),
      ((if i then -1 else 3 : ℚ) : ℝ) ≤ ((if i then -1 else 2 : ℚ) : ℝ) * scalar :=
  (infer_eq_none_iff _ _ _).mp incompatible_signed_rows

/-- The fractional candidate is least even against irrational possible solutions. -/
theorem fractional_is_real_minimum {scalar : ℝ} (nonnegative : 0 ≤ scalar)
    (feasible : ∀ i ∈ ({false, true} : Finset Bool),
      ((if i then -2 else 3 : ℚ) : ℝ) ≤ ((if i then -1 else 2 : ℚ) : ℝ) * scalar) :
    (3 / 2 : ℝ) ≤ scalar := by
  have least := inferred_minimal _ _ _ fractional_lower_and_upper nonnegative feasible
  norm_num at least ⊢
  exact least

end GameTheory.Tests.ScalarInequalities
