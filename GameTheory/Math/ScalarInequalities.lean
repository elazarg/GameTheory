import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Rat

/-! # Executable scalar feasibility with signed slopes

A finite rational table imposes inequalities `gain ≤ slope * scalar` with a
nonnegative scalar. Positive slopes impose lower bounds, negative slopes impose
upper bounds, and zero slopes can be infeasible. The largest positive-slope
ratio (or zero) is the only candidate that needs checking. No real arithmetic,
classical choice or finite-carrier conversion is used by the checker.
-/

namespace GameTheory.Math.ScalarInequalities
variable {Index : Type*}

/-- The largest lower bound imposed by a positive slope, including zero. -/
def candidate (rows : Finset Index) (gain slope : Index → ℚ) : ℚ :=
  (insert 0 (rows.image (fun index => if 0 < slope index then gain index / slope index else 0))).max'
    (Finset.insert_nonempty ..)

/-- Check the least possible nonnegative scalar against every row, including upper bounds
from negative slopes and infeasible constant rows. -/
def infer (rows : Finset Index) (gain slope : Index → ℚ) : Option ℚ :=
  if ∀ index ∈ rows, gain index ≤ slope index * candidate rows gain slope then
    some (candidate rows gain slope) else none

end GameTheory.Math.ScalarInequalities
