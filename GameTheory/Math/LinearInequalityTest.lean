module

/-
# Exact finite-system alternatives over the rationals

Empty rows give no obstruction. Empty columns can still give an inconsistent
system, certified by a positive right-hand side. These controls use rational
arithmetic and no topology or completeness.
-/

public import GameTheory.Math.LinearInequality
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Math.LinearInequalityTest

open scoped BigOperators

theorem empty_rows_feasible :
    ∃ x : Bool → ℚ, ∀ _row : Empty, (0 : ℚ) ≤ ∑ col, (0 : ℚ) * x col := by
  apply (LinearInequality.exists_solution_iff_no_certificate
    (fun (_ : Empty) (_ : Bool) => (0 : ℚ)) (fun _ => 0)).mpr
  rintro ⟨weights, _, _, positive⟩
  simp at positive

theorem empty_columns_infeasible :
    ¬ ∃ x : Empty → ℚ, ∀ _row : Unit, (1 : ℚ) ≤ ∑ col, (0 : ℚ) * x col := by
  intro feasible
  have noCertificate := (LinearInequality.exists_solution_iff_no_certificate
    (fun (_ : Unit) (_ : Empty) => (0 : ℚ)) (fun _ => 1)).mp feasible
  apply noCertificate
  refine ⟨fun _ => 1, fun _ => zero_le_one, fun col => col.elim, ?_⟩
  norm_num

end GameTheory.Math.LinearInequalityTest
