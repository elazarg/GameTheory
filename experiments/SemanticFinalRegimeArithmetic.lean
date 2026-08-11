/-
Exact arithmetic replay for `semantic_final_regime_search.py`.

These are deliberately only the finite scalar consequences of the final
minimum-semantic passports.  No theorem below asserts minimum-carrier
provenance or absence of a uniform equilibrium.
-/

import Mathlib

namespace GameTheory.Experiments.SemanticFinalRegimeArithmetic

/-- The integral interior example has first feasible entrant rate `1/2`.
The entrant's gain is `(1-p) * 1 + p * (-1)`. -/
theorem interior_entrant_breakpoint :
    (1 - (1 / 2 : ℝ)) * 1 + (1 / 2 : ℝ) * (-1) = 0 := by
  norm_num

/-- Strict infeasibility before the selected interior breakpoint. -/
theorem interior_entrant_profitable_before
    {p : ℝ} (hp : p < 1 / 2) :
    0 < (1 - p) * 1 + p * (-1) := by
  linarith

/-- At the sure-Quit boundary, the entrant gain is `1-p`; hence the first
feasible rate is exactly one. -/
theorem pure_owner_entrant_breakpoint :
    (1 - (1 : ℝ)) * 1 + (1 : ℝ) * 0 = 0 := by
  norm_num

theorem pure_owner_entrant_profitable_before
    {p : ℝ} (hp : p < 1) :
    0 < (1 - p) * 1 + p * 0 := by
  linarith

/-- The rate-one negative-collision branch and reverse-neutral branch are
simultaneously arithmetically consistent. -/
theorem pure_owner_oriented_collisions :
    ((-1 : ℝ) - 0 < 0) ∧ ((0 : ℝ) - 0 = 0) := by
  norm_num

/-- Exact punishment sandwich in both atomic examples: singleton payoff
`s=-2`, punishment `chi=0`, semantic debt `d=2`, and one-outsider cap zero. -/
theorem atomic_punishment_sandwich :
    ((-2 : ℝ) < 0) ∧
      0 - (-2) = 2 ∧
      0 - (-2) ≤ 2 ∧
      max (-1 : ℝ) 0 = 0 := by
  norm_num

/-- Each marked plateau negative control has prescribed payoff zero and
unilateral envelope one on its debtor coordinate. -/
theorem plateau_marked_atom_debt :
    ((1 : ℝ) - 0 = 1) ∧ 0 < (1 : ℝ) - 0 := by
  norm_num

end GameTheory.Experiments.SemanticFinalRegimeArithmetic

#print axioms GameTheory.Experiments.SemanticFinalRegimeArithmetic.interior_entrant_breakpoint
#print axioms GameTheory.Experiments.SemanticFinalRegimeArithmetic.pure_owner_oriented_collisions
#print axioms GameTheory.Experiments.SemanticFinalRegimeArithmetic.atomic_punishment_sandwich
