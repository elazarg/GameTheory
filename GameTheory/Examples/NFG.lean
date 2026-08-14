/-
# Normal-form examples with non-finite action spaces

This countable-action smoke test checks that deterministic NFG syntax and the
canonical semantic solution concepts remain independent of executable finite
enumeration.
-/

import GameTheory.Core.Response
import GameTheory.Core.Utility
import GameTheory.Languages.NFG
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.Examples.NFG

open GameTheory GameTheory.Languages GameTheory.Probability

/-- Two players choose natural numbers; only `(0, 0)` has positive utility. -/
abbrev natChoose : NFG.Game (Fin 2) where
  Action _ := ℕ
  Outcome := Fin 2 → ℕ
  outcome := id

/-- The utility is one at `(0, 0)` and zero everywhere else. -/
def natChooseUtility : Utility natChoose.signature :=
  fun outcome _ => if outcome 0 = 0 ∧ outcome 1 = 0 then 1 else 0

/-- The pure profile where both players choose zero. -/
abbrev natChooseZero : Profile natChoose.signature :=
  fun _ => 0

/-- `(0, 0)` is a Nash equilibrium in the canonical semantic predicate. No
finite action capability is available or needed. -/
theorem natChooseZero_isNash :
    IsNash natChoose.toGameForm (euPreference natChooseUtility)
      natChooseZero := by
  rw [isNash_iff]
  intro who replacement
  fin_cases who <;>
    by_cases hreplacement : replacement = 0 <;>
      simp [natChoose, natChooseUtility, natChooseZero, Profile.update,
        hreplacement]

/-- For player zero, action zero is dominant even though the action carrier is
countably infinite. -/
theorem natChooseZero_isDominant_zero :
    IsDominant natChoose.toGameForm (euPreference natChooseUtility) 0 0 := by
  intro alternative profile
  by_cases hopponent : profile 1 = 0
  · by_cases halternative : alternative = 0
    · simp [natChoose, natChooseUtility, Profile.update,
        hopponent, halternative]
    · simp [natChoose, natChooseUtility, Profile.update,
        hopponent, halternative]
  · simp [natChoose, natChooseUtility, Profile.update,
      hopponent]

end GameTheory.Examples.NFG
