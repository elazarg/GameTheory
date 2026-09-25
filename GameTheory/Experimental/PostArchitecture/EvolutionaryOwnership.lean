/-
# EXP-044: evolutionary static/dynamic ownership

This witness exercises the canonical static ESS kernel and its one-way Nash
bridge. The generic definitions live only in `GameTheory.Evolutionary`.
-/

import GameTheory.Evolutionary

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.EvolutionaryOwnership

open GameTheory GameTheory.Evolutionary

/-- A mutant ties the resident against the resident, but loses the second
encounter comparison. -/
def tieBreakPayoff : Bool → Bool → ℝ
  | true, true => 1
  | false, true => 1
  | true, false => 2
  | false, false => 0

theorem mutant_ties_against_resident :
    tieBreakPayoff true true = tieBreakPayoff false true := rfl

theorem resident_wins_tie_break :
    tieBreakPayoff true false > tieBreakPayoff false false := by
  norm_num [tieBreakPayoff]

theorem true_isESS : IsESS tieBreakPayoff true := by
  constructor
  · intro mutant
    cases mutant <;> norm_num [tieBreakPayoff]
  · intro mutant _ hne
    cases mutant
    · norm_num [tieBreakPayoff]
    · exact False.elim (hne rfl)

theorem true_isNash_symmetric :
    IsNash (symmetricForm Bool) (euPreference (symmetricUtility tieBreakPayoff))
      (residentProfile true) :=
  true_isESS.isNash_symmetric

end GameTheory.Experimental.PostArchitecture.EvolutionaryOwnership