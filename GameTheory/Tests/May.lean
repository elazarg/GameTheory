/-
# May theorem fixture

A three-voter strict majority exercises the characterization away from ties
and empty electorates.
-/

import GameTheory.Core.May

namespace GameTheory.Tests.May

def twoToOne : Fin 3 → SignType
  | 0 => 1
  | 1 => 1
  | 2 => -1

theorem tally_twoToOne : GameTheory.May.tally twoToOne = 1 := by
  decide

theorem majority_twoToOne : GameTheory.May.majority twoToOne = 1 := by
  rw [GameTheory.May.majority, tally_twoToOne]
  exact sign_one

theorem characterized_rule_twoToOne
    (rule : (Fin 3 → SignType) → SignType)
    (haxioms : GameTheory.May.IsAnonymous rule ∧
      GameTheory.May.IsNeutral rule ∧
      GameTheory.May.IsPositivelyResponsive rule) :
    rule twoToOne = 1 := by
  rw [(GameTheory.May.characterization rule).2 haxioms]
  exact majority_twoToOne

end GameTheory.Tests.May
