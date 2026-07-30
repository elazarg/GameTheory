/-
# Observable cheap-talk examples

Both pure equilibria of Battle of the Sexes survive the observable one-stage
cheap-talk extension as ordinary Nash equilibria.
-/

import GameTheory.Core.CheapTalk
import GameTheory.Examples.Classic

namespace GameTheory.Examples.CheapTalk

/-- Two public messages, with `false` as the babbling default. -/
def battleMessages : battleOfTheSexes.toForm.CheapTalkExtension where
  Message _ := Bool
  default _ := false

/-- Opera coordination survives when a deviator may replace both its public
message and its full message-contingent venue plan. -/
theorem battleOfTheSexes_opera_babbling_isNash :
    IsNash battleMessages.form
      (euPreference battleOfTheSexes.utility)
      (battleMessages.embedProfile bothOpera) :=
  battleMessages.babbling_isNash
    (preference := euPreference battleOfTheSexes.utility)
    battleOfTheSexes_bothOpera_isNash

/-- The same generic theorem embeds the football equilibrium. -/
theorem battleOfTheSexes_football_babbling_isNash :
    IsNash battleMessages.form
      (euPreference battleOfTheSexes.utility)
      (battleMessages.embedProfile bothFootball) :=
  battleMessages.babbling_isNash
    (preference := euPreference battleOfTheSexes.utility)
    battleOfTheSexes_bothFootball_isNash

end GameTheory.Examples.CheapTalk
