/-
# Probes for the strategic-form compilation

The compilation is only worth anything if the compiled `GameForm` still
distinguishes strategies, and if the static concepts really do apply to it
without knowing a protocol was involved. Both are checked here on the coin game
from `GameTheory.Tests.Execution`.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility
import GameTheory.Tests.Candidates

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability

/-- Always take, as a state policy. -/
def takeState : coinThenMove.StatePolicy () := fun _ _ => ⟨.take, Set.mem_univ _⟩

/-- Always leave, as a state policy. -/
def leaveState : coinThenMove.StatePolicy () := fun _ _ => ⟨.leave, Set.mem_univ _⟩

/-- The one-player profile that always takes. -/
def takeProfile : Profile coinThenMove.strategicSignature := fun _ => takeState

/-- The one-player profile that always leaves. -/
def leaveProfile : Profile coinThenMove.strategicSignature := fun _ => leaveState

theorem chooserOf_takeProfile : coinThenMove.chooserOf takeProfile = takePolicy := by
  funext state hterm
  refine Subtype.ext (funext fun i => ?_)
  by_cases hactive : state = Spot.heads ∨ state = Spot.tails <;>
    simp [ExecutionProtocol.chooserOf, ExecutionProtocol.jointOf, takePolicy, takeProfile,
      takeState, hactive]

theorem chooserOf_leaveProfile : coinThenMove.chooserOf leaveProfile = leavePolicy := by
  funext state hterm
  refine Subtype.ext (funext fun i => ?_)
  by_cases hactive : state = Spot.heads ∨ state = Spot.tails <;>
    simp [ExecutionProtocol.chooserOf, ExecutionProtocol.jointOf, leavePolicy, leaveProfile,
      leaveState, hactive]

theorem play_takeProfile :
    (coinThenMove.toGameForm 2).play takeProfile = FinDist.pure .tookIt := by
  rw [ExecutionProtocol.toGameForm_play, chooserOf_takeProfile, runFor_two_take]

theorem play_leaveProfile :
    (coinThenMove.toGameForm 2).play leaveProfile = FinDist.pure .leftIt := by
  rw [ExecutionProtocol.toGameForm_play, chooserOf_leaveProfile, runFor_two_leave]

/-- **Probe.** The compiled form still separates the two strategies, so the
compilation did not collapse the game. -/
theorem compiled_form_separates :
    (coinThenMove.toGameForm 2).play takeProfile ≠
      (coinThenMove.toGameForm 2).play leaveProfile := by
  rw [play_takeProfile, play_leaveProfile]
  intro hequal
  have hmass := congrArg (fun law => FinDist.prob law Spot.tookIt) hequal
  simp [FinDist.prob_pure_eq_ite] at hmass

/-! ## The static concepts apply unchanged

Nothing below mentions a protocol, a trace, a chooser, or a horizon. -/

/-- A payoff on stopping states: taking is worth more than leaving. -/
def takeIsBetter : Utility coinThenMove.strategicSignature :=
  fun state _ => if state = Spot.tookIt then 1 else 0

/-- The compiled game, viewed purely as a static utility game. -/
def compiledGame : UtilityGame Unit where
  form := coinThenMove.toGameForm 2
  utility := takeIsBetter

/-- Expected utility of the compiled form is computed by the static machinery,
with no protocol vocabulary in sight. -/
theorem expectedUtility_takeProfile :
    expectedUtility takeIsBetter () ((coinThenMove.toGameForm 2).play takeProfile) = 1 := by
  rw [play_takeProfile, expectedUtility_pure]
  simp [takeIsBetter]

theorem expectedUtility_leaveProfile :
    expectedUtility takeIsBetter () ((coinThenMove.toGameForm 2).play leaveProfile) = 0 := by
  rw [play_leaveProfile, expectedUtility_pure]
  simp [takeIsBetter]

/-- And the two are ranked, so the compiled game has content for the static
solution concepts to act on. -/
theorem taking_is_preferred :
    euPreference takeIsBetter ()
      ((coinThenMove.toGameForm 2).play takeProfile)
      ((coinThenMove.toGameForm 2).play leaveProfile) := by
  rw [euPreference_apply, expectedUtility_takeProfile, expectedUtility_leaveProfile]
  norm_num

end GameTheory.Tests
