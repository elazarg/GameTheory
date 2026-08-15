/-
# Probes for the strategic-form compilation

The state-policy compilation is checked on the coin game from
`GameTheory.Tests.Execution`. The information-local compilation is checked on
the hostile hidden-card model: the compiled law retains both hidden states while
the blind player's strategy is forced by its type to answer them alike. Finally
the repeated-information-state counterexample and the perfect-recall control
check that static mixing agrees with behavioral play exactly where the
compiler's hypotheses say it does.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility
import GameTheory.Tests.Execution
import GameTheory.Tests.Information
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

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

/-- The two-step state law needed by the strategic compilation probe. Kept
local to this test so it can coexist with the hidden-card test module. -/
theorem runFor_two_take_strategic :
    coinThenMove.runFor takePolicy 2 .chance = FinDist.pure .tookIt := by
  refine FinDist.ext_of_prob fun spot => ?_
  rw [ExecutionProtocol.runFor_succ_of_chance takePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor takePolicy 1 s).prob spot) = _
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_take, runFor_one_tails_take]
  ring

/-- The matching leave law for the strategic compilation probe. -/
theorem runFor_two_leave_strategic :
    coinThenMove.runFor leavePolicy 2 .chance = FinDist.pure .leftIt := by
  refine FinDist.ext_of_prob fun spot => ?_
  rw [ExecutionProtocol.runFor_succ_of_chance leavePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor leavePolicy 1 s).prob spot) = _
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_leave, runFor_one_tails_leave]
  ring

theorem play_takeProfile :
    (coinThenMove.toGameForm 2).play takeProfile = FinDist.pure .tookIt := by
  rw [ExecutionProtocol.toGameForm_play, chooserOf_takeProfile, runFor_two_take_strategic]

theorem play_leaveProfile :
    (coinThenMove.toGameForm 2).play leaveProfile = FinDist.pure .leftIt := by
  rw [ExecutionProtocol.toGameForm_play, chooserOf_leaveProfile, runFor_two_leave_strategic]

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

/-! ## Information-local compilation

The hidden-card model is hostile in two directions at once. Nature reaches two
different dealt states with positive probability, and the blind player cannot
distinguish them. The compiled strategy type must preserve both facts.
-/

/-- The first compiled step is exactly the existing deal law, after the
ordinary projection from histories to their current states. No state evaluator
was introduced to prove this. -/
theorem information_play_first_deal
    (profile : Profile dealModel.strategicSignature) :
    FinDist.map ExecutionProtocol.History.state
        ((dealModel.toGameForm 1).play profile) =
      FinDist.map dealOf fairCoin := by
  rw [InformationModel.toGameForm_play, InformationModel.run, InformationModel.runFrom,
    ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ 0 shuffle_not_terminal,
    FinDist.map_bindOnSupport]
  show (FinDist.map dealOf fairCoin).bindOnSupport (fun target realized => _) =
    FinDist.map dealOf fairCoin
  calc
    _ = (FinDist.map dealOf fairCoin).bind FinDist.pure := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      simp
    _ = _ := by simp

/-- Both genuinely different hidden states remain in the compiled outcome law.
Thus retaining histories did not collapse nature's hidden branch. -/
theorem information_compilation_retains_both_hidden_states
    (profile : Profile dealModel.strategicSignature) (card : Card) :
    Table.dealt card ∈
      (FinDist.map ExecutionProtocol.History.state
        ((dealModel.toGameForm 1).play profile)).support := by
  rw [information_play_first_deal]
  exact dealt_mem_support card

/-- Yet the blind coordinate of every compiled profile answers those states
alike. Information locality remains enforced by the strategy type, not by a
predicate added during compilation. -/
theorem information_compilation_preserves_blind_locality
    (profile : Profile dealModel.strategicSignature) :
    (profile .blind).act (dealSignals.infoOf .blind (dealHistory .high)) =
      (profile .blind).act (dealSignals.infoOf .blind (dealHistory .low)) :=
  every_blind_policy_agrees (profile .blind)

/-! ## Behavioral play versus static mixing

The static mixed extension draws one whole information-local policy per player.
Behavioral play draws locally during execution. The repeated-information-state
model separates them; the recall model on the same protocol identifies them.
-/

/-- Without the no-revisit hypothesis, behavioral compilation is genuinely not
the static mixed extension of the pure-policy compilation. -/
theorem compiled_behavioral_ne_static_mixed_without_actsOnce :
    FinDist.map ExecutionProtocol.History.state
        ((Randomized.model.toBehavioralGameForm 2).play (fun _ => Randomized.coinPolicy)) ≠
      FinDist.map ExecutionProtocol.History.state
        (((Randomized.model.toGameForm 2).mixed).play
          (fun _ => Randomized.coinPolicy.toMixed)) := by
  rw [InformationModel.toBehavioralGameForm_play, InformationModel.toGameForm_mixed_play]
  exact Randomized.runBehavioral_ne_runMixed

/-- With the sharp no-revisit condition discharged, drawing every behavioral
choice in advance commutes with the compiled form. -/
theorem compiled_behavioral_eq_static_mixed_of_actsOnce
    (behavioral : Profile Randomized.recallModel.behavioralSignature) (horizon : ℕ) :
    ((Randomized.recallModel.toGameForm horizon).mixed).play
        (fun i => (behavioral i).toMixed) =
      (Randomized.recallModel.toBehavioralGameForm horizon).play behavioral :=
  InformationModel.toGameForm_mixed_play_toMixed
    (M := Randomized.recallModel)
    (Randomized.recallModel.actsOnceWhereItMatters_of_actsOnce
      Randomized.recall_actsOnceAtEachInfoState)
    behavioral horizon

/-- With the constraint-equivalence condition supplied by perfect recall, a
static mixed profile can conversely be read behaviorally after compilation. -/
theorem compiled_mixed_eq_behavioral_of_recall
    (mixed : (i : Unit) → Randomized.recallModel.MixedPolicy i) (horizon : ℕ) :
    ((Randomized.recallModel.toGameForm horizon).mixed).play mixed =
      (Randomized.recallModel.toBehavioralGameForm horizon).play
        (fun i => (mixed i).toBehavioral) :=
  InformationModel.toGameForm_mixed_play_toBehavioral
    (M := Randomized.recallModel)
    (InformationModel.constrainsAlike_of_perfectRecall Randomized.recall_perfectRecall)
    mixed horizon

end GameTheory.Tests
