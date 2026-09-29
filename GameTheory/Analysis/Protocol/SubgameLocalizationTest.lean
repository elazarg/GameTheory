/-
# Nash and subgame perfection separate at an unreached subgame

The incumbent exits at the root and would punish at the decision. Exiting is
Nash for the exit-preferring utility, but punishing at the unreached decision is
not optimal there, so Nash does not imply subgame perfection. The generic
witnesses then give both separations of the preservation properties: a
continuation game whose equilibria follow from subgame perfection but not from
Nash, and a strategic form whose compilation into the sequential game
preserves Nash but not subgame perfection.
-/

import GameTheory.Analysis.Protocol.SubgameLocalization
import GameTheory.Tests.SubgamePerfect

noncomputable section

namespace GameTheory.Tests.SubgameLocalization

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.SubgamePerfect

instance : Fintype State :=
  ⟨{.root, .decision, .exited, .punished, .rewarded}, by intro state; cases state <;> simp⟩

/-- Utilities observe the reached state only. -/
def observe (history : arena.History) : State := history.state

def utility : State → Unit → ℝ
  | .exited, _ => 2
  | .rewarded, _ => 1
  | _, _ => 0

theorem utility_observe : (fun history : arena.History => utility (observe history) ()) =
    fun history => payoff history () := by
  funext history
  rcases history with ⟨state, trace⟩
  cases state <;> rfl

/-- Nothing steps back to the root, so the only history there is the initial one. -/
theorem eq_initHistory_of_root {state : arena.State} (trace : arena.Trace state)
    (hstate : state = .root) : (⟨state, trace⟩ : arena.History) = arena.initHistory := by
  cases trace with
  | start => rfl
  | @extend source _ _ joint isLegal realized =>
      exfalso
      subst hstate
      cases source <;> simp only [arena] at realized <;> (try split at realized) <;>
        simp at realized

/-- The history at the decision state is unique. -/
theorem eq_decisionHistory (history : arena.History) (hstate : history.state = .decision) :
    history = decisionHistory := by
  rcases history with ⟨state, trace⟩
  simp only at hstate
  cases trace with
  | start => simp at hstate
  | @extend source _ prior joint isLegal realized =>
      subst hstate
      cases source with
      | root =>
          have hprior := eq_initHistory_of_root prior rfl
          simp only [ExecutionProtocol.initHistory, ExecutionProtocol.History.mk.injEq,
            true_and] at hprior
          subst hprior
          have hjoint : joint () = some .enter := by
            by_contra hne
            have hexit : arena.step State.root ⟨joint, isLegal⟩ = PMF.pure .exited := by
              cases hchoice : joint () with
              | none => simp [arena, hchoice]
              | some action => cases action <;> simp_all [arena]
            rw [hexit, PMF.mem_support_pure_iff] at realized
            cases realized
          have hsame : joint = enterJoint := funext fun _ => hjoint
          subst hsame
          rfl
      | decision =>
          exfalso
          simp only [arena] at realized
          split at realized <;> simp at realized
      | exited => simp [arena] at realized
      | punished => simp [arena] at realized
      | rewarded => simp [arena] at realized

theorem decisionHistory_isSubgameRoot : model.IsSubgameRoot decisionHistory := by
  intro who inside outside hinside hinsideTerm _ _ _ hinfo
  have hstate : inside.state = outside.state := by
    have hinfo' : signals.infoOf () inside.trace = signals.infoOf () outside.trace := hinfo
    rwa [signals_infoOf_state, signals_infoOf_state] at hinfo'
  obtain ⟨fuel, hreach⟩ := hinside
  have hin : inside = decisionHistory := by
    cases hreach with
    | refl => rfl
    | step joint isLegal realized rest =>
        exfalso
        have hchild : arena.terminal (decisionHistory.extend isLegal realized).state := by
          have hmem := realized
          simp only [decisionHistory, arena] at hmem
          split at hmem <;> simp_all
        have := rest.eq_of_terminal hchild
        subst this
        exact hinsideTerm hchild
  subst hin
  rw [eq_decisionHistory outside hstate.symm]
  exact ExecutionProtocol.HistoryReaches.refl _ _

theorem root_holds (who : Unit) (deviation : model.Policy who) :
    (model.rootComparison arena_wellFoundedPlay observe incumbentProfile who deviation).Holds
      (utility · who) := by
  cases who
  rw [IncentiveComparison.holds_iff]
  simp only [InformationModel.rootComparison, InformationModel.continuationComparison,
    InformationModel.historyPlay, expect_map, Function.comp_def]
  rw [utility_observe]
  change arena.historyBackwardValue arena_wellFoundedPlay _ _ _ ≤
    arena.historyBackwardValue arena_wellFoundedPlay _ _ _
  rw [incumbent_value_root]
  exact historyBackwardValue_le_two _ _

theorem decision_fails :
    ¬ (model.continuationComparison (model.historyPlay arena_wellFoundedPlay) observe
        incumbentProfile () (⟨decisionHistory, decisionHistory_isSubgameRoot⟩,
          rewardingPolicy)).Holds (utility · ()) := by
  rw [IncentiveComparison.holds_iff]
  simp only [InformationModel.continuationComparison, InformationModel.historyPlay, expect_map,
    Function.comp_def]
  rw [utility_observe]
  change ¬ arena.historyBackwardValue arena_wellFoundedPlay _ _ _ ≤
    arena.historyBackwardValue arena_wellFoundedPlay _ _ _
  rw [incumbent_value_decision, rewarding_value_decision]
  norm_num

/-- Nash does not imply subgame perfection at the exiting incumbent. -/
theorem nash_not_implies_subgamePerfect :
    ¬ IncentiveComparison.Implies
      (model.rootComparison arena_wellFoundedPlay observe incumbentProfile)
      (model.continuationComparison (model.historyPlay arena_wellFoundedPlay) observe
        incumbentProfile) :=
  fun himplies => decision_fails (himplies utility root_holds () _)

/-- **Descent fails.** Some unreached continuation game of this source has its
equilibria implied by subgame perfection but not by Nash. -/
theorem descent_fails :
    ∃ (root : arena.History) (_ : model.IsSubgameRoot root),
      model.rootReach arena_wellFoundedPlay incumbentProfile root = 0 ∧
      IncentiveComparison.Implies
        (model.continuationComparison (model.historyPlay arena_wellFoundedPlay) observe
          incumbentProfile)
        (equilibriumComparison (model.subgameForm arena_wellFoundedPlay root)
          (PMF.pure incumbentProfile) (DeviationScheme.unilateralConstant _) observe) ∧
      ¬ IncentiveComparison.Implies
        (model.rootComparison arena_wellFoundedPlay observe incumbentProfile)
        (equilibriumComparison (model.subgameForm arena_wellFoundedPlay root)
          (PMF.pure incumbentProfile) (DeviationScheme.unilateralConstant _) observe) :=
  model.exists_subgameForm_separating arena_wellFoundedPlay observe incumbentProfile
    nash_not_implies_subgamePerfect

/-- **Ascent fails.** Compiling the strategic form into the sequential game
preserves Nash for every utility but not subgame perfection. -/
theorem ascent_fails :
    IncentiveComparison.Implies
        (equilibriumComparison (model.subgameForm arena_wellFoundedPlay arena.initHistory)
          (PMF.pure incumbentProfile) (DeviationScheme.unilateralConstant _) observe)
        (model.rootComparison arena_wellFoundedPlay observe incumbentProfile) ∧
      ¬ IncentiveComparison.Implies
        (equilibriumComparison (model.subgameForm arena_wellFoundedPlay arena.initHistory)
          (PMF.pure incumbentProfile) (DeviationScheme.unilateralConstant _) observe)
        (model.continuationComparison (model.historyPlay arena_wellFoundedPlay) observe
          incumbentProfile) := by
  obtain ⟨hnash, hiff⟩ := model.strategicForm_implies_iff arena_wellFoundedPlay observe
    incumbentProfile
  exact ⟨hnash, fun h => nash_not_implies_subgamePerfect (hiff.1 h)⟩

end GameTheory.Tests.SubgameLocalization
