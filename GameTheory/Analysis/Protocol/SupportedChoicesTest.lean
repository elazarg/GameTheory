/-
# A uniformly worse choice is never played

In the single decision between `0` and `1`, choosing `1` earns one and choosing
`0` earns nothing, whatever else happens. Every sequentially rational
assessment on terminal play therefore gives `0` probability zero, with no
assumption on its beliefs.
-/

import GameTheory.Analysis.Protocol.SupportedChoices
import GameTheory.Analysis.Protocol.InfiniteCarrierExistenceTest

noncomputable section

namespace GameTheory.Tests.SupportedChoices

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.Tests.InfiniteCarrierExistence

/-- Choosing `1` earns one. -/
def reward (_ : Unit) (history : execution.History) : ℝ :=
  if history.state = some 1 then 1 else 0

/-- The history certificate of the decision. -/
abbrev certificate : execution.WellFoundedHistories :=
  let _ := Fintype.ofFinite execution.History
  execution.wellFoundedHistories_of_fintype

theorem root_not_terminal : ¬ execution.terminal execution.initHistory.state := by
  simp [execution]

/-- Terminal play from the root is scored by the root choice alone. -/
theorem root_value (policies : (i : Unit) → information.BehavioralPolicy i) :
    expect (information.runBehavioralTerminalFrom certificate policies execution.initHistory)
        (reward ()) =
      expect (policies () 1) fun choice => if choice.1 = some 1 then (1 : ℝ) else 0 := by
  have legal (choice : information.Choice () 1) :
      execution.Legal execution.initHistory.state (execution.singletonJoint () choice.1) :=
    ExecutionProtocol.legal_of_legalOption root_not_terminal fun other => by
      cases other
      simpa using (information.menu_adequate () execution.initHistory.trace choice.1).mp choice.2
  have realized (choice : information.Choice () 1) :
      some (choice.1.getD 0) ∈
        (execution.step execution.initHistory.state ⟨_, legal choice⟩).support := by
    change some (choice.1.getD 0) ∈ (PMF.pure (some (choice.1.getD 0))).support
    simp
  let reached (choice : information.Choice () 1) : execution.History :=
    execution.initHistory.extend (legal choice) (realized choice)
  have hlaw : information.runBehavioralTerminalFrom certificate policies execution.initHistory =
      (policies () 1).map reached := by
    rw [information.runBehavioralTerminalFrom_of_not_terminal certificate policies
        root_not_terminal,
      information.behavioralJoint_eq_map_of_at_most_one_active policies _ root_not_terminal ()
        (fun i _ => by cases i; rfl),
      PMF.bind_map]
    refine Eq.trans ?_ (PMF.bind_pure_comp reached (policies () 1))
    refine bind_congr_on_support _ fun choice _ => ?_
    simp only [Function.comp_apply]
    change (PMF.pure (some (choice.1.getD 0))).bindOnSupport _ = _
    refine (PMF.pure_bindOnSupport _ _).trans ?_
    exact ExecutionProtocol.randomizedBackwardLaw_of_terminal (E := execution) ⟨_, rfl⟩
  rw [hlaw, expect_map]
  congr 1
  funext choice
  cases hchoice : choice.1 with
  | none => simp [reward, reached, hchoice]
  | some a => simp [reward, reached, hchoice]

/-- The root decision site. -/
def rootSite : information.InformationSite () :=
  ⟨1, ⟨⟨execution.initHistory, rfl⟩, root_not_terminal, 0, by simp⟩⟩

theorem rootSite_allNonterminal : InformationSite.AllNonterminal information rootSite :=
  fun history => by
    rw [eq_initHistory_of_info_one history.1 history.2]
    exact root_not_terminal

def zeroChoice : information.Choice () 1 := ⟨some 0, by simp⟩
def oneChoice : information.Choice () 1 := ⟨some 1, by simp⟩

theorem committed_value (strategy : (i : Unit) → information.BehavioralPolicy i)
    (choice : information.Choice () 1) (history : information.InformationHistory () rootSite.1) :
    expect (information.runBehavioralTerminalFrom certificate
        (Profile.update (sig := information.behavioralSignature) strategy ()
          ((strategy ()).commit rootSite.1 choice)) history.1) (reward ()) =
      if choice.1 = some 1 then 1 else 0 := by
  have hcommit : (strategy ()).commit rootSite.1 choice 1 = PMF.pure choice :=
    BehavioralPolicy.commit_self (strategy ()) rootSite.1 choice
  rw [eq_initHistory_of_info_one history.1 history.2, root_value, Profile.update_same,
    hcommit, expect_pure]

/-- **No sequentially rational assessment plays `0`,** whatever its beliefs. -/
theorem sequentiallyRational_never_plays_zero
    (assessment : information.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational certificate reward) :
    zeroChoice ∉ (assessment.strategy () 1).support := by
  refine assessment.not_supported_choice_of_uniform_gap
    (information.runBehavioralTerminalFrom certificate) rootSite
    (information.runnerFactorsAt_terminal certificate decisionRecall.actsOnceWhereItMatters
      rootSite_allNonterminal)
    (reward ()) (rational () rootSite) (fun _ => payoffIntegrable_of_finite _ _) zeroChoice
    ((assessment.strategy ()).commit rootSite.1 oneChoice) 0 1 (by norm_num)
    (fun history => ?_) (fun history => ?_)
  · rw [committed_value]
    simp [zeroChoice]
  · rw [committed_value]
    simp [oneChoice]

end GameTheory.Tests.SupportedChoices
