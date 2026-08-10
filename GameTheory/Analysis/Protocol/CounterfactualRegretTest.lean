/-
# Hostile counterfactual-regret witness

Nature chooses a hidden bit before one player acts at a two-history information
site.  Matching the `true` state pays twice as much as matching `false`, so a
pure-`true` replacement is profitable and a pure-`false` replacement is
strictly harmful relative to the fully mixed policy.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Analysis.Protocol.EFGTest

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRegretTest

open GameTheory Probability Protocol
open GameTheory.Protocol.InformationModel
open GameTheory.Tests.EFG

local instance : Fintype execution.History := game.historyFintype

local instance (who : Player) (site : information.InformationSite who) :
    Fintype (information.InformationHistory who site.1) := by
  classical
  infer_instance

/-- Matching the hidden `true` state is worth two; matching `false` is worth
one.  The asymmetry makes the two pure policies discriminating controls. -/
def weightedMatchingPayoff (history : execution.History) : ℝ :=
  match history.state with
  | .terminal hidden _ action =>
      if action .player = some hidden then if hidden then 2 else 1 else 0
  | _ => 0

/-- The canonical continuation runner reduces the weighted terminal payoff to
the alternative policy's action law at the shared information state. -/
theorem runBehavioralFrom_decision_weightedMatchingPayoff
    (hidden : Bool)
    (alternative : information.BehavioralPolicy Player.player) :
    (information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative) 2
      (decisionHistory hidden)).expect weightedMatchingPayoff =
        (alternative .acting).expect fun choice =>
          if choice.1 = some hidden then if hidden then 2 else 1 else 0 := by
  let drawLaw :
      FinDist ((i : Player) →
        information.Choice i
          (information.infoOf i (decisionHistory hidden).trace)) :=
    FinDist.pi fun i =>
      Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative i
        (information.infoOf i (decisionHistory hidden).trace)
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 1
      (decision_not_terminal hidden),
    FinDist.expect_bind, InformationModel.randomizedChooser,
    InformationModel.behavioralJoint, FinDist.expect_map]
  have hmarginal :
      FinDist.map (fun draws => (draws Player.player).1) drawLaw =
        FinDist.map (fun choice => choice.1) (alternative .acting) := by
    have hchoice :
        FinDist.map (fun draws => draws Player.player) drawLaw =
          alternative
            (information.infoOf Player.player
              (decisionHistory hidden).trace) := by
      unfold drawLaw
      rw [FinDist.map_apply_pi, Profile.update_same]
    have hprojected :
        FinDist.map (fun draws => (draws Player.player).1) drawLaw =
          FinDist.map (fun choice => choice.1)
            (alternative
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) := by
      have hcongr := congrArg
        (fun law : FinDist
            (information.Choice Player.player
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) =>
          FinDist.map (fun choice => choice.1) law)
        hchoice
      simpa only [FinDist.map_comp, Function.comp_def] using hcongr
    exact hprojected.trans (by rw [infoOf_decisionHistory])
  calc
    _ = drawLaw.expect (fun draws =>
        if (draws Player.player).1 = some hidden then
          if hidden then 2 else 1 else 0) := by
      apply FinDist.expect_congr
      intro draws _hdraws
      simp [execution, decisionHistory, weightedMatchingPayoff,
        ExecutionProtocol.runRandomizedFor_of_terminal]
    _ = (FinDist.map (fun draws => (draws Player.player).1) drawLaw).expect
          (fun choice : Option Bool =>
            if choice = some hidden then if hidden then 2 else 1 else 0) := by
      rw [FinDist.expect_map]
    _ = (FinDist.map (fun choice => choice.1) (alternative .acting)).expect
          (fun choice : Option Bool =>
            if choice = some hidden then if hidden then 2 else 1 else 0) := by
      rw [hmarginal]
    _ = (alternative .acting).expect fun choice =>
          if choice.1 = some hidden then if hidden then 2 else 1 else 0 := by
      rw [FinDist.expect_map]

/-- Before the information site the focal player has only supplied the forced
inactive choice, so its own reach is one on both hidden histories. -/
theorem playerReachProbability_decision (hidden : Bool) :
    information.playerReachProbability fullyMixedBehavioralProfile .player
      (decisionHistory hidden).trace = 1 := by
  simp only [decisionHistory, decisionTrace,
    InformationModel.playerReachProbability,
    InformationModel.playerStepProb,
    InformationModel.choicesOfLegal]
  rw [one_mul]
  show (fullyMixedBehavioralPolicy .waiting).prob ⟨none, _⟩ = 1
  simp [fullyMixedBehavioralPolicy]

/-- The common-own-reach premise is proved over the entire information fiber,
not assumed from the two named representatives. -/
theorem commonPlayerReach_acting
    (history : information.InformationHistory .player actingSite.1) :
    information.playerReachProbability fullyMixedBehavioralProfile .player
      history.1.trace = 1 := by
  obtain ⟨hidden, hhistory⟩ :=
    history_eq_decisionHistory_of_info_acting history.1 history.2
  have hsubtype : history = decisionInformationHistory hidden :=
    Subtype.ext hhistory
  subst history
  exact playerReachProbability_decision hidden

/-- Pure commitments used by the action-local regret controls. -/
def trueChoice : information.Choice .player actingSite.1 :=
  ⟨some true, by simp [actingSite, information]⟩

def falseChoice : information.Choice .player actingSite.1 :=
  ⟨some false, by simp [actingSite, information]⟩

theorem commit_true_eq_alwaysTrue :
    fullyMixedBehavioralPolicy.commit actingSite.1 trueChoice =
      alwaysTruePolicy := by
  funext view
  cases view <;>
    simp [BehavioralPolicy.commit, actingSite, trueChoice,
      fullyMixedBehavioralPolicy, alwaysTruePolicy]
  congr 1

theorem commit_false_eq_alwaysFalse :
    fullyMixedBehavioralPolicy.commit actingSite.1 falseChoice =
      behavioralPolicy := by
  funext view
  cases view <;>
    simp [BehavioralPolicy.commit, actingSite, falseChoice,
      fullyMixedBehavioralPolicy, behavioralPolicy]
  congr 1

/-- Canonical Bayes continuation value of the profitable pure replacement. -/
theorem bayesContinuationValue_alwaysTrue :
    bayesContinuationValue information fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) alwaysTruePolicy
      weightedMatchingPayoff 2 = 1 := by
  unfold bayesContinuationValue behavioralContinuationValue
  rw [show information.bayesBelief fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
        (informationMass_fullyMixed_pos actingSite) = decisionBelief by
      exact fullyMixedAssessment_belief_acting,
    decisionBelief, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure,
    runBehavioralFrom_decision_weightedMatchingPayoff,
    runBehavioralFrom_decision_weightedMatchingPayoff]
  simp [alwaysTruePolicy]

/-- Canonical Bayes value of the prescribed fully mixed policy. -/
theorem bayesContinuationValue_fullyMixed :
    bayesContinuationValue information fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) fullyMixedBehavioralPolicy
      weightedMatchingPayoff 2 = 3 / 4 := by
  unfold bayesContinuationValue behavioralContinuationValue
  rw [show information.bayesBelief fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
        (informationMass_fullyMixed_pos actingSite) = decisionBelief by
      exact fullyMixedAssessment_belief_acting,
    decisionBelief, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure,
    runBehavioralFrom_decision_weightedMatchingPayoff,
    runBehavioralFrom_decision_weightedMatchingPayoff]
  simp [fullyMixedBehavioralPolicy, fairCoin, FinDist.expect_map,
    FinDist.expect_mix]
  norm_num

/-- Canonical Bayes value of the strictly harmful pure replacement. -/
theorem bayesContinuationValue_alwaysFalse :
    bayesContinuationValue information fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) behavioralPolicy
      weightedMatchingPayoff 2 = 1 / 2 := by
  unfold bayesContinuationValue behavioralContinuationValue
  rw [show information.bayesBelief fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
        (informationMass_fullyMixed_pos actingSite) = decisionBelief by
      exact fullyMixedAssessment_belief_acting,
    decisionBelief, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.expect_pure,
    runBehavioralFrom_decision_weightedMatchingPayoff,
    runBehavioralFrom_decision_weightedMatchingPayoff]
  simp [behavioralPolicy]
  norm_num

/-- The profitable replacement has exact positive counterfactual regret.  This
directly consumes the scaled canonical Bayes-gain identity. -/
theorem counterfactualRegret_alwaysTrue :
    counterfactualRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 alwaysTruePolicy = 1 / 4 := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
      information fullyMixedBehavioralProfile .player actingSite
      (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) 1 commonPlayerReach_acting
      alwaysTruePolicy weightedMatchingPayoff 2
  rw [informationMass_fullyMixed_acting,
    bayesContinuationValue_alwaysTrue,
    show fullyMixedBehavioralProfile .player = fullyMixedBehavioralPolicy by rfl,
    bayesContinuationValue_fullyMixed] at hscaled
  norm_num at hscaled
  exact hscaled.symm

/-- The losing control has exact negative counterfactual regret. -/
theorem counterfactualRegret_alwaysFalse :
    counterfactualRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 behavioralPolicy = -(1 / 4) := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
      information fullyMixedBehavioralProfile .player actingSite
      (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) 1 commonPlayerReach_acting
      behavioralPolicy weightedMatchingPayoff 2
  rw [informationMass_fullyMixed_acting,
    bayesContinuationValue_alwaysFalse,
    show fullyMixedBehavioralProfile .player = fullyMixedBehavioralPolicy by rfl,
    bayesContinuationValue_fullyMixed] at hscaled
  norm_num at hscaled
  exact hscaled.symm

/-- The action-local API retains the profitable control exactly. -/
theorem counterfactualActionRegret_true :
    counterfactualActionRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 trueChoice = 1 / 4 := by
  rw [counterfactualActionRegret,
    show fullyMixedBehavioralProfile .player = fullyMixedBehavioralPolicy by rfl,
    commit_true_eq_alwaysTrue]
  exact counterfactualRegret_alwaysTrue

/-- The action-local API also retains the strictly harmful control. -/
theorem counterfactualActionRegret_false :
    counterfactualActionRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 falseChoice = -(1 / 4) := by
  rw [counterfactualActionRegret,
    show fullyMixedBehavioralProfile .player = fullyMixedBehavioralPolicy by rfl,
    commit_false_eq_alwaysFalse]
  exact counterfactualRegret_alwaysFalse

/-- The sign bridge itself is exercised on the profitable replacement. -/
theorem profitable_counterfactual_iff_profitable_bayes :
    0 < counterfactualRegret information fullyMixedBehavioralProfile .player
        actingSite weightedMatchingPayoff 2 alwaysTruePolicy ↔
      0 < bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite) alwaysTruePolicy
          weightedMatchingPayoff 2 -
        bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite)
          (fullyMixedBehavioralProfile .player) weightedMatchingPayoff 2 :=
  counterfactualRegret_pos_iff_bayesGain_pos information
    fullyMixedBehavioralProfile .player actingSite
    (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite) 1 (by norm_num)
    commonPlayerReach_acting alwaysTruePolicy weightedMatchingPayoff 2

/-- The named weaker certificate is enough for the sign theorem even though
this fixture does not claim global perfect recall. -/
theorem profitable_counterfactual_iff_profitable_bayes_of_commonReach :
    0 < counterfactualRegret information fullyMixedBehavioralProfile .player
        actingSite weightedMatchingPayoff 2 alwaysTruePolicy ↔
      0 < bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite) alwaysTruePolicy
          weightedMatchingPayoff 2 -
        bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite)
          (fullyMixedBehavioralProfile .player) weightedMatchingPayoff 2 :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach information
    fullyMixedBehavioralProfile .player actingSite
    (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite)
    ⟨1, commonPlayerReach_acting⟩ alwaysTruePolicy weightedMatchingPayoff 2

end GameTheory.Analysis.Protocol.CounterfactualRegretTest
