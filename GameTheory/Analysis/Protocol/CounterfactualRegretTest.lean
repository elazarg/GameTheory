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

open GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Protocol.InformationModel
open GameTheory.Tests.EFG

local instance : Fintype execution.History := game.historyFintype

local instance (who : Player) (site : information.InformationSite who) :
    Fintype (information.InformationHistory who site.1) := by
  classical
  infer_instance

/-- Canonical guarded expectation for the finite witness carriers. -/
noncomputable def finiteExpect {α : Type*} [Fintype α]
    (law : PMF α) (payoff : α → ℝ) : ℝ :=
  expect law payoff (payoffIntegrable_of_finite law payoff)

private theorem finiteExpect_map {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (law : PMF α) (payoff : β → ℝ) :
    finiteExpect (PMF.map f law) payoff =
      finiteExpect law (payoff ∘ f) := by
  unfold finiteExpect
  exact expect_map f law payoff
    (payoffIntegrable_of_finite law (payoff ∘ f))
    (payoffIntegrable_of_finite (PMF.map f law) payoff)

private theorem finiteExpect_bind {α β : Type*} [Fintype α] [Fintype β]
    (law : PMF α) (kernel : α → PMF β) (payoff : β → ℝ) :
    finiteExpect (law.bind kernel) payoff =
      finiteExpect law (fun a => finiteExpect (kernel a) payoff) := by
  unfold finiteExpect
  let hbind := payoffIntegrable_of_finite (law.bind kernel) payoff
  let hcond := fun a => payoffIntegrable_of_finite (kernel a) payoff
  calc
    expect (law.bind kernel) payoff
        (payoffIntegrable_of_finite (law.bind kernel) payoff) =
      expect (law.bind kernel) payoff hbind := expect_proof_irrel ..
    _ = expect law (fun a => expect (kernel a) payoff (hcond a))
        (payoffIntegrable_bind_conditionalExpectation law kernel payoff hbind hcond) :=
      expect_bind_tower law kernel payoff hbind hcond
    _ = expect law (fun a => expect (kernel a) payoff
        (payoffIntegrable_of_finite (kernel a) payoff))
        (payoffIntegrable_of_finite law
          (fun a => expect (kernel a) payoff
            (payoffIntegrable_of_finite (kernel a) payoff))) := expect_proof_irrel ..

private theorem finiteExpect_mix {α : Type*} [Fintype α]
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : PMF α) (payoff : α → ℝ) :
    finiteExpect (mix t h0 h1 μ ν) payoff =
      t * finiteExpect μ payoff + (1 - t) * finiteExpect ν payoff := by
  unfold finiteExpect
  simpa only [expect_proof_irrel] using
    (expect_mix t h0 h1 μ ν payoff
      (payoffIntegrable_of_finite μ payoff)
      (payoffIntegrable_of_finite ν payoff))

/-- Matching the hidden `true` state is worth two; matching `false` is worth
one.  The asymmetry makes the two pure policies discriminating controls. -/
def weightedMatchingPayoff (history : execution.History) : ℝ :=
  match history.state with
  | .terminal hidden _ action =>
      if action .player = some hidden then if hidden then 2 else 1 else 0
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- The canonical continuation runner reduces the weighted terminal payoff to
the alternative policy's action law at the shared information state. -/
theorem runBehavioralFrom_decision_weightedMatchingPayoff
    (hidden : Bool)
    (alternative : information.BehavioralPolicy Player.player) :
    finiteExpect (information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative) 2
      (decisionHistory hidden)) weightedMatchingPayoff =
    finiteExpect (alternative .acting) (fun choice =>
          if choice.1 = some hidden then if hidden then 2 else 1 else 0) := by
  classical
  let drawLaw :
      PMF ((i : Player) →
        information.Choice i
          (information.infoOf i (decisionHistory hidden).trace)) :=
    independentProduct fun i =>
      Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative i
        (information.infoOf i (decisionHistory hidden).trace)
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 1
      (decision_not_terminal hidden),
    finiteExpect_bind, InformationModel.randomizedChooser,
    InformationModel.behavioralJoint, finiteExpect_map]
  have hmarginal :
      PMF.map (fun draws => (draws Player.player).1) drawLaw =
        PMF.map (fun choice => choice.1) (alternative .acting) := by
    have hchoice :
        PMF.map (fun draws => draws Player.player) drawLaw =
          alternative
            (information.infoOf Player.player
              (decisionHistory hidden).trace) := by
      unfold drawLaw
      rw [independentProduct_map_eval, Profile.update_same]
    have hprojected :
        PMF.map (fun draws => (draws Player.player).1) drawLaw =
          PMF.map (fun choice => choice.1)
            (alternative
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) := by
      have hcongr := congrArg
        (fun law : PMF
            (information.Choice Player.player
              (information.infoOf Player.player
                (decisionHistory hidden).trace)) =>
          PMF.map (fun choice => choice.1) law)
        hchoice
      simpa only [PMF.map_comp, Function.comp_def] using hcongr
    exact hprojected.trans (by rw [infoOf_decisionHistory])
  calc
    _ = finiteExpect drawLaw (fun draws =>
        if (draws Player.player).1 = some hidden then
          if hidden then 2 else 1 else 0) := by
      unfold finiteExpect
      apply expect_congr_on_support
      intro draws _hdraws
      have hlegal := (draws Player.player).2
      cases hdraw : (draws Player.player).1 with
      | none =>
          simp [information, signals_infoOf, viewOfState, hdraw] at hlegal
      | some action =>
          cases action <;> cases hidden <;>
            simp [hdraw, expect_pure, execution, decisionHistory,
              weightedMatchingPayoff, PMF.pure_bindOnSupport,
              ExecutionProtocol.History.extend_state,
              ExecutionProtocol.runRandomizedFor_of_terminal]
    _ = finiteExpect
          (PMF.map (fun draws => (draws Player.player).1) drawLaw)
          (fun choice : Option Bool =>
            if choice = some hidden then if hidden then 2 else 1 else 0) := by
      simpa only [Function.comp_def] using
        (finiteExpect_map (fun draws => (draws Player.player).1) drawLaw
          (fun choice : Option Bool =>
            if choice = some hidden then if hidden then 2 else 1 else 0)).symm
    _ = finiteExpect
          (PMF.map (fun choice => choice.1) (alternative .acting))
          (fun choice : Option Bool =>
            if choice = some hidden then if hidden then 2 else 1 else 0) := by
      rw [hmarginal]
    _ = finiteExpect (alternative .acting) (fun choice =>
          if choice.1 = some hidden then if hidden then 2 else 1 else 0) := by
      simpa only [Function.comp_def] using
        finiteExpect_map (fun choice => choice.1) (alternative .acting)
          (fun action : Option Bool =>
            if action = some hidden then if hidden then 2 else 1 else 0)

/-- Before the information site the focal player has only supplied the forced
inactive choice, so its own reach is one on both hidden histories. -/
theorem playerReachProbability_decision (hidden : Bool) :
    information.playerReachProbability fullyMixedBehavioralProfile .player
      (decisionHistory hidden).trace = 1 := by
  classical
  simp only [decisionHistory, decisionTrace,
    InformationModel.playerReachProbability]
  rw [one_mul]
  unfold InformationModel.playerStepProb
  have hinactive : ¬ execution.active .initial Player.player :=
    initial_inactive Player.player
  let : Subsingleton
      (information.Choice Player.player
        (information.infoOf Player.player ExecutionProtocol.Trace.start)) :=
    ⟨fun first second => by
      apply Subtype.ext
      have hfirst := (information.menu_adequate Player.player
        ExecutionProtocol.Trace.start first.1).mp first.2
      have hsecond := (information.menu_adequate Player.player
        ExecutionProtocol.Trace.start second.1).mp second.2
      rw [LegalOption.eq_none_of_inactive first.1 hfirst hinactive,
        LegalOption.eq_none_of_inactive second.1 hsecond hinactive]⟩
  rw [eq_pure_of_subsingleton
    (fullyMixedBehavioralProfile .player
      (information.infoOf Player.player ExecutionProtocol.Trace.start))
    (information.choicesOfLegal ExecutionProtocol.Trace.start
      ⟨execution.noop, initialLegal⟩ Player.player)]
  simp

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

/-- The finite hidden-state fixture has an integrable Bayes continuation at every policy. -/
theorem bayesContext_integrable
    (alternative : information.BehavioralPolicy Player.player) :
    (Context.ofBelief
      (information.bayesBelief fullyMixedBehavioralProfile Player.player actingSite
        (information_decisionInformationAntichain .player actingSite)
        (informationMass_fullyMixed_pos actingSite))
      (fun history _alternative => information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          fullyMixedBehavioralProfile Player.player _alternative) 2 history.1)
      weightedMatchingPayoff).IntegrableAt alternative :=
  payoffIntegrable_of_finite _ _

private def bayesValue
    (alternative : information.BehavioralPolicy Player.player) : ℝ :=
  bayesContinuationValue information fullyMixedBehavioralProfile .player
    actingSite (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite) alternative
    weightedMatchingPayoff 2 (bayesContext_integrable alternative)

private theorem bayesValue_eq_average
    (alternative : information.BehavioralPolicy Player.player) :
    bayesValue alternative =
      (1 / 2) * finiteExpect (alternative .acting) (fun choice =>
        if choice.1 = some true then 2 else 0) +
      (1 / 2) * finiteExpect (alternative .acting) (fun choice =>
        if choice.1 = some false then 1 else 0) := by
  unfold bayesValue bayesContinuationValue Context.value Context.ofBelief
  let belief := information.bayesBelief fullyMixedBehavioralProfile .player
    actingSite (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite)
  let branch := fun history : information.InformationHistory .player actingSite.1 =>
    fun _alternative : information.BehavioralPolicy .player =>
      information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          fullyMixedBehavioralProfile Player.player _alternative) 2 history.1
  let branchValue := fun history : information.InformationHistory .player actingSite.1 =>
    finiteExpect (branch history alternative) weightedMatchingPayoff
  have hbelief : belief = decisionBelief :=
    fullyMixedAssessment_belief_acting
  have hlaw : belief.bind (fun history => branch history alternative) =
      decisionBelief.bind (fun history => branch history alternative) := by
    rw [hbelief]
  have houter := bayesContext_integrable alternative
  have houter' :
      PayoffIntegrable
        (decisionBelief.bind (fun history => branch history alternative))
        weightedMatchingPayoff :=
    payoffIntegrable_congr_law hlaw houter
  have hcond (history : information.InformationHistory .player actingSite.1) :
      PayoffIntegrable (branch history alternative) weightedMatchingPayoff :=
    payoffIntegrable_of_finite _ _
  have htower := expect_bind_tower decisionBelief
    (fun history => branch history alternative) weightedMatchingPayoff houter' hcond
  have hmix := expect_mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (decisionInformationHistory true))
    (PMF.pure (decisionInformationHistory false)) branchValue
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  calc
    expect (belief.bind (fun history => branch history alternative))
        weightedMatchingPayoff houter =
      expect (decisionBelief.bind (fun history => branch history alternative))
        weightedMatchingPayoff houter' :=
      expect_congr_law hlaw weightedMatchingPayoff houter houter'
    _ = expect decisionBelief branchValue
        (payoffIntegrable_bind_conditionalExpectation decisionBelief
          (fun history => branch history alternative) weightedMatchingPayoff
          houter' hcond) := htower
    _ = (1 / 2) * branchValue (decisionInformationHistory true) +
        (1 / 2) * branchValue (decisionInformationHistory false) := by
      calc
        expect decisionBelief branchValue
            (payoffIntegrable_bind_conditionalExpectation decisionBelief
              (fun history => branch history alternative) weightedMatchingPayoff
              houter' hcond) =
          expect decisionBelief branchValue
            (payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
              (PMF.pure (decisionInformationHistory true))
              (PMF.pure (decisionInformationHistory false)) branchValue
              (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)) :=
          expect_proof_irrel ..
        _ = (1 / 2) * branchValue (decisionInformationHistory true) +
            (1 / 2) * branchValue (decisionInformationHistory false) := by
          simpa only [decisionBelief, expect_pure,
            show 1 - 1 / 2 = (1 / 2 : ℝ) by norm_num] using hmix
    _ = _ := by
      simp only [branchValue, branch,
        runBehavioralFrom_decision_weightedMatchingPayoff]
      norm_num

/-- Every counterfactual continuation of the finite fixture is integrable. -/
theorem counterfactual_integrable
    (alternative : information.BehavioralPolicy Player.player) :
  information.CounterfactualContinuationIntegrable
      fullyMixedBehavioralProfile Player.player actingSite alternative
      weightedMatchingPayoff 2 := by
  intro history _hreach
  exact payoffIntegrable_of_finite
    (information.runBehavioralFrom
      (Profile.update (sig := information.behavioralSignature)
        fullyMixedBehavioralProfile Player.player alternative) 2 history.1)
    weightedMatchingPayoff

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
      weightedMatchingPayoff 2 (bayesContext_integrable alwaysTruePolicy) = 1 := by
  have hvalue : bayesValue alwaysTruePolicy = 1 := by
    rw [bayesValue_eq_average]
    norm_num [finiteExpect, alwaysTruePolicy, expect_pure]
  simpa only [bayesValue] using hvalue

/-- Canonical Bayes value of the prescribed fully mixed policy. -/
theorem bayesContinuationValue_fullyMixed :
    bayesContinuationValue information fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) fullyMixedBehavioralPolicy
      weightedMatchingPayoff 2
      (bayesContext_integrable fullyMixedBehavioralPolicy) = 3 / 4 := by
  have hvalue : bayesValue fullyMixedBehavioralPolicy = 3 / 4 := by
    rw [bayesValue_eq_average]
    simp only [fullyMixedBehavioralPolicy, finiteExpect_map]
    rw [show fairCoin = mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure true) (PMF.pure false) by rfl, finiteExpect_mix]
    rw [finiteExpect_mix]
    norm_num [finiteExpect, expect_pure]
  simpa only [bayesValue] using hvalue

/-- Canonical Bayes value of the strictly harmful pure replacement. -/
theorem bayesContinuationValue_alwaysFalse :
    bayesContinuationValue information fullyMixedBehavioralProfile .player
      actingSite (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) behavioralPolicy
      weightedMatchingPayoff 2 (bayesContext_integrable behavioralPolicy) = 1 / 2 := by
  have hvalue : bayesValue behavioralPolicy = 1 / 2 := by
    rw [bayesValue_eq_average]
    norm_num [finiteExpect, behavioralPolicy, expect_pure]
  simpa only [bayesValue] using hvalue

/-- The profitable replacement has exact positive counterfactual regret.  This
directly consumes the scaled canonical Bayes-gain identity. -/
theorem counterfactualRegret_alwaysTrue :
    counterfactualRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 alwaysTruePolicy
      (counterfactual_integrable alwaysTruePolicy)
      (counterfactual_integrable fullyMixedBehavioralPolicy) = 1 / 4 := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
      information fullyMixedBehavioralProfile .player actingSite
      (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) 1 commonPlayerReach_acting
      alwaysTruePolicy weightedMatchingPayoff 2
      (counterfactual_integrable alwaysTruePolicy)
      (counterfactual_integrable fullyMixedBehavioralPolicy)
  dsimp only at hscaled
  simp only [fullyMixedBehavioralProfile, informationMass_fullyMixed_acting,
    bayesContinuationValue_alwaysTrue, bayesContinuationValue_fullyMixed] at hscaled
  norm_num at hscaled
  exact hscaled.symm

/-- The losing control has exact negative counterfactual regret. -/
theorem counterfactualRegret_alwaysFalse :
    counterfactualRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 behavioralPolicy
      (counterfactual_integrable behavioralPolicy)
      (counterfactual_integrable fullyMixedBehavioralPolicy) = -(1 / 4) := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
      information fullyMixedBehavioralProfile .player actingSite
      (information_decisionInformationAntichain .player actingSite)
      (informationMass_fullyMixed_pos actingSite) 1 commonPlayerReach_acting
      behavioralPolicy weightedMatchingPayoff 2
      (counterfactual_integrable behavioralPolicy)
      (counterfactual_integrable fullyMixedBehavioralPolicy)
  dsimp only at hscaled
  simp only [fullyMixedBehavioralProfile, informationMass_fullyMixed_acting,
    bayesContinuationValue_alwaysFalse,
    bayesContinuationValue_fullyMixed] at hscaled
  norm_num at hscaled
  exact hscaled.symm

/-- The action-local API retains the profitable control exactly. -/
theorem counterfactualActionRegret_true :
    counterfactualActionRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 trueChoice
      (counterfactual_integrable
        (fullyMixedBehavioralPolicy.commit actingSite.1 trueChoice))
      (counterfactual_integrable fullyMixedBehavioralPolicy) = 1 / 4 := by
  simpa only [counterfactualActionRegret, fullyMixedBehavioralProfile,
    commit_true_eq_alwaysTrue] using counterfactualRegret_alwaysTrue

/-- The action-local API also retains the strictly harmful control. -/
theorem counterfactualActionRegret_false :
    counterfactualActionRegret information fullyMixedBehavioralProfile .player
      actingSite weightedMatchingPayoff 2 falseChoice
      (counterfactual_integrable
        (fullyMixedBehavioralPolicy.commit actingSite.1 falseChoice))
      (counterfactual_integrable fullyMixedBehavioralPolicy) = -(1 / 4) := by
  simpa only [counterfactualActionRegret, fullyMixedBehavioralProfile,
    commit_false_eq_alwaysFalse] using counterfactualRegret_alwaysFalse

/-- The sign bridge itself is exercised on the profitable replacement. -/
theorem profitable_counterfactual_iff_profitable_bayes :
    0 < counterfactualRegret information fullyMixedBehavioralProfile .player
        actingSite weightedMatchingPayoff 2 alwaysTruePolicy
          (counterfactual_integrable alwaysTruePolicy)
          (counterfactual_integrable fullyMixedBehavioralPolicy) ↔
      0 < bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite) alwaysTruePolicy
          weightedMatchingPayoff 2 (bayesContext_integrable alwaysTruePolicy) -
        bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite)
          (fullyMixedBehavioralProfile .player) weightedMatchingPayoff 2
          (bayesContext_integrable fullyMixedBehavioralPolicy) :=
  counterfactualRegret_pos_iff_bayesGain_pos information
    fullyMixedBehavioralProfile .player actingSite
    (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite) 1 (by norm_num)
    commonPlayerReach_acting alwaysTruePolicy weightedMatchingPayoff 2
    (counterfactual_integrable alwaysTruePolicy)
    (counterfactual_integrable fullyMixedBehavioralPolicy)

/-- The named weaker certificate is enough for the sign theorem even though
this fixture does not claim global perfect recall. -/
theorem profitable_counterfactual_iff_profitable_bayes_of_commonReach :
    0 < counterfactualRegret information fullyMixedBehavioralProfile .player
        actingSite weightedMatchingPayoff 2 alwaysTruePolicy
          (counterfactual_integrable alwaysTruePolicy)
          (counterfactual_integrable fullyMixedBehavioralPolicy) ↔
      0 < bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite) alwaysTruePolicy
          weightedMatchingPayoff 2 (bayesContext_integrable alwaysTruePolicy) -
        bayesContinuationValue information fullyMixedBehavioralProfile .player
          actingSite
          (information_decisionInformationAntichain .player actingSite)
          (informationMass_fullyMixed_pos actingSite)
          (fullyMixedBehavioralProfile .player) weightedMatchingPayoff 2
          (bayesContext_integrable fullyMixedBehavioralPolicy) :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach information
    fullyMixedBehavioralProfile .player actingSite
    (information_decisionInformationAntichain .player actingSite)
    (informationMass_fullyMixed_pos actingSite)
    ⟨1, commonPlayerReach_acting⟩ alwaysTruePolicy weightedMatchingPayoff 2
    (counterfactual_integrable alwaysTruePolicy)
    (counterfactual_integrable fullyMixedBehavioralPolicy)

end GameTheory.Analysis.Protocol.CounterfactualRegretTest
