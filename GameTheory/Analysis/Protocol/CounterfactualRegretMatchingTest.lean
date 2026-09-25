/-
# Hostile local-CFR witness

The EXP-082 hidden-information site is now equipped with an arbitrary current
action law.  Its D45 action-regret vector is exactly the ordinary regret-payoff
vector for every law, so the cumulative regret matcher receives a genuine
Protocol consumer rather than one named distribution.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegretMatching
import GameTheory.Analysis.Protocol.CounterfactualRegretTest

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRegretMatchingTest

open Filter GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheory.Analysis.Protocol.CounterfactualRegretTest
open GameTheory.Protocol.InformationModel
open GameTheory.Tests.EFG
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

local instance : Fintype execution.History := game.historyFintype

local instance (who : Player) (site : information.InformationSite who) :
    Fintype (information.InformationHistory who site.1) := by
  classical
  infer_instance

/-- A syntactically transparent copy of the unique acting site keeps the local
law's dependent action carrier judgmentally equal to `Choice .acting`. -/
@[reducible]
def localSite : information.InformationSite .player :=
  ⟨View.acting, ⟨⟨decisionHistory false, infoOf_decisionHistory false⟩,
    decision_not_terminal false, false, acting_menu_contains_false⟩⟩

def localDecisionInformationHistory (hidden : Bool) :
    information.InformationHistory .player localSite.1 :=
  ⟨decisionHistory hidden, infoOf_decisionHistory hidden⟩

def localHistoryEquivBool :
    information.InformationHistory .player localSite.1 ≃ Bool where
  toFun history :=
    match history.1.state with
    | .decision hidden _ => hidden
    | _ => false
  invFun := localDecisionInformationHistory
  left_inv history := by
    rcases history with ⟨history, hinfo⟩
    obtain ⟨hidden, hhistory⟩ :=
      history_eq_decisionHistory_of_info_acting history hinfo
    subst history
    apply Subtype.ext
    rfl
  right_inv hidden := by simp [localDecisionInformationHistory, decisionHistory]

abbrev LocalAction := information.Choice .player localSite.1

def localChoice (action : Bool) : LocalAction :=
  ⟨some action, by simp⟩

def localActionEquivBool : LocalAction ≃ Bool where
  toFun choice := choice.1.getD false
  invFun := localChoice
  left_inv choice := by
    rcases choice with ⟨choice, hchoice⟩
    cases choice with
    | none => simp at hchoice
    | some action => apply Subtype.ext; rfl
  right_inv action := by cases action <;> rfl

local instance : Fintype LocalAction :=
  Fintype.ofEquiv Bool localActionEquivBool.symm

local instance : Nonempty LocalAction := ⟨localChoice false⟩

/-- Every continuation used by this finite terminal-history fixture is integrable. -/
theorem continuationIntegrable
    (strategy : (who : Player) → information.BehavioralPolicy who)
    (alternative : information.BehavioralPolicy .player) :
    information.CounterfactualContinuationIntegrable strategy .player
      localSite alternative weightedMatchingPayoff 2 := by
  intro history _
  exact payoffIntegrable_of_finite _ _

/-- A current local law installed at the only decision information state. -/
def policyOfLaw (law : PMF LocalAction) :
    information.BehavioralPolicy .player :=
  fullyMixedBehavioralPolicy.withLaw localSite.1 law

@[simp]
theorem policyOfLaw_localSite (law : PMF LocalAction) :
    policyOfLaw law localSite.1 = law :=
  BehavioralPolicy.withLaw_self fullyMixedBehavioralPolicy localSite.1 law

def profileOfLaw (law : PMF LocalAction) (who : Player) :
    information.BehavioralPolicy who := by
  cases who
  exact policyOfLaw law

/-- The actual local action-regret vector has all its continuation guards. -/
theorem localRegretsIntegrable (law : PMF LocalAction) :
    information.LocalCounterfactualRegretsIntegrable
      (profileOfLaw law) .player localSite weightedMatchingPayoff 2 := by
  constructor
  · intro choice
    exact continuationIntegrable _ _
  · exact continuationIntegrable _ _

/-- Counterfactual value of a pure action: hidden `true` contributes one and
hidden `false` contributes one half. -/
def localUtility (choice : LocalAction) (_environment : Unit) : ℝ :=
  if choice.1 = some true then 1 else 1 / 2

/-- Counterfactual reach of either hidden history is the fair chance mass,
independently of the current focal action law. -/
theorem counterfactualReachProbability_decision_policyOfLaw
    (law : PMF LocalAction) (hidden : Bool) :
    information.counterfactualReachProbability (profileOfLaw law) .player
      (decisionHistory hidden).trace = 1 / 2 := by
  have hinvariant :=
    information.counterfactualReachProbability_eq_of_eq_off
      (first := profileOfLaw law) (second := fullyMixedBehavioralProfile)
      (who := Player.player) (fun other hne => by
        cases other
        exact False.elim (hne rfl))
      (decisionHistory hidden).trace
  have hfactor :=
    information.historyReachProbability_eq_player_mul_counterfactual
      fullyMixedBehavioralProfile .player (decisionHistory hidden).trace
  rw [historyReachProbability_decision,
    playerReachProbability_decision, one_mul] at hfactor
  simpa using hinvariant.trans hfactor.symm

theorem behavioralContinuationValue_policyOfLaw
    (law : PMF LocalAction)
    (alternative : information.BehavioralPolicy .player) (hidden : Bool) :
    information.behavioralContinuationValue (profileOfLaw law) .player
      alternative weightedMatchingPayoff 2 (decisionHistory hidden)
        (payoffIntegrable_of_finite _ _) =
        expect (alternative localSite.1) (fun choice =>
          if choice.1 = some hidden then if hidden then 2 else 1 else 0)
          (payoffIntegrable_of_finite _ _) := by
  unfold InformationModel.behavioralContinuationValue
  have hupdate :
      Profile.update (sig := information.behavioralSignature)
          (profileOfLaw law) .player alternative =
        Profile.update (sig := information.behavioralSignature)
          fullyMixedBehavioralProfile .player alternative := by
    funext who
    cases who
    rw [Profile.update_same, Profile.update_same]
  rw [hupdate]
  exact runBehavioralFrom_decision_weightedMatchingPayoff hidden alternative

/-- Closed form for the counterfactual continuation value under any current
law and any whole-policy replacement. -/
theorem counterfactualContinuationValue_policyOfLaw
    (law : PMF LocalAction)
    (alternative : information.BehavioralPolicy .player) :
    information.counterfactualContinuationValue (profileOfLaw law) .player
      localSite alternative weightedMatchingPayoff 2
        (continuationIntegrable _ _) =
      (1 / 2) * expect (alternative localSite.1) (fun choice =>
        if choice.1 = some true then 2 else 0)
          (payoffIntegrable_of_finite _ _) +
      (1 / 2) * expect (alternative localSite.1) (fun choice =>
        if choice.1 = some false then 1 else 0)
          (payoffIntegrable_of_finite _ _) := by
  unfold InformationModel.counterfactualContinuationValue
  calc
    (∑ history : information.InformationHistory .player localSite.1,
        if hreach : information.counterfactualReachProbability
            (profileOfLaw law) .player history.1.trace ≠ 0 then
          information.counterfactualReachProbability (profileOfLaw law) .player
              history.1.trace *
            information.behavioralContinuationValue (profileOfLaw law) .player
              alternative weightedMatchingPayoff 2 history.1
                (continuationIntegrable _ _ history hreach)
        else 0) =
      ∑ hidden : Bool,
        if hreach : information.counterfactualReachProbability
            (profileOfLaw law) .player (decisionHistory hidden).trace ≠ 0 then
          information.counterfactualReachProbability (profileOfLaw law) .player
              (decisionHistory hidden).trace *
            information.behavioralContinuationValue (profileOfLaw law) .player
              alternative weightedMatchingPayoff 2 (decisionHistory hidden)
                (continuationIntegrable _ _
                  (localDecisionInformationHistory hidden) hreach)
        else 0 := by
      exact Fintype.sum_equiv localHistoryEquivBool
        (fun history =>
          if hreach : information.counterfactualReachProbability
              (profileOfLaw law) .player history.1.trace ≠ 0 then
            information.counterfactualReachProbability (profileOfLaw law)
                .player history.1.trace *
              information.behavioralContinuationValue (profileOfLaw law)
                .player alternative weightedMatchingPayoff 2 history.1
                  (continuationIntegrable _ _ history hreach)
          else 0)
        (fun hidden =>
          if hreach : information.counterfactualReachProbability
              (profileOfLaw law) .player (decisionHistory hidden).trace ≠ 0 then
            information.counterfactualReachProbability (profileOfLaw law)
                .player (decisionHistory hidden).trace *
              information.behavioralContinuationValue (profileOfLaw law)
                .player alternative weightedMatchingPayoff 2
                  (decisionHistory hidden)
                  (continuationIntegrable _ _
                    (localDecisionInformationHistory hidden) hreach)
          else 0)
        (fun history => by
          have hinverse := localHistoryEquivBool.symm_apply_apply history
          exact congrArg
            (fun current : information.InformationHistory .player localSite.1 =>
              if hreach : information.counterfactualReachProbability
                  (profileOfLaw law) .player current.1.trace ≠ 0 then
                information.counterfactualReachProbability
                    (profileOfLaw law) .player current.1.trace *
                  information.behavioralContinuationValue
                    (profileOfLaw law) .player alternative
                      weightedMatchingPayoff 2 current.1
                        (continuationIntegrable _ _ current hreach)
              else 0)
            hinverse.symm)
    _ = ∑ hidden : Bool, (1 / 2 : ℝ) *
          expect (alternative localSite.1) (fun choice =>
            if choice.1 = some hidden then if hidden then 2 else 1 else 0)
              (payoffIntegrable_of_finite _ _) := by
      apply Finset.sum_congr rfl
      intro hidden _
      have hreach : information.counterfactualReachProbability
          (profileOfLaw law) .player (decisionHistory hidden).trace ≠ 0 := by
        rw [counterfactualReachProbability_decision_policyOfLaw]
        norm_num
      simp only [dite_eq_left hreach]
      calc
        _ = (1 / 2 : ℝ) *
            information.behavioralContinuationValue (profileOfLaw law) .player
              alternative weightedMatchingPayoff 2 (decisionHistory hidden)
                (continuationIntegrable _ _
                  (localDecisionInformationHistory hidden) hreach) := by
            exact congrArg (fun weight : ℝ => weight *
              information.behavioralContinuationValue (profileOfLaw law) .player
                alternative weightedMatchingPayoff 2 (decisionHistory hidden)
                  (continuationIntegrable _ _
                    (localDecisionInformationHistory hidden) hreach))
              (counterfactualReachProbability_decision_policyOfLaw law hidden)
        _ = _ := congrArg ((1 / 2 : ℝ) * ·)
          (behavioralContinuationValue_policyOfLaw law alternative hidden)
    _ = _ := by
      rw [Fintype.univ_bool]
      simp

theorem baselineCounterfactualValue_policyOfLaw (law : PMF LocalAction) :
    information.counterfactualContinuationValue (profileOfLaw law) .player
      localSite (policyOfLaw law) weightedMatchingPayoff 2
        (continuationIntegrable _ _) =
        expect law (fun choice => localUtility choice ())
          (payoffIntegrable_of_finite _ _) := by
  rw [counterfactualContinuationValue_policyOfLaw]
  simp only [policyOfLaw, BehavioralPolicy.withLaw_self]
  rw [← expect_const_mul, ← expect_const_mul, ← expect_add]
  apply expect_congr_on_support
  intro choice _
  rcases choice with ⟨choice, hchoice⟩
  cases choice with
  | none => simp at hchoice
  | some action => cases action with
    | false => simp [localUtility]
    | true => simp [localUtility]

theorem committedCounterfactualValue_policyOfLaw
    (law : PMF LocalAction) (choice : LocalAction) :
    information.counterfactualContinuationValue (profileOfLaw law) .player
      localSite ((policyOfLaw law).commit localSite.1 choice)
        weightedMatchingPayoff 2 (continuationIntegrable _ _) =
      localUtility choice () := by
  rw [counterfactualContinuationValue_policyOfLaw]
  rw [BehavioralPolicy.commit_self (M := information)]
  simp only [expect_pure]
  rcases choice with ⟨choice, hchoice⟩
  cases choice with
  | none => simp at hchoice
  | some action => cases action with
    | false => simp [localUtility]
    | true => simp [localUtility]

/-- Pointwise realization equation for every current action law. -/
theorem counterfactualActionRegret_policyOfLaw
    (law : PMF LocalAction) (choice : LocalAction) :
    information.counterfactualActionRegret (profileOfLaw law) .player
      localSite weightedMatchingPayoff 2 choice
        (continuationIntegrable _ _) (continuationIntegrable _ _) =
        localUtility choice () -
          expect law (fun current => localUtility current ())
            (payoffIntegrable_of_finite _ _) := by
  rw [InformationModel.counterfactualActionRegret,
    InformationModel.counterfactualRegret,
    show profileOfLaw law .player = policyOfLaw law by rfl,
    committedCounterfactualValue_policyOfLaw,
    baselineCounterfactualValue_policyOfLaw]

theorem localCounterfactualRegretVector_eq_regretPayoff
    (law : PMF LocalAction) (environment : Unit) :
    localCounterfactualRegretVector information (profileOfLaw law) .player
        localSite weightedMatchingPayoff 2 (localRegretsIntegrable law) =
      regretPayoff localUtility law environment (payoffIntegrable_of_finite _ _) := by
  ext choice
  exact counterfactualActionRegret_policyOfLaw law choice

theorem localUtility_bounds (choice : LocalAction) :
    (1 / 2 : ℝ) ≤ localUtility choice () ∧ localUtility choice () ≤ 1 := by
  by_cases htrue : choice.1 = some true <;>
    simp [localUtility, htrue] <;> norm_num

theorem localUtility_expect_bounds (law : PMF LocalAction) :
    (1 / 2 : ℝ) ≤ expect law (fun choice => localUtility choice ())
        (payoffIntegrable_of_finite _ _) ∧
      expect law (fun choice => localUtility choice ())
        (payoffIntegrable_of_finite _ _) ≤ 1 := by
  constructor
  · have hlower := expect_mono (μ := law)
      (f := fun _choice => (1 / 2 : ℝ))
      (g := fun choice => localUtility choice ())
      (fun choice _ => (localUtility_bounds choice).1)
      (payoffIntegrable_constant law (1 / 2))
      (payoffIntegrable_of_finite _ _)
    simpa [expect_constant] using hlower
  · exact expect_le_const law (fun choice => localUtility choice ())
      (payoffIntegrable_of_finite _ _) 1
      (fun choice _ => (localUtility_bounds choice).2)

theorem regretPayoff_norm_le_one (law : PMF LocalAction)
    (environment : Unit) :
    ‖regretPayoff localUtility law environment (payoffIntegrable_of_finite _ _)‖ ≤ 1 := by
  cases environment
  have hexpect := localUtility_expect_bounds law
  have hcoord : ∀ choice,
      |(regretPayoff localUtility law ()
        (payoffIntegrable_of_finite _ _)).ofLp choice| ≤ 1 / 2 := by
    intro choice
    rw [regretPayoff_ofLp, abs_le]
    have hvalue := localUtility_bounds choice
    constructor <;> linarith
  have hsq : ‖regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)‖ ^ 2 ≤ 1 / 2 := by
    rw [norm_sq_eq_sum]
    calc
      (∑ choice : LocalAction,
          (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp choice ^ 2) =
        ∑ action : Bool,
          (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp
            (localChoice action) ^ 2 := by
          exact Fintype.sum_equiv localActionEquivBool
            (fun choice =>
              (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp choice ^ 2)
            (fun action =>
              (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp
                (localChoice action) ^ 2)
            (fun choice => by
              have hinverse := localActionEquivBool.symm_apply_apply choice
              exact congrArg
                (fun current =>
                  (regretPayoff localUtility law ()
                    (payoffIntegrable_of_finite _ _)).ofLp current ^ 2)
                hinverse.symm)
      _ = (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp
              (localChoice true) ^ 2 +
            (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _)).ofLp
              (localChoice false) ^ 2 := by
          rw [Fintype.univ_bool]
          simp
      _ ≤ 1 / 2 := by
          have htrue := hcoord (localChoice true)
          have hfalse := hcoord (localChoice false)
          rw [abs_le] at htrue hfalse
          nlinarith
  nlinarith [norm_nonneg (regretPayoff localUtility law () (payoffIntegrable_of_finite _ _))]

/-- A fixed losing law has strictly positive regret for the better action. -/
theorem fixedFalse_positiveCounterfactualRegret :
    information.counterfactualActionRegret
      (profileOfLaw (PMF.pure (localChoice false))) .player
      localSite weightedMatchingPayoff 2 (localChoice true)
        (continuationIntegrable _ _) (continuationIntegrable _ _) =
      1 / 2 := by
  rw [counterfactualActionRegret_policyOfLaw]
  simp [expect_pure, localUtility, localChoice]
  norm_num

def falseRegretVector : EuclideanSpace ℝ LocalAction :=
  regretPayoff localUtility (PMF.pure (localChoice false)) ()
    (payoffIntegrable_of_finite _ _)

theorem falseRegretVector_true :
    falseRegretVector.ofLp (localChoice true) = 1 / 2 := by
  rw [falseRegretVector, regretPayoff_ofLp, expect_pure]
  simp [localUtility, localChoice]
  norm_num

theorem falseRegretVector_false :
    falseRegretVector.ofLp (localChoice false) = 0 := by
  rw [falseRegretVector, regretPayoff_ofLp, expect_pure]
  exact sub_self _

theorem sum_pos_falseRegretVector :
    (∑ choice : LocalAction, max (falseRegretVector.ofLp choice) 0) = 1 / 2 := by
  calc
    (∑ choice : LocalAction, max (falseRegretVector.ofLp choice) 0) =
        ∑ action : Bool,
          max (falseRegretVector.ofLp (localChoice action)) 0 := by
      exact Fintype.sum_equiv localActionEquivBool
        (fun choice => max (falseRegretVector.ofLp choice) 0)
        (fun action => max (falseRegretVector.ofLp (localChoice action)) 0)
        (fun choice => by
          have hinverse := localActionEquivBool.symm_apply_apply choice
          exact congrArg
            (fun current => max (falseRegretVector.ofLp current) 0)
            hinverse.symm)
    _ = max (falseRegretVector.ofLp (localChoice true)) 0 +
          max (falseRegretVector.ofLp (localChoice false)) 0 := by
      rw [Fintype.univ_bool]
      simp
    _ = 1 / 2 := by
      rw [falseRegretVector_true, falseRegretVector_false]
      norm_num

/-- From the losing control's accumulated regret vector, the actual update
puts all mass on the profitable action. -/
theorem regretMatch_falseRegret_prob_true :
    regretMatch falseRegretVector (localChoice true) = 1 := by
  rw [regretMatch, dite_eq_left (by
    rw [sum_pos_falseRegretVector]
    norm_num), PMF.ofFintype_apply, sum_pos_falseRegretVector,
    falseRegretVector_true]
  norm_num

/-- The finite local-CFR estimate on the hostile Protocol site. -/
theorem hiddenCounterfactualRegretMatch_sq_infDist_avg_le (t : ℕ) :
    Metric.infDist
        (avgVec
          (fun law _environment =>
            localCounterfactualRegretVector information
              (profileOfLaw law) .player localSite weightedMatchingPayoff 2
                (localRegretsIntegrable law))
          regretMatch (fun _ => ()) t)
        nonposOrthant ^ 2 * (t : ℝ) ≤ 4 := by
  have hbound :=
    counterfactualRegretMatch_sq_infDist_avg_le information .player localSite
      localUtility (fun law _environment => profileOfLaw law)
      (fun _environment => weightedMatchingPayoff) 2
      (fun law _ => localRegretsIntegrable law)
      localCounterfactualRegretVector_eq_regretPayoff
      (bound := 1) (by norm_num) regretPayoff_norm_le_one (fun _ => ()) t
  norm_num at hbound
  exact hbound

/-- The same actual local-CFR process converges to nonpositive average
counterfactual action regret. -/
theorem hiddenCounterfactualRegretMatch_approaches :
    Tendsto
      (fun t => Metric.infDist
        (avgVec
          (fun law _environment =>
            localCounterfactualRegretVector information
              (profileOfLaw law) .player localSite weightedMatchingPayoff 2
                (localRegretsIntegrable law))
          regretMatch (fun _ => ()) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information .player localSite
    localUtility (fun law _environment => profileOfLaw law)
    (fun _environment => weightedMatchingPayoff) 2
    (fun law _ => localRegretsIntegrable law)
    localCounterfactualRegretVector_eq_regretPayoff
    (bound := 1) (by norm_num) regretPayoff_norm_le_one (fun _ => ())

end GameTheory.Analysis.Protocol.CounterfactualRegretMatchingTest
