/-
# Hostile generic local-CFR realization witness

The selected site is the first decision in a two-decision perfect-recall
problem.  Its continuation therefore passes through another information state;
the generic affine runner theorem cannot succeed by reducing a one-step
terminal payoff.  The same fixture already separates harmless one-site
deviations from a profitable two-site policy change.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegretMatching
import GameTheory.Tests.SubgameOneShot

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest

open Filter GameTheory Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheory.Protocol.InformationModel
open GameTheory.Tests.SubgameOneShot
open GameTheoryMath.Approachability GameTheoryMath.OrthantProjection

/-- The first decision site, shared by the two hidden nature branches. -/
@[reducible]
def firstSite : information.InformationSite () :=
  ⟨firstKnowledge,
    ⟨⟨firstHistory false, infoOf_firstHistory false⟩,
      first_not_terminal false, false, by
        simp [GameTheory.Tests.SubgameOneShot.menu,
          GameTheory.Tests.SubgameOneShot.stageMenu, firstKnowledge]⟩⟩

def firstInformationHistory (hidden : Bool) :
    information.InformationHistory () firstSite.1 :=
  ⟨firstHistory hidden, infoOf_firstHistory hidden⟩

def firstHistoryEquivBool :
    information.InformationHistory () firstSite.1 ≃ Bool where
  toFun history :=
    match history.1.state with
    | .first hidden => hidden
    | _ => false
  invFun := firstInformationHistory
  left_inv history := by
    rcases history with ⟨history, hinfo⟩
    rcases history with ⟨state, trace⟩
    have hstage := knowledge_stage trace
    rw [hinfo] at hstage
    cases state with
    | root => simp [firstKnowledge, State.stage] at hstage
    | first hidden =>
        apply Subtype.ext
        exact history_eq_of_state_eq rfl
    | second hidden firstAction =>
        simp [firstKnowledge, State.stage] at hstage
    | done hidden firstAction secondAction =>
        simp [firstKnowledge, State.stage] at hstage
  right_inv hidden := by
    simp [firstInformationHistory, firstHistory]

local instance : Fintype
    (information.InformationHistory () firstSite.1) :=
  Fintype.ofEquiv Bool firstHistoryEquivBool.symm

abbrev FirstAction := information.Choice () firstSite.1

def firstChoice (action : Bool) : FirstAction :=
  ⟨some action, by
    simp [GameTheory.Tests.SubgameOneShot.menu,
      GameTheory.Tests.SubgameOneShot.stageMenu, firstKnowledge]⟩

def firstActionEquivBool : FirstAction ≃ Bool where
  toFun choice := choice.1.getD false
  invFun := firstChoice
  left_inv choice := by
    rcases choice with ⟨choice, hchoice⟩
    cases choice with
    | none =>
        simp [GameTheory.Tests.SubgameOneShot.menu,
          GameTheory.Tests.SubgameOneShot.stageMenu, firstKnowledge] at hchoice
    | some action => apply Subtype.ext; rfl
  right_inv action := by cases action <;> rfl

local instance : Fintype FirstAction :=
  Fintype.ofEquiv Bool firstActionEquivBool.symm

local instance : Nonempty FirstAction := ⟨firstChoice false⟩

/-- Every history in this fiber is a genuine first-stage decision, not a
nominally active terminal history. -/
theorem firstSite_allNonterminal :
    InformationSite.AllNonterminal information firstSite := by
  intro history
  rw [← firstHistoryEquivBool.symm_apply_apply history]
  exact first_not_terminal _

/-- The baseline fixes the downstream second-stage choice to `true`; only the
first-stage law is supplied by the learner. -/
def baselinePolicy : information.BehavioralPolicy () :=
  (prescribedPolicy false true).toBehavioral

def baselineStrategy (_who : Unit) : information.BehavioralPolicy () :=
  baselinePolicy

def terminalPayoff (history : twoStage.History) : ℝ := utility history ()

/-- The downstream continuation is genuinely action-sensitive: with the same
second-stage action `true`, the first-stage choices yield terminal values zero
and one. -/
theorem downstreamContinuation_nonconstant :
    continuationValue (profileOf (prescribedPolicy false true))
        (firstHistory false) = 0 ∧
      continuationValue (profileOf (prescribedPolicy true true))
        (firstHistory false) = 1 := by
  constructor <;> rw [continuationValue_prescribed_first] <;> rfl

/-- Two-step runner affinity on the hostile fixture.  One step would stop at
the second decision; fuel two genuinely retains the downstream policy. -/
theorem twoStage_runBehavioralFrom_affine
    (law : FinDist FirstAction) (hidden : Bool) :
    information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          baselineStrategy ()
            (baselinePolicy.withLaw firstSite.1 law))
        2 (firstHistory hidden) =
      law.bind fun choice =>
        information.runBehavioralFrom
          (Profile.update (sig := information.behavioralSignature)
            baselineStrategy ()
              (baselinePolicy.commit firstSite.1 choice))
          2 (firstHistory hidden) := by
  exact information.runBehavioralFrom_update_withLaw_eq_bind
    information_actsOnce baselineStrategy () baselinePolicy firstSite.1 law
      (firstHistory hidden) (infoOf_firstHistory hidden)
      (first_not_terminal hidden) (first_active hidden) 1

/-- The generic D47 theorem discharges D46's pointwise realization equation
for every current law on this two-stage site. -/
theorem twoStage_localRealization
    (law : FinDist FirstAction) (environment : Unit) :
    localCounterfactualRegretVector information
        (strategyWithLocalLaw information baselineStrategy () firstSite law)
        () firstSite terminalPayoff 2 =
      regretPayoff
        (fun choice (_current : Unit) =>
          counterfactualActionUtility information baselineStrategy ()
            firstSite terminalPayoff 2 choice)
        law environment :=
  localCounterfactualRegretVector_strategyWithLocalLaw information
    information_actsOnce baselineStrategy () firstSite
      firstSite_allNonterminal law terminalPayoff 1 environment

/-- With the ordinary boundedness premise required by regret matching, the
actual two-stage Protocol payoff process converges.  No model-specific
realization equation remains. -/
theorem twoStage_regretMatch_approaches
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law environment,
      ‖regretPayoff
        (fun choice (_current : Unit) =>
          counterfactualActionUtility information baselineStrategy ()
            firstSite terminalPayoff 2 choice)
        law environment‖ ≤ bound) :
    Tendsto
      (fun t => Metric.infDist
        (avgVec
          (fun law _environment =>
            localCounterfactualRegretVector information
              (strategyWithLocalLaw information baselineStrategy ()
                firstSite law)
              () firstSite terminalPayoff 2)
          regretMatch (fun _ => ()) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information () firstSite
    (fun choice (_current : Unit) =>
      counterfactualActionUtility information baselineStrategy ()
        firstSite terminalPayoff 2 choice)
    (fun law _environment =>
      strategyWithLocalLaw information baselineStrategy () firstSite law)
    (fun _environment => terminalPayoff) 2 twoStage_localRealization
    hbound0 hbound (fun _ => ())

/-- Failure control inherited from the same fixture: locally harmless actual
one-site deviations do not imply global equilibrium. -/
theorem localTestsStillDoNotImplySPE :
    HasNoProfitableSingleInformationDeviationInSubgames incumbent ∧
      ¬ information.IsSubgamePerfect wellFoundedPlay incumbent utility :=
  ⟨incumbent_hasNoProfitableSingleInformationDeviationInSubgames,
    incumbent_not_isSubgamePerfect⟩

end GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest
