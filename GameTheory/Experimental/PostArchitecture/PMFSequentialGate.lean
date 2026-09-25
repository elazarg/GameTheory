/-
# General-PMF sequential gate

The chance-first countable decision fixture is expressed using the public
execution and information interfaces. The off-path fixture checks whole-policy
assessment and guarded continuation values.
-/

import GameTheory.Protocol.Information
import GameTheory.Protocol.Context
import GameTheory.Protocol.BehavioralBayes
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PMFSequentialGate

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

inductive DecisionScene where
  | root
  | early (draw : ℕ)
  | chance (draw : ℕ)
  | late (first second : ℕ)
  | done (first second action : ℕ)

def decisionTerminal : DecisionScene → Prop
  | .done _ _ _ => True
  | _ => False

def sceneInfo : DecisionScene → Option Unit
  | .early _ | .late _ _ => some ()
  | _ => none

abbrev canonicalDecision : ExecutionProtocol PUnit where
  State := DecisionScene
  Action := fun _ => ℕ
  init := .root
  active := fun s _ => sceneInfo s = some ()
  available := fun _ _ => Set.univ
  terminal := decisionTerminal
  step := fun s action =>
    match s with
    | .root => geometric.map fun n =>
        if n = 0 then .done 0 0 0
        else if Even n then .early n else .chance n
    | .early n => PMF.pure (.done n 0 ((action.1 ()).getD 0))
    | .chance n => geometric.map (.late n)
    | .late n m => PMF.pure (.done n m ((action.1 ()).getD 0))
    | .done _ _ _ => False.elim (action.2.1 trivial)
  progress := by
    intro s _
    classical
    refine ⟨fun _ => if sceneInfo s = some () then some 0 else none, ?_⟩
    intro i
    by_cases h : sceneInfo s = some ()
    · simp [h]
    · simp [h]

def canonicalSignals : InfoSignals canonicalDecision where
  PublicSignal := Option Unit
  PrivateSignal := fun _ => Unit
  initialPublic := none
  initialPrivate := fun _ => ()
  publicSignal := fun event => sceneInfo event.target
  privateSignal := fun _ _ => ()
  InfoState := fun _ => Option Unit
  initInfo := fun _ _ signal => signal
  pushInfo := fun _ _ _ _ signal => signal

theorem canonicalSignals_infoOf {s : DecisionScene}
    (trace : Trace canonicalDecision s) (i : PUnit) :
    canonicalSignals.infoOf i trace = sceneInfo s := by
  exact Trace.rec
    (motive := fun s tr => canonicalSignals.infoOf i tr = sceneInfo s)
    (by rfl)
    (by intro source target prior joint isLegal realized ih; rfl)
    trace

abbrev canonicalInformation : InformationModel canonicalDecision where
  toInfoSignals := canonicalSignals
  menu := fun _ info =>
    match info with
    | some _ => {choice | choice.isSome}
    | none => {none}
  menu_adequate := by
    intro i s trace choice
    cases i
    rw [canonicalSignals_infoOf trace ()]
    unfold LegalOption
    cases hinfo : sceneInfo s <;> cases choice <;>
      simp [canonicalDecision, hinfo]

theorem rootLegal : canonicalDecision.Legal .root canonicalDecision.noop :=
  canonicalDecision.noop_isLegal (by simp [decisionTerminal]) (by
    intro i
    simp [sceneInfo])

theorem chanceLegal (n : ℕ) :
    canonicalDecision.Legal (.chance n) canonicalDecision.noop :=
  canonicalDecision.noop_isLegal (by simp [decisionTerminal]) (by
    intro i
    simp [sceneInfo])

theorem rootLaw :
    canonicalDecision.step .root ⟨canonicalDecision.noop, rootLegal⟩ =
      geometric.map (fun n => if n = 0 then DecisionScene.done 0 0 0
        else if Even n then DecisionScene.early n else DecisionScene.chance n) := rfl

abbrev rootHistory : canonicalDecision.History := ⟨.root, .start⟩

abbrev earlyHistory (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    canonicalDecision.History :=
  rootHistory.extend rootLegal (by
    show DecisionScene.early n ∈
      (canonicalDecision.step .root ⟨canonicalDecision.noop, rootLegal⟩).support
    rw [rootLaw, PMF.mem_support_map_iff]
    exact ⟨n, (geometric_positive n).ne', by simp [hn0, hn]⟩)

abbrev chanceHistory (n : ℕ) (hn : ¬ Even n) :
    canonicalDecision.History :=
  rootHistory.extend rootLegal (by
    show DecisionScene.chance n ∈
      (canonicalDecision.step .root ⟨canonicalDecision.noop, rootLegal⟩).support
    rw [rootLaw, PMF.mem_support_map_iff]
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact hn (by decide)
    exact ⟨n, (geometric_positive n).ne', by simp [hn0, hn]⟩)

abbrev lateHistory (n m : ℕ) (hn : ¬ Even n) :
    canonicalDecision.History :=
  (chanceHistory n hn).extend (chanceLegal n) (by
    show DecisionScene.late n m ∈
      (canonicalDecision.step (.chance n)
        ⟨canonicalDecision.noop, chanceLegal n⟩).support
    rw [PMF.mem_support_map_iff]
    exact ⟨m, (geometric_positive m).ne', rfl⟩)

theorem earlyHistory_depth (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    (earlyHistory n hn0 hn).trace.length = 1 := rfl

theorem lateHistory_depth (n m : ℕ) (hn : ¬ Even n) :
    (lateHistory n m hn).trace.length = 2 := rfl

theorem earlyHistory_info (n : ℕ) (hn0 : n ≠ 0) (hn : Even n) :
    canonicalInformation.infoOf () (earlyHistory n hn0 hn).trace = some () := by
  exact canonicalSignals_infoOf _ ()

theorem lateHistory_info (n m : ℕ) (hn : ¬ Even n) :
    canonicalInformation.infoOf () (lateHistory n m hn).trace = some () := by
  exact canonicalSignals_infoOf _ ()

def localBehavioral (law : PMF ℕ) : canonicalInformation.BehavioralPolicy ()
  | none => PMF.pure ⟨none, by simp⟩
  | some () => law.map (fun action =>
      ⟨some action, by simp⟩)

def behavioralProfile (law : PMF ℕ) :
    (i : PUnit) → canonicalInformation.BehavioralPolicy i
  | () => localBehavioral law

theorem localBehavioral_early (law : PMF ℕ) (n : ℕ) (hn0 : n ≠ 0)
    (hn : Even n) :
    behavioralProfile law ()
      (canonicalInformation.infoOf () (earlyHistory n hn0 hn).trace) =
      law.map (fun action =>
        (⟨some action, by simp⟩ :
          canonicalInformation.Choice () (some ()))) := rfl

theorem localBehavioral_late (law : PMF ℕ) (n m : ℕ)
    (hn : ¬ Even n) :
    behavioralProfile law ()
      (canonicalInformation.infoOf () (lateHistory n m hn).trace) =
      law.map (fun action =>
        (⟨some action, by simp⟩ :
          canonicalInformation.Choice () (some ()))) := rfl

theorem exploding_not_integrable : ¬ PayoffIntegrable geometric exploding := by
  intro hp
  apply exploding_not_summable
  have hnonneg (n : ℕ) : 0 ≤ exploding n := by
    unfold exploding
    positivity
  have heq : (fun n => (geometric n).toReal * |exploding n|) =
      (fun n => (geometric n).toReal * exploding n) := by
    funext n
    rw [abs_of_nonneg (hnonneg n)]
  unfold PayoffIntegrable at hp
  rwa [heq] at hp

/-- Even an empty deviation family cannot make an undefined incumbent value
look optimal. -/
theorem divergent_incumbent_not_optimal_with_no_alternatives :
    ¬ ({ outcome := fun _ : Unit => geometric,
         continuation := exploding } : GameTheory.Protocol.Context Unit ℕ).IsLocallyOptimal
        ∅ () := by
  intro hoptimal
  exact exploding_not_integrable hoptimal.1

def decisionSite : canonicalInformation.InformationSite () :=
  canonicalInformation.informationSite ()
    (earlyHistory 2 (by decide) (by decide)) 0
    (by simp [canonicalDecision, decisionTerminal])
    (by rw [earlyHistory_info]; simp)

theorem decisionSite_info : decisionSite.1 = some () := rfl

theorem decisionSite_allNonterminal : decisionSite.AllNonterminal := by
  intro history
  have hinfo : sceneInfo history.1.state = some () := by
    have hscene := canonicalSignals_infoOf history.1.trace ()
    exact hscene.symm.trans (history.2.trans decisionSite_info)
  cases hstate : history.1.state with
  | root => simp [sceneInfo, hstate] at hinfo
  | early n => simp [decisionTerminal]
  | chance n => simp [sceneInfo, hstate] at hinfo
  | late n m => simp [decisionTerminal]
  | done n m a => simp [sceneInfo, hstate] at hinfo

theorem decisionSuccessorTerminal {s reached : DecisionScene}
    (hinfo : sceneInfo s = some ())
    {joint : ∀ _ : PUnit, Option ℕ}
    (hlegal : canonicalDecision.Legal s joint)
    (hrealized : reached ∈
      (canonicalDecision.step s ⟨joint, hlegal⟩).support) :
    canonicalDecision.terminal reached := by
  cases s with
  | root => simp [sceneInfo] at hinfo
  | early n =>
      have heq : reached = DecisionScene.done n 0 ((joint ()).getD 0) := by
        simpa [canonicalDecision] using hrealized
      rw [heq]
      trivial
  | chance n => simp [sceneInfo] at hinfo
  | late n m =>
      have heq : reached = DecisionScene.done n m ((joint ()).getD 0) := by
        simpa [canonicalDecision] using hrealized
      rw [heq]
      trivial
  | done n m a => simp [sceneInfo] at hinfo

theorem decisionSite_antichain : decisionSite.IsHistoryAntichain := by
  intro first second joint isLegal reached realized fuel hreach
  have hinfo : sceneInfo first.1.state = some () := by
    have hscene := canonicalSignals_infoOf first.1.trace ()
    exact hscene.symm.trans (first.2.trans decisionSite_info)
  have hterminal := decisionSuccessorTerminal hinfo isLegal realized
  have heq := hreach.eq_of_terminal hterminal
  have hnonterminal := decisionSite_allNonterminal second
  rw [heq] at hnonterminal
  exact hnonterminal hterminal

theorem rootNonterminal : ¬ canonicalDecision.terminal rootHistory.state := by
  simp [decisionTerminal]

theorem chanceNonterminal (n : ℕ) (hn : ¬ Even n) :
    ¬ canonicalDecision.terminal (chanceHistory n hn).state := by
  simp [chanceHistory, decisionTerminal]

theorem rootBehavioralJoint (law : PMF ℕ) :
    canonicalInformation.behavioralJoint
      (behavioralProfile law) rootHistory.trace rootNonterminal =
      PMF.pure ⟨canonicalDecision.noop, rootLegal⟩ := by
  have hnone : ∀ i : PUnit, ¬ canonicalDecision.active rootHistory.state i := by
    intro i
    simp [sceneInfo]
  rw [canonicalInformation.behavioralJoint_eq_pure_of_no_active
    (behavioralProfile law) rootHistory.trace rootNonterminal hnone]
  congr 1

theorem chanceBehavioralJoint (law : PMF ℕ) (n : ℕ)
    (hn : ¬ Even n) :
    canonicalInformation.behavioralJoint
      (behavioralProfile law) (chanceHistory n hn).trace
        (chanceNonterminal n hn) =
      PMF.pure ⟨canonicalDecision.noop, chanceLegal n⟩ := by
  have hnone : ∀ i : PUnit,
      ¬ canonicalDecision.active (chanceHistory n hn).state i := by
    intro i
    simp [chanceHistory, sceneInfo]
  rw [canonicalInformation.behavioralJoint_eq_pure_of_no_active
    (behavioralProfile law) (chanceHistory n hn).trace
    (chanceNonterminal n hn) hnone]
  congr 1

theorem runRootOne (law : PMF ℕ) :
    canonicalInformation.runBehavioralFrom
      (behavioralProfile law) 1 rootHistory =
      (canonicalDecision.step .root
        ⟨canonicalDecision.noop, rootLegal⟩).bindOnSupport
        (fun _ realized => PMF.pure (rootHistory.extend rootLegal realized)) := by
  rw [canonicalInformation.runBehavioralFrom_succ_of_not_terminal
    (behavioralProfile law) 0 rootNonterminal,
    rootBehavioralJoint, PMF.pure_bind]
  apply bindOnSupport_congr
  intro target realized
  rfl

theorem earlyHistory_reached (law : PMF ℕ) (n : ℕ)
    (hn0 : n ≠ 0) (hn : Even n) :
    earlyHistory n hn0 hn ∈
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 1 rootHistory).support := by
  rw [runRootOne, PMF.mem_support_bindOnSupport_iff]
  have htarget : DecisionScene.early n ∈
      (canonicalDecision.step .root
        ⟨canonicalDecision.noop, rootLegal⟩).support := by
    rw [rootLaw, PMF.mem_support_map_iff]
    exact ⟨n, (geometric_positive n).ne', by simp [hn0, hn]⟩
  refine ⟨.early n, htarget, ?_⟩
  simp [earlyHistory]

theorem chanceHistory_reached (law : PMF ℕ) (n : ℕ)
    (hn : ¬ Even n) :
    chanceHistory n hn ∈
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 1 rootHistory).support := by
  rw [runRootOne, PMF.mem_support_bindOnSupport_iff]
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (by decide)
  have htarget : DecisionScene.chance n ∈
      (canonicalDecision.step .root
        ⟨canonicalDecision.noop, rootLegal⟩).support := by
    rw [rootLaw, PMF.mem_support_map_iff]
    exact ⟨n, (geometric_positive n).ne', by simp [hn0, hn]⟩
  refine ⟨.chance n, htarget, ?_⟩
  simp [chanceHistory]

theorem runChanceOne (law : PMF ℕ) (n : ℕ) (hn : ¬ Even n) :
    canonicalInformation.runBehavioralFrom
      (behavioralProfile law) 1 (chanceHistory n hn) =
      (canonicalDecision.step (.chance n)
        ⟨canonicalDecision.noop, chanceLegal n⟩).bindOnSupport
        (fun _ realized => PMF.pure
          ((chanceHistory n hn).extend (chanceLegal n) realized)) := by
  rw [canonicalInformation.runBehavioralFrom_succ_of_not_terminal
    (behavioralProfile law) 0 (chanceNonterminal n hn),
    chanceBehavioralJoint, PMF.pure_bind]
  apply bindOnSupport_congr
  intro target realized
  rfl

theorem lateHistory_reached_from_chance (law : PMF ℕ)
    (n m : ℕ) (hn : ¬ Even n) :
    lateHistory n m hn ∈
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 1 (chanceHistory n hn)).support := by
  rw [runChanceOne, PMF.mem_support_bindOnSupport_iff]
  have htarget : DecisionScene.late n m ∈
      (canonicalDecision.step (.chance n)
        ⟨canonicalDecision.noop, chanceLegal n⟩).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨m, (geometric_positive m).ne', rfl⟩
  refine ⟨.late n m, htarget, ?_⟩
  simp [lateHistory]

theorem lateHistory_reached (law : PMF ℕ) (n m : ℕ)
    (hn : ¬ Even n) :
    lateHistory n m hn ∈
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 2 rootHistory).support := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
    canonicalInformation.runBehavioralFrom_add, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr
    ⟨chanceHistory n hn, chanceHistory_reached law n hn,
      lateHistory_reached_from_chance law n m hn⟩

abbrev rootExitHistory : canonicalDecision.History :=
  rootHistory.extend rootLegal (by
    show DecisionScene.done 0 0 0 ∈
      (canonicalDecision.step .root
        ⟨canonicalDecision.noop, rootLegal⟩).support
    rw [rootLaw, PMF.mem_support_map_iff]
    exact ⟨0, (geometric_positive 0).ne', by simp⟩)

theorem rootExitHistory_terminal :
    canonicalDecision.terminal rootExitHistory.state := by
  simp [rootExitHistory, decisionTerminal]

theorem rootExitHistory_depth : rootExitHistory.trace.length = 1 := rfl

theorem rootExitHistory_reached (law : PMF ℕ) :
    rootExitHistory ∈
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 1 rootHistory).support := by
  rw [runRootOne, PMF.mem_support_bindOnSupport_iff]
  refine ⟨.done 0 0 0, ?_, ?_⟩
  · rw [rootLaw, PMF.mem_support_map_iff]
    exact ⟨0, (geometric_positive 0).ne', by simp⟩
  · simp [rootExitHistory]

theorem decisionSite_positiveMass (law : PMF ℕ) :
    0 < canonicalInformation.informationMass
      (behavioralProfile law) () decisionSite := by
  let history : canonicalInformation.InformationHistory () decisionSite.1 :=
    ⟨earlyHistory 2 (by decide) (by decide), by
      exact (earlyHistory_info 2 (by decide) (by decide)).trans
        decisionSite_info.symm⟩
  have hreach : 0 < canonicalInformation.historyReachWeight
      (behavioralProfile law) history.1 := by
    have hsupp : history.1 ∈
        (canonicalInformation.runBehavioralFrom
          (behavioralProfile law) 1 rootHistory).support := by
      simpa [history] using earlyHistory_reached law 2
        (by decide) (by decide)
    have hne := (PMF.mem_support_iff _ _).mp hsupp
    have hpos : 0 <
        (canonicalInformation.runBehavioralFrom
          (behavioralProfile law) 1 rootHistory) history.1 :=
      pos_iff_ne_zero.mpr hne
    simpa only [InformationModel.historyReachWeight, earlyHistory_depth,
      InformationModel.runBehavioral, history, rootHistory,
      ExecutionProtocol.initHistory] using hpos
  exact lt_of_lt_of_le hreach (by
    unfold InformationModel.informationMass
    exact ENNReal.le_tsum
      (f := fun history : canonicalInformation.InformationHistory () decisionSite.1 =>
        canonicalInformation.historyReachWeight (behavioralProfile law) history.1)
      history)

def decisionBayesBelief (law : PMF ℕ) :
    PMF (canonicalInformation.InformationHistory () decisionSite.1) :=
  canonicalInformation.bayesBelief (behavioralProfile law) () decisionSite
    decisionSite_antichain (decisionSite_positiveMass law)

theorem decisionBayesBelief_ratio (law : PMF ℕ)
    (history : canonicalInformation.InformationHistory () decisionSite.1) :
    decisionBayesBelief law history =
      canonicalInformation.historyReachWeight
        (behavioralProfile law) history.1 /
        canonicalInformation.informationMass
          (behavioralProfile law) () decisionSite := by
  exact canonicalInformation.bayesBelief_apply
    (behavioralProfile law) () decisionSite
    decisionSite_antichain (decisionSite_positiveMass law) history

open Classical in
def decisionBayesAssessment (law : PMF ℕ) :
    canonicalInformation.BehavioralAssessment where
  strategy := behavioralProfile law
  belief := fun i site =>
    if hanti : site.IsHistoryAntichain then
      if hmass : 0 < canonicalInformation.informationMass
          (behavioralProfile law) i site then
        canonicalInformation.bayesBelief
          (behavioralProfile law) i site hanti hmass
      else PMF.pure (Classical.choose site.2)
    else PMF.pure (Classical.choose site.2)

theorem decisionBayesAssessment_atSite (law : PMF ℕ) :
    (decisionBayesAssessment law).belief () decisionSite =
      decisionBayesBelief law := by
  simp [decisionBayesAssessment, decisionBayesBelief,
    decisionSite_antichain, decisionSite_positiveMass]

theorem decisionBayesAssessment_consistentAtSite (law : PMF ℕ) :
    InformationModel.BehavioralAssessment.IsBayesConsistentAt
      canonicalInformation (decisionBayesAssessment law) () decisionSite
        decisionSite_antichain (decisionSite_positiveMass law) := by
  apply (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff
    canonicalInformation (decisionBayesAssessment law) () decisionSite
    decisionSite_antichain (decisionSite_positiveMass law)).2
  exact decisionBayesAssessment_atSite law

theorem decisionBayesBelief_support_iff (law : PMF ℕ)
    (history : canonicalInformation.InformationHistory () decisionSite.1) :
    history ∈ (decisionBayesBelief law).support ↔
      canonicalInformation.historyReachWeight
        (behavioralProfile law) history.1 ≠ 0 := by
  unfold decisionBayesBelief InformationModel.bayesBelief
  exact PMF.mem_support_normalize_iff _ _ history

theorem decisionBayesBelief_mem_of_reached (law : PMF ℕ)
    (history : canonicalInformation.InformationHistory () decisionSite.1)
    (hreach : history.1 ∈
      (canonicalInformation.runBehavioral
        (behavioralProfile law) history.1.trace.length).support) :
    history ∈ (decisionBayesBelief law).support := by
  rw [decisionBayesBelief_support_iff]
  exact (PMF.mem_support_iff _ _).mp hreach

def earlyInformationHistory (k : ℕ) :
    canonicalInformation.InformationHistory () decisionSite.1 := by
  let n := 2 * k + 2
  have hn0 : n ≠ 0 := by omega
  have hn : Even n := ⟨k + 1, by omega⟩
  exact ⟨earlyHistory n hn0 hn,
    (earlyHistory_info n hn0 hn).trans decisionSite_info.symm⟩

def lateInformationHistory (k : ℕ) :
    canonicalInformation.InformationHistory () decisionSite.1 :=
  ⟨lateHistory 1 k (by decide),
    (lateHistory_info 1 k (by decide)).trans decisionSite_info.symm⟩

theorem earlyInformationHistory_depth (k : ℕ) :
    (earlyInformationHistory k).1.trace.length = 1 := rfl

theorem lateInformationHistory_depth (k : ℕ) :
    (lateInformationHistory k).1.trace.length = 2 := rfl

theorem decisionTrace_zero_root {state : DecisionScene}
    (trace : Trace canonicalDecision state) (hzero : trace.length = 0) :
    state = .root := by
  exact Trace.rec
    (motive := fun (state : DecisionScene) tr =>
      tr.length = 0 → state = DecisionScene.root)
    (by intro _; rfl)
    (by intro source target prior joint legal realized ih hz
        simp [Trace.length] at hz)
    trace hzero

theorem decisionSite_positiveDepth
    (history : canonicalInformation.InformationHistory () decisionSite.1) :
    0 < history.1.trace.length := by
  by_contra hn
  have hz : history.1.trace.length = 0 := by omega
  have hroot := decisionTrace_zero_root history.1.trace hz
  have hinfo := canonicalSignals_infoOf history.1.trace ()
  have hscene : sceneInfo history.1.state = some () :=
    hinfo.symm.trans (history.2.trans decisionSite_info)
  rw [hroot] at hscene
  simp [sceneInfo] at hscene

theorem rootExitHistory_disjointDecisionSite
    (history : canonicalInformation.InformationHistory () decisionSite.1) :
    Disjoint (InformationModel.historyCone history.1)
      (InformationModel.historyCone rootExitHistory) := by
  apply Set.disjoint_left.mpr
  intro target hdecision hexit
  obtain ⟨decisionFuel, hdecision⟩ := hdecision
  obtain ⟨exitFuel, hexit⟩ := hexit
  have htarget : target = rootExitHistory :=
    hexit.eq_of_terminal rootExitHistory_terminal
  subst target
  have hle := hdecision.trace_length_le
  have hlength : history.1.trace.length = rootExitHistory.trace.length := by
    have hpositive := decisionSite_positiveDepth history
    rw [rootExitHistory_depth] at hle ⊢
    omega
  have hsame : rootExitHistory = history.1 :=
    hdecision.eq_of_trace_length_eq hlength
  have hterm : canonicalDecision.terminal history.1.state := by
    rw [← hsame]
    exact rootExitHistory_terminal
  exact decisionSite_allNonterminal history hterm

theorem rootExitHistory_positiveWeight (law : PMF ℕ) :
    0 < canonicalInformation.historyReachWeight
      (behavioralProfile law) rootExitHistory := by
  have hne := (PMF.mem_support_iff _ _).mp (rootExitHistory_reached law)
  have hpos : 0 <
      (canonicalInformation.runBehavioralFrom
        (behavioralProfile law) 1 rootHistory) rootExitHistory :=
    pos_iff_ne_zero.mpr hne
  simpa only [InformationModel.historyReachWeight,
    InformationModel.runBehavioral, rootExitHistory_depth,
    rootHistory, ExecutionProtocol.initHistory] using hpos

theorem decisionSite_mass_lt_one (law : PMF ℕ) :
    canonicalInformation.informationMass
      (behavioralProfile law) () decisionSite < 1 := by
  exact canonicalInformation.informationMass_lt_one_of_outside_pos
    (behavioralProfile law) () decisionSite decisionSite_antichain
    rootExitHistory rootExitHistory_disjointDecisionSite
    (rootExitHistory_positiveWeight law)

theorem earlyInformationHistory_mem (law : PMF ℕ) (k : ℕ) :
    earlyInformationHistory k ∈ (decisionBayesBelief law).support := by
  apply decisionBayesBelief_mem_of_reached
  rw [earlyInformationHistory_depth]
  simpa only [InformationModel.runBehavioral,
    earlyInformationHistory, rootHistory, ExecutionProtocol.initHistory] using
      earlyHistory_reached law (2 * k + 2) (by omega)
        (show Even (2 * k + 2) from ⟨k + 1, by omega⟩)

theorem lateInformationHistory_mem (law : PMF ℕ) (k : ℕ) :
    lateInformationHistory k ∈ (decisionBayesBelief law).support := by
  apply decisionBayesBelief_mem_of_reached
  rw [lateInformationHistory_depth]
  simpa only [InformationModel.runBehavioral,
    lateInformationHistory, rootHistory, ExecutionProtocol.initHistory] using
      lateHistory_reached law 1 k (by decide)

theorem earlyInformationHistory_injective :
    Function.Injective earlyInformationHistory := by
  intro k l h
  have hstate := congrArg
    (fun history : canonicalInformation.InformationHistory () decisionSite.1 =>
      history.1.state) h
  simp only [earlyInformationHistory, earlyHistory, History.extend_state,
    DecisionScene.early.injEq] at hstate
  omega

theorem lateInformationHistory_injective :
    Function.Injective lateInformationHistory := by
  intro k l h
  have hstate := congrArg
    (fun history : canonicalInformation.InformationHistory () decisionSite.1 =>
      history.1.state) h
  simp only [lateInformationHistory, lateHistory, History.extend,
    DecisionScene.late.injEq] at hstate
  exact hstate.2

theorem decisionBayesBelief_infiniteSupport (law : PMF ℕ) :
    (decisionBayesBelief law).support.Infinite := by
  apply (Set.infinite_range_of_injective
    earlyInformationHistory_injective).mono
  rintro history ⟨k, rfl⟩
  exact earlyInformationHistory_mem law k

theorem decisionBayesBelief_infiniteEarlySupport (law : PMF ℕ) :
    {history ∈ (decisionBayesBelief law).support |
      history.1.trace.length = 1}.Infinite := by
  apply (Set.infinite_range_of_injective
    earlyInformationHistory_injective).mono
  rintro history ⟨k, rfl⟩
  exact ⟨earlyInformationHistory_mem law k, earlyInformationHistory_depth k⟩

theorem decisionBayesBelief_infiniteLateSupport (law : PMF ℕ) :
    {history ∈ (decisionBayesBelief law).support |
      history.1.trace.length = 2}.Infinite := by
  apply (Set.infinite_range_of_injective
    lateInformationHistory_injective).mono
  rintro history ⟨k, rfl⟩
  exact ⟨lateInformationHistory_mem law k, lateInformationHistory_depth k⟩

theorem decisionSite_eq_of_site
    (site : canonicalInformation.InformationSite ()) :
    site = decisionSite := by
  apply Subtype.ext
  obtain ⟨⟨history, hinfo⟩, hterminal, action, hmenu⟩ := site.2
  cases hvalue : site.1 with
  | none =>
      simp [canonicalInformation, hvalue] at hmenu
  | some value =>
      cases value
      rfl

theorem canonicalDecisionInformationAntichain :
    canonicalInformation.DecisionInformationAntichain := by
  intro i site
  cases i
  rw [decisionSite_eq_of_site site]
  exact decisionSite_antichain

theorem geometricDecisionAssessment_bayesConsistent :
    InformationModel.BehavioralAssessment.IsBayesConsistent
      canonicalInformation (decisionBayesAssessment geometric)
      canonicalDecisionInformationAntichain := by
  intro i site hmass
  cases i
  have hsite := decisionSite_eq_of_site site
  cases hsite
  exact decisionBayesAssessment_consistentAtSite geometric

theorem geometricDecisionAssessment_has_infinite_bayes_fiber :
    (decisionBayesBelief geometric).support.Infinite :=
  decisionBayesBelief_infiniteSupport geometric

def remaining : DecisionScene → ℕ
  | .root => 3
  | .chance _ => 2
  | .early _ | .late _ _ => 1
  | .done _ _ _ => 0

theorem remaining_decreases {s target : DecisionScene}
    {joint : ∀ _ : PUnit, Option ℕ}
    (hlegal : canonicalDecision.Legal s joint)
    (hrealized : target ∈
      (canonicalDecision.step s ⟨joint, hlegal⟩).support) :
    remaining target + 1 ≤ remaining s := by
  cases s with
  | root =>
      rw [PMF.mem_support_map_iff] at hrealized
      obtain ⟨n, _, rfl⟩ := hrealized
      by_cases hn0 : n = 0
      · simp [hn0, remaining]
      · by_cases heven : Even n <;> simp [hn0, heven, remaining]
  | early n =>
      have heq : target = .done n 0 ((joint ()).getD 0) := by
        simpa [canonicalDecision] using hrealized
      simp [heq, remaining]
  | chance n =>
      rw [PMF.mem_support_map_iff] at hrealized
      obtain ⟨m, _, rfl⟩ := hrealized
      simp [remaining]
  | late n m =>
      have heq : target = .done n m ((joint ()).getD 0) := by
        simpa [canonicalDecision] using hrealized
      simp [heq, remaining]
  | done n m a => exact False.elim (hlegal.1 trivial)

theorem trace_rank_bound {s : DecisionScene}
    (trace : Trace canonicalDecision s) :
    remaining s + trace.length ≤ 3 := by
  exact Trace.rec
    (motive := fun s tr => remaining s + tr.length ≤ 3)
    (by decide)
    (by
      intro source target prior joint isLegal realized ih
      have hdec := remaining_decreases isLegal realized
      simp only [Trace.length]
      omega)
    trace

theorem boundedHorizonThree : canonicalDecision.BoundedHorizon 3 := by
  intro s trace hlength
  have hrank := trace_rank_bound trace
  have hzero : remaining s = 0 := by omega
  cases s <;> simp [remaining, decisionTerminal] at hzero ⊢

theorem behavioralFuelStable (law : PMF ℕ) (extra : ℕ) :
    canonicalInformation.runBehavioral
      (behavioralProfile law) (3 + extra) =
      canonicalInformation.runBehavioral
        (behavioralProfile law) 3 := by
  exact canonicalInformation.runBehavioralFrom_bound_add
    (behavioralProfile law) boundedHorizonThree extra
    canonicalDecision.initHistory

theorem assessmentContinuationFuelStable
    (A : canonicalInformation.BehavioralAssessment)
    (extra : ℕ) {i : PUnit}
    (site : canonicalInformation.InformationSite i)
    (payoff : canonicalDecision.History → ℝ) :
    A.continuationContext site payoff (3 + extra) =
      A.continuationContext site payoff 3 := by
  exact A.continuationContext_bound_add 3 boundedHorizonThree extra site payoff

theorem assessmentRationalityFuelStable
    (A : canonicalInformation.BehavioralAssessment)
    (extra : ℕ) (payoff : PUnit → canonicalDecision.History → ℝ) :
    A.IsSequentiallyRationalWithin payoff (3 + extra) ↔
      A.IsSequentiallyRationalWithin payoff 3 := by
  exact A.isSequentiallyRationalWithin_bound_add
    3 boundedHorizonThree extra payoff

namespace OffPath

inductive Scene where
  | root
  | second
  | done (win : Bool)

def info : Scene → Option Bool
  | .root => some false
  | .second => some true
  | .done _ => none

abbrev execution : ExecutionProtocol PUnit where
  State := Scene
  Action := fun _ => Bool
  init := .root
  active := fun s _ => (info s).isSome = true
  available := fun _ _ => Set.univ
  terminal := fun s => match s with | .done _ => True | _ => False
  step := fun s action =>
    match s with
    | .root =>
        if (action.1 ()).getD false then PMF.pure .second
        else PMF.pure (.done false)
    | .second => PMF.pure (.done ((action.1 ()).getD false))
    | .done _ => False.elim (action.2.1 trivial)
  progress := by
    intro s hnonterminal
    cases s with
    | root => exact ⟨fun _ => some false, by intro i; simp [info]⟩
    | second => exact ⟨fun _ => some false, by intro i; simp [info]⟩
    | done win => exact False.elim (hnonterminal trivial)

abbrev signals : InfoSignals execution where
  PublicSignal := Option Bool
  PrivateSignal := fun _ => Unit
  initialPublic := some false
  initialPrivate := fun _ => ()
  publicSignal := fun event => info event.target
  privateSignal := fun _ _ => ()
  InfoState := fun _ => Option Bool
  initInfo := fun _ _ signal => signal
  pushInfo := fun _ _ _ _ signal => signal

theorem signals_infoOf {s : Scene} (trace : Trace execution s) (i : PUnit) :
    signals.infoOf i trace = info s := by
  exact Trace.rec
    (motive := fun s tr => signals.infoOf i tr = info s)
    (by rfl)
    (by intro source target prior joint legal realized ih; rfl)
    trace

abbrev information : InformationModel execution where
  toInfoSignals := signals
  menu := fun _ view =>
    match view with
    | some _ => {choice | choice.isSome}
    | none => {none}
  menu_adequate := by
    intro i s trace choice
    cases i
    rw [signals_infoOf trace ()]
    unfold LegalOption
    cases s <;> cases choice <;> simp [execution, info]

def policy (rootChoice secondChoice : Bool) : information.Policy ()
  | none => ⟨none, by simp⟩
  | some false => ⟨some rootChoice, by simp⟩
  | some true => ⟨some secondChoice, by simp⟩

def profile (rootChoice secondChoice : Bool) :
    (i : PUnit) → information.BehavioralPolicy i
  | () => (policy rootChoice secondChoice).toBehavioral

/-- A whole policy is evaluated through both decisions, including the
continuation after the incumbent's zero-reach `stop` branch. -/
theorem finalStateLaw (rootChoice secondChoice : Bool) :
    (information.runBehavioralFrom
      (profile rootChoice secondChoice) 2 execution.initHistory).map
        (fun history => history.state) =
      PMF.pure (.done (rootChoice && secondChoice)) := by
  rw [show information.runBehavioralFrom
      (profile rootChoice secondChoice) 2 execution.initHistory =
        information.runFrom (fun _ => policy rootChoice secondChoice)
          2 execution.initHistory from
    information.runBehavioralFrom_toBehavioral
      (fun _ => policy rootChoice secondChoice) 2 execution.initHistory]
  cases rootChoice <;> cases secondChoice <;>
    simp [InformationModel.runFrom, ExecutionProtocol.runHistoryFor,
      InformationModel.historyChooser, InformationModel.jointAt,
      InformationModel.Policy.act, ExecutionProtocol.initHistory,
      InfoSignals.infoOf, History.extend, signals, policy, info] <;>
    rw [PMF.pure_map]

theorem rootOnlyDeviationStillLoses :
    (information.runBehavioralFrom
      (profile true false) 2 execution.initHistory).map
        (fun history => history.state) = PMF.pure (.done false) := by
  simpa using finalStateLaw true false

theorem fullPolicyDeviationWins :
    (information.runBehavioralFrom
      (profile true true) 2 execution.initHistory).map
        (fun history => history.state) = PMF.pure (.done true) := by
  simpa using finalStateLaw true true

theorem rootGoLegal : execution.Legal .root (fun _ => some true) := by
  constructor
  · simp
  · intro i
    cases i
    simp [IsLegalJoint, execution, info]

abbrev secondHistory : execution.History :=
  execution.initHistory.extend rootGoLegal (by
    show Scene.second ∈
      (execution.step .root ⟨fun _ => some true, rootGoLegal⟩).support
    simp [execution])

theorem secondHistory_info :
    information.infoOf () secondHistory.trace = some true := by
  exact signals_infoOf secondHistory.trace ()

def secondSite : information.InformationSite () :=
  information.informationSite () secondHistory true
    (by simp [secondHistory, History.extend, execution]) (by
      rw [secondHistory_info]
      simp)

theorem secondSite_info : secondSite.1 = some true :=
  secondHistory_info

def incumbentAssessment : information.BehavioralAssessment :=
  InformationModel.BehavioralAssessment.ofStrategy (profile false false)

theorem incumbentAssessment_strategy :
    incumbentAssessment.strategy = profile false false := rfl

theorem incumbentOneStepStateLaw :
    (information.runBehavioralFrom (profile false false) 1
      execution.initHistory).map (fun history => history.state) =
      PMF.pure (.done false) := by
  rw [show information.runBehavioralFrom (profile false false) 1
      execution.initHistory =
    information.runFrom (fun _ => policy false false) 1
      execution.initHistory from
    information.runBehavioralFrom_toBehavioral
      (fun _ => policy false false) 1 execution.initHistory]
  simp [InformationModel.runFrom, ExecutionProtocol.runHistoryFor,
    InformationModel.historyChooser, InformationModel.jointAt,
    InformationModel.Policy.act, ExecutionProtocol.initHistory,
    InfoSignals.infoOf, History.extend, signals, policy, info]
  rw [PMF.pure_map]

theorem secondHistory_zeroIncumbentReach :
    secondHistory ∉
      (information.runBehavioralFrom (profile false false) 1
        execution.initHistory).support := by
  intro hreach
  have hstate : Scene.second ∈
      ((information.runBehavioralFrom (profile false false) 1
        execution.initHistory).map (fun history => history.state)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨secondHistory, hreach, rfl⟩
  rw [incumbentOneStepStateLaw] at hstate
  simp at hstate

theorem secondSite_hasBelief :
    ∃ history : information.InformationHistory () secondSite.1,
      history ∈ (incumbentAssessment.belief () secondSite).support := by
  exact (incumbentAssessment.belief () secondSite).support_nonempty

theorem secondSite_historyState
    (history : information.InformationHistory () secondSite.1) :
    history.1.state = .second := by
  have hinfo := signals_infoOf history.1.trace ()
  have hscene : info history.1.state = some true :=
    hinfo.symm.trans (history.2.trans secondSite_info)
  cases hstate : history.1.state with
  | root => simp [hstate, info] at hscene
  | second => rfl
  | done win => simp [hstate, info] at hscene

def remaining : Scene → ℕ
  | .root => 2
  | .second => 1
  | .done _ => 0

theorem remaining_decreases {state target : Scene}
    {joint : ∀ _ : PUnit, Option Bool}
    (hlegal : execution.Legal state joint)
    (hrealized : target ∈ (execution.step state ⟨joint, hlegal⟩).support) :
    remaining target + 1 ≤ remaining state := by
  cases state with
  | root =>
      by_cases hgo : (joint ()).getD false
      · have heq : target = .second := by
          simpa [execution, hgo] using hrealized
        simp [heq, remaining]
      · have heq : target = .done false := by
          simpa [execution, hgo] using hrealized
        simp [heq, remaining]
  | second =>
      have heq : target = .done ((joint ()).getD false) := by
        simpa [execution] using hrealized
      simp [heq, remaining]
  | done win => exact False.elim (hlegal.1 trivial)

theorem trace_rank_bound {state : Scene} (trace : Trace execution state) :
    remaining state + trace.length ≤ 2 := by
  exact Trace.rec
    (motive := fun state tr => remaining state + tr.length ≤ 2)
    (by decide)
    (by
      intro source target prior joint legal realized ih
      have hdec := remaining_decreases legal realized
      simp only [Trace.length]
      omega)
    trace

theorem trace_length_zero_root {state : Scene}
    (trace : Trace execution state) (hzero : trace.length = 0) :
    state = .root := by
  exact Trace.rec
    (motive := fun (state : Scene) tr => tr.length = 0 → state = Scene.root)
    (by intro _; rfl)
    (by intro source target prior joint legal realized ih hz
        simp [Trace.length] at hz)
    trace hzero

theorem secondSite_historyDepth
    (history : information.InformationHistory () secondSite.1) :
    history.1.trace.length = 1 := by
  have hrank := trace_rank_bound history.1.trace
  have hremaining : remaining history.1.state = 1 := by
    rw [secondSite_historyState history]
    rfl
  have hpositive : 0 < history.1.trace.length := by
    by_contra hn
    have hzero : history.1.trace.length = 0 := by omega
    have hroot := trace_length_zero_root history.1.trace hzero
    exact Scene.noConfusion ((secondSite_historyState history).symm.trans hroot)
  omega

theorem secondSite_zeroIncumbentReach
    (history : information.InformationHistory () secondSite.1) :
    history.1 ∉
      (information.runBehavioralFrom (profile false false) 1
        execution.initHistory).support := by
  intro hreach
  have hstate : Scene.second ∈
      ((information.runBehavioralFrom (profile false false) 1
        execution.initHistory).map (fun h => h.state)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨history.1, hreach, secondSite_historyState history⟩
  rw [incumbentOneStepStateLaw] at hstate
  simp at hstate

theorem secondSite_zeroIncumbentMass :
    information.informationMass
      incumbentAssessment.strategy () secondSite = 0 := by
  unfold InformationModel.informationMass
  simp only [incumbentAssessment_strategy]
  apply ENNReal.tsum_eq_zero.mpr
  intro history
  unfold InformationModel.historyReachWeight InformationModel.runBehavioral
  rw [secondSite_historyDepth history]
  exact (PMF.apply_eq_zero_iff _ _).2
    (secondSite_zeroIncumbentReach history)

theorem secondFromStateLaw (rootChoice secondChoice : Bool)
    (history : execution.History) (hstate : history.state = .second) :
    (information.runBehavioralFrom
      (profile rootChoice secondChoice) 2 history).map
        (fun next => next.state) = PMF.pure (.done secondChoice) := by
  obtain ⟨state, trace⟩ := history
  cases state with
  | root => simp at hstate
  | done win => simp at hstate
  | second =>
      have hinfo : information.infoOf () trace = some true := by
        simpa [info] using signals_infoOf trace ()
      have hsignal : signals.infoOf () trace = some true := hinfo
      rw [show information.runBehavioralFrom
          (profile rootChoice secondChoice) 2 ⟨.second, trace⟩ =
        information.runFrom (fun _ => policy rootChoice secondChoice)
          2 ⟨.second, trace⟩ from
        information.runBehavioralFrom_toBehavioral
          (fun _ => policy rootChoice secondChoice) 2 ⟨.second, trace⟩]
      simp [InformationModel.runFrom, ExecutionProtocol.runHistoryFor,
        InformationModel.historyChooser, InformationModel.jointAt,
        InformationModel.Policy.act, policy, info, History.extend]
      rw [PMF.pure_map]
      have haction :
          ((policy rootChoice secondChoice (signals.infoOf () trace)).1).getD false =
            secondChoice := by
        rw [hsignal]
        rfl
      exact congrArg (fun action : Bool => PMF.pure (Scene.done action))
        haction

def statePayoff : Scene → ℝ
  | .done true => 1
  | _ => 0

def payoff : execution.History → ℝ :=
  fun history => statePayoff history.state

theorem statePayoff_bounded (state : Scene) :
    |statePayoff state| ≤ 1 := by
  cases state with
  | root => simp [statePayoff]
  | second => simp [statePayoff]
  | done win => cases win <;> simp [statePayoff]

theorem payoff_bounded (history : execution.History) :
    |payoff history| ≤ 1 :=
  statePayoff_bounded history.state

theorem contextStateLaw (rootChoice secondChoice : Bool) :
    ((incumbentAssessment.continuationContext secondSite payoff 2).outcome
      ((policy rootChoice secondChoice).toBehavioral)).map
        (fun history => history.state) =
      PMF.pure (.done secondChoice) := by
  rw [InformationModel.BehavioralAssessment.continuationContext,
    Context.ofBelief, PMF.map_bind]
  have hprofile : Profile.update
      (sig := information.behavioralSignature)
      incumbentAssessment.strategy ()
        ((policy rootChoice secondChoice).toBehavioral) =
      profile rootChoice secondChoice := by
    funext i
    cases i
    simp [profile, Profile.update_same]
  simp only [hprofile]
  calc
    _ = (incumbentAssessment.belief () secondSite).bind
          (fun _ => PMF.pure (Scene.done secondChoice)) := by
        apply bind_congr_on_support
        intro history _
        exact secondFromStateLaw rootChoice secondChoice history.1
          (secondSite_historyState history)
    _ = PMF.pure (.done secondChoice) := PMF.bind_const _ _

theorem expect_of_stateLaw (law : PMF execution.History) (result : Bool)
    (hlaw : law.map (fun history => history.state) = PMF.pure (.done result))
    (hintegrable : PayoffIntegrable law payoff) :
    expect law payoff hintegrable = if result then 1 else 0 := by
  have hconst : PayoffIntegrable law (fun _ => if result then 1 else 0) :=
    payoffIntegrable_of_bounded (C := 1) _ _ (by
      intro history
      cases result <;> norm_num)
  have hpayoff (history : execution.History) (hsupport : history ∈ law.support) :
      payoff history = if result then 1 else 0 := by
    have hstate : history.state ∈
        (law.map (fun next => next.state)).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨history, hsupport, rfl⟩
    rw [hlaw, PMF.mem_support_pure_iff] at hstate
    cases result <;> simp [payoff, statePayoff, hstate]
  calc
    expect law payoff hintegrable =
        expect law (fun _ => if result then 1 else 0) hconst :=
      expect_congr_on_support hpayoff hintegrable hconst
    _ = if result then 1 else 0 := expect_constant law _ hconst

theorem contextValue (rootChoice secondChoice : Bool)
    (hintegrable :
      (incumbentAssessment.continuationContext secondSite payoff 2).IntegrableAt
        ((policy rootChoice secondChoice).toBehavioral)) :
    (incumbentAssessment.continuationContext secondSite payoff 2).value
      ((policy rootChoice secondChoice).toBehavioral) hintegrable =
        if secondChoice then 1 else 0 := by
  exact expect_of_stateLaw _ secondChoice
    (contextStateLaw rootChoice secondChoice) hintegrable

theorem incumbent_not_locallyOptimalAtSecond :
    ¬ (incumbentAssessment.continuationContext secondSite payoff 2).IsLocallyOptimal
      Set.univ (incumbentAssessment.strategy ()) := by
  intro hoptimal
  let ctx := incumbentAssessment.continuationContext secondSite payoff 2
  have hinc : ctx.IntegrableAt (incumbentAssessment.strategy ()) := hoptimal.1
  have halt : ctx.IntegrableAt ((policy false true).toBehavioral) :=
    payoffIntegrable_of_bounded _ _ payoff_bounded
  have hcompare := hoptimal.2.2
    ((policy false true).toBehavioral) (Set.mem_univ _) hinc halt
  have hincValue := contextValue false false
    (by simpa [ctx, incumbentAssessment_strategy, profile] using hinc)
  have haltValue := contextValue false true halt
  simp only [incumbentAssessment_strategy, profile] at hcompare
  rw [hincValue, haltValue] at hcompare
  norm_num at hcompare

theorem incumbent_not_sequentiallyRationalWithin :
    ¬ incumbentAssessment.IsSequentiallyRationalWithin
      (fun _ => payoff) 2 := by
  intro hrational
  exact incumbent_not_locallyOptimalAtSecond (hrational () secondSite)

end OffPath

end GameTheory.Experimental.PMFSequentialGate
