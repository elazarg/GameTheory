/-
# Same-trace two-player Protocol regret learning

Two Boolean players act simultaneously in the existing one-shot FOSG
Protocol.  Both run local counterfactual regret matching, and their learned
laws are assembled into one zero-sum action trace.  The payoff is separable but
not constant: both players have a strict improving action, both initial regret
contributions are positive, and both learned laws move.
-/

import GameTheory.Analysis.Protocol.CounterfactualRootRegret
import GameTheory.Analysis.ZeroSumLearning
import GameTheory.Examples.FOSG

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualZeroSumLearningTest

open Filter GameTheory Probability Protocol
open GameTheory.Languages GameTheory.Languages.NFG.OneShotFOSG
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Approachability
open GameTheoryMath.Approachability GameTheoryMath.OrthantProjection

abbrev source := GameTheory.Examples.FOSG.twoBit
abbrev execution := source.execution
abbrev information := source.information

local instance infoDecidableEq (who : Bool) :
    DecidableEq (information.InfoState who) := Classical.decEq _

def initialSite (who : Bool) : information.InformationSite who :=
  information.informationSite who execution.initHistory false
    (by simp [execution])
    (by
      show some false ∈ NFG.OneShotFOSG.menu
        GameTheory.Examples.FOSG.twoBitSource who (.acting)
      exact ⟨false, rfl⟩)

@[simp]
theorem initialSite_info (who : Bool) :
    (initialSite who).1 = (show information.InfoState who from .acting) := rfl

def choiceOfAction (who action : Bool) :
    information.Choice who (initialSite who).1 :=
  ⟨some action, by
    show ∃ current : Bool, some action = some current
    exact ⟨action, rfl⟩⟩

private theorem exists_action_eq (who : Bool)
    (choice : information.Choice who (initialSite who).1) :
    ∃ action : Bool, choice.1 = some action := by
  rcases choice with ⟨value, hchoice⟩
  cases value with
  | none =>
      rw [initialSite_info] at hchoice
      simp [NFG.OneShotFOSG.menu] at hchoice
  | some action => exact ⟨action, rfl⟩

def actionOfChoice (who : Bool)
    (choice : information.Choice who (initialSite who).1) : Bool :=
  Classical.choose (exists_action_eq who choice)

theorem choice_eq_some_actionOfChoice (who : Bool)
    (choice : information.Choice who (initialSite who).1) :
    choice.1 = some (actionOfChoice who choice) :=
  Classical.choose_spec (exists_action_eq who choice)

def initialChoiceEquiv (who : Bool) :
    information.Choice who (initialSite who).1 ≃ Bool where
  toFun := actionOfChoice who
  invFun := choiceOfAction who
  left_inv choice := by
    apply Subtype.ext
    exact (choice_eq_some_actionOfChoice who choice).symm
  right_inv action := by
    have h := choice_eq_some_actionOfChoice who (choiceOfAction who action)
    exact Option.some.inj h.symm

@[simp]
theorem actionOfChoice_choiceOfAction (who action : Bool) :
    actionOfChoice who (choiceOfAction who action) = action :=
  (initialChoiceEquiv who).apply_symm_apply action

local instance initialChoiceFintype (who : Bool) :
    Fintype (information.Choice who (initialSite who).1) := by
  exact Fintype.ofEquiv Bool (initialChoiceEquiv who).symm

local instance initialChoiceNonempty (who : Bool) :
    Nonempty (information.Choice who (initialSite who).1) := by
  exact ⟨choiceOfAction who false⟩

theorem initial_not_mem_step
    (state : NFG.OneShotFOSG.State GameTheory.Examples.FOSG.twoBitSource)
    (joint : Bool → Option Bool) (hlegal : execution.Legal state joint) :
    NFG.OneShotFOSG.State.initial ∉
      (execution.step state ⟨joint, hlegal⟩).support := by
  cases state with
  | initial => simp [execution]
  | finished actions => exact False.elim (hlegal.1 trivial)

theorem trace_initial_eq_start :
  ∀ trace : execution.Trace NFG.OneShotFOSG.State.initial,
      trace = .start
  | .start => rfl
  | .extend _ joint isLegal realized =>
      False.elim (initial_not_mem_step _ joint isLegal realized)

theorem initialInformationHistory_eq (who : Bool)
    (history : information.InformationHistory who (initialSite who).1) :
    history.1 = execution.initHistory := by
  rcases history with ⟨⟨state, trace⟩, hinfo⟩
  rw [NFG.OneShotFOSG.infoOf_eq_viewOfState] at hinfo
  cases state with
  | finished actions => simp [NFG.OneShotFOSG.viewOfState] at hinfo
  | initial =>
      show (⟨NFG.OneShotFOSG.State.initial, trace⟩ : execution.History) =
        execution.initHistory
      rw [trace_initial_eq_start trace]
      rfl

def initialHistoryEquivUnit (who : Bool) :
    information.InformationHistory who (initialSite who).1 ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨execution.initHistory, rfl⟩
  left_inv history := by
    apply Subtype.ext
    exact (initialInformationHistory_eq who history).symm
  right_inv value := by cases value; rfl

local instance initialHistoryFintype (who : Bool) :
    Fintype (information.InformationHistory who (initialSite who).1) :=
  Fintype.ofEquiv Unit (initialHistoryEquivUnit who).symm

local instance initialHistoryUnique (who : Bool) :
    Unique (information.InformationHistory who (initialSite who).1) where
  default := ⟨execution.initHistory, rfl⟩
  uniq history := by
    apply Subtype.ext
    exact initialInformationHistory_eq who history

theorem initialSite_allNonterminal (who : Bool) :
    InformationSite.AllNonterminal information (initialSite who) := by
  intro history
  rw [initialInformationHistory_eq who history]
  simp [execution]

theorem information_actsOnce : information.ActsOnceWhereItMatters := by
  intro who state trace
  cases trace with
  | start => simp [InfoSignals.actedAt]
  | @extend priorState _ prior joint isLegal realized =>
      cases priorState with
      | finished actions => exact False.elim (isLegal.1 trivial)
      | initial =>
          rw [trace_initial_eq_start prior]
          cases hchoice : joint who <;> simp [InfoSignals.actedAt, hchoice]

def fallbackChoice (who : Bool) :
    information.Choice who (initialSite who).1 :=
  Classical.choice (initialChoiceNonempty who)

def fallbackAction (who : Bool) : Bool :=
  actionOfChoice who (fallbackChoice who)

def improvingChoice (who : Bool) :
    information.Choice who (initialSite who).1 :=
  choiceOfAction who !(fallbackAction who)

def score (who action : Bool) : ℝ :=
  if action = fallbackAction who then 0 else 1

theorem fallbackChoice_eq_choiceOfAction (who : Bool) :
    fallbackChoice who = choiceOfAction who (fallbackAction who) := by
  apply Subtype.ext
  exact choice_eq_some_actionOfChoice who (fallbackChoice who)

@[simp]
theorem score_fallbackAction (who : Bool) : score who (fallbackAction who) = 0 := by
  simp [score]

@[simp]
theorem score_improvingAction (who : Bool) :
    score who (!(fallbackAction who)) = 1 := by
  cases haction : fallbackAction who <;> simp [score, haction]

/-- The row values its own `true` action; the column has the opposite utility
and therefore values its own `true` action as well. -/
def matrixPayoff
    (row : information.Choice false (initialSite false).1)
    (col : information.Choice true (initialSite true).1) : ℝ :=
  score false (actionOfChoice false row) -
    score true (actionOfChoice true col)

def outcomeUtility
    (outcome : GameTheory.Examples.FOSG.twoBitSource.Outcome)
    (who : Bool) : ℝ :=
  if who then score true outcome.2 - score false outcome.1
  else score false outcome.1 - score true outcome.2

def protocolUtility (history : execution.History) (who : Bool) : ℝ :=
  NFG.OneShotFOSG.utilityOfOutcome GameTheory.Examples.FOSG.twoBitSource
    outcomeUtility
    (NFG.OneShotFOSG.outcomeOfState
      GameTheory.Examples.FOSG.twoBitSource history.state) who

def actionPolicy (who action : Bool) : information.BehavioralPolicy who :=
  (NFG.OneShotFOSG.Policy.ofAction
    GameTheory.Examples.FOSG.twoBitSource action).toBehavioral

def behavioralProfile (actions : Bool → Bool) :
    (who : Bool) → information.BehavioralPolicy who :=
  fun who => actionPolicy who (actions who)

@[simp]
theorem outcomeUtility_twoBit (actions : Bool → Bool) (who : Bool) :
    outcomeUtility
        (GameTheory.Examples.FOSG.twoBitSource.outcome actions) who =
      if who then score true (actions true) - score false (actions false)
      else score false (actions false) - score true (actions true) := by
  cases who <;>
    simp [outcomeUtility, GameTheory.Examples.FOSG.twoBitSource]

theorem expectedUtility_behavioralProfile (actions : Bool → Bool)
    (who : Bool) :
    expectedUtility protocolUtility who
        (information.runBehavioral (behavioralProfile actions) 1) =
      if who then score true (actions true) - score false (actions false)
      else score false (actions false) - score true (actions true) := by
  let policies := NFG.OneShotFOSG.policyProfile
    GameTheory.Examples.FOSG.twoBitSource actions
  have hbehavioral : behavioralProfile actions =
      fun player => (policies player).toBehavioral := rfl
  rw [hbehavioral, ← InformationModel.toBehavioralGameForm_play]
  calc
    expectedUtility protocolUtility who
        ((information.toBehavioralGameForm 1).play
          (fun player => (policies player).toBehavioral)) =
      expectedUtility protocolUtility who
        ((information.toGameForm 1).play policies) := by
          rw [InformationModel.toBehavioralGameForm_play_toBehavioral]
    _ = expectedUtility
        (NFG.OneShotFOSG.utilityOfOutcome
          GameTheory.Examples.FOSG.twoBitSource outcomeUtility) who
        (FinDist.map
          (fun history => NFG.OneShotFOSG.outcomeOfState
            GameTheory.Examples.FOSG.twoBitSource history.state)
          ((information.toGameForm 1).play policies)) := by
            rw [expectedUtility_map]
            rfl
    _ = expectedUtility
        (NFG.OneShotFOSG.utilityOfOutcome
          GameTheory.Examples.FOSG.twoBitSource outcomeUtility) who
        ((NFG.OneShotFOSG.toProtocolForm
          GameTheory.Examples.FOSG.twoBitSource).play
            (NFG.OneShotFOSG.policyProfile
              GameTheory.Examples.FOSG.twoBitSource actions)) := rfl
    _ = _ := by
      rw [NFG.OneShotFOSG.toProtocolForm_play_policyProfile]
      simp only [FinDist.map_pure, expectedUtility_pure,
        NFG.OneShotFOSG.utilityOfOutcome]
      exact outcomeUtility_twoBit actions who

def baselineProfile : (who : Bool) → information.BehavioralPolicy who :=
  fun who => actionPolicy who (fallbackAction who)

def committedActions (who : Bool)
    (choice : information.Choice who (initialSite who).1) : Bool → Bool :=
  fun player => if player = who then actionOfChoice who choice
    else fallbackAction player

theorem run_updatedBaseline_eq_behavioralProfile (who : Bool)
    (choice : information.Choice who (initialSite who).1) :
    information.runBehavioral
        (Profile.update (sig := information.behavioralSignature)
          baselineProfile who
            ((baselineProfile who).commit (initialSite who).1 choice)) 1 =
      information.runBehavioral
        (behavioralProfile (committedActions who choice)) 1 := by
  unfold InformationModel.runBehavioral
  apply information.runBehavioralFrom_congr
  intro history _hreach hnonterminal player
  have hhistory : history = execution.initHistory := by
    rcases history with ⟨state, trace⟩
    cases state with
    | finished actions => exact False.elim (hnonterminal trivial)
    | initial =>
        show (⟨NFG.OneShotFOSG.State.initial, trace⟩ : execution.History) =
          execution.initHistory
        rw [trace_initial_eq_start trace]
        rfl
  subst history
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same]
    show (baselineProfile who).commit (initialSite who).1 choice
        (initialSite who).1 =
      behavioralProfile (committedActions who choice) who (initialSite who).1
    rw [BehavioralPolicy.commit_self (M := information)]
    apply congrArg FinDist.pure
    apply Subtype.ext
    calc
      choice.1 = some (actionOfChoice who choice) :=
        choice_eq_some_actionOfChoice who choice
      _ = _ := by
        show some (actionOfChoice who choice) =
          some (committedActions who choice who)
        simp [committedActions]
  · rw [Profile.update_of_ne _ _ hplayer]
    show baselineProfile player (initialSite player).1 =
      behavioralProfile (committedActions who choice) player
        (initialSite player).1
    simp [baselineProfile, behavioralProfile, committedActions, hplayer]

def localStrategyOf (who : Bool)
    (law : FinDist (information.Choice who (initialSite who).1)) (_ : Unit) :
    (player : Bool) → information.BehavioralPolicy player :=
  strategyWithLocalLaw information baselineProfile who (initialSite who) law

def localUtility (who : Bool)
    (choice : information.Choice who (initialSite who).1) (_ : Unit) : ℝ :=
  score who (actionOfChoice who choice)

def localPayoff (who : Bool) (_ : Unit) : execution.History → ℝ :=
  fun history => protocolUtility history who

theorem initial_counterfactualActionUtility (who : Bool)
    (choice : information.Choice who (initialSite who).1) :
    counterfactualActionUtility information baselineProfile who
        (initialSite who) (fun history => protocolUtility history who) 1 choice =
      score who (actionOfChoice who choice) := by
  unfold counterfactualActionUtility counterfactualContinuationValue
  rw [Fintype.sum_unique]
  unfold behavioralContinuationValue
  rw [initialInformationHistory_eq who
    (default : information.InformationHistory who (initialSite who).1)]
  have hreach : information.counterfactualReachProbability baselineProfile who
      execution.initHistory.trace = 1 := rfl
  rw [hreach, one_mul]
  have hrun := congrArg (expectedUtility protocolUtility who)
    (run_updatedBaseline_eq_behavioralProfile who choice)
  rw [expectedUtility_behavioralProfile] at hrun
  unfold expectedUtility at hrun
  cases who <;>
    simpa [InformationModel.runBehavioral, committedActions] using hrun

theorem local_realization (who : Bool)
    (law : FinDist (information.Choice who (initialSite who).1))
    (environment : Unit) :
    localCounterfactualRegretVector information
        (localStrategyOf who law environment) who (initialSite who)
          (localPayoff who environment) 1 =
      regretPayoff (localUtility who) law environment := by
  have h := information.localCounterfactualRegretVector_strategyWithLocalLaw
    information_actsOnce baselineProfile who (initialSite who)
      (initialSite_allNonterminal who) law
      (fun history => protocolUtility history who) 0 environment
  unfold localStrategyOf localPayoff
  rw [h]
  congr 2
  funext choice current
  exact initial_counterfactualActionUtility who choice

theorem localUtility_mem_Icc (who : Bool)
    (choice : information.Choice who (initialSite who).1)
    (environment : Unit) : localUtility who choice environment ∈ Set.Icc 0 1 := by
  by_cases haction : actionOfChoice who choice = fallbackAction who <;>
    simp [localUtility, score, haction]

theorem local_regretPayoff_norm_le (who : Bool)
    (law : FinDist (information.Choice who (initialSite who).1))
    (environment : Unit) :
    ‖regretPayoff (localUtility who) law environment‖ ≤
      (Fintype.card (information.Choice who (initialSite who).1) : ℝ) := by
  simpa using regretPayoff_norm_le_card_mul_width (localUtility who)
    (lo := 0) (hi := 1) (localUtility_mem_Icc who) law environment

def localAverage (who : Bool) (t : ℕ) :
    EuclideanSpace ℝ (information.Choice who (initialSite who).1) :=
  counterfactualRegretMatchAverage information who (initialSite who)
    (localStrategyOf who) (localPayoff who) 1 (fun _ => ()) t

def learnedLaw (who : Bool) (round : ℕ) :
    FinDist (information.Choice who (initialSite who).1) :=
  regretMatch (localAverage who round)

def localGain (who : Bool)
    (deviation : information.Choice who (initialSite who).1)
    (round : ℕ) : ℝ :=
  localUtility who deviation () -
    (learnedLaw who round).expect (fun current => localUtility who current ())

theorem localVector_coordinate_eq_gain (who : Bool)
    (deviation : information.Choice who (initialSite who).1)
    (round : ℕ) :
    (localCounterfactualRegretVector information
      (localStrategyOf who (learnedLaw who round) ()) who (initialSite who)
        (localPayoff who ()) 1).ofLp deviation = localGain who deviation round := by
  rw [local_realization, regretPayoff_ofLp]
  rfl

theorem learnedLaw_zero (who : Bool) :
    learnedLaw who 0 = FinDist.pure (fallbackChoice who) := by
  simp [learnedLaw, localAverage, counterfactualRegretMatchAverage,
    avgVec, regretMatch, fallbackChoice]

theorem localGain_improving_zero (who : Bool) :
    localGain who (improvingChoice who) 0 = 1 := by
  rw [localGain, learnedLaw_zero, FinDist.expect_pure]
  rw [fallbackChoice_eq_choiceOfAction]
  simp [localUtility, improvingChoice]

theorem localAverage_one_improving (who : Bool) :
    (localAverage who 1).ofLp (improvingChoice who) = 1 := by
  unfold localAverage counterfactualRegretMatchAverage
  simp only [avgVec]
  norm_num
  simpa [learnedLaw, localAverage, counterfactualRegretMatchAverage, avgVec]
    using (localVector_coordinate_eq_gain who (improvingChoice who) 0).trans
      (localGain_improving_zero who)

theorem localAverage_one_positiveSum (who : Bool) :
    0 < ∑ choice, max ((localAverage who 1).ofLp choice) 0 := by
  have hle : max ((localAverage who 1).ofLp (improvingChoice who)) 0 ≤
      ∑ choice, max ((localAverage who 1).ofLp choice) 0 :=
    Finset.single_le_sum
      (fun current _ => le_max_right _ 0)
      (Finset.mem_univ (improvingChoice who))
  rw [localAverage_one_improving] at hle
  norm_num at hle ⊢
  exact lt_of_lt_of_le zero_lt_one hle

theorem learnedLaw_one_expectedUtility_pos (who : Bool) :
    0 < (learnedLaw who 1).expect
      (fun choice => localUtility who choice ()) := by
  have hnumer : 0 < ∑ choice,
      max ((localAverage who 1).ofLp choice) 0 *
        localUtility who choice () := by
    have hle :
        max ((localAverage who 1).ofLp (improvingChoice who)) 0 *
            localUtility who (improvingChoice who) () ≤
          ∑ choice,
            max ((localAverage who 1).ofLp choice) 0 *
              localUtility who choice () :=
      Finset.single_le_sum
        (fun current _ => mul_nonneg (le_max_right _ 0)
          (localUtility_mem_Icc who current ()).1)
        (Finset.mem_univ (improvingChoice who))
    rw [localAverage_one_improving] at hle
    simp [localUtility, improvingChoice] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  rw [learnedLaw,
    expect_regretMatch_pos (localAverage_one_positiveSum who)]
  exact div_pos hnumer (localAverage_one_positiveSum who)

theorem learnedLaw_zero_expectedUtility (who : Bool) :
    (learnedLaw who 0).expect
      (fun choice => localUtility who choice ()) = 0 := by
  rw [learnedLaw_zero, FinDist.expect_pure, fallbackChoice_eq_choiceOfAction]
  simp [localUtility]

/-- The hostile fixture genuinely learns: after observing the initial round,
the next law differs from the arbitrary fallback law. -/
theorem learnedLaw_one_ne_zero (who : Bool) :
    learnedLaw who 1 ≠ learnedLaw who 0 := by
  intro heq
  have hexpect := congrArg
    (fun law : FinDist (information.Choice who (initialSite who).1) =>
      law.expect (fun choice => localUtility who choice ())) heq
  rw [learnedLaw_zero_expectedUtility] at hexpect
  linarith [learnedLaw_one_expectedUtility_pos who]

def mixedRoundProfile (round : ℕ) :
    Profile (MatrixGame.form
      (information.Choice false (initialSite false).1)
      (information.Choice true (initialSite true).1)).sig.mixed :=
  MatrixGame.mixedProfile (learnedLaw false round) (learnedLaw true round)

def roundLaw (round : ℕ) :
    FinDist (Profile (MatrixGame.form
      (information.Choice false (initialSite false).1)
      (information.Choice true (initialSite true).1)).sig) :=
  FinDist.pi (mixedRoundProfile round)

theorem expectedPayoff_eq_scoreDifference
    (row : FinDist (information.Choice false (initialSite false).1))
    (col : FinDist (information.Choice true (initialSite true).1)) :
    MatrixGame.expectedPayoff matrixPayoff row col =
      row.expect (fun choice => localUtility false choice ()) -
        col.expect (fun choice => localUtility true choice ()) := by
  exact MatrixGame.expectedPayoff_sub
    (fun choice => localUtility false choice ())
    (fun choice => localUtility true choice ()) row col

theorem local_approaches (who : Bool) :
    Tendsto
      (fun t => Metric.infDist (localAverage who t) nonposOrthant)
      atTop (nhds 0) := by
  simpa only [localAverage, counterfactualRegretMatchAverage] using
    counterfactualRegretMatch_approaches information who (initialSite who)
      (localUtility who) (localStrategyOf who) (localPayoff who) 1
      (local_realization who) (bound :=
        Fintype.card (information.Choice who (initialSite who).1))
      (by positivity) (local_regretPayoff_norm_le who) (fun _ => ())

theorem localGain_positiveAverage_tendsto_zero (who : Bool) :
    ∀ deviation : information.Choice who (initialSite who).1,
      Tendsto
        (fun t => max
          ((∑ round ∈ Finset.range t, localGain who deviation round) /
            (t : ℝ)) 0)
        atTop (nhds 0) := by
  apply counterfactualRegretMatches_positiveRootGains_tendsto_zero
    information (fun _ : Unit => Unit) who (fun _ => initialSite who)
    (fun _ => localStrategyOf who) (fun _ => localPayoff who)
    (fun _ => 1) (fun _ _ => ()) (localGain who)
    (fun _ _ => 1) (fun _ _ => by exact ⟨by norm_num, by norm_num⟩)
    (fun deviation _ => deviation)
  · intro deviation round
    rw [Fintype.sum_unique, one_mul]
    exact (localVector_coordinate_eq_gain who deviation round).ge
  · intro key
    cases key
    exact local_approaches who

theorem rowExternalRegret_roundLaw_eq_localGain
    (row : information.Choice false (initialSite false).1) (round : ℕ) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw round) 0 row = localGain false row round := by
  rw [roundLaw, (MatrixGame.utilityGame matrixPayoff).externalRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_zero,
    MatrixGame.expectedUtility_zero_mixedProfile,
    MatrixGame.expectedUtility_zero_mixedProfile,
    expectedPayoff_eq_scoreDifference,
    expectedPayoff_eq_scoreDifference]
  unfold localGain
  have hpure : (FinDist.pure row).expect
      (fun choice => localUtility false choice ()) =
        localUtility false row () := FinDist.expect_pure ..
  calc
    _ = (FinDist.pure row).expect
          (fun choice => localUtility false choice ()) -
        (learnedLaw false round).expect
          (fun choice => localUtility false choice ()) := by
            let a : ℝ := (FinDist.pure row).expect
              (fun choice => localUtility false choice ())
            let b : ℝ := (learnedLaw false round).expect
              (fun choice => localUtility false choice ())
            let c : ℝ := (learnedLaw true round).expect
              (fun choice => localUtility true choice ())
            show (a - c) - (b - c) = a - b
            ring
    _ = _ := congrArg (fun value => value -
      (learnedLaw false round).expect
        (fun choice => localUtility false choice ())) hpure

theorem columnExternalRegret_roundLaw_eq_localGain
    (col : information.Choice true (initialSite true).1) (round : ℕ) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw round) 1 col = localGain true col round := by
  rw [roundLaw, (MatrixGame.utilityGame matrixPayoff).externalRegret_pi]
  unfold mixedRoundProfile
  rw [MatrixGame.mixedProfile_update_one,
    MatrixGame.expectedUtility_one_mixedProfile,
    MatrixGame.expectedUtility_one_mixedProfile,
    expectedPayoff_eq_scoreDifference,
    expectedPayoff_eq_scoreDifference]
  unfold localGain
  have hpure : (FinDist.pure col).expect
      (fun choice => localUtility true choice ()) =
        localUtility true col () := FinDist.expect_pure ..
  calc
    _ = (FinDist.pure col).expect
          (fun choice => localUtility true choice ()) -
        (learnedLaw true round).expect
          (fun choice => localUtility true choice ()) := by
            let a : ℝ := (FinDist.pure col).expect
              (fun choice => localUtility true choice ())
            let b : ℝ := (learnedLaw false round).expect
              (fun choice => localUtility false choice ())
            let c : ℝ := (learnedLaw true round).expect
              (fun choice => localUtility true choice ())
            show -(b - a) - -(b - c) = a - c
            ring
    _ = _ := congrArg (fun value => value -
      (learnedLaw true round).expect
        (fun choice => localUtility true choice ())) hpure

theorem rowExternalRegret_round_zero_eq_one :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw 0) 0 (improvingChoice false) = 1 := by
  rw [rowExternalRegret_roundLaw_eq_localGain,
    localGain_improving_zero]

theorem columnExternalRegret_round_zero_eq_one :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (roundLaw 0) 1 (improvingChoice true) = 1 := by
  rw [columnExternalRegret_roundLaw_eq_localGain,
    localGain_improving_zero]

/-- Both local learners contribute to the shared initial exploitability gap;
the D51 cancellation theorem computes the exact value `2`. -/
theorem initial_saddleGap_eq_two :
    MatrixGame.expectedPayoff matrixPayoff
          (FinDist.pure (improvingChoice false))
          (MatrixGame.columnMarginal (roundLaw 0)) -
        MatrixGame.expectedPayoff matrixPayoff
          (MatrixGame.rowMarginal (roundLaw 0))
          (FinDist.pure (improvingChoice true)) = 2 := by
  rw [MatrixGame.saddleGap_eq_externalRegret_add,
    rowExternalRegret_round_zero_eq_one,
    columnExternalRegret_round_zero_eq_one]
  norm_num

def finRoundLaw {T : ℕ} (round : Fin T) :
    FinDist (Profile (MatrixGame.form
      (information.Choice false (initialSite false).1)
      (information.Choice true (initialSite true).1)).sig) :=
  roundLaw round

def averageLaw (t : ℕ) :
    FinDist (Profile (MatrixGame.form
      (information.Choice false (initialSite false).1)
      (information.Choice true (initialSite true).1)).sig) :=
  (MatrixGame.form
    (information.Choice false (initialSite false).1)
    (information.Choice true (initialSite true).1)).timeAverage
      (finRoundLaw (T := t + 1))

theorem rowExternalRegret_average_tendsto_zero
    (row : information.Choice false (initialSite false).1) :
    Tendsto
      (fun t => max
        ((MatrixGame.utilityGame matrixPayoff).externalRegret
          (averageLaw t) 0 row) 0)
      atTop (nhds 0) := by
  have hshift := (localGain_positiveAverage_tendsto_zero false row).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [averageLaw,
    (MatrixGame.utilityGame matrixPayoff).externalRegret_timeAverage]
  simp only [finRoundLaw]
  have hsum :
      (∑ round : Fin (t + 1),
        (MatrixGame.utilityGame matrixPayoff).externalRegret
          (roundLaw round) 0 row) =
        ∑ round : Fin (t + 1), localGain false row round := by
    apply Finset.sum_congr rfl
    intro round _
    exact rowExternalRegret_roundLaw_eq_localGain row round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => localGain false row round) (t + 1)]

theorem columnExternalRegret_average_tendsto_zero
    (col : information.Choice true (initialSite true).1) :
    Tendsto
      (fun t => max
        ((MatrixGame.utilityGame matrixPayoff).externalRegret
          (averageLaw t) 1 col) 0)
      atTop (nhds 0) := by
  have hshift := (localGain_positiveAverage_tendsto_zero true col).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [averageLaw,
    (MatrixGame.utilityGame matrixPayoff).externalRegret_timeAverage]
  simp only [finRoundLaw]
  have hsum :
      (∑ round : Fin (t + 1),
        (MatrixGame.utilityGame matrixPayoff).externalRegret
          (roundLaw round) 1 col) =
        ∑ round : Fin (t + 1), localGain true col round := by
    apply Finset.sum_congr rfl
    intro round _
    exact columnExternalRegret_roundLaw_eq_localGain col round
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun round => localGain true col round) (t + 1)]

def rowRegretBound (t : ℕ) : ℝ :=
  ∑ row : information.Choice false (initialSite false).1,
    max ((MatrixGame.utilityGame matrixPayoff).externalRegret
      (averageLaw t) 0 row) 0

def columnRegretBound (t : ℕ) : ℝ :=
  ∑ col : information.Choice true (initialSite true).1,
    max ((MatrixGame.utilityGame matrixPayoff).externalRegret
      (averageLaw t) 1 col) 0

theorem rowRegretBound_tendsto_zero :
    Tendsto rowRegretBound atTop (nhds 0) := by
  unfold rowRegretBound
  simpa using
    tendsto_finsetSum Finset.univ (fun row _ =>
      rowExternalRegret_average_tendsto_zero row)

theorem columnRegretBound_tendsto_zero :
    Tendsto columnRegretBound atTop (nhds 0) := by
  unfold columnRegretBound
  simpa using
    tendsto_finsetSum Finset.univ (fun col _ =>
      columnExternalRegret_average_tendsto_zero col)

theorem externalRegret_le_rowRegretBound (t : ℕ)
    (row : information.Choice false (initialSite false).1) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (averageLaw t) 0 row ≤ rowRegretBound t := by
  apply le_trans (le_max_left _ 0)
  exact Finset.single_le_sum
    (fun current _ => le_max_right _ _) (Finset.mem_univ row)

theorem externalRegret_le_columnRegretBound (t : ℕ)
    (col : information.Choice true (initialSite true).1) :
    (MatrixGame.utilityGame matrixPayoff).externalRegret
        (averageLaw t) 1 col ≤ columnRegretBound t := by
  apply le_trans (le_max_left _ 0)
  exact Finset.single_le_sum
    (fun current _ => le_max_right _ _) (Finset.mem_univ col)

/-- **Same-trace CFR-to-Nash consumer.** Both D50 bounds concern the one
time-average law assembled from the two actual local learners, and D51 turns
them into the canonical approximate mixed Nash certificate. -/
theorem empiricalMarginals_isεNash (t : ℕ) :
    IsεNash
      (MatrixGame.form
        (information.Choice false (initialSite false).1)
        (information.Choice true (initialSite true).1)).mixed
      (MatrixGame.utility matrixPayoff)
      (rowRegretBound t + columnRegretBound t)
      (MatrixGame.mixedProfile
        (MatrixGame.rowMarginal (averageLaw t))
        (MatrixGame.columnMarginal (averageLaw t))) :=
  MatrixGame.marginalProfile_isεNash_of_externalRegret_le
    matrixPayoff (averageLaw t)
      (externalRegret_le_rowRegretBound t)
      (externalRegret_le_columnRegretBound t)

theorem empiricalNashTolerance_tendsto_zero :
    Tendsto (fun t => rowRegretBound t + columnRegretBound t)
      atTop (nhds 0) := by
  simpa using rowRegretBound_tendsto_zero.add
    columnRegretBound_tendsto_zero

end GameTheory.Analysis.Protocol.CounterfactualZeroSumLearningTest
