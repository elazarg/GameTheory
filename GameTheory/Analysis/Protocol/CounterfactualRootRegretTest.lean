/-
# Hostile finite root-regret consumer

The two-site complementarity deviation is repeated unchanged.  Its canonical
root gain stays one, and the finite aggregation theorem must recover that gain
from the zero first-site vector and the unit off-path second-site vector.  This
is also the failed-learner control for the eventual convergence consumer.
-/

import GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
import GameTheory.Analysis.Protocol.CounterfactualRootRegret

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRootRegretTest

open Filter GameTheory Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest
open GameTheory.Analysis.Protocol.CounterfactualDecompositionTest
open GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
open GameTheory.Tests.SubgameOneShot
open GameTheoryMath.Approachability GameTheoryMath.OrthantProjection

/-- The two topologically relevant sites of the hostile deviation. -/
@[reducible]
def rootSite : Bool → information.InformationSite ()
  | false => firstSite
  | true => secondSite true

abbrev SecondTrueAction := information.Choice () (secondSite true).1

def secondTrueActionEquivBool : SecondTrueAction ≃ Bool where
  toFun choice := choice.1.getD false
  invFun := secondChoice true
  left_inv choice := by
    rcases choice with ⟨choice, hchoice⟩
    cases choice with
    | none =>
        simp [GameTheory.Tests.SubgameOneShot.menu,
          GameTheory.Tests.SubgameOneShot.stageMenu, secondKnowledge] at hchoice
    | some action => apply Subtype.ext; rfl
  right_inv action := by cases action <;> rfl

local instance : Fintype
    (information.InformationHistory () firstSite.1) :=
  Fintype.ofEquiv Bool firstHistoryEquivBool.symm

local instance : Fintype
    (information.InformationHistory () (secondSite true).1) :=
  Fintype.ofEquiv Bool (secondHistoryEquivBool true).symm

local instance : Fintype
    (information.Choice () firstSite.1) :=
  Fintype.ofEquiv Bool firstActionEquivBool.symm

local instance : Fintype SecondTrueAction :=
  Fintype.ofEquiv Bool secondTrueActionEquivBool.symm

local instance : Nonempty (information.Choice () firstSite.1) :=
  ⟨firstChoice false⟩

local instance : Nonempty SecondTrueAction :=
  ⟨secondChoice true false⟩

local instance (key : Bool) : Fintype
    (information.InformationHistory () (rootSite key).1) := by
  cases key
  · infer_instance
  · infer_instance

local instance (key : Bool) : Fintype
    (information.Choice () (rootSite key).1) := by
  cases key
  · infer_instance
  · infer_instance

local instance (key : Bool) : Nonempty
    (information.Choice () (rootSite key).1) := by
  cases key
  · infer_instance
  · infer_instance

/-- The coordinated pure deviation selects `true` at both sites. -/
def rootDeviation : (key : Bool) →
    information.Choice () (rootSite key).1
  | false => firstChoice true
  | true => secondChoice true true

/-- This deliberately ignores the regret matcher's law.  It repeats the bad
incumbent environment at the first site and the first-committed environment at
the off-path second site. -/
def failedStrategyOf (key : Bool)
    (_law : FinDist (information.Choice () (rootSite key).1)) (_current : Unit) :
    (player : Unit) → information.BehavioralPolicy player := by
  cases key
  · exact incumbentBehavioralStrategy
  · exact firstCommittedStrategy

def failedPayoffOf (_key : Bool) (_current : Unit) : twoStage.History → ℝ :=
  terminalPayoff

def localFuel : Bool → ℕ
  | false => 2
  | true => 1

/-- The scalar sequence is the actual canonical behavioral root gain, not a
fixture-local proxy. -/
def failedRootGain (_round : ℕ) : ℝ :=
  (information.runBehavioral finalCommittedStrategy 3).expect terminalPayoff -
    (information.runBehavioral incumbentBehavioralStrategy 3).expect
      terminalPayoff

theorem failedRootGain_eq_one (round : ℕ) : failedRootGain round = 1 :=
  wholeDeviation_rootGain_eq_one

/-- Every repeated root gain is exactly the D48 two-site sum consumed by the
finite aggregation theorem. -/
theorem failedRootGain_decomposition (round : ℕ) :
    failedRootGain round = ∑ key : Bool,
      1 *
        (localCounterfactualRegretVector information
          (failedStrategyOf key
            (regretMatch
              (counterfactualRegretMatchAverage information () (rootSite key)
                (failedStrategyOf key) (failedPayoffOf key) (localFuel key)
                (fun _ => ()) round)) ())
          () (rootSite key) terminalPayoff (localFuel key)).ofLp
            (rootDeviation key) := by
  rw [failedRootGain_eq_one]
  rw [Fintype.sum_bool]
  simp only [rootSite, failedStrategyOf, localFuel, rootDeviation, one_mul]
  rw [show
      (localCounterfactualRegretVector information
        incumbentBehavioralStrategy () firstSite terminalPayoff 2).ofLp
          (firstChoice true) =
        information.counterfactualActionRegret incumbentBehavioralStrategy ()
          firstSite terminalPayoff 2 (firstChoice true) by rfl,
    show
      (localCounterfactualRegretVector information
        firstCommittedStrategy () (secondSite true) terminalPayoff 1).ofLp
          (secondChoice true true) =
        information.counterfactualActionRegret firstCommittedStrategy ()
          (secondSite true) terminalPayoff 1 (secondChoice true true) by rfl,
    first_counterfactualActionRegret,
    firstCommitted_second_counterfactualActionRegret]
  norm_num

/-- The new finite-family theorem bounds an actual nonzero root deviation and
therefore cannot pass merely because every local term was defined. -/
theorem failedRootGain_le_localDistances :
    max ((∑ round ∈ Finset.range 1, failedRootGain round) / (1 : ℝ)) 0 ≤
      ∑ key : Bool, Metric.infDist
        (counterfactualRegretMatchAverage information () (rootSite key)
          (failedStrategyOf key) (failedPayoffOf key) (localFuel key)
          (fun _ => ()) 1)
        nonposOrthant := by
  simpa only [Nat.cast_one] using
    counterfactualRegretMatches_positiveRootGain_le information
      (fun _key => Unit) () rootSite failedStrategyOf failedPayoffOf localFuel
      (fun _key _round => ()) failedRootGain (fun _ => 1)
      (fun _ => by constructor <;> norm_num) rootDeviation
      failedRootGain_decomposition 1 (by norm_num)

/-- Negative control: without a realizing learner, positive root regret stays
exactly one at every nonempty horizon. -/
theorem failedRootGain_positiveAverage_eq_one (t : ℕ) (ht : 0 < t) :
    max ((∑ round ∈ Finset.range t, failedRootGain round) / (t : ℝ)) 0 = 1 := by
  simp only [failedRootGain_eq_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [mul_one, div_self htReal, max_eq_left]
  norm_num

/-! ## Simultaneous two-site regret matching -/

def firstBasePolicy (secondLaw : FinDist SecondTrueAction) :
    information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.withLaw (secondSite true).1 secondLaw

def firstBaseStrategy (secondLaw : FinDist SecondTrueAction)
    (_player : Unit) : information.BehavioralPolicy () :=
  firstBasePolicy secondLaw

def secondBasePolicy (firstLaw : FinDist FirstAction) :
    information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.withLaw firstSite.1 firstLaw

def secondBaseStrategy (firstLaw : FinDist FirstAction)
    (_player : Unit) : information.BehavioralPolicy () :=
  secondBasePolicy firstLaw

def LocalEnvironment : Bool → Type
  | false => FinDist SecondTrueAction
  | true => FinDist FirstAction

/-- Each local D46 process receives the other site's current law as its
environment. -/
def cfrStrategyOf : (key : Bool) →
    FinDist (information.Choice () (rootSite key).1) →
    LocalEnvironment key →
    (player : Unit) → information.BehavioralPolicy player
  | false, law, current =>
      strategyWithLocalLaw information (firstBaseStrategy current) ()
        firstSite law
  | true, law, current =>
      strategyWithLocalLaw information (secondBaseStrategy current) ()
        (secondSite true) law

def jointPolicy (firstLaw : FinDist FirstAction)
    (secondLaw : FinDist SecondTrueAction) :
    information.BehavioralPolicy () :=
  (incumbentBehavioralPolicy.withLaw firstSite.1 firstLaw).withLaw
    (secondSite true).1 secondLaw

def jointStrategy (firstLaw : FinDist FirstAction)
    (secondLaw : FinDist SecondTrueAction) (_player : Unit) :
    information.BehavioralPolicy () :=
  jointPolicy firstLaw secondLaw

theorem firstSite_ne_secondTrue : firstSite.1 ≠ (secondSite true).1 := by
  simp [firstKnowledge, secondKnowledge]

theorem cfrStrategyOf_false_eq_joint
    (firstLaw : FinDist FirstAction) (secondLaw : FinDist SecondTrueAction) :
    cfrStrategyOf false firstLaw secondLaw =
      jointStrategy firstLaw secondLaw := by
  funext player info
  cases player
  simp only [cfrStrategyOf]
  unfold strategyWithLocalLaw firstBaseStrategy firstBasePolicy
    jointStrategy jointPolicy
  rw [Profile.update_same]
  by_cases hfirst : info = firstSite.1
  · subst info
    rw [BehavioralPolicy.withLaw_self (M := information),
      BehavioralPolicy.withLaw_of_ne (M := information) _ _ _
        firstSite_ne_secondTrue,
      BehavioralPolicy.withLaw_self (M := information)]
  · by_cases hsecond : info = (secondSite true).1
    · subst info
      rw [BehavioralPolicy.withLaw_of_ne (M := information) _ _ _
          firstSite_ne_secondTrue.symm,
        BehavioralPolicy.withLaw_self (M := information),
        BehavioralPolicy.withLaw_self (M := information)]
    · rw [BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hfirst,
        BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hsecond,
        BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hsecond,
        BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hfirst]

theorem cfrStrategyOf_true_eq_joint
    (firstLaw : FinDist FirstAction) (secondLaw : FinDist SecondTrueAction) :
    cfrStrategyOf true secondLaw firstLaw =
      jointStrategy firstLaw secondLaw := by
  funext player
  cases player
  simp only [cfrStrategyOf]
  unfold strategyWithLocalLaw secondBaseStrategy
    secondBasePolicy jointStrategy jointPolicy
  rw [Profile.update_same]

structure TwoSiteCFRState where
  first : EuclideanSpace ℝ FirstAction
  second : EuclideanSpace ℝ SecondTrueAction

def strategyOfState (state : TwoSiteCFRState) :
    (player : Unit) → information.BehavioralPolicy player :=
  jointStrategy (regretMatch state.first) (regretMatch state.second)

def firstInstantaneous (state : TwoSiteCFRState) :
    EuclideanSpace ℝ FirstAction :=
  localCounterfactualRegretVector information (strategyOfState state) ()
    firstSite terminalPayoff 2

def secondInstantaneous (state : TwoSiteCFRState) :
    EuclideanSpace ℝ SecondTrueAction :=
  localCounterfactualRegretVector information (strategyOfState state) ()
    (secondSite true) terminalPayoff 1

/-- Simultaneous local regret matching, expressed as the same Cesaro recurrence
used by `avgVec` at both sites. -/
def twoSiteCFRState : ℕ → TwoSiteCFRState
  | 0 => ⟨0, 0⟩
  | n + 1 =>
      let current := twoSiteCFRState n
      ⟨((n : ℝ) / ((n : ℝ) + 1)) • current.first +
          (1 / ((n : ℝ) + 1)) • firstInstantaneous current,
        ((n : ℝ) / ((n : ℝ) + 1)) • current.second +
          (1 / ((n : ℝ) + 1)) • secondInstantaneous current⟩

def cfrEnvironment : (key : Bool) → ℕ → LocalEnvironment key
  | false, round => regretMatch (twoSiteCFRState round).second
  | true, round => regretMatch (twoSiteCFRState round).first

def cfrPayoffOf (_key : Bool) (_current : LocalEnvironment _key) :
    twoStage.History → ℝ := terminalPayoff

/-- The mutually coupled state is definitionally the pair of D46 running
averages; neither local convergence is assumed. -/
theorem cfrAverages_eq_state (round : ℕ) :
    counterfactualRegretMatchAverage information () firstSite
        (cfrStrategyOf false) (cfrPayoffOf false) 2
        (cfrEnvironment false) round = (twoSiteCFRState round).first ∧
      counterfactualRegretMatchAverage information () (secondSite true)
        (cfrStrategyOf true) (cfrPayoffOf true) 1
        (cfrEnvironment true) round = (twoSiteCFRState round).second := by
  induction round with
  | zero => simp [counterfactualRegretMatchAverage, avgVec, twoSiteCFRState]
  | succ round ih =>
      constructor
      · show
          ((round : ℝ) / ((round : ℝ) + 1)) •
              counterfactualRegretMatchAverage information () firstSite
                (cfrStrategyOf false) (cfrPayoffOf false) 2
                (cfrEnvironment false) round +
            (1 / ((round : ℝ) + 1)) •
              localCounterfactualRegretVector information
                (cfrStrategyOf false
                  (regretMatch
                    (counterfactualRegretMatchAverage information () firstSite
                      (cfrStrategyOf false) (cfrPayoffOf false) 2
                      (cfrEnvironment false) round))
                  (cfrEnvironment false round))
                () firstSite terminalPayoff 2 =
            (twoSiteCFRState (round + 1)).first
        rw [ih.1]
        simp only [cfrEnvironment]
        rw [cfrStrategyOf_false_eq_joint]
        rfl
      · show
          ((round : ℝ) / ((round : ℝ) + 1)) •
              counterfactualRegretMatchAverage information ()
                (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
                (cfrEnvironment true) round +
            (1 / ((round : ℝ) + 1)) •
              localCounterfactualRegretVector information
                (cfrStrategyOf true
                  (regretMatch
                    (counterfactualRegretMatchAverage information ()
                      (secondSite true) (cfrStrategyOf true)
                      (cfrPayoffOf true) 1 (cfrEnvironment true) round))
                  (cfrEnvironment true round))
                () (secondSite true) terminalPayoff 1 =
            (twoSiteCFRState (round + 1)).second
        rw [ih.2]
        simp only [cfrEnvironment]
        rw [cfrStrategyOf_true_eq_joint]
        rfl

/-- The ordinary first-site utility with the second-site law as environment. -/
def firstCFRUtility (choice : FirstAction)
    (secondLaw : FinDist SecondTrueAction) : ℝ :=
  information.counterfactualActionUtility
    (firstBaseStrategy secondLaw) () firstSite terminalPayoff 2 choice

/-- The ordinary second-site utility with the first-site law as environment. -/
def secondCFRUtility (choice : SecondTrueAction)
    (firstLaw : FinDist FirstAction) : ℝ :=
  information.counterfactualActionUtility
    (secondBaseStrategy firstLaw) () (secondSite true) terminalPayoff 1 choice

/-- The first coupled process satisfies D46's realization equation by D47. -/
theorem cfrRealization_first (law : FinDist FirstAction)
    (current : FinDist SecondTrueAction) :
    localCounterfactualRegretVector information
        (strategyWithLocalLaw information (firstBaseStrategy current) ()
          firstSite law) () firstSite terminalPayoff 2 =
      regretPayoff firstCFRUtility law current := by
  calc
    _ = regretPayoff
        (fun choice (_environment : FinDist SecondTrueAction) =>
          information.counterfactualActionUtility
            (firstBaseStrategy current) () firstSite terminalPayoff 2 choice)
        law current :=
      localCounterfactualRegretVector_strategyWithLocalLaw information
      information_actsOnce (firstBaseStrategy current) () firstSite
        firstSite_allNonterminal law terminalPayoff 1 current
    _ = regretPayoff firstCFRUtility law current := by
      ext choice
      rfl

/-- The off-path coupled process independently satisfies the same D46
realization contract. -/
theorem cfrRealization_second (law : FinDist SecondTrueAction)
    (current : FinDist FirstAction) :
    localCounterfactualRegretVector information
        (strategyWithLocalLaw information (secondBaseStrategy current) ()
          (secondSite true) law) () (secondSite true)
          terminalPayoff 1 =
      regretPayoff secondCFRUtility law current := by
  calc
    _ = regretPayoff
        (fun choice (_environment : FinDist FirstAction) =>
          information.counterfactualActionUtility
            (secondBaseStrategy current) () (secondSite true)
              terminalPayoff 1 choice)
        law current :=
      localCounterfactualRegretVector_strategyWithLocalLaw information
      information_actsOnce (secondBaseStrategy current) () (secondSite true)
        (secondSite_allNonterminal true) law terminalPayoff 0 current
    _ = regretPayoff secondCFRUtility law current := by
      ext choice
      rfl

def firstCommittedPolicyOfState (state : TwoSiteCFRState) :
    information.BehavioralPolicy () :=
  (strategyOfState state ()).commit firstSite.1 (firstChoice true)

def firstCommittedStrategyOfState (state : TwoSiteCFRState)
    (_player : Unit) : information.BehavioralPolicy () :=
  firstCommittedPolicyOfState state

def deviatedPolicyOfState (state : TwoSiteCFRState) :
    information.BehavioralPolicy () :=
  (firstCommittedPolicyOfState state).commit (secondSite true).1
    (secondChoice true true)

def deviatedStrategyOfState (state : TwoSiteCFRState)
    (_player : Unit) : information.BehavioralPolicy () :=
  deviatedPolicyOfState state

/-- The successful process is measured by the canonical root evaluator. -/
def cfrRootGain (round : ℕ) : ℝ :=
  (information.runBehavioral
      (deviatedStrategyOfState (twoSiteCFRState round)) 3).expect
        terminalPayoff -
    (information.runBehavioral (strategyOfState (twoSiteCFRState round)) 3).expect
      terminalPayoff

theorem ownReach_first_of_strategy
    (strategy : (player : Unit) → information.BehavioralPolicy player)
    (hidden : Bool) :
    information.playerReachProbability strategy ()
      (firstHistory hidden).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_firstHistory]
  rfl

theorem commonOwnReach_first_of_strategy
    (strategy : (player : Unit) → information.BehavioralPolicy player)
    (history : information.InformationHistory () firstSite.1) :
    information.playerReachProbability strategy () history.1.trace = 1 := by
  rw [← firstHistoryEquivBool.symm_apply_apply history]
  exact ownReach_first_of_strategy strategy _

theorem ownReach_secondTrue_after_firstCommit
    (state : TwoSiteCFRState)
    (hidden : Bool) :
    information.playerReachProbability (firstCommittedStrategyOfState state) ()
      (secondHistory hidden true).trace = 1 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
  rw [show decodeRecord [(Stage.first, true)] =
      [(firstKnowledge, true)] by rfl,
    InformationModel.ownPlayReachProbability]
  have hpolicy : firstCommittedPolicyOfState state firstKnowledge =
      FinDist.pure (firstChoice true) := by
    unfold firstCommittedPolicyOfState
    rw [BehavioralPolicy.commit_self (M := information)]
  rw [show firstCommittedStrategyOfState state () firstKnowledge =
      FinDist.pure (firstChoice true) from hpolicy]
  simp [firstChoice, InformationModel.ownPlayReachProbability]

theorem commonOwnReach_secondTrue_after_firstCommit
    (state : TwoSiteCFRState)
    (history : information.InformationHistory () (secondSite true).1) :
    information.playerReachProbability (firstCommittedStrategyOfState state) ()
      history.1.trace = 1 := by
  rw [← (secondHistoryEquivBool true).symm_apply_apply history]
  exact ownReach_secondTrue_after_firstCommit state _

theorem firstStep_rootGain
    (state : TwoSiteCFRState) :
    (information.runBehavioral (firstCommittedStrategyOfState state) 3).expect
          terminalPayoff -
        (information.runBehavioral (strategyOfState state) 3).expect
          terminalPayoff =
      information.counterfactualActionRegret (strategyOfState state) ()
        firstSite terminalPayoff 2 (firstChoice true) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (strategyOfState state) () firstSite
      (firstCommittedPolicyOfState state) 1 2 firstSite_commonDepth
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne) 1
      (commonOwnReach_first_of_strategy (strategyOfState state)) terminalPayoff
  have hprofile : firstCommittedStrategyOfState state =
      Profile.update (sig := information.behavioralSignature)
        (strategyOfState state) () (firstCommittedPolicyOfState state) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  rw [show information.counterfactualRegret (strategyOfState state) ()
      firstSite terminalPayoff 2 (firstCommittedPolicyOfState state) =
      information.counterfactualActionRegret (strategyOfState state) ()
        firstSite terminalPayoff 2 (firstChoice true) by rfl] at hroot
  norm_num at hroot ⊢
  exact hroot

theorem secondStep_rootGain
    (state : TwoSiteCFRState) :
    (information.runBehavioral (deviatedStrategyOfState state) 3).expect
          terminalPayoff -
        (information.runBehavioral
          (firstCommittedStrategyOfState state) 3).expect terminalPayoff =
      information.counterfactualActionRegret
        (firstCommittedStrategyOfState state) () (secondSite true)
          terminalPayoff 1 (secondChoice true true) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (firstCommittedStrategyOfState state) () (secondSite true)
      (deviatedPolicyOfState state) 2 1 (secondSite_commonDepth true)
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne) 1
      (commonOwnReach_secondTrue_after_firstCommit state) terminalPayoff
  have hprofile : deviatedStrategyOfState state =
      Profile.update (sig := information.behavioralSignature)
        (firstCommittedStrategyOfState state) ()
          (deviatedPolicyOfState state) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  rw [show information.counterfactualRegret
      (firstCommittedStrategyOfState state) () (secondSite true)
        terminalPayoff 1 (deviatedPolicyOfState state) =
      information.counterfactualActionRegret
        (firstCommittedStrategyOfState state) () (secondSite true)
          terminalPayoff 1 (secondChoice true true) by rfl] at hroot
  norm_num at hroot ⊢
  exact hroot

theorem secondRegret_after_firstCommit_eq
    (state : TwoSiteCFRState) :
    information.counterfactualActionRegret
        (firstCommittedStrategyOfState state) () (secondSite true)
          terminalPayoff 1 (secondChoice true true) =
      information.counterfactualActionRegret (strategyOfState state) ()
        (secondSite true) terminalPayoff 1 (secondChoice true true) := by
  exact information.counterfactualActionRegret_eq_of_agree_off_pastSite
    (firstCommittedStrategyOfState state) (strategyOfState state) () firstSite
      1 firstSite_commonDepth
      (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      (fun hinfo => BehavioralPolicy.commit_of_ne _ _ _ hinfo)
      (secondSite true) secondInformationHistory_after_firstDepth
      terminalPayoff 1 (secondChoice true true)

/-- D48 gives the exact per-round decomposition used by the aggregate theorem.
Both terms are the actual coupled D46 local vectors. -/
theorem cfrRootGain_decomposition (round : ℕ) :
    cfrRootGain round = ∑ key : Bool,
      1 *
        (localCounterfactualRegretVector information
          (cfrStrategyOf key
            (regretMatch
              (counterfactualRegretMatchAverage information () (rootSite key)
                (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key)
                (cfrEnvironment key) round))
            (cfrEnvironment key round))
          () (rootSite key) terminalPayoff (localFuel key)).ofLp
            (rootDeviation key) := by
  have havg := cfrAverages_eq_state round
  rw [Fintype.sum_bool]
  simp only [rootSite, localFuel, rootDeviation, one_mul]
  rw [havg.1, havg.2]
  simp only [cfrEnvironment]
  rw [cfrStrategyOf_false_eq_joint, cfrStrategyOf_true_eq_joint]
  show cfrRootGain round =
    information.counterfactualActionRegret
        (strategyOfState (twoSiteCFRState round)) () (secondSite true)
          terminalPayoff 1 (secondChoice true true) +
      information.counterfactualActionRegret
        (strategyOfState (twoSiteCFRState round)) () firstSite
          terminalPayoff 2 (firstChoice true)
  unfold cfrRootGain
  rw [← secondRegret_after_firstCommit_eq,
    ← secondStep_rootGain, ← firstStep_rootGain]
  ring

/-- At every finite horizon, the positive average of the canonical root gains
is controlled by both actual local regret-matching distances. -/
theorem twoSiteCFR_positiveRootGain_le_localDistances
    (t : ℕ) (ht : 0 < t) :
    max ((∑ round ∈ Finset.range t, cfrRootGain round) / (t : ℝ)) 0 ≤
      ∑ key : Bool, Metric.infDist
        (counterfactualRegretMatchAverage information () (rootSite key)
          (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key)
          (cfrEnvironment key) t)
        nonposOrthant := by
  let firstAverage :=
    counterfactualRegretMatchAverage information () firstSite
      (cfrStrategyOf false) (cfrPayoffOf false) 2
      (cfrEnvironment false) t
  let secondAverage :=
    counterfactualRegretMatchAverage information () (secondSite true)
      (cfrStrategyOf true) (cfrPayoffOf true) 1
      (cfrEnvironment true) t
  have hfirstVector :=
    counterfactualRegretMatchAverage_smul_eq_sum information () firstSite
      (cfrStrategyOf false) (cfrPayoffOf false) 2
      (cfrEnvironment false) t
  have hsecondVector :=
    counterfactualRegretMatchAverage_smul_eq_sum information ()
      (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
      (cfrEnvironment true) t
  have hfirstCoordinate :
      ∑ round ∈ Finset.range t,
        (localCounterfactualRegretVector information
          (cfrStrategyOf false
            (regretMatch
              (counterfactualRegretMatchAverage information () firstSite
                (cfrStrategyOf false) (cfrPayoffOf false) 2
                (cfrEnvironment false) round))
            (cfrEnvironment false round))
          () firstSite terminalPayoff 2).ofLp (firstChoice true) =
        (t : ℝ) * firstAverage.ofLp (firstChoice true) := by
    have happly := congrArg
      (fun value : EuclideanSpace ℝ FirstAction =>
        value.ofLp (firstChoice true)) hfirstVector
    simpa [firstAverage, cfrPayoffOf] using happly.symm
  have hsecondCoordinate :
      ∑ round ∈ Finset.range t,
        (localCounterfactualRegretVector information
          (cfrStrategyOf true
            (regretMatch
              (counterfactualRegretMatchAverage information ()
                (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
                (cfrEnvironment true) round))
            (cfrEnvironment true round))
          () (secondSite true) terminalPayoff 1).ofLp
            (secondChoice true true) =
        (t : ℝ) * secondAverage.ofLp (secondChoice true true) := by
    have happly := congrArg
      (fun value : EuclideanSpace ℝ SecondTrueAction =>
        value.ofLp (secondChoice true true)) hsecondVector
    simpa [secondAverage, cfrPayoffOf] using happly.symm
  have hrootSum :
      (∑ round ∈ Finset.range t, cfrRootGain round) =
        (t : ℝ) * secondAverage.ofLp (secondChoice true true) +
          (t : ℝ) * firstAverage.ofLp (firstChoice true) := by
    calc
      (∑ round ∈ Finset.range t, cfrRootGain round) =
          ∑ round ∈ Finset.range t,
            ((localCounterfactualRegretVector information
              (cfrStrategyOf true
                (regretMatch
                  (counterfactualRegretMatchAverage information ()
                    (secondSite true) (cfrStrategyOf true)
                    (cfrPayoffOf true) 1 (cfrEnvironment true) round))
                (cfrEnvironment true round))
              () (secondSite true) terminalPayoff 1).ofLp
                (secondChoice true true) +
              (localCounterfactualRegretVector information
                (cfrStrategyOf false
                  (regretMatch
                    (counterfactualRegretMatchAverage information () firstSite
                      (cfrStrategyOf false) (cfrPayoffOf false) 2
                      (cfrEnvironment false) round))
                  (cfrEnvironment false round))
                () firstSite terminalPayoff 2).ofLp (firstChoice true)) := by
        apply Finset.sum_congr rfl
        intro round _
        rw [cfrRootGain_decomposition, Fintype.sum_bool]
        simp only [rootSite, localFuel, rootDeviation, one_mul]
      _ = _ := by
        rw [Finset.sum_add_distrib, hsecondCoordinate, hfirstCoordinate]
  have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hmean :
      (∑ round ∈ Finset.range t, cfrRootGain round) / (t : ℝ) =
        secondAverage.ofLp (secondChoice true true) +
          firstAverage.ofLp (firstChoice true) := by
    rw [hrootSum]
    field_simp
  rw [hmean, Fintype.sum_bool, max_le_iff]
  constructor
  · have hsecond := positivePart_le_infDist secondAverage
      (secondChoice true true)
    have hfirst := positivePart_le_infDist firstAverage (firstChoice true)
    exact (add_le_add (le_max_left _ 0) (le_max_left _ 0)).trans
      (add_le_add hsecond hfirst)
  · exact add_nonneg Metric.infDist_nonneg Metric.infDist_nonneg

/-- D46 drives the first coupled local process to its nonpositive orthant. -/
theorem firstCFR_approaches {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law current,
      ‖regretPayoff firstCFRUtility law current‖ ≤ bound) :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () firstSite
          (cfrStrategyOf false) (cfrPayoffOf false) 2
          (cfrEnvironment false) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information () firstSite
    firstCFRUtility (cfrStrategyOf false) (cfrPayoffOf false) 2
      cfrRealization_first hbound0 hbound (cfrEnvironment false)

/-- D46 independently drives the off-path second process to its orthant. -/
theorem secondCFR_approaches {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law current,
      ‖regretPayoff secondCFRUtility law current‖ ≤ bound) :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () (secondSite true)
          (cfrStrategyOf true) (cfrPayoffOf true) 1
          (cfrEnvironment true) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information () (secondSite true)
    secondCFRUtility (cfrStrategyOf true) (cfrPayoffOf true) 1
      cfrRealization_second hbound0 hbound (cfrEnvironment true)

/-- **Concrete two-site CFR root theorem.** Ordinary per-site payoff-vector
bounds let D46 prove both local limits; the finite D48 aggregation then drives
the positive canonical root gain to zero. No convergence premise is assumed. -/
theorem twoSiteCFR_positiveRootGain_tendsto_zero
    {firstBound secondBound : ℝ}
    (hfirst0 : 0 ≤ firstBound)
    (hfirst : ∀ law current,
      ‖regretPayoff firstCFRUtility law current‖ ≤ firstBound)
    (hsecond0 : 0 ≤ secondBound)
    (hsecond : ∀ law current,
      ‖regretPayoff secondCFRUtility law current‖ ≤ secondBound) :
    Tendsto
      (fun t => max
        ((∑ round ∈ Finset.range t, cfrRootGain round) / (t : ℝ)) 0)
      atTop (nhds 0) := by
  have hfirstLimit := firstCFR_approaches hfirst0 hfirst
  have hsecondLimit := secondCFR_approaches hsecond0 hsecond
  have hsum : Tendsto
      (fun t =>
        Metric.infDist
            (counterfactualRegretMatchAverage information ()
              (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
              (cfrEnvironment true) t) nonposOrthant +
          Metric.infDist
            (counterfactualRegretMatchAverage information () firstSite
              (cfrStrategyOf false) (cfrPayoffOf false) 2
              (cfrEnvironment false) t) nonposOrthant)
      atTop (nhds 0) := by
    simpa using hsecondLimit.add hfirstLimit
  have hupper : ∀ t,
      max ((∑ round ∈ Finset.range t, cfrRootGain round) / (t : ℝ)) 0 ≤
        Metric.infDist
            (counterfactualRegretMatchAverage information ()
              (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
              (cfrEnvironment true) t) nonposOrthant +
          Metric.infDist
            (counterfactualRegretMatchAverage information () firstSite
              (cfrStrategyOf false) (cfrPayoffOf false) 2
              (cfrEnvironment false) t) nonposOrthant := by
    intro t
    cases t with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
          div_zero, max_self]
        exact add_nonneg Metric.infDist_nonneg Metric.infDist_nonneg
    | succ t =>
        simpa only [Fintype.sum_bool, rootSite, localFuel] using
          twoSiteCFR_positiveRootGain_le_localDistances (t + 1)
            (Nat.succ_pos t)
  exact squeeze_zero (fun t => le_max_right _ _) hupper hsum

end GameTheory.Analysis.Protocol.CounterfactualRootRegretTest
