/-
# Hostile finite root-regret consumer

The two-site complementarity deviation is repeated unchanged.  Its canonical
root gain stays one, and the finite aggregation theorem must recover that gain
from the zero first-site vector and the unit off-path second-site vector.  This
is also the failed-learner control for the eventual convergence consumer.
-/

import GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
import GameTheory.Analysis.Protocol.CounterfactualRootRegret
import GameTheory.Core.Learning
import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.Analysis.Protocol.CounterfactualRootRegretTest

open Filter GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheory.Protocol.InformationModel
open GameTheory.Analysis.Protocol.CounterfactualRegretLinearityTest
open GameTheory.Analysis.Protocol.CounterfactualDecompositionTest
open GameTheory.Analysis.Protocol.CounterfactualRootBridgeTest
open GameTheory.Tests.SubgameOneShot
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

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
    (_law : PMF (information.Choice () (rootSite key).1)) (_current : Unit) :
    (player : Unit) → information.BehavioralPolicy player := by
  cases key
  · exact incumbentBehavioralStrategy
  · exact firstCommittedStrategy

def failedPayoffOf (_key : Bool) (_current : Unit) : twoStage.History → ℝ :=
  terminalPayoff

def localFuel : Bool → ℕ
  | false => 2
  | true => 1

theorem rootGuard
    (strategy : (who : Unit) → information.BehavioralPolicy who)
    (key : Bool) :
    information.LocalCounterfactualRegretsIntegrable strategy ()
      (rootSite key) terminalPayoff (localFuel key) := by
  constructor
  · intro choice
    exact counterfactualIntegrable strategy (rootSite key)
      ((strategy ()).commit (rootSite key).1 choice) (localFuel key)
  · exact counterfactualIntegrable strategy (rootSite key)
      (strategy ()) (localFuel key)

/-- The scalar sequence is the actual canonical behavioral root gain, not a
fixture-local proxy. -/
def failedRootGain (_round : ℕ) : ℝ :=
  rootValue finalCommittedStrategy - rootValue incumbentBehavioralStrategy

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
                (fun _ _ => rootGuard _ key)
                (fun _ => ()) round)) ())
          () (rootSite key) terminalPayoff (localFuel key)
          (rootGuard _ key)).ofLp
            (rootDeviation key) := by
  rw [failedRootGain_eq_one]
  rw [Fintype.sum_bool]
  simp only [rootSite, failedStrategyOf, localFuel, rootDeviation, one_mul]
  rw [show
      (localCounterfactualRegretVector information
        incumbentBehavioralStrategy () firstSite terminalPayoff 2
        (rootGuard _ false)).ofLp
          (firstChoice true) =
        guardedActionRegret incumbentBehavioralStrategy firstSite 2
          (firstChoice true) by rfl,
    show
      (localCounterfactualRegretVector information
        firstCommittedStrategy () (secondSite true) terminalPayoff 1
        (rootGuard _ true)).ofLp
          (secondChoice true true) =
        guardedActionRegret firstCommittedStrategy (secondSite true) 1
          (secondChoice true true) by rfl,
    show guardedActionRegret incumbentBehavioralStrategy firstSite 2
      (firstChoice true) = 0 by
      simpa only [guardedActionRegret] using first_counterfactualActionRegret,
    firstCommitted_second_counterfactualActionRegret]
  norm_num

/-- The new finite-family theorem bounds an actual nonzero root deviation and
therefore cannot pass merely because every local term was defined. -/
theorem failedRootGain_le_localDistances :
    max ((∑ round ∈ Finset.range 1, failedRootGain round) / (1 : ℝ)) 0 ≤
      ∑ key : Bool, Metric.infDist
        (counterfactualRegretMatchAverage information () (rootSite key)
          (failedStrategyOf key) (failedPayoffOf key) (localFuel key)
          (fun _ _ => rootGuard _ key)
          (fun _ => ()) 1)
        nonposOrthant := by
  simpa only [Nat.cast_one] using
    counterfactualRegretMatches_positiveRootGain_le information
      (fun _key => Unit) () rootSite failedStrategyOf failedPayoffOf localFuel
      (fun _key _round => ()) (fun key _ _ => rootGuard _ key)
      failedRootGain (fun _ => 1)
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

def firstBasePolicy (secondLaw : PMF SecondTrueAction) :
    information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.withLaw (secondSite true).1 secondLaw

def firstBaseStrategy (secondLaw : PMF SecondTrueAction)
    (_player : Unit) : information.BehavioralPolicy () :=
  firstBasePolicy secondLaw

def secondBasePolicy (firstLaw : PMF FirstAction) :
    information.BehavioralPolicy () :=
  incumbentBehavioralPolicy.withLaw firstSite.1 firstLaw

def secondBaseStrategy (firstLaw : PMF FirstAction)
    (_player : Unit) : information.BehavioralPolicy () :=
  secondBasePolicy firstLaw

def LocalEnvironment : Bool → Type
  | false => PMF SecondTrueAction
  | true => PMF FirstAction

/-- Each local D46 process receives the other site's current law as its
environment. -/
def cfrStrategyOf : (key : Bool) →
    PMF (information.Choice () (rootSite key).1) →
    LocalEnvironment key →
    (player : Unit) → information.BehavioralPolicy player
  | false, law, current =>
      strategyWithLocalLaw information (firstBaseStrategy current) ()
        firstSite law
  | true, law, current =>
      strategyWithLocalLaw information (secondBaseStrategy current) ()
        (secondSite true) law

def jointPolicy (firstLaw : PMF FirstAction)
    (secondLaw : PMF SecondTrueAction) :
    information.BehavioralPolicy () :=
  (incumbentBehavioralPolicy.withLaw firstSite.1 firstLaw).withLaw
    (secondSite true).1 secondLaw

def jointStrategy (firstLaw : PMF FirstAction)
    (secondLaw : PMF SecondTrueAction) (_player : Unit) :
    information.BehavioralPolicy () :=
  jointPolicy firstLaw secondLaw

theorem firstSite_ne_secondTrue : firstSite.1 ≠ (secondSite true).1 := by
  simp [firstKnowledge, secondKnowledge]

theorem cfrStrategyOf_false_eq_joint
    (firstLaw : PMF FirstAction) (secondLaw : PMF SecondTrueAction) :
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
    (firstLaw : PMF FirstAction) (secondLaw : PMF SecondTrueAction) :
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
    firstSite terminalPayoff 2 (rootGuard _ false)

def secondInstantaneous (state : TwoSiteCFRState) :
    EuclideanSpace ℝ SecondTrueAction :=
  localCounterfactualRegretVector information (strategyOfState state) ()
    (secondSite true) terminalPayoff 1 (rootGuard _ true)

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
        (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
        (cfrEnvironment false) round = (twoSiteCFRState round).first ∧
      counterfactualRegretMatchAverage information () (secondSite true)
        (cfrStrategyOf true) (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true)
        (cfrEnvironment true) round = (twoSiteCFRState round).second := by
  induction round with
  | zero => simp [counterfactualRegretMatchAverage, avgVec, twoSiteCFRState]
  | succ round ih =>
      constructor
      · show
          ((round : ℝ) / ((round : ℝ) + 1)) •
              counterfactualRegretMatchAverage information () firstSite
                (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
                (cfrEnvironment false) round +
            (1 / ((round : ℝ) + 1)) •
              localCounterfactualRegretVector information
                (cfrStrategyOf false
                  (regretMatch
                    (counterfactualRegretMatchAverage information () firstSite
                      (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
                      (cfrEnvironment false) round))
                  (cfrEnvironment false round))
                () firstSite terminalPayoff 2 (rootGuard _ false) =
            (twoSiteCFRState (round + 1)).first
        rw [ih.1]
        simp only [cfrEnvironment]
        simp only [cfrStrategyOf_false_eq_joint]
        rfl
      · show
          ((round : ℝ) / ((round : ℝ) + 1)) •
              counterfactualRegretMatchAverage information ()
                (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
                (fun _ _ => rootGuard _ true)
                (cfrEnvironment true) round +
            (1 / ((round : ℝ) + 1)) •
              localCounterfactualRegretVector information
                (cfrStrategyOf true
                  (regretMatch
                    (counterfactualRegretMatchAverage information ()
                      (secondSite true) (cfrStrategyOf true)
                      (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true)
                      (cfrEnvironment true) round))
                  (cfrEnvironment true round))
                () (secondSite true) terminalPayoff 1 (rootGuard _ true) =
            (twoSiteCFRState (round + 1)).second
        rw [ih.2]
        simp only [cfrEnvironment]
        simp only [cfrStrategyOf_true_eq_joint]
        rfl

/-- The ordinary first-site utility with the second-site law as environment. -/
def firstCFRUtility (choice : FirstAction)
    (secondLaw : PMF SecondTrueAction) : ℝ :=
  information.counterfactualActionUtility
    (firstBaseStrategy secondLaw) () firstSite terminalPayoff 2 choice
    ((rootGuard _ false).1 choice)

/-- The ordinary second-site utility with the first-site law as environment. -/
def secondCFRUtility (choice : SecondTrueAction)
    (firstLaw : PMF FirstAction) : ℝ :=
  information.counterfactualActionUtility
    (secondBaseStrategy firstLaw) () (secondSite true) terminalPayoff 1 choice
    ((rootGuard _ true).1 choice)

theorem terminalPayoff_mem_Icc (history : twoStage.History) :
    terminalPayoff history ∈ Set.Icc (0 : ℝ) 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | root => simp [terminalPayoff, utility]
  | first hidden => simp [terminalPayoff, utility]
  | second hidden firstAction => simp [terminalPayoff, utility]
  | done hidden firstAction secondAction =>
      cases firstAction <;> cases secondAction <;>
        simp [terminalPayoff, utility]

theorem behavioralContinuationValue_mem_Icc
    (strategy : (player : Unit) → information.BehavioralPolicy player)
    (alternative : information.BehavioralPolicy ()) (fuel : ℕ)
    (history : twoStage.History) :
    information.behavioralContinuationValue strategy () alternative
        terminalPayoff fuel history (terminalPayoff_integrable _) ∈
      Set.Icc (0 : ℝ) 1 := by
  unfold InformationModel.behavioralContinuationValue
  constructor
  · exact expect_nonneg
      (information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          strategy () alternative) fuel history)
      terminalPayoff (terminalPayoff_integrable _)
      (fun final _ => (terminalPayoff_mem_Icc final).1)
  · exact expect_le_const
      (information.runBehavioralFrom
        (Profile.update (sig := information.behavioralSignature)
          strategy () alternative) fuel history)
      terminalPayoff (terminalPayoff_integrable _) 1
      (fun final _ => (terminalPayoff_mem_Icc final).2)

theorem counterfactualReach_first_any
    (strategy : (player : Unit) → information.BehavioralPolicy player)
    (hidden : Bool) :
    information.counterfactualReachProbability strategy ()
        (firstHistory hidden).trace = 1 / 2 := by
  calc
    information.counterfactualReachProbability strategy ()
        (firstHistory hidden).trace =
      information.counterfactualReachProbability incumbentBehavioralStrategy ()
        (firstHistory hidden).trace :=
          information.counterfactualReachProbability_eq_of_eq_off
            (fun other hne => False.elim (hne (Subsingleton.elim other ()))) _
    _ = 1 / 2 := counterfactualReach_first hidden

theorem counterfactualReach_secondTrue_any
    (strategy : (player : Unit) → information.BehavioralPolicy player)
    (hidden : Bool) :
    information.counterfactualReachProbability strategy ()
        (secondHistory hidden true).trace = 1 / 2 := by
  calc
    information.counterfactualReachProbability strategy ()
        (secondHistory hidden true).trace =
      information.counterfactualReachProbability incumbentBehavioralStrategy ()
        (secondHistory hidden true).trace :=
          information.counterfactualReachProbability_eq_of_eq_off
            (fun other hne => False.elim (hne (Subsingleton.elim other ()))) _
    _ = 1 / 2 := counterfactualReach_second hidden true

theorem counterfactualReachMass_first
    (strategy : (player : Unit) → information.BehavioralPolicy player) :
    (∑ history : information.InformationHistory () firstSite.1,
      information.counterfactualReachProbability strategy () history.1.trace) = 1 := by
  calc
    (∑ history : information.InformationHistory () firstSite.1,
      information.counterfactualReachProbability strategy () history.1.trace) =
        ∑ hidden : Bool,
          information.counterfactualReachProbability strategy ()
            (firstHistory hidden).trace := by
              exact Fintype.sum_equiv firstHistoryEquivBool
                (fun history => information.counterfactualReachProbability
                  strategy () history.1.trace)
                (fun hidden => information.counterfactualReachProbability
                  strategy () (firstHistory hidden).trace)
                (fun history => by
                  have hinverse := firstHistoryEquivBool.symm_apply_apply history
                  exact congrArg
                    (fun current : information.InformationHistory () firstSite.1 =>
                      information.counterfactualReachProbability strategy ()
                        current.1.trace)
                    hinverse.symm)
    _ = 1 := by
      rw [Fintype.sum_bool, counterfactualReach_first_any,
        counterfactualReach_first_any]
      norm_num

theorem counterfactualReachMass_secondTrue
    (strategy : (player : Unit) → information.BehavioralPolicy player) :
    (∑ history : information.InformationHistory () (secondSite true).1,
      information.counterfactualReachProbability strategy () history.1.trace) = 1 := by
  calc
    (∑ history : information.InformationHistory () (secondSite true).1,
      information.counterfactualReachProbability strategy () history.1.trace) =
        ∑ hidden : Bool,
          information.counterfactualReachProbability strategy ()
            (secondHistory hidden true).trace := by
              exact Fintype.sum_equiv (secondHistoryEquivBool true)
                (fun history => information.counterfactualReachProbability
                  strategy () history.1.trace)
                (fun hidden => information.counterfactualReachProbability
                  strategy () (secondHistory hidden true).trace)
                (fun history => by
                  have hinverse :=
                    (secondHistoryEquivBool true).symm_apply_apply history
                  exact congrArg
                    (fun current : information.InformationHistory ()
                        (secondSite true).1 =>
                      information.counterfactualReachProbability strategy ()
                        current.1.trace)
                    hinverse.symm)
    _ = 1 := by
      rw [Fintype.sum_bool, counterfactualReach_secondTrue_any,
        counterfactualReach_secondTrue_any]
      norm_num

theorem firstCFRUtility_mem_Icc (choice : FirstAction)
    (secondLaw : PMF SecondTrueAction) :
    firstCFRUtility choice secondLaw ∈ Set.Icc (0 : ℝ) 1 := by
  exact information.counterfactualActionUtility_mem_Icc
    (firstBaseStrategy secondLaw) () firstSite terminalPayoff 2 choice
    ((rootGuard _ false).1 choice)
    (counterfactualReachMass_first (firstBaseStrategy secondLaw))
    (fun history _ => behavioralContinuationValue_mem_Icc
      (firstBaseStrategy secondLaw)
      ((firstBaseStrategy secondLaw ()).commit firstSite.1 choice) 2 history.1)

theorem secondCFRUtility_mem_Icc (choice : SecondTrueAction)
    (firstLaw : PMF FirstAction) :
    secondCFRUtility choice firstLaw ∈ Set.Icc (0 : ℝ) 1 := by
  exact information.counterfactualActionUtility_mem_Icc
    (secondBaseStrategy firstLaw) () (secondSite true) terminalPayoff 1 choice
    ((rootGuard _ true).1 choice)
    (counterfactualReachMass_secondTrue (secondBaseStrategy firstLaw))
    (fun history _ => behavioralContinuationValue_mem_Icc
      (secondBaseStrategy firstLaw)
      ((secondBaseStrategy firstLaw ()).commit (secondSite true).1 choice)
      1 history.1)

theorem firstCFR_regretPayoff_norm_le
    (law : PMF FirstAction) (current : PMF SecondTrueAction) :
    ‖regretPayoff firstCFRUtility law current
      (payoffIntegrable_of_finite _ _)‖ ≤
      (Fintype.card FirstAction : ℝ) := by
  simpa using regretPayoff_norm_le_card_mul_width firstCFRUtility
    (lo := 0) (hi := 1) firstCFRUtility_mem_Icc law current

theorem secondCFR_regretPayoff_norm_le
    (law : PMF SecondTrueAction) (current : PMF FirstAction) :
    ‖regretPayoff secondCFRUtility law current
      (payoffIntegrable_of_finite _ _)‖ ≤
      (Fintype.card SecondTrueAction : ℝ) := by
  simpa using regretPayoff_norm_le_card_mul_width secondCFRUtility
    (lo := 0) (hi := 1) secondCFRUtility_mem_Icc law current

/-- The first coupled process satisfies D46's realization equation by D47. -/
theorem cfrRealization_first (law : PMF FirstAction)
    (current : PMF SecondTrueAction) :
    localCounterfactualRegretVector information
        (strategyWithLocalLaw information (firstBaseStrategy current) ()
          firstSite law) () firstSite terminalPayoff 2
          (rootGuard _ false) =
      regretPayoff firstCFRUtility law current
        (payoffIntegrable_of_finite _ _) := by
  calc
    _ = regretPayoff
        (fun choice (_environment : PMF SecondTrueAction) =>
          information.counterfactualActionUtility
            (firstBaseStrategy current) () firstSite terminalPayoff 2 choice
            ((rootGuard _ false).1 choice))
        law current (payoffIntegrable_of_finite _ _) :=
      localCounterfactualRegretVector_strategyWithLocalLaw information
      information_actsOnce (firstBaseStrategy current) () firstSite
        firstSite_allNonterminal law terminalPayoff 1 current
        (rootGuard _ false) (rootGuard _ false).1
    _ = regretPayoff firstCFRUtility law current
          (payoffIntegrable_of_finite _ _) := by
      ext choice
      rfl

/-- The off-path coupled process independently satisfies the same D46
realization contract. -/
theorem cfrRealization_second (law : PMF SecondTrueAction)
    (current : PMF FirstAction) :
    localCounterfactualRegretVector information
        (strategyWithLocalLaw information (secondBaseStrategy current) ()
          (secondSite true) law) () (secondSite true)
          terminalPayoff 1 (rootGuard _ true) =
      regretPayoff secondCFRUtility law current
        (payoffIntegrable_of_finite _ _) := by
  calc
    _ = regretPayoff
        (fun choice (_environment : PMF FirstAction) =>
          information.counterfactualActionUtility
            (secondBaseStrategy current) () (secondSite true)
              terminalPayoff 1 choice ((rootGuard _ true).1 choice))
        law current (payoffIntegrable_of_finite _ _) :=
      localCounterfactualRegretVector_strategyWithLocalLaw information
      information_actsOnce (secondBaseStrategy current) () (secondSite true)
        (secondSite_allNonterminal true) law terminalPayoff 0 current
        (rootGuard _ true) (rootGuard _ true).1
    _ = regretPayoff secondCFRUtility law current
          (payoffIntegrable_of_finite _ _) := by
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
  rootValue (deviatedStrategyOfState (twoSiteCFRState round)) -
    rootValue (strategyOfState (twoSiteCFRState round))

/-! ## Every payoff-relevant pure plan -/

/-- A pure plan records the first action and the action after first playing
`true`.  The action after `false` is payoff-irrelevant in this fixture. -/
abbrev PayoffPlan := Bool × Bool

def planFirstCommittedPolicyOfState (state : TwoSiteCFRState)
    (plan : PayoffPlan) : information.BehavioralPolicy () :=
  (strategyOfState state ()).commit firstSite.1 (firstChoice plan.1)

def planFirstCommittedStrategyOfState (state : TwoSiteCFRState)
    (plan : PayoffPlan) (_player : Unit) : information.BehavioralPolicy () :=
  planFirstCommittedPolicyOfState state plan

def planDeviatedPolicyOfState (state : TwoSiteCFRState)
    (plan : PayoffPlan) : information.BehavioralPolicy () :=
  (planFirstCommittedPolicyOfState state plan).commit (secondSite true).1
    (secondChoice true plan.2)

def planDeviatedStrategyOfState (state : TwoSiteCFRState)
    (plan : PayoffPlan) (_player : Unit) : information.BehavioralPolicy () :=
  planDeviatedPolicyOfState state plan

/-- The replacement policy after both payoff-relevant coordinates are fixed.
Unlike the learner state, it is independent of the round. -/
def fixedPlanPolicy (plan : PayoffPlan) : information.BehavioralPolicy () :=
  (incumbentBehavioralPolicy.commit firstSite.1 (firstChoice plan.1)).commit
    (secondSite true).1 (secondChoice true plan.2)

def fixedPlanStrategy (plan : PayoffPlan)
    (_player : Unit) : information.BehavioralPolicy () :=
  fixedPlanPolicy plan

/-- Committing both learned coordinates erases both current laws.  This is the
fact that later makes the root gain a fixed-strategy external regret. -/
theorem planDeviatedPolicyOfState_eq_fixed
    (state : TwoSiteCFRState) (plan : PayoffPlan) :
    planDeviatedPolicyOfState state plan = fixedPlanPolicy plan := by
  funext info
  unfold planDeviatedPolicyOfState fixedPlanPolicy
    planFirstCommittedPolicyOfState
  by_cases hsecond : info = (secondSite true).1
  · subst info
    rw [BehavioralPolicy.commit_self (M := information),
      BehavioralPolicy.commit_self (M := information)]
  · rw [BehavioralPolicy.commit_of_ne (M := information) _ _ _ hsecond,
      BehavioralPolicy.commit_of_ne (M := information) _ _ _ hsecond]
    by_cases hfirst : info = firstSite.1
    · subst info
      rw [BehavioralPolicy.commit_self (M := information),
        BehavioralPolicy.commit_self (M := information)]
    · rw [BehavioralPolicy.commit_of_ne (M := information) _ _ _ hfirst,
        BehavioralPolicy.commit_of_ne (M := information) _ _ _ hfirst]
      unfold strategyOfState jointStrategy jointPolicy
      rw [BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hsecond,
        BehavioralPolicy.withLaw_of_ne (M := information) _ _ _ hfirst]

/-- Canonical root gain against a fixed payoff-relevant pure plan. -/
def planRootGain (plan : PayoffPlan) (round : ℕ) : ℝ :=
  rootValue (fixedPlanStrategy plan) -
    rootValue (strategyOfState (twoSiteCFRState round))

/-- Alternative own reach is one at the first site.  It reaches the
`second-after-true` site exactly when the plan's first action is `true`. -/
def planReach (plan : PayoffPlan) : Bool → ℝ
  | false => 1
  | true => if plan.1 then 1 else 0

def planChoice (plan : PayoffPlan) : (key : Bool) →
    information.Choice () (rootSite key).1
  | false => firstChoice plan.1
  | true => secondChoice true plan.2

theorem planReach_mem_Icc (plan : PayoffPlan) (key : Bool) :
    planReach plan key ∈ Set.Icc (0 : ℝ) 1 := by
  rcases plan with ⟨first, second⟩
  cases key <;> cases first <;> simp [planReach]

theorem ownReach_secondTrue_after_planFirstCommit
    (state : TwoSiteCFRState) (plan : PayoffPlan) (hidden : Bool) :
    information.playerReachProbability
        (planFirstCommittedStrategyOfState state plan) ()
        (secondHistory hidden true).trace =
      if plan.1 then 1 else 0 := by
  rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
    ← decodeRecord_infoOf_eq_ownPlay, infoOf_secondHistory]
  rw [show decodeRecord [(Stage.first, true)] =
      [(firstKnowledge, true)] by rfl,
    InformationModel.ownPlayReachProbability]
  have hpolicy : planFirstCommittedPolicyOfState state plan firstKnowledge =
      PMF.pure (firstChoice plan.1) := by
    unfold planFirstCommittedPolicyOfState
    rw [BehavioralPolicy.commit_self (M := information)]
  rw [show planFirstCommittedStrategyOfState state plan () firstKnowledge =
      PMF.pure (firstChoice plan.1) from hpolicy]
  cases plan.1
  · simp [PMF.pure_map, firstChoice,
      InformationModel.ownPlayReachProbability, PMF.pure_apply]
  · simp [PMF.pure_map, firstChoice,
      InformationModel.ownPlayReachProbability, PMF.pure_apply]

theorem commonOwnReach_secondTrue_after_planFirstCommit
    (state : TwoSiteCFRState) (plan : PayoffPlan)
    (history : information.InformationHistory () (secondSite true).1) :
    information.playerReachProbability
        (planFirstCommittedStrategyOfState state plan) () history.1.trace =
      if plan.1 then 1 else 0 := by
  rw [← (secondHistoryEquivBool true).symm_apply_apply history]
  exact ownReach_secondTrue_after_planFirstCommit state plan _

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
      PMF.pure (firstChoice true) := by
    unfold firstCommittedPolicyOfState
    rw [BehavioralPolicy.commit_self (M := information)]
  rw [show firstCommittedStrategyOfState state () firstKnowledge =
      PMF.pure (firstChoice true) from hpolicy]
  simp [firstChoice, InformationModel.ownPlayReachProbability,
    PMF.pure_map]

theorem commonOwnReach_secondTrue_after_firstCommit
    (state : TwoSiteCFRState)
    (history : information.InformationHistory () (secondSite true).1) :
    information.playerReachProbability (firstCommittedStrategyOfState state) ()
      history.1.trace = 1 := by
  rw [← (secondHistoryEquivBool true).symm_apply_apply history]
  exact ownReach_secondTrue_after_firstCommit state _

theorem planFirstStep_rootGain
    (state : TwoSiteCFRState) (plan : PayoffPlan) :
    rootValue (planFirstCommittedStrategyOfState state plan) -
        rootValue (strategyOfState state) =
      guardedActionRegret (strategyOfState state) firstSite 2
        (firstChoice plan.1) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (strategyOfState state) () firstSite
      (planFirstCommittedPolicyOfState state plan) 1 2 firstSite_commonDepth
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne) 1
      (commonOwnReach_first_of_strategy (strategyOfState state)) terminalPayoff
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
      (counterfactualIntegrable (strategyOfState state) firstSite
        (planFirstCommittedPolicyOfState state plan) 2)
      (counterfactualIntegrable (strategyOfState state) firstSite
        (strategyOfState state ()) 2)
  have hprofile : planFirstCommittedStrategyOfState state plan =
      Profile.update (sig := information.behavioralSignature)
        (strategyOfState state) ()
          (planFirstCommittedPolicyOfState state plan) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  simpa [rootValue, guardedActionRegret,
    InformationModel.counterfactualActionRegret,
    planFirstCommittedPolicyOfState] using hroot

theorem planSecondStep_rootGain
    (state : TwoSiteCFRState) (plan : PayoffPlan) :
    rootValue (planDeviatedStrategyOfState state plan) -
        rootValue (planFirstCommittedStrategyOfState state plan) =
      (if plan.1 then 1 else 0) *
        guardedActionRegret (planFirstCommittedStrategyOfState state plan)
          (secondSite true) 1 (secondChoice true plan.2) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (planFirstCommittedStrategyOfState state plan) () (secondSite true)
      (planDeviatedPolicyOfState state plan) 2 1
      (secondSite_commonDepth true)
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne)
      (if plan.1 then 1 else 0)
      (commonOwnReach_secondTrue_after_planFirstCommit state plan)
      terminalPayoff
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
      (counterfactualIntegrable
        (planFirstCommittedStrategyOfState state plan) (secondSite true)
        (planDeviatedPolicyOfState state plan) 1)
      (counterfactualIntegrable
        (planFirstCommittedStrategyOfState state plan) (secondSite true)
        (planFirstCommittedStrategyOfState state plan ()) 1)
  have hprofile : planDeviatedStrategyOfState state plan =
      Profile.update (sig := information.behavioralSignature)
        (planFirstCommittedStrategyOfState state plan) ()
          (planDeviatedPolicyOfState state plan) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  simpa [rootValue, guardedActionRegret,
    InformationModel.counterfactualActionRegret,
    planDeviatedPolicyOfState,
    show planFirstCommittedStrategyOfState state plan () =
      planFirstCommittedPolicyOfState state plan by rfl] using hroot

theorem firstStep_rootGain
    (state : TwoSiteCFRState) :
    rootValue (firstCommittedStrategyOfState state) -
        rootValue (strategyOfState state) =
      guardedActionRegret (strategyOfState state) firstSite 2
        (firstChoice true) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (strategyOfState state) () firstSite
      (firstCommittedPolicyOfState state) 1 2 firstSite_commonDepth
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne) 1
      (commonOwnReach_first_of_strategy (strategyOfState state)) terminalPayoff
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
      (counterfactualIntegrable (strategyOfState state) firstSite
        (firstCommittedPolicyOfState state) 2)
      (counterfactualIntegrable (strategyOfState state) firstSite
        (strategyOfState state ()) 2)
  have hprofile : firstCommittedStrategyOfState state =
      Profile.update (sig := information.behavioralSignature)
        (strategyOfState state) () (firstCommittedPolicyOfState state) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  simpa [rootValue, guardedActionRegret,
    InformationModel.counterfactualActionRegret,
    firstCommittedPolicyOfState] using hroot

theorem secondStep_rootGain
    (state : TwoSiteCFRState) :
    rootValue (deviatedStrategyOfState state) -
        rootValue (firstCommittedStrategyOfState state) =
      guardedActionRegret (firstCommittedStrategyOfState state)
        (secondSite true) 1 (secondChoice true true) := by
  have hroot := information.rootGain_eq_ownReach_mul_counterfactualRegret
    (firstCommittedStrategyOfState state) () (secondSite true)
      (deviatedPolicyOfState state) 2 1 (secondSite_commonDepth true)
      (fun hne => BehavioralPolicy.commit_of_ne _ _ _ hne) 1
      (commonOwnReach_secondTrue_after_firstCommit state) terminalPayoff
      (terminalPayoff_integrable _) (terminalPayoff_integrable _)
      (counterfactualIntegrable (firstCommittedStrategyOfState state)
        (secondSite true) (deviatedPolicyOfState state) 1)
      (counterfactualIntegrable (firstCommittedStrategyOfState state)
        (secondSite true) (firstCommittedStrategyOfState state ()) 1)
  have hprofile : deviatedStrategyOfState state =
      Profile.update (sig := information.behavioralSignature)
        (firstCommittedStrategyOfState state) ()
          (deviatedPolicyOfState state) := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [← hprofile] at hroot
  simpa [rootValue, guardedActionRegret,
    InformationModel.counterfactualActionRegret,
    deviatedPolicyOfState,
    show firstCommittedStrategyOfState state () =
      firstCommittedPolicyOfState state by rfl] using hroot

theorem secondRegret_after_firstCommit_eq
    (state : TwoSiteCFRState) :
    guardedActionRegret (firstCommittedStrategyOfState state)
        (secondSite true) 1 (secondChoice true true) =
      guardedActionRegret (strategyOfState state)
        (secondSite true) 1 (secondChoice true true) := by
  simpa only [guardedActionRegret] using
    (information.counterfactualActionRegret_eq_of_agree_off_pastSite
    (firstCommittedStrategyOfState state) (strategyOfState state) () firstSite
      1 firstSite_commonDepth
      (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      (fun hinfo => BehavioralPolicy.commit_of_ne _ _ _ hinfo)
      (secondSite true) secondInformationHistory_after_firstDepth
      terminalPayoff 1 (secondChoice true true)
      ((rootGuard _ true).1 (secondChoice true true))
      (rootGuard _ true).2
      ((rootGuard _ true).1 (secondChoice true true))
      (rootGuard _ true).2)

theorem planSecondRegret_after_firstCommit_eq
    (state : TwoSiteCFRState) (plan : PayoffPlan) :
    guardedActionRegret (planFirstCommittedStrategyOfState state plan)
        (secondSite true) 1 (secondChoice true plan.2) =
      guardedActionRegret (strategyOfState state)
        (secondSite true) 1 (secondChoice true plan.2) := by
  simpa only [guardedActionRegret] using
    (information.counterfactualActionRegret_eq_of_agree_off_pastSite
    (planFirstCommittedStrategyOfState state plan) (strategyOfState state) ()
      firstSite 1 firstSite_commonDepth
      (fun other hne => False.elim (hne (Subsingleton.elim other ())))
      (fun hinfo => BehavioralPolicy.commit_of_ne _ _ _ hinfo)
      (secondSite true) secondInformationHistory_after_firstDepth
      terminalPayoff 1 (secondChoice true plan.2)
      ((rootGuard _ true).1 (secondChoice true plan.2))
      (rootGuard _ true).2
      ((rootGuard _ true).1 (secondChoice true plan.2))
      (rootGuard _ true).2)

/-- Every payoff-relevant pure plan has an exact D48 decomposition.  Plans
starting with `false` receive zero reach at the later `true` site, so they are
included without pretending that unreachable local behavior matters. -/
theorem planRootGain_decomposition (plan : PayoffPlan) (round : ℕ) :
    planRootGain plan round = ∑ key : Bool,
      planReach plan key *
        (localCounterfactualRegretVector information
          (cfrStrategyOf key
            (regretMatch
              (counterfactualRegretMatchAverage information () (rootSite key)
                (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
                (cfrEnvironment key) round))
            (cfrEnvironment key round))
          () (rootSite key) terminalPayoff (localFuel key)
          (rootGuard _ key)).ofLp
            (planChoice plan key) := by
  have havg := cfrAverages_eq_state round
  rw [Fintype.sum_bool]
  simp only [rootSite, localFuel, planReach, planChoice, one_mul]
  simp only [havg.1, havg.2]
  simp only [cfrEnvironment]
  simp only [cfrStrategyOf_false_eq_joint,
    cfrStrategyOf_true_eq_joint]
  show planRootGain plan round =
    (if plan.1 then 1 else 0) *
        guardedActionRegret
          (strategyOfState (twoSiteCFRState round))
          (secondSite true) 1 (secondChoice true plan.2) +
      guardedActionRegret
        (strategyOfState (twoSiteCFRState round))
        firstSite 2 (firstChoice plan.1)
  unfold planRootGain
  unfold fixedPlanStrategy
  rw [← planDeviatedPolicyOfState_eq_fixed]
  show
    rootValue (planDeviatedStrategyOfState (twoSiteCFRState round) plan) -
        rootValue (strategyOfState (twoSiteCFRState round)) = _
  rw [← planSecondRegret_after_firstCommit_eq,
    ← planSecondStep_rootGain, ← planFirstStep_rootGain]
  ring

/-- One deviation-independent local-distance bound controls all four
payoff-relevant pure plans at every finite horizon. -/
theorem allPayoffPlans_positiveRootGain_le_localDistances
    (t : ℕ) (ht : 0 < t) :
    ∀ plan : PayoffPlan,
      max ((∑ round ∈ Finset.range t, planRootGain plan round) / (t : ℝ)) 0 ≤
        ∑ key : Bool, Metric.infDist
          (counterfactualRegretMatchAverage information () (rootSite key)
            (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
            (cfrEnvironment key) t)
          nonposOrthant := by
  exact counterfactualRegretMatches_positiveRootGains_le information
    (fun key => LocalEnvironment key) () rootSite cfrStrategyOf cfrPayoffOf
    localFuel cfrEnvironment (fun key _ _ => rootGuard _ key)
    planRootGain planReach planReach_mem_Icc planChoice
    (fun plan round => (planRootGain_decomposition plan round).le) t ht

/-! ## Canonical strategic external regret -/

@[reducible]
def behavioralUtilityGame : UtilityGame Unit where
  form := information.toBehavioralGameForm 3
  utility history _who := terminalPayoff history

theorem behavioralUtility_integrable (who : Unit)
    (law : PMF twoStage.History) :
    UtilityIntegrable behavioralUtilityGame.utility who law := by
  cases who
  exact terminalPayoff_integrable law

def guardedExternalRegret
    (law : PMF (Profile behavioralUtilityGame.form.sig)) (who : Unit)
    (replacement : behavioralUtilityGame.form.sig.Strategy who) : ℝ :=
  behavioralUtilityGame.externalRegret law who replacement
    (behavioralUtility_integrable who _)
    (behavioralUtility_integrable who _)

theorem guardedExternalRegret_pure
    (strategy : Profile behavioralUtilityGame.form.sig)
    (replacement : behavioralUtilityGame.form.sig.Strategy ()) :
    guardedExternalRegret (PMF.pure strategy) () replacement =
      rootValue (Profile.update strategy () replacement) -
        rootValue strategy := by
  unfold guardedExternalRegret
  rw [behavioralUtilityGame.externalRegret_eq_expect_gain
    (PMF.pure strategy) () replacement
    (behavioralUtility_integrable () _)
    (behavioralUtility_integrable () _)
    (fun _ => behavioralUtility_integrable () _)
    (fun _ => behavioralUtility_integrable () _)]
  rw [expect_pure]
  rfl

def cfrRoundLaw (round : ℕ) :
    PMF (Profile behavioralUtilityGame.form.sig) :=
  PMF.pure (strategyOfState (twoSiteCFRState round))

/-- The scalar controlled above is exactly the Core library's external regret
against a fixed behavioral strategy.  The replacement is independent of the
round; only the status quo is learned. -/
theorem externalRegret_cfrRoundLaw_eq_planRootGain
    (plan : PayoffPlan) (round : ℕ) :
    guardedExternalRegret (cfrRoundLaw round) ()
        (fixedPlanPolicy plan) =
      planRootGain plan round := by
  rw [show cfrRoundLaw round =
      PMF.pure (strategyOfState (twoSiteCFRState round)) by rfl,
    guardedExternalRegret_pure]
  have hupdate :
      Profile.update (sig := behavioralUtilityGame.form.sig)
          (strategyOfState (twoSiteCFRState round)) () (fixedPlanPolicy plan) =
        fixedPlanStrategy plan := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [hupdate]
  rfl

def incumbentRoundLaw : PMF (Profile behavioralUtilityGame.form.sig) :=
  PMF.pure incumbentBehavioralStrategy

def coordinatedRoundLaw : PMF (Profile behavioralUtilityGame.form.sig) :=
  PMF.pure finalCommittedStrategy

theorem fixedPlanPolicy_true_true_eq_final :
    fixedPlanPolicy (true, true) = finalCommittedStrategy () := by
  unfold fixedPlanPolicy finalCommittedStrategy
  rw [Profile.update_same]
  rfl

theorem fixedPlanPolicy_false_false_eq_incumbent :
    fixedPlanPolicy (false, false) = incumbentBehavioralPolicy := by
  funext info
  unfold fixedPlanPolicy
  by_cases hsecond : info = (secondSite true).1
  · subst info
    rw [BehavioralPolicy.commit_self (M := information)]
    rfl
  · rw [BehavioralPolicy.commit_of_ne (M := information) _ _ _ hsecond]
    by_cases hfirst : info = firstSite.1
    · subst info
      rw [BehavioralPolicy.commit_self (M := information)]
      rfl
    · rw [BehavioralPolicy.commit_of_ne (M := information) _ _ _ hfirst]

/-- Positive control at the canonical interface: the coordinated fixed
replacement has exact unit external regret against the incumbent. -/
theorem incumbent_to_coordinated_externalRegret_eq_one :
    guardedExternalRegret incumbentRoundLaw ()
        (fixedPlanPolicy (true, true)) = 1 := by
  rw [fixedPlanPolicy_true_true_eq_final]
  rw [incumbentRoundLaw, guardedExternalRegret_pure]
  have hupdate :
      Profile.update (sig := behavioralUtilityGame.form.sig)
          incumbentBehavioralStrategy () (finalCommittedStrategy ()) =
        finalCommittedStrategy := by
    funext player
    cases player
    rw [Profile.update_same]
  rw [hupdate]
  exact wholeDeviation_rootGain_eq_one

/-- Nonprofitable control at the same interface: reversing the two fixed
strategies gives exact external regret `-1`. -/
theorem coordinated_to_incumbent_externalRegret_eq_neg_one :
    guardedExternalRegret coordinatedRoundLaw ()
        (fixedPlanPolicy (false, false)) = -1 := by
  rw [fixedPlanPolicy_false_false_eq_incumbent]
  rw [coordinatedRoundLaw, guardedExternalRegret_pure]
  have hupdate :
      Profile.update (sig := behavioralUtilityGame.form.sig)
          finalCommittedStrategy () incumbentBehavioralPolicy =
        incumbentBehavioralStrategy := by
    funext player
    cases player
    rw [Profile.update_same]
    rfl
  rw [hupdate]
  calc
    rootValue incumbentBehavioralStrategy -
        rootValue finalCommittedStrategy =
      -(rootValue finalCommittedStrategy -
        rootValue incumbentBehavioralStrategy) := by ring
    _ = -1 := by rw [wholeDeviation_rootGain_eq_one]

/-- Thus the same deviation-independent right-hand side controls the canonical
finite-horizon external regret of every payoff-relevant pure plan. -/
theorem allPayoffPlans_externalRegret_le_localDistances
    (t : ℕ) (ht : 0 < t) :
    ∀ plan : PayoffPlan,
      max
          ((∑ round ∈ Finset.range t,
              guardedExternalRegret (cfrRoundLaw round) ()
                (fixedPlanPolicy plan)) / (t : ℝ))
          0 ≤
        ∑ key : Bool, Metric.infDist
          (counterfactualRegretMatchAverage information () (rootSite key)
            (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
            (cfrEnvironment key) t)
          nonposOrthant := by
  simpa only [externalRegret_cfrRoundLaw_eq_planRootGain] using
    allPayoffPlans_positiveRootGain_le_localDistances t ht

def cfrFinRoundLaw {T : ℕ} (round : Fin T) :
    PMF (Profile behavioralUtilityGame.form.sig) :=
  cfrRoundLaw round

theorem guardedExternalRegret_timeAverage {T : ℕ} [NeZero T]
    (roundLaw : Fin T → PMF (Profile behavioralUtilityGame.form.sig))
    (replacement : behavioralUtilityGame.form.sig.Strategy ()) :
    guardedExternalRegret
        (behavioralUtilityGame.form.timeAverage roundLaw) () replacement =
      (∑ round : Fin T,
        guardedExternalRegret (roundLaw round) () replacement) / T := by
  unfold guardedExternalRegret
  exact behavioralUtilityGame.externalRegret_timeAverage roundLaw ()
    replacement (fun _ => behavioralUtility_integrable () _)
      (fun _ => behavioralUtility_integrable () _)

/-- Direct time-average consumer of the canonical Core identity.  This is the
form downstream coarse-correlated-equilibrium reductions inspect. -/
theorem allPayoffPlans_timeAverageExternalRegret_le_localDistances
    (T : ℕ) [NeZero T] :
    ∀ plan : PayoffPlan,
      max
          (guardedExternalRegret
            (behavioralUtilityGame.form.timeAverage
              (cfrFinRoundLaw (T := T))) () (fixedPlanPolicy plan))
          0 ≤
        ∑ key : Bool, Metric.infDist
          (counterfactualRegretMatchAverage information () (rootSite key)
            (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
            (cfrEnvironment key) T)
          nonposOrthant := by
  intro plan
  rw [guardedExternalRegret_timeAverage]
  simp only [cfrFinRoundLaw]
  rw [Fin.sum_univ_eq_sum_range (fun round =>
    guardedExternalRegret (cfrRoundLaw round) ()
      (fixedPlanPolicy plan)) T]
  exact allPayoffPlans_externalRegret_le_localDistances T
    (Nat.pos_of_ne_zero (NeZero.ne T)) plan

/-- D48 gives the exact per-round decomposition used by the aggregate theorem.
Both terms are the actual coupled D46 local vectors. -/
theorem cfrRootGain_decomposition (round : ℕ) :
    cfrRootGain round = ∑ key : Bool,
      1 *
        (localCounterfactualRegretVector information
          (cfrStrategyOf key
            (regretMatch
              (counterfactualRegretMatchAverage information () (rootSite key)
                (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
                (cfrEnvironment key) round))
            (cfrEnvironment key round))
          () (rootSite key) terminalPayoff (localFuel key)
          (rootGuard _ key)).ofLp
            (rootDeviation key) := by
  have havg := cfrAverages_eq_state round
  rw [Fintype.sum_bool]
  simp only [rootSite, localFuel, rootDeviation, one_mul]
  simp only [havg.1, havg.2]
  simp only [cfrEnvironment]
  simp only [cfrStrategyOf_false_eq_joint,
    cfrStrategyOf_true_eq_joint]
  show cfrRootGain round =
    guardedActionRegret (strategyOfState (twoSiteCFRState round))
        (secondSite true) 1 (secondChoice true true) +
      guardedActionRegret (strategyOfState (twoSiteCFRState round))
        firstSite 2 (firstChoice true)
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
          (cfrStrategyOf key) (cfrPayoffOf key) (localFuel key) (fun _ _ => rootGuard _ key)
          (cfrEnvironment key) t)
        nonposOrthant := by
  let firstAverage :=
    counterfactualRegretMatchAverage information () firstSite
      (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
      (cfrEnvironment false) t
  let secondAverage :=
    counterfactualRegretMatchAverage information () (secondSite true)
      (cfrStrategyOf true) (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true)
      (cfrEnvironment true) t
  have hfirstVector :=
    counterfactualRegretMatchAverage_smul_eq_sum information () firstSite
      (cfrStrategyOf false) (cfrPayoffOf false) 2
      (fun _ _ => rootGuard _ false)
      (cfrEnvironment false) t
  have hsecondVector :=
    counterfactualRegretMatchAverage_smul_eq_sum information ()
      (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
      (fun _ _ => rootGuard _ true)
      (cfrEnvironment true) t
  have hfirstCoordinate :
      ∑ round ∈ Finset.range t,
        (localCounterfactualRegretVector information
          (cfrStrategyOf false
            (regretMatch
              (counterfactualRegretMatchAverage information () firstSite
                (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
                (cfrEnvironment false) round))
            (cfrEnvironment false round))
          () firstSite terminalPayoff 2
          (rootGuard _ false)).ofLp (firstChoice true) =
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
                (fun _ _ => rootGuard _ true)
                (cfrEnvironment true) round))
            (cfrEnvironment true round))
          () (secondSite true) terminalPayoff 1
          (rootGuard _ true)).ofLp
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
                    (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true) (cfrEnvironment true) round))
                (cfrEnvironment true round))
              () (secondSite true) terminalPayoff 1
              (rootGuard _ true)).ofLp
                (secondChoice true true) +
              (localCounterfactualRegretVector information
                (cfrStrategyOf false
                  (regretMatch
                    (counterfactualRegretMatchAverage information () firstSite
                      (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
                      (cfrEnvironment false) round))
                  (cfrEnvironment false round))
                () firstSite terminalPayoff 2
                (rootGuard _ false)).ofLp (firstChoice true)) := by
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
      ‖regretPayoff firstCFRUtility law current
        (payoffIntegrable_of_finite _ _)‖ ≤ bound) :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () firstSite
          (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
          (cfrEnvironment false) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information () firstSite
    firstCFRUtility (cfrStrategyOf false) (cfrPayoffOf false) 2
      (fun _ _ => rootGuard _ false)
      cfrRealization_first hbound0 hbound (cfrEnvironment false)

/-- D46 independently drives the off-path second process to its orthant. -/
theorem secondCFR_approaches {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law current,
      ‖regretPayoff secondCFRUtility law current
        (payoffIntegrable_of_finite _ _)‖ ≤ bound) :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () (secondSite true)
          (cfrStrategyOf true) (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true)
          (cfrEnvironment true) t)
        nonposOrthant)
      atTop (nhds 0) :=
  counterfactualRegretMatch_approaches information () (secondSite true)
    secondCFRUtility (cfrStrategyOf true) (cfrPayoffOf true) 1
      (fun _ _ => rootGuard _ true)
      cfrRealization_second hbound0 hbound (cfrEnvironment true)

/-- The `[0,1]` payoff certificate discharges D46's first-site vector bound. -/
theorem firstCFR_approaches_from_payoffRange :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () firstSite
          (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
          (cfrEnvironment false) t)
        nonposOrthant)
      atTop (nhds 0) :=
  firstCFR_approaches (bound := Fintype.card FirstAction)
    (by positivity) firstCFR_regretPayoff_norm_le

/-- The same public certificate discharges the off-path second-site bound. -/
theorem secondCFR_approaches_from_payoffRange :
    Tendsto
      (fun t => Metric.infDist
        (counterfactualRegretMatchAverage information () (secondSite true)
          (cfrStrategyOf true) (cfrPayoffOf true) 1 (fun _ _ => rootGuard _ true)
          (cfrEnvironment true) t)
        nonposOrthant)
      atTop (nhds 0) :=
  secondCFR_approaches (bound := Fintype.card SecondTrueAction)
    (by positivity) secondCFR_regretPayoff_norm_le

/-- **Uniform CFR root convergence.** Both D46 limits are derived from the
payoff range, and their one common D50 bound drives every payoff-relevant pure
plan's positive average root gain to zero. -/
theorem allPayoffPlans_positiveRootGain_tendsto_zero :
    ∀ plan : PayoffPlan,
      Tendsto
        (fun t => max
          ((∑ round ∈ Finset.range t, planRootGain plan round) / (t : ℝ)) 0)
        atTop (nhds 0) := by
  exact counterfactualRegretMatches_positiveRootGains_tendsto_zero information
    (fun key => LocalEnvironment key) () rootSite cfrStrategyOf cfrPayoffOf
    localFuel cfrEnvironment (fun key _ _ => rootGuard _ key)
    planRootGain planReach planReach_mem_Icc planChoice
    (fun plan round => (planRootGain_decomposition plan round).le)
    (fun key => by
      cases key
      · exact firstCFR_approaches_from_payoffRange
      · exact secondCFR_approaches_from_payoffRange)

/-- The convergence statement is now in Core's canonical external-regret
vocabulary, still quantified over all payoff-relevant pure plans. -/
theorem allPayoffPlans_externalRegret_tendsto_zero :
    ∀ plan : PayoffPlan,
      Tendsto
        (fun t => max
          ((∑ round ∈ Finset.range t,
            guardedExternalRegret (cfrRoundLaw round) ()
              (fixedPlanPolicy plan)) / (t : ℝ)) 0)
        atTop (nhds 0) := by
  intro plan
  simpa only [externalRegret_cfrRoundLaw_eq_planRootGain] using
    allPayoffPlans_positiveRootGain_tendsto_zero plan

/-- The actual compiled-game time average has the same vanishing positive
external regret.  This directly consumes `externalRegret_timeAverage`. -/
theorem allPayoffPlans_timeAverageExternalRegret_tendsto_zero :
    ∀ plan : PayoffPlan,
      Tendsto
        (fun t => max
          (guardedExternalRegret
            (behavioralUtilityGame.form.timeAverage
              (cfrFinRoundLaw (T := t + 1))) () (fixedPlanPolicy plan)) 0)
        atTop (nhds 0) := by
  intro plan
  have hshift := (allPayoffPlans_externalRegret_tendsto_zero plan).comp
    (tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro t
  apply congrArg (fun value : ℝ => max value 0)
  rw [guardedExternalRegret_timeAverage]
  simp only [cfrFinRoundLaw]
  rw [Fin.sum_univ_eq_sum_range (fun round =>
    guardedExternalRegret (cfrRoundLaw round) ()
      (fixedPlanPolicy plan)) (t + 1)]

/-- **Concrete two-site CFR root theorem.** Ordinary per-site payoff-vector
bounds let D46 prove both local limits; the finite D48 aggregation then drives
the positive canonical root gain to zero. No convergence premise is assumed. -/
theorem twoSiteCFR_positiveRootGain_tendsto_zero
    {firstBound secondBound : ℝ}
    (hfirst0 : 0 ≤ firstBound)
    (hfirst : ∀ law current,
      ‖regretPayoff firstCFRUtility law current
        (payoffIntegrable_of_finite _ _)‖ ≤ firstBound)
    (hsecond0 : 0 ≤ secondBound)
    (hsecond : ∀ law current,
      ‖regretPayoff secondCFRUtility law current
        (payoffIntegrable_of_finite _ _)‖ ≤ secondBound) :
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
              (fun _ _ => rootGuard _ true)
              (cfrEnvironment true) t) nonposOrthant +
          Metric.infDist
            (counterfactualRegretMatchAverage information () firstSite
              (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
              (cfrEnvironment false) t) nonposOrthant)
      atTop (nhds 0) := by
    simpa using hsecondLimit.add hfirstLimit
  have hupper : ∀ t,
      max ((∑ round ∈ Finset.range t, cfrRootGain round) / (t : ℝ)) 0 ≤
        Metric.infDist
            (counterfactualRegretMatchAverage information ()
              (secondSite true) (cfrStrategyOf true) (cfrPayoffOf true) 1
              (fun _ _ => rootGuard _ true)
              (cfrEnvironment true) t) nonposOrthant +
          Metric.infDist
            (counterfactualRegretMatchAverage information () firstSite
              (cfrStrategyOf false) (cfrPayoffOf false) 2 (fun _ _ => rootGuard _ false)
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
