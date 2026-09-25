/-
# Counterfactual regret and Bayes continuation gain

Counterfactual continuation values reuse canonical Protocol histories,
behavioral continuations, and Bayes beliefs.  Exact scaling and sign theorems
connect their regret to ordinary behavioral-policy deviation gains.  Common
own reach is a named weaker certificate; perfect recall discharges it.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.BehavioralMixture

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Continuation utility from one supplied history after replacing one
player's whole behavioral policy. -/
def behavioralContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) (history : E.History)
    (hintegrable : PayoffIntegrable
      (M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) fuel history) payoff) : ℝ :=
  expect (M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) fuel history) payoff hintegrable

/-- Actual-law certificates needed at positive counterfactual-weight histories.
Histories with zero counterfactual coefficient require no continuation value. -/
def CounterfactualContinuationIntegrable [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) : Prop :=
  ∀ history : M.InformationHistory who site.1,
    M.counterfactualReachProbability strategy who history.1.trace ≠ 0 →
      PayoffIntegrable
        (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature)
            strategy who alternative) fuel history.1) payoff

/-- A continuation value at an information site weighted by everybody except
the focal player's reach. -/
def counterfactualContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hintegrable : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel) : ℝ :=
  ∑ history : M.InformationHistory who site.1,
    if hreach : M.counterfactualReachProbability strategy who history.1.trace ≠ 0 then
      M.counterfactualReachProbability strategy who history.1.trace *
        behavioralContinuationValue M strategy who alternative payoff fuel
          history.1 (hintegrable history hreach)
    else 0

/-- Changing only the focal player's baseline policy leaves counterfactual
continuation value unchanged when the supplied continuation policy is fixed.
Counterfactual reach omits that baseline coordinate, and the continuation
runner overwrites it. -/
theorem counterfactualContinuationValue_eq_of_eq_off
    [Fintype ι] [DecidableEq ι]
    {first second : (player : ι) → M.BehavioralPolicy player}
    {who : ι}
    (hagree : ∀ other, other ≠ who → first other = second other)
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hfirst : CounterfactualContinuationIntegrable M first who site
      alternative payoff fuel)
    (hsecond : CounterfactualContinuationIntegrable M second who site
      alternative payoff fuel) :
    counterfactualContinuationValue M first who site
        alternative payoff fuel hfirst =
      counterfactualContinuationValue M second who site
        alternative payoff fuel hsecond := by
  have hupdated :
      Profile.update (sig := M.behavioralSignature) first who alternative =
        Profile.update (sig := M.behavioralSignature) second who alternative := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Profile.update_same, Profile.update_same]
    · rw [Profile.update_of_ne _ _ hplayer,
        Profile.update_of_ne _ _ hplayer, hagree player hplayer]
  unfold counterfactualContinuationValue
  apply Finset.sum_congr rfl
  intro history _
  have hreach := M.counterfactualReachProbability_eq_of_eq_off
    hagree history.1.trace
  have hrun := congrArg (fun profile => M.runBehavioralFrom profile fuel history.1)
    hupdated
  by_cases hz : M.counterfactualReachProbability first who history.1.trace = 0
  · have hz' : M.counterfactualReachProbability second who history.1.trace = 0 := by
      rw [← hreach]
      exact hz
    simp [hreach, hz']
  · have hnz : M.counterfactualReachProbability second who history.1.trace ≠ 0 := by
      rw [← hreach]
      exact hz
    simp only [dite_eq_left hz, dite_eq_left hnz]
    have hvalue :
        behavioralContinuationValue M first who alternative payoff fuel history.1
            (hfirst history hz) =
          behavioralContinuationValue M second who alternative payoff fuel history.1
            (hsecond history hnz) := by
      unfold behavioralContinuationValue
      exact expect_congr_law hrun payoff (hfirst history hz) (hsecond history hnz)
    rw [hreach, hvalue]

/-- At a nonterminal history in a no-revisit decision fiber, ordinary
continuation value is affine in the selected information-local law. -/
theorem behavioralContinuationValue_withLaw_eq_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (policy : M.BehavioralPolicy who)
    (law : PMF (M.Choice who site.1))
    (history : M.InformationHistory who site.1)
    (hterm : ¬ E.terminal history.1.state)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hbase : PayoffIntegrable
      (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) strategy who
          (policy.withLaw site.1 law)) (fuel + 1) history.1) payoff)
    (hcommit : ∀ choice, choice ∈ law.support →
      PayoffIntegrable
        (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) strategy who
            (policy.commit site.1 choice)) (fuel + 1) history.1) payoff)
    (value : M.Choice who site.1 → ℝ)
    (hvalue : ∀ choice, ∀ hchoice : choice ∈ law.support,
      value choice = behavioralContinuationValue M strategy who
        (policy.commit site.1 choice) payoff (fuel + 1) history.1
        (hcommit choice hchoice)) :
    ∃ hvalueIntegrable : PayoffIntegrable law value,
      behavioralContinuationValue M strategy who
          (policy.withLaw site.1 law) payoff (fuel + 1) history.1 hbase =
        expect law value hvalueIntegrable := by
  let q := fun choice : M.Choice who site.1 => M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature) strategy who
      (policy.commit site.1 choice)) (fuel + 1) history.1
  have hrun := M.runBehavioralFrom_update_withLaw_eq_bind hactsOnce strategy who
    policy site.1 law history.1 history.2 hterm
      (InformationSite.active M site history) fuel
  have hbind : PayoffIntegrable (law.bind q) payoff := by
    rw [← hrun]
    exact hbase
  have hcond : ∀ choice, choice ∈ law.support →
      PayoffIntegrable (q choice) payoff := by
    intro choice hchoice
    exact hcommit choice hchoice
  have hvalue' : ∀ choice, ∀ hchoice : choice ∈ law.support,
      value choice =
        expect (q choice) payoff
          (payoffIntegrable_bind_conditional_on_support law q payoff hbind
            choice hchoice) := by
    intro choice hchoice
    rw [hvalue choice hchoice]
    rfl
  unfold behavioralContinuationValue
  have htower := expect_bind_tower_on_support law q payoff hbind value hvalue'
  have houter := payoffIntegrable_bind_conditionalValue_on_support law q
    payoff hbind value hvalue'
  refine ⟨houter, ?_⟩
  exact (expect_congr_law hrun payoff hbase hbind).trans htower

/-- Counterfactual continuation value is affine in a law installed at a
nonterminal, no-revisit information site.  The reach weights stay canonical;
only the existing behavioral continuation runner is factored. -/
theorem counterfactualContinuationValue_withLaw_eq_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (policy : M.BehavioralPolicy who)
    (law : PMF (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (policy.withLaw site.1 law) payoff (fuel + 1))
    (hcommit : ∀ choice, choice ∈ law.support →
      CounterfactualContinuationIntegrable M strategy who site
        (policy.commit site.1 choice) payoff (fuel + 1)) :
    ∃ hvalue : PayoffIntegrable law (extendFromSupport law fun choice hchoice =>
      counterfactualContinuationValue M strategy who site
        (policy.commit site.1 choice) payoff (fuel + 1)
        (hcommit choice hchoice)),
    counterfactualContinuationValue M strategy who site
        (policy.withLaw site.1 law) payoff (fuel + 1) hbase =
      expect law (extendFromSupport law fun choice hchoice =>
        counterfactualContinuationValue M strategy who site
          (policy.commit site.1 choice) payoff (fuel + 1)
        (hcommit choice hchoice)) hvalue := by
  classical
  let value : M.Choice who site.1 → ℝ := extendFromSupport law fun choice hchoice =>
    counterfactualContinuationValue M strategy who site
      (policy.commit site.1 choice) payoff (fuel + 1) (hcommit choice hchoice)
  let branchValue : ∀ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace ≠ 0 →
        M.Choice who site.1 → ℝ := fun history hreach =>
    extendFromSupport law fun choice hchoice =>
      behavioralContinuationValue M strategy who
        (policy.commit site.1 choice) payoff (fuel + 1) history.1
        (hcommit choice hchoice history hreach)
  let term : M.InformationHistory who site.1 → M.Choice who site.1 → ℝ :=
    fun history choice =>
      if hreach : M.counterfactualReachProbability strategy who
          history.1.trace ≠ 0 then
        M.counterfactualReachProbability strategy who history.1.trace *
          branchValue history hreach choice
      else 0
  have hvalue_sum : ∀ choice, choice ∈ law.support →
      value choice = ∑ history, term history choice := by
    intro choice hchoice
    simp only [value, extendFromSupport, dite_eq_left hchoice]
    unfold counterfactualContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace ≠ 0
    · simp only [term, dite_eq_left hreach, branchValue, extendFromSupport,
        dite_eq_left hchoice]
    · simp only [term, dite_eq_right hreach]
  have hterm_integrable : ∀ history,
      PayoffIntegrable law (term history) := by
    intro history
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace ≠ 0
    · have hsingle := M.behavioralContinuationValue_withLaw_eq_expect
        hactsOnce strategy who site policy law history
        (hallNonterminal history) payoff fuel (hbase history hreach)
        (fun choice hchoice => hcommit choice hchoice history hreach)
        (branchValue history hreach)
        (by intro choice hchoice
            simp only [branchValue, extendFromSupport, dite_eq_left hchoice])
      rcases hsingle with ⟨hbranch, _⟩
      have hweighted : PayoffIntegrable law (fun choice =>
          M.counterfactualReachProbability strategy who history.1.trace *
            branchValue history hreach choice) :=
        payoffIntegrable_const_mul hbranch
      simpa [term, hreach] using hweighted
    · have hzero : M.counterfactualReachProbability strategy who
          history.1.trace = 0 := by simpa using hreach
      simp [term, hzero, payoffIntegrable_zero]
  have hterm_expect : ∀ history,
      expect law (term history) (hterm_integrable history) =
        if hreach : M.counterfactualReachProbability strategy who
            history.1.trace ≠ 0 then
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              (policy.withLaw site.1 law) payoff (fuel + 1) history.1
              (hbase history hreach)
        else 0 := by
    intro history
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace ≠ 0
    · have hsingle := M.behavioralContinuationValue_withLaw_eq_expect
        hactsOnce strategy who site policy law history
        (hallNonterminal history) payoff fuel (hbase history hreach)
        (fun choice hchoice => hcommit choice hchoice history hreach)
        (branchValue history hreach)
        (by intro choice hchoice
            simp only [branchValue, extendFromSupport, dite_eq_left hchoice])
      rcases hsingle with ⟨hbranch, hvalue⟩
      calc
        expect law (term history) (hterm_integrable history) =
            expect law (fun choice =>
              M.counterfactualReachProbability strategy who history.1.trace *
                branchValue history hreach choice)
              (payoffIntegrable_const_mul hbranch) := by
          apply expect_congr_on_support
          intro choice _
          simp [term, hreach]
        _ = M.counterfactualReachProbability strategy who history.1.trace *
              expect law (branchValue history hreach) hbranch :=
          expect_const_mul hbranch
        _ = if h : M.counterfactualReachProbability strategy who
                history.1.trace ≠ 0 then
              M.counterfactualReachProbability strategy who history.1.trace *
                behavioralContinuationValue M strategy who
                  (policy.withLaw site.1 law) payoff (fuel + 1) history.1
                  (hbase history h)
            else 0 := by
              rw [dite_eq_left hreach]
              rw [← hvalue]
    · have hzero : M.counterfactualReachProbability strategy who
          history.1.trace = 0 := by simpa using hreach
      simp [term, branchValue, hzero, expect]
  obtain ⟨houter, houter_expect⟩ :=
    expect_eq_sum_on_support law term value hterm_integrable hvalue_sum
  have hresult :
      counterfactualContinuationValue M strategy who site
          (policy.withLaw site.1 law) payoff (fuel + 1) hbase =
        expect law value houter := by
    rw [counterfactualContinuationValue, houter_expect]
    apply Finset.sum_congr rfl
    intro history _
    exact (hterm_expect history).symm
  exact ⟨houter, hresult⟩

/-- Counterfactual regret of a whole continuation-policy replacement. Positive
values mean that the replacement improves the counterfactual continuation
value at the information site. -/
def counterfactualRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy who)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) : ℝ :=
  counterfactualContinuationValue M strategy who site alternative payoff fuel
      halternative -
    counterfactualContinuationValue M strategy who site (strategy who) payoff fuel
      hincumbent

/-- Counterfactual regret for committing to one pure choice at the selected
information site while preserving the behavioral policy everywhere else. -/
def counterfactualActionRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1)
    (haction : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) : ℝ :=
  counterfactualRegret M strategy who site payoff fuel
    ((strategy who).commit site.1 choice) haction hincumbent

/-- Counterfactual continuation payoff of one pure local commitment.  This is
the ordinary finite-action utility whose external regret is D45 action regret
when the selected information state is not revisited. -/
def counterfactualActionUtility [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1)
    (hintegrable : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff fuel) : ℝ :=
  counterfactualContinuationValue M strategy who site
    ((strategy who).commit site.1 choice) payoff fuel hintegrable

/-- At a nonterminal no-revisit site, the current counterfactual continuation
value is the expectation of its pure-commitment continuation utilities. -/
theorem counterfactualContinuationValue_eq_expect_actionUtility
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff (fuel + 1))
    (hcommit : ∀ choice, choice ∈ (strategy who site.1).support →
      CounterfactualContinuationIntegrable M strategy who site
        ((strategy who).commit site.1 choice) payoff (fuel + 1)) :
    ∃ hvalue : PayoffIntegrable (strategy who site.1)
      (extendFromSupport (strategy who site.1) fun choice hchoice =>
        counterfactualActionUtility M strategy who site payoff (fuel + 1)
          choice (hcommit choice hchoice)),
    counterfactualContinuationValue M strategy who site
        (strategy who) payoff (fuel + 1) hbase =
      expect (strategy who site.1)
        (extendFromSupport (strategy who site.1) fun choice hchoice =>
          counterfactualActionUtility M strategy who site payoff (fuel + 1)
            choice (hcommit choice hchoice)) hvalue := by
  have hsame : (strategy who).withLaw site.1 (strategy who site.1) =
      strategy who := BehavioralPolicy.withLaw_eq_self _ _
  have hwith : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).withLaw site.1 (strategy who site.1)) payoff (fuel + 1) := by
    rw [hsame]
    exact hbase
  simpa only [counterfactualActionUtility, hsame] using
    (M.counterfactualContinuationValue_withLaw_eq_expect hactsOnce
      strategy who site hallNonterminal (strategy who)
      (strategy who site.1) payoff fuel hwith hcommit)

/-- D45 action regret is exactly external regret for the pure-commitment
continuation utility.  This is the generic realization equation D46 had to
assume model by model. -/
theorem counterfactualActionRegret_eq_sub_expect
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1)
    (haction : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff (fuel + 1))
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff (fuel + 1))
    (hcommit : ∀ other, other ∈ (strategy who site.1).support →
      CounterfactualContinuationIntegrable M strategy who site
        ((strategy who).commit site.1 other) payoff (fuel + 1)) :
    ∃ hvalue : PayoffIntegrable (strategy who site.1)
      (extendFromSupport (strategy who site.1) fun other hother =>
        counterfactualActionUtility M strategy who site payoff (fuel + 1)
          other (hcommit other hother)),
      counterfactualActionRegret M strategy who site payoff (fuel + 1)
          choice haction hbase =
        counterfactualActionUtility M strategy who site payoff (fuel + 1)
          choice haction -
        expect (strategy who site.1)
          (extendFromSupport (strategy who site.1) fun other hother =>
            counterfactualActionUtility M strategy who site payoff (fuel + 1)
              other (hcommit other hother)) hvalue := by
  obtain ⟨hvalue, heq⟩ :=
    M.counterfactualContinuationValue_eq_expect_actionUtility hactsOnce
      strategy who site hallNonterminal payoff fuel hbase hcommit
  refine ⟨hvalue, ?_⟩
  simp only [counterfactualActionRegret, counterfactualRegret,
    counterfactualActionUtility, heq]

/-- The ordinary continuation value under the canonical Bayes belief at a
positive-mass information site. -/
def bayesContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hintegrable :
      (GameTheory.Protocol.Context.ofBelief
        (M.bayesBelief strategy who site hantichain hmass)
        (fun history _alternative => M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature)
            strategy who _alternative) fuel history.1)
        payoff).IntegrableAt alternative) : ℝ :=
  (GameTheory.Protocol.Context.ofBelief
    (M.bayesBelief strategy who site hantichain hmass)
    (fun history _alternative => M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        strategy who _alternative) fuel history.1)
    payoff).value alternative hintegrable

/-- A normalized counterfactual-reach fiber turns pointwise continuation
payoff bounds into the same bounds on pure-action counterfactual utility. -/
theorem counterfactualActionUtility_mem_Icc
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1)
    (haction : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff fuel)
    {lo hi : ℝ}
    (hmass : ∑ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace = 1)
    (hcontinuation : ∀ history : M.InformationHistory who site.1,
      ∀ hreach : M.counterfactualReachProbability strategy who
          history.1.trace ≠ 0,
      behavioralContinuationValue M strategy who
          ((strategy who).commit site.1 choice) payoff fuel history.1
          (haction history hreach) ∈
        Set.Icc lo hi) :
    counterfactualActionUtility M strategy who site payoff fuel choice
      haction ∈
      Set.Icc lo hi := by
  unfold counterfactualActionUtility counterfactualContinuationValue
  constructor
  · calc
      lo = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * lo := by
            rw [hmass, one_mul]
      _ = ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace * lo := by
            rw [Finset.sum_mul]
      _ ≤ ∑ history : M.InformationHistory who site.1,
          if hreach : M.counterfactualReachProbability strategy who
              history.1.trace ≠ 0 then
            M.counterfactualReachProbability strategy who history.1.trace *
              behavioralContinuationValue M strategy who
                ((strategy who).commit site.1 choice) payoff fuel history.1
                (haction history hreach)
          else 0 := by
            apply Finset.sum_le_sum
            intro history _
            by_cases hreach : M.counterfactualReachProbability strategy who
                history.1.trace ≠ 0
            · rw [dite_eq_left hreach]
              exact mul_le_mul_of_nonneg_left
                (hcontinuation history hreach).1
                (counterfactualReachProbability_nonneg M strategy who
                  history.1.trace)
            · have hzero : M.counterfactualReachProbability strategy who
                  history.1.trace = 0 := by simpa using hreach
              simp [hzero]
  · calc
      (∑ history : M.InformationHistory who site.1,
          if hreach : M.counterfactualReachProbability strategy who
              history.1.trace ≠ 0 then
            M.counterfactualReachProbability strategy who history.1.trace *
              behavioralContinuationValue M strategy who
                ((strategy who).commit site.1 choice) payoff fuel history.1
                (haction history hreach)
          else 0) ≤
          ∑ history : M.InformationHistory who site.1,
            M.counterfactualReachProbability strategy who history.1.trace * hi := by
              apply Finset.sum_le_sum
              intro history _
              by_cases hreach : M.counterfactualReachProbability strategy who
                  history.1.trace ≠ 0
              · rw [dite_eq_left hreach]
                exact mul_le_mul_of_nonneg_left
                  (hcontinuation history hreach).2
                  (counterfactualReachProbability_nonneg M strategy who
                    history.1.trace)
              · have hzero : M.counterfactualReachProbability strategy who
                    history.1.trace = 0 := by simpa using hreach
                simp [hzero]
      _ = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * hi := by
            rw [Finset.sum_mul]
      _ = hi := by rw [hmass, one_mul]

/-- Named certificate that the focal player's own reach is constant on one
information fiber.  Perfect recall implies it, while absent-minded models may
establish it directly at selected sites. -/
def CommonPlayerReachAt
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) : Prop :=
  ∃ reach : ℝ, ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = reach

/-- Perfect recall supplies common own reach at every decision information
site. -/
theorem commonPlayerReachAt_of_perfectRecall
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) :
    CommonPlayerReachAt M strategy who site := by
  obtain ⟨reference, _hnonterminal, _haction⟩ := site.2
  refine ⟨M.playerReachProbability strategy who reference.1.trace, ?_⟩
  intro history
  exact playerReachProbability_eq_of_perfectRecall M hrecall strategy who
    history.1.trace reference.1.trace (history.2.trans reference.2.symm)

/-- Positive information mass forces the certified common own reach to be
positive; a zero-own-reach fiber cannot have positive actual mass. -/
theorem commonPlayerReach_pos
    [Fintype ι] [DecidableEq ι]
    {strategy : (player : ι) → M.BehavioralPolicy player}
    {who : ι} {site : M.InformationSite who}
    (reach : ℝ)
    (hcommon : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = reach)
    (hmass : 0 < M.informationMass strategy who site) :
    0 < reach := by
  obtain ⟨history, hhistoryWeight⟩ :=
    (M.informationMass_pos_iff strategy who site).mp hmass
  have hhistory : 0 <
      (M.historyReachWeight strategy history.1).toReal :=
    ENNReal.toReal_pos (ne_of_gt hhistoryWeight)
      ((M.runBehavioral strategy history.1.trace.length).apply_ne_top
        history.1)
  rw [M.historyReachProbability_eq_player_mul_counterfactual
    strategy who history.1.trace, hcommon history] at hhistory
  exact pos_of_mul_pos_left hhistory
    (counterfactualReachProbability_nonneg M strategy who history.1.trace)

/-- A supported Bayesian history has nonzero counterfactual reach. -/
theorem counterfactualReach_ne_zero_of_bayesSupport
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (history : M.InformationHistory who site.1)
    (hs : history ∈
      (M.bayesBelief strategy who site hantichain hmass).support) :
    M.counterfactualReachProbability strategy who history.1.trace ≠ 0 := by
  let belief := M.bayesBelief strategy who site hantichain hmass
  have hweight_ne : M.historyReachWeight strategy history.1 ≠ 0 := by
    intro hzero
    have hbeliefZero : belief history = 0 := by
      rw [M.bayesBelief_apply strategy who site hantichain hmass history,
        hzero]
      simp
    exact (belief.mem_support_iff history).mp hs hbeliefZero
  have hweightPos : 0 < M.historyReachWeight strategy history.1 :=
    pos_iff_ne_zero.mpr hweight_ne
  have hreal : 0 < (M.historyReachWeight strategy history.1).toReal :=
    ENNReal.toReal_pos (ne_of_gt hweightPos)
      ((M.runBehavioral strategy history.1.trace.length).apply_ne_top
        history.1)
  rw [M.historyReachProbability_eq_player_mul_counterfactual
    strategy who history.1.trace] at hreal
  intro hzero
  rw [hzero, mul_zero] at hreal
  exact (lt_irrefl (0 : ℝ)) hreal

/-- Counterfactual integration at positive-weight histories certifies the
actual posterior continuation law on a finite information fiber. -/
theorem bayesContinuationIntegrable_of_counterfactual
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hcounter : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel) :
    (GameTheory.Protocol.Context.ofBelief
      (M.bayesBelief strategy who site hantichain hmass)
      (fun history _alternative => M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature)
          strategy who _alternative) fuel history.1)
      payoff).IntegrableAt alternative := by
  let belief := M.bayesBelief strategy who site hantichain hmass
  have hcond : ∀ history : M.InformationHistory who site.1,
      history ∈ belief.support →
        PayoffIntegrable
          (M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature)
              strategy who alternative) fuel history.1) payoff := by
    intro history hs
    exact hcounter history
      (M.counterfactualReach_ne_zero_of_bayesSupport strategy who site
        hantichain hmass history hs)
  exact payoffIntegrable_bind_of_finite_support belief
    (fun history => M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) fuel history.1) payoff
    (Set.finite_univ.subset (Set.subset_univ _)) hcond

private theorem informationMass_toReal_pos
    [Fintype ι] (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site) :
    0 < (M.informationMass strategy who site).toReal := by
  apply ENNReal.toReal_pos (ne_of_gt hmass)
  exact ne_of_lt (lt_of_le_of_lt
    (M.informationMass_le_one strategy who site hantichain)
    ENNReal.one_lt_top)

/-- If the focal player's own reach is common across one information fiber,
the canonical Bayes continuation value and the counterfactual value differ by
exactly the expected normalization factors. -/
theorem informationMass_mul_bayesContinuationValue_eq
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (hcounter : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel) :
    let hbayes := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel hcounter
    (M.informationMass strategy who site).toReal *
        bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel hbayes =
      ownReach *
        counterfactualContinuationValue M strategy who site alternative payoff fuel
          hcounter := by
  classical
  let belief := M.bayesBelief strategy who site hantichain hmass
  let kernel := fun history : M.InformationHistory who site.1 =>
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) fuel history.1
  let value : M.InformationHistory who site.1 → ℝ := fun history =>
    if hreach : M.counterfactualReachProbability strategy who
        history.1.trace ≠ 0 then
      behavioralContinuationValue M strategy who alternative payoff fuel
        history.1 (hcounter history hreach)
    else 0
  let hbayes := M.bayesContinuationIntegrable_of_counterfactual
    strategy who site hantichain hmass alternative payoff fuel hcounter
  have hcond : ∀ history, ∀ hs : history ∈ belief.support,
      value history = expect (kernel history) payoff
        (payoffIntegrable_bind_conditional_on_support belief kernel payoff
          hbayes history hs) := by
    intro history hs
    have hreach := M.counterfactualReach_ne_zero_of_bayesSupport
      strategy who site hantichain hmass history hs
    simp only [value, dite_eq_left hreach, behavioralContinuationValue]
    rfl
  have houter := payoffIntegrable_bind_conditionalValue_on_support
    belief kernel payoff hbayes value hcond
  have htower : bayesContinuationValue M strategy who site hantichain hmass
      alternative payoff fuel hbayes = expect belief value houter :=
    expect_bind_tower_on_support belief kernel payoff hbayes value hcond
  have hmassRealPos : 0 < (M.informationMass strategy who site).toReal :=
    M.informationMass_toReal_pos strategy who site hantichain hmass
  have hatom (history : M.InformationHistory who site.1) :
      (M.informationMass strategy who site).toReal *
          (belief history).toReal =
        ownReach * M.counterfactualReachProbability strategy who
          history.1.trace := by
    have hnormalized :
        (M.informationMass strategy who site).toReal *
            (belief history).toReal =
          (M.historyReachWeight strategy history.1).toReal := by
      rw [M.bayesBelief_apply, ENNReal.toReal_div]
      exact mul_div_cancel₀ _ (ne_of_gt hmassRealPos)
    rw [hnormalized, M.historyReachProbability_eq_player_mul_counterfactual,
      hown history]
  calc
    (M.informationMass strategy who site).toReal *
        bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel hbayes =
      (M.informationMass strategy who site).toReal *
        ∑ history, (belief history).toReal * value history := by
          rw [htower, expect_eq_sum]
    _ = ∑ history : M.InformationHistory who site.1,
          ownReach * M.counterfactualReachProbability strategy who
            history.1.trace * value history := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro history _
          rw [← mul_assoc, hatom history]
    _ = ownReach * counterfactualContinuationValue M strategy who site
          alternative payoff fuel hcounter := by
          rw [counterfactualContinuationValue, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro history _
          by_cases hreach : M.counterfactualReachProbability strategy who
              history.1.trace ≠ 0
          · simp only [value, dite_eq_left hreach]
            ring
          · have hzero : M.counterfactualReachProbability strategy who
                history.1.trace = 0 := by simpa using hreach
            simp [value, hzero]

/-- The scaled ordinary behavioral-policy deviation gain is exactly the scaled
counterfactual regret. This is the theorem-level consumer missing from a bare
counterfactual-regret definition. -/
theorem informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAlternative := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel halternative
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff fuel hbayesAlternative -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel hbayesIncumbent) =
      ownReach *
        counterfactualRegret M strategy who site payoff fuel alternative
          halternative hincumbent := by
  dsimp only
  rw [counterfactualRegret, mul_sub, mul_sub,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown alternative payoff fuel halternative,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown (strategy who) payoff fuel hincumbent]

/-- Action-local specialization of the exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesActionGain_eq_ownReach_mul_counterfactualActionRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (haction : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAction := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff fuel haction
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            ((strategy who).commit site.1 choice) payoff fuel hbayesAction -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel hbayesIncumbent) =
      ownReach *
        counterfactualActionRegret M strategy who site payoff fuel choice
          haction hincumbent := by
  exact informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
    strategy who site hantichain hmass ownReach hown
      ((strategy who).commit site.1 choice) payoff fuel haction hincumbent

/-- With positive common own reach, counterfactual regret detects exactly the
same profitable deviations as the ordinary canonical Bayes continuation. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ) (hownpos : 0 < ownReach)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAlternative := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel halternative
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    0 < counterfactualRegret M strategy who site payoff fuel alternative
        halternative hincumbent ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel hbayesAlternative -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel hbayesIncumbent := by
  dsimp only
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass ownReach hown alternative payoff fuel
      halternative hincumbent
  dsimp only at hscaled
  have hmassRealPos := M.informationMass_toReal_pos strategy who site
    hantichain hmass
  constructor
  · intro hregret
    have hpositive : 0 < ownReach *
        counterfactualRegret M strategy who site payoff fuel alternative
          halternative hincumbent :=
      mul_pos hownpos hregret
    rw [← hscaled] at hpositive
    exact (mul_pos_iff_of_pos_left hmassRealPos).mp hpositive
  · intro hgain
    have hpositive : 0 < (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff fuel
            (M.bayesContinuationIntegrable_of_counterfactual strategy who site
              hantichain hmass alternative payoff fuel halternative) -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel
            (M.bayesContinuationIntegrable_of_counterfactual strategy who site
              hantichain hmass (strategy who) payoff fuel hincumbent)) :=
      mul_pos hmassRealPos hgain
    rw [hscaled] at hpositive
    exact (mul_pos_iff_of_pos_left hownpos).mp hpositive

/-- Certificate-facing exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesGain_eq_commonReach_mul_counterfactualRegret
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAlternative := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel halternative
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    ∃ reach : ℝ,
      (M.informationMass strategy who site).toReal *
          (bayesContinuationValue M strategy who site hantichain hmass
              alternative payoff fuel hbayesAlternative -
            bayesContinuationValue M strategy who site hantichain hmass
              (strategy who) payoff fuel hbayesIncumbent) =
        reach *
          counterfactualRegret M strategy who site payoff fuel alternative
            halternative hincumbent := by
  rcases common with ⟨reach, hcommon⟩
  exact ⟨reach,
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass reach hcommon
        alternative payoff fuel halternative hincumbent⟩

/-- At any positive-mass site carrying common own reach, counterfactual regret
detects exactly the profitable canonical Bayes continuation deviations. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAlternative := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel halternative
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    0 < counterfactualRegret M strategy who site payoff fuel alternative
        halternative hincumbent ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel hbayesAlternative -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel hbayesIncumbent := by
  rcases common with ⟨reach, hcommon⟩
  exact counterfactualRegret_pos_iff_bayesGain_pos M strategy who site
    hantichain hmass reach
      (commonPlayerReach_pos M reach hcommon hmass)
      hcommon alternative payoff fuel halternative hincumbent

/-- Familiar perfect-recall specialization: no fiberwise reach proof remains
at the call site. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (halternative : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAlternative := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass alternative payoff fuel halternative
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    0 < counterfactualRegret M strategy who site payoff fuel alternative
        halternative hincumbent ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel hbayesAlternative -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel hbayesIncumbent :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach M strategy who site
    hantichain hmass
    (commonPlayerReachAt_of_perfectRecall M hrecall strategy who site)
    alternative payoff fuel halternative hincumbent

/-- Perfect-recall action-local specialization.  Positive counterfactual
action regret is exactly an ordinary profitable pure commitment at the
canonical Bayes continuation game. -/
theorem counterfactualActionRegret_pos_iff_bayesActionGain_pos_of_perfectRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ)
    (haction : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).commit site.1 choice) payoff fuel)
    (hincumbent : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff fuel) :
    let hbayesAction := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff fuel haction
    let hbayesIncumbent := M.bayesContinuationIntegrable_of_counterfactual
      strategy who site hantichain hmass (strategy who) payoff fuel hincumbent
    0 < counterfactualActionRegret M strategy who site payoff fuel choice
        haction hincumbent ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          ((strategy who).commit site.1 choice) payoff fuel hbayesAction -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel hbayesIncumbent := by
  exact counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall M hrecall
    strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff fuel haction hincumbent

end InformationModel

end GameTheory.Protocol
