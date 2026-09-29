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
    (payoff : E.History → ℝ) (fuel : ℕ) (history : E.History) : ℝ :=
  expect (M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) fuel history) payoff

/-- Integrability of the continuation law at every history with positive
counterfactual weight. Histories with zero counterfactual coefficient
contribute nothing to the counterfactual value. -/
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
    (payoff : E.History → ℝ) (fuel : ℕ) : ℝ :=
  ∑ history : M.InformationHistory who site.1,
    M.counterfactualReachProbability strategy who history.1.trace *
      behavioralContinuationValue M strategy who alternative payoff fuel history.1

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
    (payoff : E.History → ℝ) (fuel : ℕ) :
    counterfactualContinuationValue M first who site alternative payoff fuel =
      counterfactualContinuationValue M second who site alternative payoff fuel := by
  have hupdated :
      Profile.update (sig := M.behavioralSignature) first who alternative =
        Profile.update (sig := M.behavioralSignature) second who alternative := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Profile.update_same, Profile.update_same]
    · rw [Profile.update_of_ne _ _ hplayer,
        Profile.update_of_ne _ _ hplayer, hagree player hplayer]
  unfold counterfactualContinuationValue behavioralContinuationValue
  apply Finset.sum_congr rfl
  intro history _
  rw [M.counterfactualReachProbability_eq_of_eq_off hagree history.1.trace,
    hupdated]

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
          (policy.withLaw site.1 law)) (fuel + 1) history.1) payoff) :
    PayoffIntegrable law (fun choice => behavioralContinuationValue M strategy who
        (policy.commit site.1 choice) payoff (fuel + 1) history.1) ∧
      behavioralContinuationValue M strategy who
          (policy.withLaw site.1 law) payoff (fuel + 1) history.1 =
        expect law (fun choice => behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff (fuel + 1) history.1) := by
  let q := fun choice : M.Choice who site.1 => M.runBehavioralFrom
    (Profile.update (sig := M.behavioralSignature) strategy who
      (policy.commit site.1 choice)) (fuel + 1) history.1
  have hrun := M.runBehavioralFrom_update_withLaw_eq_bind hactsOnce strategy who
    policy site.1 law history.1 history.2 hterm
      (InformationSite.active M site history) fuel
  have hbind : PayoffIntegrable (law.bind q) payoff := by
    rw [← hrun]
    exact hbase
  have hvalue : ∀ choice ∈ law.support,
      behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff (fuel + 1) history.1 =
        expect (q choice) payoff := fun _ _ => rfl
  exact ⟨payoffIntegrable_bind_conditionalValue_on_support law q payoff hbind _ hvalue,
    (expect_congr_law hrun payoff).trans
      (expect_bind_tower_on_support law q payoff hbind _ hvalue)⟩

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
      (policy.withLaw site.1 law) payoff (fuel + 1)) :
    PayoffIntegrable law (fun choice => counterfactualContinuationValue M strategy
        who site (policy.commit site.1 choice) payoff (fuel + 1)) ∧
      counterfactualContinuationValue M strategy who site
          (policy.withLaw site.1 law) payoff (fuel + 1) =
        expect law (fun choice => counterfactualContinuationValue M strategy who
          site (policy.commit site.1 choice) payoff (fuel + 1)) := by
  classical
  let term : M.InformationHistory who site.1 → M.Choice who site.1 → ℝ :=
    fun history choice =>
      M.counterfactualReachProbability strategy who history.1.trace *
        behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff (fuel + 1) history.1
  have hterm (history : M.InformationHistory who site.1) :
      PayoffIntegrable law (term history) ∧
        expect law (term history) =
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              (policy.withLaw site.1 law) payoff (fuel + 1) history.1 := by
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace = 0
    · simp only [term, hreach, zero_mul]
      exact ⟨payoffIntegrable_zero law, expect_zero law⟩
    · obtain ⟨hbranch, hvalue⟩ := M.behavioralContinuationValue_withLaw_eq_expect
        hactsOnce strategy who site policy law history
        (hallNonterminal history) payoff fuel (hbase history hreach)
      exact ⟨payoffIntegrable_const_mul hbranch, by rw [hvalue]; exact expect_const_mul⟩
  obtain ⟨houter, houter_expect⟩ :=
    expect_eq_sum_on_support law term (fun choice => counterfactualContinuationValue
      M strategy who site (policy.commit site.1 choice) payoff (fuel + 1))
      (fun history => (hterm history).1) (fun _ _ => rfl)
  refine ⟨houter, ?_⟩
  rw [houter_expect, counterfactualContinuationValue]
  exact Finset.sum_congr rfl fun history _ => (hterm history).2.symm

/-- Counterfactual regret of a whole continuation-policy replacement. Positive
values mean that the replacement improves the counterfactual continuation
value at the information site. -/
def counterfactualRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (alternative : M.BehavioralPolicy who) : ℝ :=
  counterfactualContinuationValue M strategy who site alternative payoff fuel -
    counterfactualContinuationValue M strategy who site (strategy who) payoff fuel

/-- Counterfactual regret for committing to one pure choice at the selected
information site while preserving the behavioral policy everywhere else. -/
def counterfactualActionRegret [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualRegret M strategy who site payoff fuel
    ((strategy who).commit site.1 choice)

/-- Counterfactual continuation payoff of one pure local commitment.  This is
the ordinary finite-action utility whose external regret is the counterfactual
action regret when the selected information state is not revisited. -/
def counterfactualActionUtility [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualContinuationValue M strategy who site
    ((strategy who).commit site.1 choice) payoff fuel

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
      (strategy who) payoff (fuel + 1)) :
    PayoffIntegrable (strategy who site.1)
        (counterfactualActionUtility M strategy who site payoff (fuel + 1)) ∧
      counterfactualContinuationValue M strategy who site
          (strategy who) payoff (fuel + 1) =
        expect (strategy who site.1)
          (counterfactualActionUtility M strategy who site payoff (fuel + 1)) := by
  have hsame : (strategy who).withLaw site.1 (strategy who site.1) =
      strategy who := BehavioralPolicy.withLaw_eq_self _ _
  have hwith : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).withLaw site.1 (strategy who site.1)) payoff (fuel + 1) := by
    rw [hsame]
    exact hbase
  have h := M.counterfactualContinuationValue_withLaw_eq_expect hactsOnce
    strategy who site hallNonterminal (strategy who) (strategy who site.1)
    payoff fuel hwith
  rw [hsame] at h
  exact h

/-- Counterfactual action regret is exactly external regret for the
pure-commitment continuation utility. -/
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
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff (fuel + 1)) :
    PayoffIntegrable (strategy who site.1)
        (counterfactualActionUtility M strategy who site payoff (fuel + 1)) ∧
      counterfactualActionRegret M strategy who site payoff (fuel + 1) choice =
        counterfactualActionUtility M strategy who site payoff (fuel + 1) choice -
          expect (strategy who site.1)
            (counterfactualActionUtility M strategy who site payoff (fuel + 1)) := by
  obtain ⟨hvalue, heq⟩ :=
    M.counterfactualContinuationValue_eq_expect_actionUtility hactsOnce
      strategy who site hallNonterminal payoff fuel hbase
  refine ⟨hvalue, ?_⟩
  rw [counterfactualActionRegret, counterfactualRegret, heq]
  rfl

/-- The ordinary continuation value under the canonical Bayes belief at a
positive-mass information site. -/
def bayesContinuationValue [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (fuel : ℕ) : ℝ :=
  (GameTheory.Protocol.Context.ofBelief
    (M.bayesBelief strategy who site hantichain hmass)
    (fun history _alternative => M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        strategy who _alternative) fuel history.1)
    payoff).value alternative

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
    {lo hi : ℝ}
    (hmass : ∑ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace = 1)
    (hcontinuation : ∀ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace ≠ 0 →
      behavioralContinuationValue M strategy who
          ((strategy who).commit site.1 choice) payoff fuel history.1 ∈
        Set.Icc lo hi) :
    counterfactualActionUtility M strategy who site payoff fuel choice ∈
      Set.Icc lo hi := by
  unfold counterfactualActionUtility counterfactualContinuationValue
  have hweighted (history : M.InformationHistory who site.1) :
      M.counterfactualReachProbability strategy who history.1.trace * lo ≤
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff fuel history.1 ∧
        M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff fuel history.1 ≤
          M.counterfactualReachProbability strategy who history.1.trace * hi := by
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace = 0
    · simp [hreach]
    · have hnonneg := counterfactualReachProbability_nonneg M strategy who
        history.1.trace
      exact ⟨mul_le_mul_of_nonneg_left (hcontinuation history hreach).1 hnonneg,
        mul_le_mul_of_nonneg_left (hcontinuation history hreach).2 hnonneg⟩
  constructor
  · calc
      lo = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * lo := by
            rw [hmass, one_mul]
      _ = ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace * lo := by
            rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun history _ => (hweighted history).1
  · calc
      _ ≤ ∑ history : M.InformationHistory who site.1,
            M.counterfactualReachProbability strategy who history.1.trace * hi :=
          Finset.sum_le_sum fun history _ => (hweighted history).2
      _ = (∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace) * hi := by
            rw [Finset.sum_mul]
      _ = hi := by rw [hmass, one_mul]

/-- Named certificate that the focal player's own reach is constant on one
information fiber.  Decision recall implies it, while absent-minded models may
establish it directly at selected sites. -/
def CommonPlayerReachAt
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) : Prop :=
  ∃ reach : ℝ, ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = reach

/-- Decision recall supplies common own reach at every decision information
site. -/
theorem commonPlayerReachAt_of_decisionRecall
    (hrecall : M.DecisionRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who) :
    CommonPlayerReachAt M strategy who site := by
  obtain ⟨reference, _hnonterminal, _haction⟩ := site.2
  exact ⟨M.playerReachProbability strategy who reference.1.trace, fun history =>
    playerReachProbability_eq_of_decisionRecall M hrecall strategy who site history reference⟩

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

/-- Counterfactual integration at positive-weight histories integrates the
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
    (M.informationMass strategy who site).toReal *
        bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel =
      ownReach *
        counterfactualContinuationValue M strategy who site alternative payoff fuel := by
  classical
  let belief := M.bayesBelief strategy who site hantichain hmass
  let kernel := fun history : M.InformationHistory who site.1 =>
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) fuel history.1
  let value : M.InformationHistory who site.1 → ℝ := fun history =>
    behavioralContinuationValue M strategy who alternative payoff fuel history.1
  have hbayes := M.bayesContinuationIntegrable_of_counterfactual
    strategy who site hantichain hmass alternative payoff fuel hcounter
  have htower : bayesContinuationValue M strategy who site hantichain hmass
      alternative payoff fuel = expect belief value :=
    expect_bind_tower_on_support belief kernel payoff hbayes value fun _ _ => rfl
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
          alternative payoff fuel =
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
          alternative payoff fuel := by
          rw [counterfactualContinuationValue, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro history _
          rw [mul_assoc]

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
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff fuel -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel) =
      ownReach *
        counterfactualRegret M strategy who site payoff fuel alternative := by
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
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            ((strategy who).commit site.1 choice) payoff fuel -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff fuel) =
      ownReach *
        counterfactualActionRegret M strategy who site payoff fuel choice :=
  informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
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
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass ownReach hown alternative payoff fuel
      halternative hincumbent
  have hmassRealPos := M.informationMass_toReal_pos strategy who site
    hantichain hmass
  rw [← mul_pos_iff_of_pos_left hownpos, ← hscaled,
    mul_pos_iff_of_pos_left hmassRealPos]

/-- Common-reach form of the exact deviation-gain decomposition. -/
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
    ∃ reach : ℝ,
      (M.informationMass strategy who site).toReal *
          (bayesContinuationValue M strategy who site hantichain hmass
              alternative payoff fuel -
            bayesContinuationValue M strategy who site hantichain hmass
              (strategy who) payoff fuel) =
        reach *
          counterfactualRegret M strategy who site payoff fuel alternative := by
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
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel := by
  rcases common with ⟨reach, hcommon⟩
  exact counterfactualRegret_pos_iff_bayesGain_pos M strategy who site
    hantichain hmass reach
      (commonPlayerReach_pos M reach hcommon hmass)
      hcommon alternative payoff fuel halternative hincumbent

/-- Decision-recall specialization: no fiberwise reach proof remains at the
call site. Perfect recall supplies it through `decisionRecall_of_perfectRecall`. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_decisionRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
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
    0 < counterfactualRegret M strategy who site payoff fuel alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach M strategy who site
    hantichain hmass
    (commonPlayerReachAt_of_decisionRecall M hrecall strategy who site)
    alternative payoff fuel halternative hincumbent

/-- Decision-recall action-local specialization.  Positive counterfactual
action regret is exactly an ordinary profitable pure commitment at the
canonical Bayes continuation game. -/
theorem counterfactualActionRegret_pos_iff_bayesActionGain_pos_of_decisionRecall
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
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
    0 < counterfactualActionRegret M strategy who site payoff fuel choice ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          ((strategy who).commit site.1 choice) payoff fuel -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff fuel :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_decisionRecall M hrecall
    strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff fuel haction hincumbent

end InformationModel

end GameTheory.Protocol
