/-
# Counterfactual regret and Bayes continuation gain

Counterfactual continuation values reuse canonical Protocol histories and
Bayes beliefs, and score continued play with any continuation runner: terminal
play, or play cut off after a fixed number of steps. Exact scaling and sign
theorems connect their regret to ordinary behavioral-policy deviation gains
for every runner. Affinity in a law installed at a site is the one identity
that uses the runner's structure, through `RunnerFactorsAt`. Common own reach
is a named weaker certificate; perfect recall discharges it.
-/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Analysis.Protocol.BehavioralBayes
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.BehavioralMixture
import GameTheory.Protocol.BehavioralTerminal

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Continuation utility from one supplied history after replacing one
player's whole behavioral policy, with continued play computed by `run`. -/
def behavioralContinuationValue [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) (history : E.History) : ℝ :=
  expect (run
    (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) history) payoff

/-- Integrability of the continuation law at every history with positive
counterfactual weight. Histories with zero counterfactual coefficient
contribute nothing to the counterfactual value. -/
def CounterfactualContinuationIntegrable [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) : Prop :=
  ∀ history : M.InformationHistory who site.1,
    M.counterfactualReachProbability strategy who history.1.trace ≠ 0 →
      PayoffIntegrable
        (run
          (Profile.update (sig := M.behavioralSignature)
            strategy who alternative) history.1) payoff

/-- A continuation value at an information site weighted by everybody except
the focal player's reach. -/
def counterfactualContinuationValue [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) : ℝ :=
  ∑' history : M.InformationHistory who site.1,
    M.counterfactualReachProbability strategy who history.1.trace *
      behavioralContinuationValue M strategy who alternative payoff run history.1

/-- Changing only the focal player's baseline policy leaves counterfactual
continuation value unchanged when the supplied continuation policy is fixed.
Counterfactual reach omits that baseline coordinate, and the continuation
runner overwrites it. -/
theorem counterfactualContinuationValue_eq_of_eq_off
    [E.FiniteMovers] [DecidableEq ι]
    {first second : (player : ι) → M.BehavioralPolicy player}
    {who : ι}
    (hagree : ∀ other, other ≠ who → first other = second other)
    (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) :
    counterfactualContinuationValue M first who site alternative payoff run =
      counterfactualContinuationValue M second who site alternative payoff run := by
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
  apply tsum_congr
  intro history
  rw [M.counterfactualReachProbability_eq_of_eq_off hagree history.1.trace,
    hupdated]

/-- A continuation runner factors a law installed at a decision site: from
every history of the site, running a policy with `law` installed there draws a
choice from `law` and runs the policy committed to that choice. Terminal play
has this property at every nonterminal site that cannot matter twice, and so
does play cut off after at least one step. -/
def RunnerFactorsAt [DecidableEq ι] (run : M.ContinuationRunner) (who : ι)
    [DecidableEq (M.InfoState who)] (site : M.InformationSite who) : Prop :=
  ∀ (strategy : (player : ι) → M.BehavioralPolicy player)
    (policy : M.BehavioralPolicy who) (law : PMF (M.Choice who site.1))
    (history : M.InformationHistory who site.1),
    run (Profile.update (sig := M.behavioralSignature) strategy who
        (policy.withLaw site.1 law)) history.1 =
      law.bind fun choice =>
        run (Profile.update (sig := M.behavioralSignature) strategy who
          (policy.commit site.1 choice)) history.1

/-- Play cut off after at least one step factors a law installed at a
nonterminal site that cannot matter twice. -/
theorem runnerFactorsAt_truncated [E.FiniteMovers] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    {who : ι} [DecidableEq (M.InfoState who)] {site : M.InformationSite who}
    (hallNonterminal : InformationSite.AllNonterminal M site) (fuel : ℕ) :
    M.RunnerFactorsAt (M.truncatedRunner (fuel + 1)) who site :=
  fun strategy policy law history =>
    M.runBehavioralFrom_update_withLaw_eq_bind hactsOnce strategy who policy site.1 law
      history.1 history.2 (hallNonterminal history) (InformationSite.active M site history)
      fuel

/-- Terminal play factors a law installed at a nonterminal site that cannot
matter twice. -/
theorem runnerFactorsAt_terminal [E.FiniteMovers] [DecidableEq ι]
    (certificate : E.WellFoundedHistories)
    (hactsOnce : M.ActsOnceWhereItMatters)
    {who : ι} [DecidableEq (M.InfoState who)] {site : M.InformationSite who}
    (hallNonterminal : InformationSite.AllNonterminal M site) :
    M.RunnerFactorsAt (M.runBehavioralTerminalFrom certificate) who site :=
  fun strategy policy law history =>
    M.runBehavioralTerminalFrom_update_withLaw_eq_bind certificate hactsOnce strategy who
      policy site.1 law history.1 history.2 (hallNonterminal history)
      (InformationSite.active M site history)

/-- Where the runner factors a law installed at a site history, ordinary
continuation value from that history is affine in the law. -/
theorem behavioralContinuationValue_withLaw_eq_expect
    [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (policy : M.BehavioralPolicy who)
    (law : PMF (M.Choice who site.1))
    (history : M.InformationHistory who site.1)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hrun : run (Profile.update (sig := M.behavioralSignature) strategy who
        (policy.withLaw site.1 law)) history.1 =
      law.bind fun choice =>
        run (Profile.update (sig := M.behavioralSignature) strategy who
          (policy.commit site.1 choice)) history.1)
    (hbase : PayoffIntegrable
      (run (Profile.update (sig := M.behavioralSignature) strategy who
          (policy.withLaw site.1 law)) history.1) payoff) :
    PayoffIntegrable law (fun choice => behavioralContinuationValue M strategy who
        (policy.commit site.1 choice) payoff run history.1) ∧
      behavioralContinuationValue M strategy who
          (policy.withLaw site.1 law) payoff run history.1 =
        expect law (fun choice => behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff run history.1) := by
  let q := fun choice : M.Choice who site.1 =>
    run (Profile.update (sig := M.behavioralSignature) strategy who
      (policy.commit site.1 choice)) history.1
  have hbind : PayoffIntegrable (law.bind q) payoff := by
    rw [← hrun]
    exact hbase
  have hvalue : ∀ choice ∈ law.support,
      behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff run history.1 =
        expect (q choice) payoff := fun _ _ => rfl
  exact ⟨payoffIntegrable_bind_conditionalValue_on_support law q payoff hbind _ hvalue,
    (expect_congr_law hrun payoff).trans
      (expect_bind_tower_on_support law q payoff hbind _ hvalue)⟩

/-- Counterfactual continuation value is affine in a law installed at a site
where the runner factors it. The reach weights stay canonical; only the
continuation is factored. -/
theorem counterfactualContinuationValue_withLaw_eq_expect
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (policy : M.BehavioralPolicy who)
    (law : PMF (M.Choice who site.1))
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hfactor : M.RunnerFactorsAt run who site)
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (policy.withLaw site.1 law) payoff run) :
    PayoffIntegrable law (fun choice => counterfactualContinuationValue M strategy
        who site (policy.commit site.1 choice) payoff run) ∧
      counterfactualContinuationValue M strategy who site
          (policy.withLaw site.1 law) payoff run =
        expect law (fun choice => counterfactualContinuationValue M strategy who
          site (policy.commit site.1 choice) payoff run) := by
  classical
  let term : M.InformationHistory who site.1 → M.Choice who site.1 → ℝ :=
    fun history choice =>
      M.counterfactualReachProbability strategy who history.1.trace *
        behavioralContinuationValue M strategy who
          (policy.commit site.1 choice) payoff run history.1
  have hterm (history : M.InformationHistory who site.1) :
      PayoffIntegrable law (term history) ∧
        expect law (term history) =
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              (policy.withLaw site.1 law) payoff run history.1 := by
    by_cases hreach : M.counterfactualReachProbability strategy who
        history.1.trace = 0
    · simp only [term, hreach, zero_mul]
      exact ⟨payoffIntegrable_zero law, expect_zero law⟩
    · obtain ⟨hbranch, hvalue⟩ := M.behavioralContinuationValue_withLaw_eq_expect
        strategy who site policy law history payoff run
        (hfactor strategy policy law history) (hbase history hreach)
      exact ⟨payoffIntegrable_const_mul hbranch, by rw [hvalue]; exact expect_const_mul⟩
  obtain ⟨houter, houter_expect⟩ :=
    expect_eq_sum_on_support law term (fun choice => counterfactualContinuationValue
      M strategy who site (policy.commit site.1 choice) payoff run)
      (fun history => (hterm history).1) (fun _ _ => tsum_fintype _)
  refine ⟨houter, ?_⟩
  rw [houter_expect, counterfactualContinuationValue, tsum_fintype]
  exact Finset.sum_congr rfl fun history _ => (hterm history).2.symm

/-- Counterfactual regret of a whole continuation-policy replacement. Positive
values mean that the replacement improves the counterfactual continuation
value at the information site. -/
def counterfactualRegret [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (alternative : M.BehavioralPolicy who) : ℝ :=
  counterfactualContinuationValue M strategy who site alternative payoff run -
    counterfactualContinuationValue M strategy who site (strategy who) payoff run

/-- Counterfactual regret for committing to one pure choice at the selected
information site while preserving the behavioral policy everywhere else. -/
def counterfactualActionRegret [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualRegret M strategy who site payoff run
    ((strategy who).commit site.1 choice)

/-- Counterfactual continuation payoff of one pure local commitment.  This is
the ordinary finite-action utility whose external regret is the counterfactual
action regret when the selected information state is not revisited. -/
def counterfactualActionUtility [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (choice : M.Choice who site.1) : ℝ :=
  counterfactualContinuationValue M strategy who site
    ((strategy who).commit site.1 choice) payoff run

/-- Where the runner factors a law installed at the site, the current
counterfactual continuation value is the expectation of its pure-commitment
continuation utilities. -/
theorem counterfactualContinuationValue_eq_expect_actionUtility
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hfactor : M.RunnerFactorsAt run who site)
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff run) :
    PayoffIntegrable (strategy who site.1)
        (counterfactualActionUtility M strategy who site payoff run) ∧
      counterfactualContinuationValue M strategy who site
          (strategy who) payoff run =
        expect (strategy who site.1)
          (counterfactualActionUtility M strategy who site payoff run) := by
  have hsame : (strategy who).withLaw site.1 (strategy who site.1) =
      strategy who := BehavioralPolicy.withLaw_eq_self _ _
  have hwith : CounterfactualContinuationIntegrable M strategy who site
      ((strategy who).withLaw site.1 (strategy who site.1)) payoff run := by
    rw [hsame]
    exact hbase
  have h := M.counterfactualContinuationValue_withLaw_eq_expect
    strategy who site (strategy who) (strategy who site.1) payoff run hfactor hwith
  rw [hsame] at h
  exact h

/-- Counterfactual action regret is exactly external regret for the
pure-commitment continuation utility. -/
theorem counterfactualActionRegret_eq_sub_expect
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hfactor : M.RunnerFactorsAt run who site)
    (choice : M.Choice who site.1)
    (hbase : CounterfactualContinuationIntegrable M strategy who site
      (strategy who) payoff run) :
    PayoffIntegrable (strategy who site.1)
        (counterfactualActionUtility M strategy who site payoff run) ∧
      counterfactualActionRegret M strategy who site payoff run choice =
        counterfactualActionUtility M strategy who site payoff run choice -
          expect (strategy who site.1)
            (counterfactualActionUtility M strategy who site payoff run) := by
  obtain ⟨hvalue, heq⟩ :=
    M.counterfactualContinuationValue_eq_expect_actionUtility
      strategy who site payoff run hfactor hbase
  refine ⟨hvalue, ?_⟩
  rw [counterfactualActionRegret, counterfactualRegret, heq]
  rfl

/-- The ordinary continuation value under the canonical Bayes belief at a
positive-mass information site. -/
def bayesContinuationValue [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) : ℝ :=
  (GameTheory.Protocol.Context.ofBelief
    (M.bayesBelief strategy who site hantichain hmass)
    (fun history _alternative => run
      (Profile.update (sig := M.behavioralSignature)
        strategy who _alternative) history.1)
    payoff).value alternative

/-- The posterior continuation law of the Bayes context integrates the payoff.
This is the certificate the canonical Bayes continuation value needs; on a
finite information fiber it follows from counterfactual integrability. -/
def BayesContinuationIntegrable [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) : Prop :=
  (GameTheory.Protocol.Context.ofBelief
    (M.bayesBelief strategy who site hantichain hmass)
    (fun history _alternative => run
      (Profile.update (sig := M.behavioralSignature)
        strategy who _alternative) history.1)
    payoff).IntegrableAt alternative

/-- A normalized counterfactual-reach fiber turns pointwise continuation
payoff bounds into the same bounds on pure-action counterfactual utility. -/
theorem counterfactualActionUtility_mem_Icc
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (choice : M.Choice who site.1)
    {lo hi : ℝ}
    (hmass : ∑ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace = 1)
    (hcontinuation : ∀ history : M.InformationHistory who site.1,
      M.counterfactualReachProbability strategy who history.1.trace ≠ 0 →
      behavioralContinuationValue M strategy who
          ((strategy who).commit site.1 choice) payoff run history.1 ∈
        Set.Icc lo hi) :
    counterfactualActionUtility M strategy who site payoff run choice ∈
      Set.Icc lo hi := by
  unfold counterfactualActionUtility counterfactualContinuationValue
  rw [tsum_fintype]
  have hweighted (history : M.InformationHistory who site.1) :
      M.counterfactualReachProbability strategy who history.1.trace * lo ≤
          M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff run history.1 ∧
        M.counterfactualReachProbability strategy who history.1.trace *
            behavioralContinuationValue M strategy who
              ((strategy who).commit site.1 choice) payoff run history.1 ≤
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
    [E.FiniteMovers] [DecidableEq ι]
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
    [E.FiniteMovers] [DecidableEq ι]
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
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hcounter : CounterfactualContinuationIntegrable M strategy who site
      alternative payoff run) :
    BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run := by
  let belief := M.bayesBelief strategy who site hantichain hmass
  have hcond : ∀ history : M.InformationHistory who site.1,
      history ∈ belief.support →
        PayoffIntegrable
          (run
            (Profile.update (sig := M.behavioralSignature)
              strategy who alternative) history.1) payoff := by
    intro history hs
    exact hcounter history
      (M.counterfactualReach_ne_zero_of_bayesSupport strategy who site
        hantichain hmass history hs)
  exact payoffIntegrable_bind_of_finite_support belief
    (fun history => run
      (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) history.1) payoff
    (Set.finite_univ.subset (Set.subset_univ _)) hcond

private theorem informationMass_toReal_pos
    [E.FiniteMovers] (strategy : (player : ι) → M.BehavioralPolicy player)
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
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hbayes : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run) :
    (M.informationMass strategy who site).toReal *
        bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff run =
      ownReach *
        counterfactualContinuationValue M strategy who site alternative payoff run := by
  classical
  let belief := M.bayesBelief strategy who site hantichain hmass
  let kernel := fun history : M.InformationHistory who site.1 =>
    run
      (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) history.1
  let value : M.InformationHistory who site.1 → ℝ := fun history =>
    behavioralContinuationValue M strategy who alternative payoff run history.1
  have htower : bayesContinuationValue M strategy who site hantichain hmass
      alternative payoff run = expect belief value :=
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
          alternative payoff run =
      (M.informationMass strategy who site).toReal *
        ∑' history, (belief history).toReal * value history := by
          rw [htower]
          rfl
    _ = ∑' history : M.InformationHistory who site.1,
          ownReach * M.counterfactualReachProbability strategy who
            history.1.trace * value history := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro history
          rw [← mul_assoc, hatom history]
    _ = ownReach * counterfactualContinuationValue M strategy who site
          alternative payoff run := by
          rw [counterfactualContinuationValue, ← tsum_mul_left]
          apply tsum_congr
          intro history
          rw [mul_assoc]

/-- The scaled ordinary behavioral-policy deviation gain is exactly the scaled
counterfactual regret. This is the theorem-level consumer missing from a bare
counterfactual-regret definition. -/
theorem informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (halternative : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            alternative payoff run -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff run) =
      ownReach *
        counterfactualRegret M strategy who site payoff run alternative := by
  rw [counterfactualRegret, mul_sub, mul_sub,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown alternative payoff run halternative,
    informationMass_mul_bayesContinuationValue_eq M strategy who site
      hantichain hmass ownReach hown (strategy who) payoff run hincumbent]

/-- Action-local specialization of the exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesActionGain_eq_ownReach_mul_counterfactualActionRegret
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (haction : BayesContinuationIntegrable M strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    (M.informationMass strategy who site).toReal *
        (bayesContinuationValue M strategy who site hantichain hmass
            ((strategy who).commit site.1 choice) payoff run -
          bayesContinuationValue M strategy who site hantichain hmass
            (strategy who) payoff run) =
      ownReach *
        counterfactualActionRegret M strategy who site payoff run choice :=
  informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
    strategy who site hantichain hmass ownReach hown
      ((strategy who).commit site.1 choice) payoff run haction hincumbent

/-- With positive common own reach, counterfactual regret detects exactly the
same profitable deviations as the ordinary canonical Bayes continuation. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (ownReach : ℝ) (hownpos : 0 < ownReach)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (halternative : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    0 < counterfactualRegret M strategy who site payoff run alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff run -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff run := by
  have hscaled :=
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass ownReach hown alternative payoff run
      halternative hincumbent
  have hmassRealPos := M.informationMass_toReal_pos strategy who site
    hantichain hmass
  rw [← mul_pos_iff_of_pos_left hownpos, ← hscaled,
    mul_pos_iff_of_pos_left hmassRealPos]

/-- Common-reach form of the exact deviation-gain decomposition. -/
theorem informationMass_mul_bayesGain_eq_commonReach_mul_counterfactualRegret
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (halternative : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    ∃ reach : ℝ,
      (M.informationMass strategy who site).toReal *
          (bayesContinuationValue M strategy who site hantichain hmass
              alternative payoff run -
            bayesContinuationValue M strategy who site hantichain hmass
              (strategy who) payoff run) =
        reach *
          counterfactualRegret M strategy who site payoff run alternative := by
  rcases common with ⟨reach, hcommon⟩
  exact ⟨reach,
    informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret M
      strategy who site hantichain hmass reach hcommon
        alternative payoff run halternative hincumbent⟩

/-- At any positive-mass site carrying common own reach, counterfactual regret
detects exactly the profitable canonical Bayes continuation deviations. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (common : CommonPlayerReachAt M strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (halternative : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    0 < counterfactualRegret M strategy who site payoff run alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff run -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff run := by
  rcases common with ⟨reach, hcommon⟩
  exact counterfactualRegret_pos_iff_bayesGain_pos M strategy who site
    hantichain hmass reach
      (commonPlayerReach_pos M reach hcommon hmass)
      hcommon alternative payoff run halternative hincumbent

/-- Decision-recall specialization: no fiberwise reach proof remains at the
call site. Perfect recall supplies it through `decisionRecall_of_perfectRecall`. -/
theorem counterfactualRegret_pos_iff_bayesGain_pos_of_decisionRecall
    [E.FiniteMovers] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (halternative : BayesContinuationIntegrable M strategy who site hantichain hmass
      alternative payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    0 < counterfactualRegret M strategy who site payoff run alternative ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          alternative payoff run -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff run :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_commonReach M strategy who site
    hantichain hmass
    (commonPlayerReachAt_of_decisionRecall M hrecall strategy who site)
    alternative payoff run halternative hincumbent

/-- Decision-recall action-local specialization.  Positive counterfactual
action regret is exactly an ordinary profitable pure commitment at the
canonical Bayes continuation game. -/
theorem counterfactualActionRegret_pos_iff_bayesActionGain_pos_of_decisionRecall
    [E.FiniteMovers] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy who site)
    (choice : M.Choice who site.1)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (haction : BayesContinuationIntegrable M strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff run)
    (hincumbent : BayesContinuationIntegrable M strategy who site hantichain hmass
      (strategy who) payoff run) :
    0 < counterfactualActionRegret M strategy who site payoff run choice ↔
      0 < bayesContinuationValue M strategy who site hantichain hmass
          ((strategy who).commit site.1 choice) payoff run -
        bayesContinuationValue M strategy who site hantichain hmass
          (strategy who) payoff run :=
  counterfactualRegret_pos_iff_bayesGain_pos_of_decisionRecall M hrecall
    strategy who site hantichain hmass
      ((strategy who).commit site.1 choice) payoff run haction hincumbent

end InformationModel

end GameTheory.Protocol
