/-
# Counterfactual decomposition

This module starts the global bridge at its semantic cut. A local behavioral
replacement is invisible strictly before a common-depth information site, and
when the root law splits there into the prefix law and a continuation runner,
the root gain is the expected continuation gain at that cut. Later theorems
reindex the cut law over the information fiber and identify the result with
counterfactual regret for the same runner.

Two runners qualify. Terminal play splits at every depth, so its identities
need no horizon. Play cut off at a fixed step count splits with a rolling
deadline: the root is cut at the site depth plus the continuation's steps.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegret

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Runner congruence needs agreement only at histories where another step can
still be taken. In particular, policies may first differ exactly at the end of
the supplied fuel block. -/
theorem runBehavioralFrom_congr_before
    [E.FiniteMovers]
    {first second : (i : ι) → M.BehavioralPolicy i} :
    ∀ (fuel : ℕ) (history : E.History),
      (∀ (later : E.History),
        ExecutionProtocol.ReachesWithin E fuel history later →
        ¬ E.terminal later.state →
        later.trace.length < history.trace.length + fuel →
        ∀ i,
          first i (M.infoOf i later.trace) =
            second i (M.infoOf i later.trace)) →
      M.runBehavioralFrom first fuel history =
        M.runBehavioralFrom second fuel history := by
  intro fuel
  induction fuel with
  | zero =>
      intro history _hagree
      rfl
  | succ fuel ih =>
      intro history hagree
      by_cases hterm : E.terminal history.state
      · rw [M.runBehavioralFrom_of_terminal _ _ hterm,
          M.runBehavioralFrom_of_terminal _ _ hterm]
      · have hhere : M.behavioralJoint first history.trace hterm =
            M.behavioralJoint second history.trace hterm :=
          M.behavioralJoint_congr history.trace hterm fun i =>
            hagree history (.refl _ _) hterm (by omega) i
        rw [M.runBehavioralFrom_succ_of_not_terminal first fuel hterm,
          M.runBehavioralFrom_succ_of_not_terminal second fuel hterm,
          hhere]
        refine bind_congr_on_support _ fun draw _ => ?_
        refine bindOnSupport_congr _ fun target realized => ?_
        apply ih
        intro later hreach hlater hlength i
        apply hagree later (.step draw.1 draw.2 realized hreach) hlater
        simp [ExecutionProtocol.History.extend,
          ExecutionProtocol.Trace.length] at hlength ⊢
        omega

/-- Replacing one information-local policy cannot affect the law strictly
before a common-depth site. The alternative need agree with the baseline only
away from that one information state. -/
theorem runBehavioral_prefix_eq_of_agree_off_site
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who) (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) depth =
      M.runBehavioral strategy depth := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro later _hreach hterm hbefore player
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hinfo : M.infoOf who later.trace = site.1
    · have hatDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hinfo⟩
      have hlt : later.trace.length < depth := by
        simpa [ExecutionProtocol.initHistory,
          ExecutionProtocol.Trace.length] using hbefore
      exact False.elim (by omega)
    · exact hagree hinfo
  · rw [Profile.update_of_ne _ _ hplayer]

/-- A continuation runner reads a profile only where play can still move: two
profiles that choose alike at every nonterminal history reachable from a start
yield the same law from it. -/
def RunnerReadsReachable (run : M.ContinuationRunner) : Prop :=
  ∀ (first second : (i : ι) → M.BehavioralPolicy i) (history : E.History),
    (∀ later, E.HistoryReaches history later → ¬ E.terminal later.state →
      ∀ i, first i (M.infoOf i later.trace) = second i (M.infoOf i later.trace)) →
    run first history = run second history

theorem runnerReadsReachable_truncated [E.FiniteMovers] (fuel : ℕ) :
    M.RunnerReadsReachable (M.truncatedRunner fuel) :=
  fun _ _ history hagree => M.runBehavioralFrom_congr fuel history
    fun later hreach hterm i => hagree later ⟨fuel, hreach⟩ hterm i

theorem runnerReadsReachable_terminal [E.FiniteMovers] (certificate : E.WellFoundedHistories) :
    M.RunnerReadsReachable (M.runBehavioralTerminalFrom certificate) :=
  fun _ _ history hagree => M.runBehavioralTerminalFrom_congr certificate history hagree

/-- Play cut off at `depth + fuel` splits at `depth` into the prefix law and
play cut off after `fuel` more steps. -/
theorem runBehavioral_add_eq_bind [E.FiniteMovers]
    (policies : (i : ι) → M.BehavioralPolicy i) (depth fuel : ℕ) :
    M.runBehavioral policies (depth + fuel) =
      (M.runBehavioral policies depth).bind (M.truncatedRunner fuel policies) :=
  M.runBehavioralFrom_add policies depth fuel E.initHistory

/-- Terminal play from the root splits at every depth into the prefix law and
terminal play from there. -/
theorem runBehavioralTerminalFrom_init_eq_bind [E.FiniteMovers]
    (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (depth : ℕ) :
    M.runBehavioralTerminalFrom certificate policies E.initHistory =
      (M.runBehavioral policies depth).bind
        (M.runBehavioralTerminalFrom certificate policies) :=
  M.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate policies depth
    E.initHistory

/-- If two profiles have the same law at a cut and each root law splits there
into the prefix law and a continuation runner, whole-law integrability derives
both supported continuation values and their integrable cut-law difference. -/
theorem rootGain_eq_prefixExpectation
    [E.FiniteMovers]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) (depth : ℕ)
    (root : ((i : ι) → M.BehavioralPolicy i) → PMF E.History)
    (run : M.ContinuationRunner)
    (hsplit : ∀ policies, root policies =
      (M.runBehavioral policies depth).bind (run policies))
    (hprefix : M.runBehavioral first depth =
      M.runBehavioral second depth)
    (hfirst : PayoffIntegrable (root first) payoff)
    (hsecond : PayoffIntegrable (root second) payoff) :
    ∃ gain : E.History → ℝ,
      PayoffIntegrable (M.runBehavioral second depth) gain ∧
      (∀ history ∈ (M.runBehavioral second depth).support,
        PayoffIntegrable (run first history) payoff ∧
          PayoffIntegrable (run second history) payoff ∧
          gain history =
            expect (run first history) payoff -
              expect (run second history) payoff) ∧
      expect (root first) payoff - expect (root second) payoff =
        expect (M.runBehavioral second depth) gain := by
  classical
  let cut := M.runBehavioral second depth
  let firstKernel := run first
  let secondKernel := run second
  have hfirstLaw : root first = cut.bind firstKernel :=
    (hsplit first).trans
      (congrArg (fun law : PMF E.History => law.bind firstKernel) hprefix)
  have hsecondLaw : root second = cut.bind secondKernel := hsplit second
  have hfirstBind : PayoffIntegrable (cut.bind firstKernel) payoff := by
    rw [← hfirstLaw]
    exact hfirst
  have hsecondBind : PayoffIntegrable (cut.bind secondKernel) payoff := by
    rw [← hsecondLaw]
    exact hsecond
  let hfirstCond := payoffIntegrable_bind_conditional_on_support
    cut firstKernel payoff hfirstBind
  let hsecondCond := payoffIntegrable_bind_conditional_on_support
    cut secondKernel payoff hsecondBind
  let firstValue := fun history => expect (firstKernel history) payoff
  let secondValue := fun history => expect (secondKernel history) payoff
  have hfirstPoint : ∀ history ∈ cut.support,
      firstValue history = expect (firstKernel history) payoff := fun _ _ => rfl
  have hsecondPoint : ∀ history ∈ cut.support,
      secondValue history = expect (secondKernel history) payoff := fun _ _ => rfl
  have hfirstOuter := payoffIntegrable_bind_conditionalValue_on_support
    cut firstKernel payoff hfirstBind firstValue hfirstPoint
  have hsecondOuter := payoffIntegrable_bind_conditionalValue_on_support
    cut secondKernel payoff hsecondBind secondValue hsecondPoint
  let gain := fun history => firstValue history - secondValue history
  have hgain : PayoffIntegrable cut gain :=
    payoffIntegrable_sub hfirstOuter hsecondOuter
  refine ⟨gain, hgain, ?_, ?_⟩
  · intro history hhistory
    exact ⟨hfirstCond history hhistory, hsecondCond history hhistory, rfl⟩
  · have hfirstExpect := expect_congr_law hfirstLaw payoff
    have hsecondExpect := expect_congr_law hsecondLaw payoff
    calc
      expect (root first) payoff - expect (root second) payoff =
          expect cut firstValue -
            expect cut secondValue := by
        rw [hfirstExpect, hsecondExpect]
        rw [expect_bind_tower_on_support cut firstKernel payoff hfirstBind
          firstValue hfirstPoint]
        rw [expect_bind_tower_on_support cut secondKernel payoff hsecondBind
          secondValue hsecondPoint]
      _ = expect cut gain := (expect_sub hfirstOuter hsecondOuter).symm

/-- Reindexing a common-depth cut law over one information fiber exposes the
canonical counterfactual coefficient. Histories outside the fiber need only
have zero gain on the finite support actually reached at the cut. -/
theorem prefixExpectation_eq_ownReach_mul_counterfactualSum
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (depth : ℕ) (hdepth : InformationSite.CommonDepth M site depth)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (gain : E.History → ℝ)
    (localGain : M.InformationHistory who site.1 → ℝ)
    (hzero : ∀ history ∈ (M.runBehavioral strategy depth).support,
      M.infoOf who history.trace ≠ site.1 → gain history = 0)
    (hlocal : ∀ history : M.InformationHistory who site.1,
      history.1 ∈ (M.runBehavioral strategy depth).support →
        gain history.1 = localGain history) :
    expect (M.runBehavioral strategy depth) gain =
      ownReach *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
             localGain history := by
  unfold expect
  calc
    (∑' history : E.History,
        (M.runBehavioral strategy depth history).toReal * gain history) =
      ∑' history : E.History,
        {history | M.infoOf who history.trace = site.1}.indicator
          (fun current =>
            (M.runBehavioral strategy depth current).toReal * gain current)
          history := by
        apply tsum_congr
        intro history
        by_cases hinfo : M.infoOf who history.trace = site.1
        · simp [Set.indicator, hinfo]
        · by_cases hsupport :
              history ∈ (M.runBehavioral strategy depth).support
          · rw [hzero history hsupport hinfo, mul_zero]
            simp [Set.indicator, hinfo]
          · have hmass : M.runBehavioral strategy depth history = 0 :=
              (M.runBehavioral strategy depth).apply_eq_zero_iff history |>.2
                hsupport
            rw [hmass]
            simp
            simp [Set.indicator, hinfo]
    _ = ∑' history : M.InformationHistory who site.1,
          (M.runBehavioral strategy depth history.1).toReal *
            gain history.1 := by
      exact (tsum_subtype
        {history | M.infoOf who history.trace = site.1}
        (fun current =>
          (M.runBehavioral strategy depth current).toReal * gain current)).symm
    _ = ∑ history : M.InformationHistory who site.1,
          (M.runBehavioral strategy depth history.1).toReal *
            gain history.1 := tsum_fintype _
    _ = ∑ history : M.InformationHistory who site.1,
          (M.runBehavioral strategy depth history.1).toReal *
            localGain history := by
      apply Finset.sum_congr rfl
      intro history _
      by_cases hsupport :
          history.1 ∈ (M.runBehavioral strategy depth).support
      · rw [hlocal history hsupport]
      · have hmass : M.runBehavioral strategy depth history.1 = 0 :=
          (M.runBehavioral strategy depth).apply_eq_zero_iff history.1 |>.2
            hsupport
        simp [hmass]
    _ = ∑ history : M.InformationHistory who site.1,
          ownReach *
            (M.counterfactualReachProbability strategy who history.1.trace *
              localGain history) := by
      apply Finset.sum_congr rfl
      intro history _
      have hprob : (M.runBehavioral strategy depth history.1).toReal =
          (M.historyReachWeight strategy history.1).toReal := by
        unfold InformationModel.historyReachWeight
        rw [hdepth history]
      rw [hprob,
        M.historyReachProbability_eq_player_mul_counterfactual
          strategy who history.1.trace,
        hown history]
      ring
    _ = ownReach *
         ∑ history : M.InformationHistory who site.1,
           M.counterfactualReachProbability strategy who history.1.trace *
             localGain history := by
      rw [Finset.mul_sum]

/-- Outside a common-depth site, a policy replacement cannot affect any later
continuation: reaching the site later would put two comparable histories at
the same trace depth. -/
theorem run_update_eq_of_outside_commonDepth
    [DecidableEq ι]
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (history : E.History) (hlength : history.trace.length = depth)
    (hinfo : M.infoOf who history.trace ≠ site.1) :
    run (Profile.update (sig := M.behavioralSignature)
          strategy who alternative) history =
      run strategy history := by
  apply hrun
  intro later hreach _hlater player
  obtain ⟨_, hreach⟩ := hreach
  by_cases hplayer : player = who
  · subst player
    rw [Profile.update_same]
    by_cases hlaterInfo : M.infoOf who later.trace = site.1
    · have hlaterDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hlaterInfo⟩
      have hequal : later = history :=
        hreach.eq_of_trace_length_eq (by omega)
      subst later
      exact False.elim (hinfo hlaterInfo)
    · exact hagree hlaterInfo
  · rw [Profile.update_of_ne _ _ hplayer]

/-- Policy differences confined to an earlier common-depth information site
are invisible to every continuation that starts strictly after that depth. -/
theorem run_eq_of_agree_off_pastSite
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (first second : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who) (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hothers : ∀ player, player ≠ who → first player = second player)
    (hwho : ∀ {info : M.InfoState who}, info ≠ site.1 →
      first who info = second who info)
    (history : E.History) (hafter : depth < history.trace.length) :
    run first history = run second history := by
  apply hrun
  intro later hreach _hlater player
  obtain ⟨_, hreach⟩ := hreach
  by_cases hplayer : player = who
  · subst player
    by_cases hinfo : M.infoOf who later.trace = site.1
    · have hlaterDepth : later.trace.length = depth := by
        simpa using hdepth ⟨later, hinfo⟩
      have hle := hreach.trace_length_le
      exact False.elim (by omega)
    · exact hwho hinfo
  · exact congrFun (hothers player hplayer)
      (M.infoOf player later.trace)

/-- Changes confined to an earlier common-depth information site do not alter
action regret at a strictly later site. Counterfactual reach already omits the
focal player's policy, and the continuation cannot revisit the earlier
site. -/
theorem counterfactualActionRegret_eq_of_agree_off_pastSite
    [E.FiniteMovers] [DecidableEq ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (pastSite : M.InformationSite who) (pastDepth : ℕ)
    (hpastDepth : InformationSite.CommonDepth M pastSite pastDepth)
    (hplayers : ∀ other, other ≠ who → first other = second other)
    (hwho : ∀ {info : M.InfoState who}, info ≠ pastSite.1 →
      first who info = second who info)
    (laterSite : M.InformationSite who)
    [Fintype (M.InformationHistory who laterSite.1)]
    (hlater : ∀ history : M.InformationHistory who laterSite.1,
      pastDepth < history.1.trace.length)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner)
    (hrun : M.RunnerReadsReachable run)
    (choice : M.Choice who laterSite.1) :
    M.counterfactualActionRegret first who laterSite payoff run choice =
      M.counterfactualActionRegret second who laterSite payoff run choice := by
  have hcontinuation : ∀
      (firstPolicy secondPolicy : M.BehavioralPolicy who),
      (∀ {info : M.InfoState who}, info ≠ pastSite.1 →
        firstPolicy info = secondPolicy info) →
      M.counterfactualContinuationValue first who laterSite firstPolicy
          payoff run =
        M.counterfactualContinuationValue second who laterSite secondPolicy
          payoff run := by
    intro firstPolicy secondPolicy hpolicy
    unfold InformationModel.counterfactualContinuationValue
      InformationModel.behavioralContinuationValue
    apply Finset.sum_congr rfl
    intro history _
    have hreachEq := M.counterfactualReachProbability_eq_of_eq_off
      hplayers history.1.trace
    have hcont := M.run_eq_of_agree_off_pastSite run hrun
      (Profile.update (sig := M.behavioralSignature) first who firstPolicy)
      (Profile.update (sig := M.behavioralSignature) second who secondPolicy)
      who pastSite pastDepth hpastDepth
      (fun other hne => by
        rw [Profile.update_of_ne _ _ hne, Profile.update_of_ne _ _ hne]
        exact hplayers other hne)
      (fun hinfo => by
        rw [Profile.update_same, Profile.update_same]
        exact hpolicy hinfo)
      history.1 (hlater history)
    rw [hreachEq, hcont]
  have hcommitted : ∀ {info : M.InfoState who}, info ≠ pastSite.1 →
      (first who).commit laterSite.1 choice info =
        (second who).commit laterSite.1 choice info := by
    intro info hinfo
    by_cases hlaterInfo : info = laterSite.1
    · subst info
      rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self]
    · rw [BehavioralPolicy.commit_of_ne _ _ _ hlaterInfo,
          BehavioralPolicy.commit_of_ne _ _ _ hlaterInfo]
      exact hwho hinfo
  unfold InformationModel.counterfactualActionRegret
    InformationModel.counterfactualRegret
  rw [hcontinuation ((first who).commit laterSite.1 choice)
      ((second who).commit laterSite.1 choice) hcommitted,
    hcontinuation (first who) (second who) hwho]

/-- The cut gain vanishes on every reached history outside the local
replacement site, including histories absorbed before the cut depth. -/
theorem cutGain_eq_zero_of_info_ne
    [E.FiniteMovers] [DecidableEq ι]
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (payoff : E.History → ℝ)
    (history : E.History)
    (hsupport : history ∈ (M.runBehavioral strategy depth).support)
    (hinfo : M.infoOf who history.trace ≠ site.1) :
    expect (run (Profile.update (sig := M.behavioralSignature)
        strategy who alternative) history) payoff -
      expect (run strategy history) payoff = 0 := by
  have hruns : run (Profile.update (sig := M.behavioralSignature)
      strategy who alternative) history = run strategy history := by
    by_cases hterm : E.terminal history.state
    · apply hrun
      intro later hreach hlater
      obtain ⟨_, hreach⟩ := hreach
      have hsame := hreach.eq_of_terminal hterm
      subst later
      exact False.elim (hlater hterm)
    · have hcut :=
        M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
          strategy depth E.initHistory history (by
            simpa [InformationModel.runBehavioral] using hsupport)
      rcases hcut with hterminal | hlength
      · exact False.elim (hterm hterminal)
      · have hlength' : history.trace.length = depth := by
          simpa [ExecutionProtocol.initHistory,
            ExecutionProtocol.Trace.length] using hlength
        exact M.run_update_eq_of_outside_commonDepth run hrun
          strategy who site alternative depth hdepth hagree history hlength' hinfo
  have hvalues := expect_congr_law hruns payoff
  rw [hvalues, sub_self]

/-- Whole-policy counterfactual regret is the counterfactual sum of the
corresponding ordinary behavioral continuation gains. -/
theorem counterfactualRegret_eq_sum_behavioralContinuationGain
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (run : M.ContinuationRunner) :
    M.counterfactualRegret strategy who site payoff run alternative =
      ∑ history : M.InformationHistory who site.1,
        M.counterfactualReachProbability strategy who history.1.trace *
          (expect (run
              (Profile.update (sig := M.behavioralSignature)
                strategy who alternative) history.1) payoff -
            expect (run
              (Profile.update (sig := M.behavioralSignature)
                strategy who (strategy who)) history.1) payoff) := by
  unfold InformationModel.counterfactualRegret
    InformationModel.counterfactualContinuationValue
    InformationModel.behavioralContinuationValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro history _
  ring

/-- **Single-site root decomposition.** For a local policy replacement at a
common-depth information site, when the root law splits at the site depth into
the prefix law and a continuation runner that reads only reachable histories,
the exact root gain is own reach times the counterfactual regret for that
runner. Early terminal histories are absorbed. -/
theorem rootGain_eq_ownReach_mul_counterfactualRegret
    [E.FiniteMovers] [DecidableEq ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (ownReach : ℝ)
    (hown : ∀ history : M.InformationHistory who site.1,
      M.playerReachProbability strategy who history.1.trace = ownReach)
    (payoff : E.History → ℝ)
    (root : ((i : ι) → M.BehavioralPolicy i) → PMF E.History)
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (hsplit : ∀ policies, root policies =
      (M.runBehavioral policies depth).bind (run policies))
    (hupdated : PayoffIntegrable (root
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative)) payoff)
    (hbaseline : PayoffIntegrable (root strategy) payoff) :
    expect (root
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative)) payoff -
      expect (root strategy) payoff =
        ownReach *
          M.counterfactualRegret strategy who site payoff run alternative := by
  let updated := Profile.update (sig := M.behavioralSignature)
    strategy who alternative
  have hprefix : M.runBehavioral updated depth =
      M.runBehavioral strategy depth :=
    M.runBehavioral_prefix_eq_of_agree_off_site strategy who site
      alternative depth hdepth hagree
  obtain ⟨gain, -, hpoint, hroot⟩ :=
    M.rootGain_eq_prefixExpectation updated strategy payoff depth root run hsplit
      hprefix hupdated hbaseline
  let localGain : M.InformationHistory who site.1 → ℝ := fun history =>
    expect (run updated history.1) payoff -
      expect (run strategy history.1) payoff
  have hzero : ∀ history ∈ (M.runBehavioral strategy depth).support,
      M.infoOf who history.trace ≠ site.1 → gain history = 0 := by
    intro history hsupport hinfo
    rw [(hpoint history hsupport).2.2]
    exact M.cutGain_eq_zero_of_info_ne run hrun strategy who site alternative depth
      hdepth hagree payoff history hsupport hinfo
  have hlocal : ∀ history : M.InformationHistory who site.1,
      history.1 ∈ (M.runBehavioral strategy depth).support →
        gain history.1 = localGain history :=
    fun history hsupport => (hpoint history.1 hsupport).2.2
  calc
    expect (root updated) payoff - expect (root strategy) payoff =
      expect (M.runBehavioral strategy depth) gain := hroot
    _ = ownReach *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability strategy who history.1.trace *
            localGain history := by
      exact M.prefixExpectation_eq_ownReach_mul_counterfactualSum
        strategy who site depth hdepth ownReach hown gain localGain
          hzero hlocal
    _ = ownReach *
        M.counterfactualRegret strategy who site payoff run alternative := by
      rw [M.counterfactualRegret_eq_sum_behavioralContinuationGain]
      simp only [localGain, updated, Profile.update_eq_self]

/-- Decision recall supplies the common own-reach coefficient in the
single-site root decomposition. The coefficient is read at the decision
history already carried by `InformationSite`. -/
theorem rootGain_eq_representativeReach_mul_counterfactualRegret_of_decisionRecall
    [E.FiniteMovers] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (hagree : ∀ {info : M.InfoState who}, info ≠ site.1 →
      alternative info = strategy who info)
    (payoff : E.History → ℝ)
    (root : ((i : ι) → M.BehavioralPolicy i) → PMF E.History)
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (hsplit : ∀ policies, root policies =
      (M.runBehavioral policies depth).bind (run policies))
    (hupdated : PayoffIntegrable (root
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative)) payoff)
    (hbaseline : PayoffIntegrable (root strategy) payoff) :
    expect (root
        (Profile.update (sig := M.behavioralSignature)
          strategy who alternative)) payoff -
      expect (root strategy) payoff =
        M.playerReachProbability strategy who site.2.choose.1.trace *
          M.counterfactualRegret strategy who site payoff run alternative := by
  apply M.rootGain_eq_ownReach_mul_counterfactualRegret strategy who site
    alternative depth hdepth hagree _ _ payoff root run hrun hsplit hupdated hbaseline
  intro history
  exact M.playerReachProbability_eq_of_decisionRecall hrecall strategy who site
    history site.2.choose

/-- Pure-action specialization of the decision-recall root bridge. -/
theorem rootGain_eq_representativeReach_mul_counterfactualActionRegret_of_decisionRecall
    [E.FiniteMovers] [DecidableEq ι]
    (hrecall : M.DecisionRecall)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (choice : M.Choice who site.1)
    (depth : ℕ)
    (hdepth : InformationSite.CommonDepth M site depth)
    (payoff : E.History → ℝ)
    (root : ((i : ι) → M.BehavioralPolicy i) → PMF E.History)
    (run : M.ContinuationRunner) (hrun : M.RunnerReadsReachable run)
    (hsplit : ∀ policies, root policies =
      (M.runBehavioral policies depth).bind (run policies))
    (hactionRoot : PayoffIntegrable (root
        (Profile.update (sig := M.behavioralSignature) strategy who
          ((strategy who).commit site.1 choice))) payoff)
    (hbaselineRoot : PayoffIntegrable (root strategy) payoff) :
    expect (root
        (Profile.update (sig := M.behavioralSignature) strategy who
          ((strategy who).commit site.1 choice))) payoff -
      expect (root strategy) payoff =
        M.playerReachProbability strategy who site.2.choose.1.trace *
          M.counterfactualActionRegret strategy who site payoff run choice := by
  exact M.rootGain_eq_representativeReach_mul_counterfactualRegret_of_decisionRecall
    hrecall strategy who site ((strategy who).commit site.1 choice)
      depth hdepth (fun hne =>
        BehavioralPolicy.commit_of_ne (strategy who) site.1 choice hne)
      payoff root run hrun hsplit hactionRoot hbaselineRoot

/-- A finite topological chain of single-site root identities telescopes to a
whole-policy root-gain decomposition. Callers obtain each premise from
`rootGain_eq_ownReach_mul_counterfactualRegret`; this lemma performs no second
evaluation and introduces no aggregate regret definition. -/
theorem rootGain_eq_sum_stepCounterfactualTerms
    (strategies : ℕ → (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ)
    (root : ((i : ι) → M.BehavioralPolicy i) → PMF E.History) (steps : ℕ)
    (ownReach localRegret : ℕ → ℝ)
    (hstep : ∀ step < steps,
      expect (root (strategies (step + 1))) payoff -
        expect (root (strategies step)) payoff =
        ownReach step * localRegret step) :
    expect (root (strategies steps)) payoff -
      expect (root (strategies 0)) payoff =
      ∑ step ∈ Finset.range steps,
        ownReach step * localRegret step := by
  let value : ℕ → ℝ := fun step =>
    if h : step ≤ steps then
      expect (root (strategies step)) payoff
    else 0
  have hvalue (step : ℕ) (hle : step ≤ steps) :
      value step = expect (root (strategies step)) payoff := by
    simp [value, hle]
  calc
    expect (root (strategies steps)) payoff -
      expect (root (strategies 0)) payoff
         = value steps - value 0 := by
      rw [hvalue steps le_rfl, hvalue 0 (Nat.zero_le steps)]
    _ = ∑ step ∈ Finset.range steps, (value (step + 1) - value step) :=
      (Finset.sum_range_sub value steps).symm
    _ = ∑ step ∈ Finset.range steps,
          ownReach step * localRegret step := by
      apply Finset.sum_congr rfl
      intro step hmem
      have hlt := Finset.mem_range.mp hmem
      rw [hvalue (step + 1) (Nat.succ_le_of_lt hlt), hvalue step hlt.le]
      exact hstep step hlt

end InformationModel

end GameTheory.Protocol
