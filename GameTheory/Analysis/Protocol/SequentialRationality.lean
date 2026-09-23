/-
# Finite continuation optimality

The proof uses the canonical behavioral runner throughout. Its occupation
identity sums one-step value differences over complete histories, so decision
information sets need not lie at a common trace depth.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Analysis.Protocol.BehavioralBayes

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- Expected one-step changes telescope along the canonical behavioral run. -/
theorem runBehavioral_expect_sub_eq_sum_stepGains
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) (fuel : ℕ) :
    (M.runBehavioral strategy fuel).expect value - value E.initHistory =
      ∑ time ∈ Finset.range fuel,
        (M.runBehavioral strategy time).expect (fun history =>
          (M.runBehavioralFrom strategy 1 history).expect value - value history) := by
  have hstep (time : ℕ) :
      (M.runBehavioral strategy (time + 1)).expect value -
          (M.runBehavioral strategy time).expect value =
        (M.runBehavioral strategy time).expect (fun history =>
          (M.runBehavioralFrom strategy 1 history).expect value - value history) := by
    rw [FinDist.expect_sub]
    congr 1
    rw [runBehavioral, M.runBehavioralFrom_add, FinDist.expect_bind]
    rfl
  have hzero : (M.runBehavioral strategy 0).expect value = value E.initHistory :=
    FinDist.expect_pure _ _
  rw [← hzero, ← Finset.sum_range_sub
    (fun time => (M.runBehavioral strategy time).expect value) fuel]
  exact Finset.sum_congr rfl fun time _ => hstep time

/-- A nonterminal history can occur in a root run only at its own trace length. -/
theorem runBehavioral_prob_eq_zero_of_length_ne
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (history : E.History)
    (hterminal : ¬ E.terminal history.state)
    (hlength : history.trace.length ≠ fuel) :
    (M.runBehavioral strategy fuel).prob history = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro hsupport
  have heither := M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
    strategy fuel E.initHistory history hsupport
  rcases heither with hterminal' | hlength'
  · exact hterminal hterminal'
  · apply hlength
    simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length] using hlength'

/-- In bounded play, summing a function that vanishes at terminal histories
over elapsed times gives its complete-history reach-weighted sum. -/
theorem sum_runBehavioral_expect_eq_sum_historyReach
    [Fintype ι] [Fintype E.History]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound)
    (hterminal : ∀ history : E.History, E.terminal history.state → value history = 0) :
    (∑ time ∈ Finset.range bound, (M.runBehavioral strategy time).expect value) =
      ∑ history : E.History, M.historyReachProbability strategy history * value history := by
  classical
  simp_rw [FinDist.expect_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hterm : E.terminal history.state
  · simp [hterminal history hterm]
  · have hlt : history.trace.length < bound := by
      by_contra hnot
      exact hterm (hbound history.state history.trace (Nat.le_of_not_gt hnot))
    rw [Finset.sum_eq_single history.trace.length]
    · rfl
    · intro time _ htime
      rw [M.runBehavioral_prob_eq_zero_of_length_ne strategy time history hterm
        (Ne.symm htime), zero_mul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hlt))

/-- The finite occupation identity, with no synchrony assumption on the
histories being grouped by an information model. -/
theorem runBehavioral_expect_sub_eq_sum_historyStepGains
    [Fintype ι] [Fintype E.History]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    (M.runBehavioral strategy bound).expect value - value E.initHistory =
      ∑ history : E.History,
        M.historyReachProbability strategy history *
          ((M.runBehavioralFrom strategy 1 history).expect value - value history) := by
  rw [M.runBehavioral_expect_sub_eq_sum_stepGains]
  apply M.sum_runBehavioral_expect_eq_sum_historyReach strategy _ hbound
  intro history hterminal
  rw [M.runBehavioralFrom_of_terminal strategy 1 hterminal, FinDist.expect_pure, sub_self]

/-- A certified terminal continuation value is harmonic under its own policy. -/
theorem runBehavioralFrom_expect_continuation_eq
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (history : E.History) :
    (M.runBehavioralFrom strategy 1 history).expect
        (fun next => (M.runBehavioralFrom strategy bound next).expect payoff) =
      (M.runBehavioralFrom strategy bound history).expect payoff := by
  rw [← FinDist.expect_bind, ← M.runBehavioralFrom_add]
  rw [Nat.add_comm 1 bound, M.runBehavioralFrom_bound_add strategy hbound]

/-- The gain of replacing an entire profile is the alternative profile's
reach-weighted sum of one-step changes in the baseline continuation value. -/
theorem behavioralGain_eq_sum_historyStepGains
    [Fintype ι] [Fintype E.History]
    (baseline alternative : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    (M.runBehavioral alternative bound).expect payoff -
        (M.runBehavioral baseline bound).expect payoff =
      ∑ history : E.History,
        M.historyReachProbability alternative history *
          ((M.runBehavioralFrom alternative 1 history).expect
              (fun next => (M.runBehavioralFrom baseline bound next).expect payoff) -
            (M.runBehavioralFrom baseline bound history).expect payoff) := by
  have hvalue :
      (M.runBehavioral alternative bound).expect
          (fun next => (M.runBehavioralFrom baseline bound next).expect payoff) =
        (M.runBehavioral alternative bound).expect payoff := by
    apply FinDist.expect_congr
    intro next hnext
    rw [M.runBehavioralFrom_of_terminal baseline bound
      (M.runBehavioralFrom_terminal_of_bound alternative hbound E.initHistory next hnext),
      FinDist.expect_pure]
  have hid := M.runBehavioral_expect_sub_eq_sum_historyStepGains alternative
    (fun next => (M.runBehavioralFrom baseline bound next).expect payoff) hbound
  rw [hvalue] at hid
  exact hid

/-- Installing one local law changes the current draw and then leaves the
baseline continuation unchanged, because perfect recall excludes a revisit. -/
theorem continuation_withLaw_eq_step_expect
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (baseline : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (alternative : M.BehavioralPolicy who)
    (history : E.History) (hactive : E.active history.state who)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) baseline who
          ((baseline who).withLaw (M.infoOf who history.trace)
            (alternative (M.infoOf who history.trace)))) bound history).expect payoff =
      (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) baseline who alternative)
          1 history).expect
        (fun next => (M.runBehavioralFrom baseline bound next).expect payoff) := by
  by_cases hterm : E.terminal history.state
  · simp [M.runBehavioralFrom_of_terminal _ _ hterm]
  let changed := Profile.update (sig := M.behavioralSignature) baseline who
    ((baseline who).withLaw (M.infoOf who history.trace)
      (alternative (M.infoOf who history.trace)))
  let other := Profile.update (sig := M.behavioralSignature) baseline who alternative
  have hjoint : M.behavioralJoint changed history.trace hterm =
      M.behavioralJoint other history.trace hterm := by
    apply M.behavioralJoint_congr
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [changed, other, Profile.update_same, BehavioralPolicy.withLaw_self]
    · simp [changed, other, Profile.update_of_ne _ _ hplayer]
  have hafter (draw : {joint // E.Legal history.state joint})
      (next : E.State) (realized : next ∈ (E.step history.state draw).support) :
      M.runBehavioralFrom changed bound (history.extend draw.2 realized) =
        M.runBehavioralFrom baseline bound (history.extend draw.2 realized) := by
    apply M.runBehavioralFrom_congr
    intro later hreach _ player
    by_cases hplayer : player = who
    · subst player
      simp only [changed, Profile.update_same]
      exact BehavioralPolicy.withLaw_of_ne _ _ _
        (M.infoOf_ne_of_perfectRecall_after_step hrecall who draw.2 realized hactive hreach)
    · simp [changed, Profile.update_of_ne _ _ hplayer]
  show (M.runBehavioralFrom changed bound history).expect payoff = _
  rw [← M.runBehavioralFrom_bound_add changed hbound 1 history,
    M.runBehavioralFrom_succ_of_not_terminal changed bound hterm,
    M.runBehavioralFrom_succ_of_not_terminal other 0 hterm,
    FinDist.expect_bind, FinDist.expect_bind, hjoint]
  apply FinDist.expect_congr
  intro draw _
  apply FinDist.expect_bindOnSupport_congr
  intro next realized
  rw [hafter]
  show _ = (FinDist.pure (history.extend draw.2 realized)).expect _
  rw [FinDist.expect_pure]

/-- The focal player's own contribution to history reach is nonnegative. -/
theorem playerReachProbability_nonneg
    (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    0 ≤ M.playerReachProbability strategy who trace := by
  induction trace with
  | start => exact zero_le_one
  | extend prior joint isLegal realized ih =>
      exact mul_nonneg ih (FinDist.prob_nonneg _ _)

/-- Whole-policy root optimality follows from counterfactual optimality of
every local replacement. Perfect recall makes the alternative own reach a
common nonnegative factor on each information fiber. -/
theorem behavioralRootGain_nonpos_of_counterfactualLocalGain_nonpos
    [Fintype ι] [DecidableEq ι] [Fintype E.History]
    (hrecall : M.PerfectRecall)
    (baseline : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [Fintype (M.InfoState who)] [DecidableEq (M.InfoState who)]
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound)
    (hlocal : ∀ site : M.InformationSite who,
      M.counterfactualRegret baseline who site payoff bound
        ((baseline who).withLaw site.1 (alternative site.1)) ≤ 0) :
    (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) baseline who alternative)
          bound).expect payoff ≤
      (M.runBehavioral baseline bound).expect payoff := by
  classical
  let changed := Profile.update (sig := M.behavioralSignature) baseline who alternative
  let gain : E.History → ℝ := fun history =>
    (M.runBehavioralFrom changed 1 history).expect
        (fun next => (M.runBehavioralFrom baseline bound next).expect payoff) -
      (M.runBehavioralFrom baseline bound history).expect payoff
  have hterminal (history : E.History) (hterm : E.terminal history.state) :
      gain history = 0 := by
    simp [gain, M.runBehavioralFrom_of_terminal _ _ hterm]
  have hinactive (history : E.History) (hnot : ¬ E.active history.state who) :
      gain history = 0 := by
    have hone : M.runBehavioralFrom changed 1 history =
        M.runBehavioralFrom baseline 1 history := by
      by_cases hterm : E.terminal history.state
      · rw [M.runBehavioralFrom_of_terminal _ _ hterm,
          M.runBehavioralFrom_of_terminal _ _ hterm]
      · rw [M.runBehavioralFrom_succ_of_not_terminal changed 0 hterm,
          M.runBehavioralFrom_succ_of_not_terminal baseline 0 hterm]
        have hjoint : M.behavioralJoint changed history.trace hterm =
            M.behavioralJoint baseline history.trace hterm := by
          apply M.behavioralJoint_congr
          intro player
          by_cases hplayer : player = who
          · subst player
            exact M.behavioral_eq_of_not_active _ _ history.trace hnot
          · simp [changed, Profile.update_of_ne _ _ hplayer]
        rw [hjoint]
        rfl
    dsimp [gain]
    rw [hone, M.runBehavioralFrom_expect_continuation_eq baseline payoff hbound, sub_self]
  have hnonpos (info : M.InfoState who) :
      (∑ history : M.InformationHistory who info,
        M.historyReachProbability changed history.1 * gain history.1) ≤ 0 := by
    by_cases hsite : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info
    · let site : M.InformationSite who := ⟨info, hsite⟩
      have hgain (history : M.InformationHistory who info) :
          gain history.1 =
            (M.runBehavioralFrom
                (Profile.update (sig := M.behavioralSignature) baseline who
                  ((baseline who).withLaw info (alternative info)))
                  bound history.1).expect payoff -
              (M.runBehavioralFrom baseline bound history.1).expect payoff := by
        have heq := M.continuation_withLaw_eq_step_expect hrecall baseline who
          alternative history.1 (InformationSite.active M site history) payoff hbound
        rw [history.2] at heq
        exact congrArg (fun x => x -
          (M.runBehavioralFrom baseline bound history.1).expect payoff) heq.symm
      let reach := M.playerReachProbability changed who site.2.choose.1.trace
      have hfactor (history : M.InformationHistory who info) :
          M.historyReachProbability changed history.1 =
            reach * M.counterfactualReachProbability baseline who history.1.trace := by
        rw [M.historyReachProbability_eq_player_mul_counterfactual changed who history.1.trace,
          M.playerReachProbability_eq_of_perfectRecall hrecall changed who
            history.1.trace site.2.choose.1.trace
              (history.2.trans site.2.choose.2.symm)]
        congr 1
        exact M.counterfactualReachProbability_eq_of_eq_off
          (fun other hother => Profile.update_of_ne _ _ hother) history.1.trace
      have heq :
          (∑ history : M.InformationHistory who info,
            M.historyReachProbability changed history.1 * gain history.1) =
          reach * M.counterfactualRegret baseline who site payoff bound
            ((baseline who).withLaw info (alternative info)) := by
        unfold counterfactualRegret counterfactualContinuationValue behavioralContinuationValue
        rw [Profile.update_eq_self, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro history _
        rw [hfactor, hgain]
        ring
      rw [heq]
      exact mul_nonpos_of_nonneg_of_nonpos
        (M.playerReachProbability_nonneg changed who _) (hlocal site)
    · apply Finset.sum_nonpos
      intro history _
      by_cases hterm : E.terminal history.1.state
      · rw [hterminal history.1 hterm, mul_zero]
      · have hnot : ¬ E.active history.1.state who := by
          intro hactive
          obtain ⟨draw, _⟩ := (alternative info).support_nonempty
          have hlegal : LegalOption E history.1.state who draw.1 := by
            apply (M.menu_adequate who history.1.trace draw.1).mp
            simpa only [history.2] using draw.2
          obtain ⟨action, ha⟩ := hlegal.exists_eq_some_of_active draw.1 hactive
          apply hsite
          exact ⟨history, hterm, action, by rw [← ha]; exact draw.2⟩
        rw [hinactive history.1 hnot, mul_zero]
  apply sub_nonpos.mp
  rw [M.behavioralGain_eq_sum_historyStepGains baseline changed payoff hbound]
  show (∑ history : E.History,
    M.historyReachProbability changed history * gain history) ≤ 0
  rw [← Fintype.sum_fiberwise (fun history : E.History => M.infoOf who history.trace)]
  exact Finset.sum_nonpos fun info _ => hnonpos info

/-- Use an alternative policy at a selected information state and after that
decision. Perfect recall identifies the remembered decision history with the
actual one at every reached information state. -/
def BehavioralPolicy.spliceAfter {who : ι}
    (baseline alternative : M.BehavioralPolicy who) (info : M.InfoState who) :
    M.BehavioralPolicy who := by
  classical
  exact fun later =>
    if later = info ∨ info ∈ (M.recordAt who later).map Prod.fst then
      alternative later else baseline later

theorem BehavioralPolicy.spliceAfter_at_history
    (hrecall : M.PerfectRecall) {who : ι}
    [DecidableEq (M.InfoState who)]
    (baseline alternative : M.BehavioralPolicy who) (info : M.InfoState who)
    (history : E.History) :
    baseline.spliceAfter M alternative info (M.infoOf who history.trace) =
      if M.infoOf who history.trace = info ∨ info ∈ M.actedAt who history.trace then
        alternative (M.infoOf who history.trace) else baseline (M.infoOf who history.trace) := by
  classical
  simp only [spliceAfter, M.recordAt_eq_ownPlay hrecall who history,
    ← M.actedAt_eq_map_ownPlay]

/-- The current decision is absent from the player's past decisions under
perfect recall. Nonterminality ensures that a genuine action can be taken. -/
theorem infoOf_not_mem_actedAt_of_perfectRecall
    [Fintype ι] (hrecall : M.PerfectRecall)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (history : E.History)
    (hterm : ¬ E.terminal history.state) (hactive : E.active history.state who) :
    M.infoOf who history.trace ∉ M.actedAt who history.trace := by
  obtain ⟨draw, _⟩ := (M.behavioralJoint strategy history.trace hterm).support_nonempty
  obtain ⟨next, realized⟩ := (E.step history.state draw).support_nonempty
  obtain ⟨action, haction⟩ :=
    (E.legalOption_of_legal draw.2 who).exists_eq_some_of_active (draw.1 who) hactive
  have hnodup := InfoSignals.PerfectRecall.actsOnceAtEachInfoState M.toInfoSignals hrecall who
    (history.extend draw.2 realized).trace
  simp only [ExecutionProtocol.History.extend, InfoSignals.actedAt, haction,
    List.nodup_cons] at hnodup
  exact hnodup.1

private theorem supported_one_step_eq_extend
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (next : E.History) (hnext : next ∈ (M.runBehavioralFrom strategy 1 history).support) :
    ∃ (draw : {joint // E.Legal history.state joint}) (reached : E.State)
      (realized : reached ∈ (E.step history.state draw).support),
      next = history.extend draw.2 realized := by
  rw [M.runBehavioralFrom_succ_of_not_terminal strategy 0 hterm,
    FinDist.support_bind] at hnext
  obtain ⟨draw, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
  rw [FinDist.support_bindOnSupport] at hnext
  obtain ⟨reached, realized, hnext⟩ := Set.mem_iUnion₂.mp hnext
  refine ⟨draw, reached, realized, ?_⟩
  exact FinDist.mem_support_pure.mp hnext

/-- Once play starts at the selected information set, the spliced policy is
indistinguishable from the entire alternative continuation policy. -/
theorem runBehavioralFrom_spliceAfter_eq
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (baseline : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (history : M.InformationHistory who site.1) (fuel : ℕ) :
    M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) baseline who
          ((baseline who).spliceAfter M alternative site.1)) fuel history.1 =
      M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) baseline who alternative)
          fuel history.1 := by
  classical
  apply M.runBehavioralFrom_congr
  intro later hreach _ player
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same, BehavioralPolicy.spliceAfter_at_history M hrecall]
    apply ite_eq_left
    cases hreach with
    | refl => exact Or.inl history.2
    | @step _ _ _ joint isLegal reached realized rest =>
        right
        obtain ⟨action, haction⟩ :=
          (E.legalOption_of_legal isLegal who).exists_eq_some_of_active (joint who)
            (InformationSite.active M site history)
        apply (M.actedAt_isSuffix_of_reachesWithin who rest).subset
        simp [ExecutionProtocol.History.extend, InfoSignals.actedAt, haction, history.2]
  · simp [Profile.update_of_ne _ _ hplayer]

/-- The gain from splicing a continuation after an information set is the
reach-weighted sum of gains on its entire fiber, even if its histories occur
at different trace depths. -/
theorem rootGain_spliceAfter_eq_sum_informationGain
    [Fintype ι] [DecidableEq ι] [Fintype E.History]
    (hrecall : M.PerfectRecall)
    (baseline : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) baseline who
          ((baseline who).spliceAfter M alternative site.1)) bound).expect payoff -
        (M.runBehavioral baseline bound).expect payoff =
      ∑ history : M.InformationHistory who site.1,
        M.historyReachProbability baseline history.1 *
          ((M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) baseline who alternative)
                bound history.1).expect payoff -
            (M.runBehavioralFrom baseline bound history.1).expect payoff) := by
  classical
  let changed := Profile.update (sig := M.behavioralSignature) baseline who
    ((baseline who).spliceAfter M alternative site.1)
  let difference : E.History → ℝ := fun history =>
    (M.runBehavioralFrom changed bound history).expect payoff -
      (M.runBehavioralFrom baseline bound history).expect payoff
  let stopped : E.History → ℝ := fun history =>
    if site.1 ∈ M.actedAt who history.trace then 0 else difference history
  have hterminal (history : E.History) (hterm : E.terminal history.state) :
      difference history = 0 := by
    simp [difference, M.runBehavioralFrom_of_terminal _ _ hterm]
  have hstoppedTerminal (history : E.History) (hterm : E.terminal history.state) :
      stopped history = 0 := by
    simp [stopped, hterminal history hterm]
  have hresidual (history : E.History) :
      (M.runBehavioralFrom baseline 1 history).expect stopped - stopped history =
        if M.infoOf who history.trace = site.1 then -difference history else 0 := by
    by_cases hterm : E.terminal history.state
    · simp [M.runBehavioralFrom_of_terminal _ _ hterm, hterminal history hterm]
    by_cases hpast : site.1 ∈ M.actedAt who history.trace
    · have hinfo : M.infoOf who history.trace ≠ site.1 := by
        intro heq
        have hnot := M.infoOf_not_mem_actedAt_of_perfectRecall hrecall baseline who
          history hterm (InformationSite.active M site ⟨history, heq⟩)
        rw [heq] at hnot
        exact hnot hpast
      have hnext : (M.runBehavioralFrom baseline 1 history).expect stopped = 0 := by
        rw [← FinDist.expect_const (M.runBehavioralFrom baseline 1 history) (0 : ℝ)]
        apply FinDist.expect_congr
        intro next hnext
        have hreach := E.runRandomizedFor_reachesWithin
          (M.randomizedChooser baseline) 1 history next hnext
        exact ite_eq_left ((M.actedAt_isSuffix_of_reachesWithin who hreach).subset hpast)
      rw [hnext, show stopped history = 0 from ite_eq_left hpast, ite_eq_right hinfo, sub_self]
    · by_cases hinfo : M.infoOf who history.trace = site.1
      · have hnext : (M.runBehavioralFrom baseline 1 history).expect stopped = 0 := by
          rw [← FinDist.expect_const (M.runBehavioralFrom baseline 1 history) (0 : ℝ)]
          apply FinDist.expect_congr
          intro next hnext
          obtain ⟨draw, reached, realized, rfl⟩ :=
            supported_one_step_eq_extend M baseline history hterm next hnext
          obtain ⟨action, haction⟩ :=
            (E.legalOption_of_legal draw.2 who).exists_eq_some_of_active (draw.1 who)
              (InformationSite.active M site ⟨history, hinfo⟩)
          apply ite_eq_left
          simp [ExecutionProtocol.History.extend, InfoSignals.actedAt, haction, hinfo]
        rw [hnext, show stopped history = difference history from ite_eq_right hpast,
          ite_eq_left hinfo, zero_sub]
      · have hone : M.runBehavioralFrom changed 1 history =
            M.runBehavioralFrom baseline 1 history := by
          rw [M.runBehavioralFrom_succ_of_not_terminal changed 0 hterm,
            M.runBehavioralFrom_succ_of_not_terminal baseline 0 hterm]
          have hjoint : M.behavioralJoint changed history.trace hterm =
              M.behavioralJoint baseline history.trace hterm := by
            apply M.behavioralJoint_congr
            intro player
            by_cases hplayer : player = who
            · subst player
              simp [changed, Profile.update_same,
                BehavioralPolicy.spliceAfter_at_history M hrecall, hinfo, hpast]
            · simp [changed, Profile.update_of_ne _ _ hplayer]
          rw [hjoint]
          rfl
        have hnext : (M.runBehavioralFrom baseline 1 history).expect stopped =
            (M.runBehavioralFrom baseline 1 history).expect difference := by
          apply FinDist.expect_congr
          intro next hnext
          obtain ⟨draw, reached, realized, rfl⟩ :=
            supported_one_step_eq_extend M baseline history hterm next hnext
          apply ite_eq_right
          simp only [ExecutionProtocol.History.extend, InfoSignals.actedAt]
          cases haction : draw.1 who with
          | none => exact hpast
          | some action => simp [Ne.symm hinfo, hpast]
        rw [hnext, show stopped history = difference history from ite_eq_right hpast,
          ite_eq_right hinfo]
        dsimp [difference]
        rw [FinDist.expect_sub, ← hone,
          M.runBehavioralFrom_expect_continuation_eq changed payoff hbound,
          hone, M.runBehavioralFrom_expect_continuation_eq baseline payoff hbound]
        ring
  have hsum :
      (∑ history : E.History,
        if M.infoOf who history.trace = site.1 then
          M.historyReachProbability baseline history * difference history else 0) =
        ∑ history : M.InformationHistory who site.1,
          M.historyReachProbability baseline history.1 * difference history.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp)
      (fun history => M.historyReachProbability baseline history * difference history)
  have hid := M.runBehavioral_expect_sub_eq_sum_historyStepGains baseline stopped hbound
  have hend : (M.runBehavioral baseline bound).expect stopped = 0 := by
    rw [← FinDist.expect_const (M.runBehavioral baseline bound) (0 : ℝ)]
    apply FinDist.expect_congr
    intro history hhistory
    exact hstoppedTerminal history
      (M.runBehavioralFrom_terminal_of_bound baseline hbound E.initHistory history hhistory)
  have hstart : stopped E.initHistory = difference E.initHistory := by
    simp [stopped, ExecutionProtocol.initHistory, InfoSignals.actedAt]
  have hscores :
      (∑ history : E.History,
        M.historyReachProbability baseline history *
          ((M.runBehavioralFrom baseline 1 history).expect stopped - stopped history)) =
        -(∑ history : M.InformationHistory who site.1,
          M.historyReachProbability baseline history.1 * difference history.1) := by
    rw [← hsum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro history _
    rw [hresidual]
    split_ifs <;> ring
  rw [hend, hstart, zero_sub, hscores, neg_inj] at hid
  show difference E.initHistory = _
  rw [hid]
  apply Finset.sum_congr rfl
  intro history _
  dsimp [difference, changed]
  rw [M.runBehavioralFrom_spliceAfter_eq hrecall baseline who site alternative history]

/-- A Bayes-consistent assessment evaluates a positive-mass information set
with the canonical normalized-reach continuation value. -/
theorem BehavioralAssessment.continuationContext_value_eq_bayesContinuationValue
    [Fintype ι] [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass assessment.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt (M := M) assessment who site
      hantichain hmass)
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ) :
    (assessment.continuationContext site payoff fuel).value alternative =
      M.bayesContinuationValue assessment.strategy who site hantichain hmass
        alternative payoff fuel := by
  have hbelief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site hantichain hmass := by
    apply FinDist.ext_of_prob
    intro history
    rw [M.bayesBelief_prob]
    exact hbayes history
  rw [BehavioralAssessment.continuationContext_value, FinDist.expect_bind, hbelief]
  rfl

/-- Multiplying a Bayes continuation gain by the information-event mass
recovers the unnormalized sum on that information fiber. -/
theorem BehavioralAssessment.informationMass_mul_continuationGain_eq_sum
    [Fintype ι] [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass assessment.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt (M := M) assessment who site
      hantichain hmass)
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ) :
    M.informationMass assessment.strategy who site *
        ((assessment.continuationContext site payoff fuel).value alternative -
          (assessment.continuationContext site payoff fuel).value (assessment.strategy who)) =
      ∑ history : M.InformationHistory who site.1,
        M.historyReachProbability assessment.strategy history.1 *
          ((M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
                fuel history.1).expect payoff -
            (M.runBehavioralFrom assessment.strategy fuel history.1).expect payoff) := by
  rw [BehavioralAssessment.continuationContext_value,
    BehavioralAssessment.continuationContext_value, Profile.update_eq_self,
    FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub,
    FinDist.expect_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro history _
  rw [hbayes history]
  field_simp [hmass.ne']

/-- In a finite perfect-recall protocol with a certified terminal horizon,
local optimality against every allowed law implies optimality against every
whole continuation policy whose local laws are allowed. The allowed sets may
vary by player and information state; only their product structure is used.

Full support makes all information events positive, and Bayes consistency
supplies their conditional beliefs. No common-depth or nonterminal-fiber
assumption is imposed. -/
theorem BehavioralAssessment.continuation_value_le_of_locallyOptimal
    [Fintype ι] [DecidableEq ι] [Fintype E.History]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hrecall : M.PerfectRecall)
    (assessment : M.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : BehavioralAssessment.IsBayesConsistent M assessment
      (M.decisionInformationAntichain_of_perfectRecall hrecall))
    (Allowed : (i : ι) → (info : M.InfoState i) → FinDist (M.Choice i info) → Prop)
    (hfeasible : ∀ i info, Allowed i info (assessment.strategy i info))
    (payoff : ι → E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound)
    (hlocal : ∀ (i : ι) (site : M.InformationSite i)
      (law : FinDist (M.Choice i site.1)), Allowed i site.1 law →
        (assessment.continuationContext site (payoff i) bound).value
            ((assessment.strategy i).withLaw site.1 law) ≤
          (assessment.continuationContext site (payoff i) bound).value (assessment.strategy i))
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (halternative : ∀ info, Allowed who info (alternative info)) :
    (assessment.continuationContext site (payoff who) bound).value alternative ≤
      (assessment.continuationContext site (payoff who) bound).value (assessment.strategy who) := by
  classical
  let spliced := (assessment.strategy who).spliceAfter M alternative site.1
  have hspliced (info : M.InfoState who) : Allowed who info (spliced info) := by
    dsimp [spliced, BehavioralPolicy.spliceAfter]
    split_ifs
    · exact halternative info
    · exact hfeasible who info
  have hcounterfactual (later : M.InformationSite who) :
      M.counterfactualRegret assessment.strategy who later (payoff who) bound
        ((assessment.strategy who).withLaw later.1 (spliced later.1)) ≤ 0 := by
    have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who later
    have hantichain := M.decisionInformationAntichain_of_perfectRecall hrecall who later
    have hle := hlocal who later (spliced later.1) (hspliced later.1)
    rw [assessment.continuationContext_value_eq_bayesContinuationValue M who later
        hantichain hmass (hbayes who later hmass),
      assessment.continuationContext_value_eq_bayesContinuationValue M who later
        hantichain hmass (hbayes who later hmass)] at hle
    apply le_of_not_gt
    intro hpositive
    have hgain := (M.counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall hrecall
      assessment.strategy who later hantichain hmass
      ((assessment.strategy who).withLaw later.1 (spliced later.1)) (payoff who) bound).mp hpositive
    linarith
  have hroot := M.behavioralRootGain_nonpos_of_counterfactualLocalGain_nonpos hrecall
    assessment.strategy who spliced (payoff who) hbound hcounterfactual
  have hcut := M.rootGain_spliceAfter_eq_sum_informationGain hrecall assessment.strategy
    who site alternative (payoff who) hbound
  have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who site
  have hnormalized := assessment.informationMass_mul_continuationGain_eq_sum M who site
    (M.decisionInformationAntichain_of_perfectRecall hrecall who site)
    hmass (hbayes who site hmass) alternative (payoff who) bound
  have hgain : M.informationMass assessment.strategy who site *
      ((assessment.continuationContext site (payoff who) bound).value alternative -
        (assessment.continuationContext site (payoff who) bound).value
          (assessment.strategy who)) ≤ 0 := by
    rw [hnormalized, ← hcut]
    exact sub_nonpos.mpr hroot
  apply sub_nonpos.mp
  nlinarith

end InformationModel

end GameTheory.Protocol
