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

/-- The conditional one-step continuation expectation, extended by zero off
the current root-run support. Its certificate comes from the next-run law. -/
noncomputable def runBehavioralStepContinuation
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) (time : ℕ)
    (hintegrable : PayoffIntegrable (M.runBehavioral strategy (time + 1)) value) :
    E.History → ℝ := by
  classical
  let law := M.runBehavioral strategy time
  let kernel := fun history => M.runBehavioralFrom strategy 1 history
  have hbind : PayoffIntegrable (law.bind kernel) value := by
    simpa only [law, kernel, runBehavioral, M.runBehavioralFrom_add] using hintegrable
  exact extendFromSupport law (fun history hs =>
    expect (kernel history) value
      (payoffIntegrable_bind_conditional_on_support law kernel value hbind history hs))

/-- On root-run support, the continuation helper is the actual conditional
expectation with its guard derived from the next-run law. -/
theorem runBehavioralStepContinuation_eq_on_support
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) (time : ℕ)
    (hintegrable : PayoffIntegrable (M.runBehavioral strategy (time + 1)) value)
    (history : E.History) (hsupport :
      history ∈ (M.runBehavioral strategy time).support) :
    M.runBehavioralStepContinuation strategy value time hintegrable history =
      expect (M.runBehavioralFrom strategy 1 history) value
        (payoffIntegrable_bind_conditional_on_support
          (M.runBehavioral strategy time)
          (M.runBehavioralFrom strategy 1) value
          (by simpa only [runBehavioral, M.runBehavioralFrom_add] using hintegrable)
          history hsupport) := by
  simp [runBehavioralStepContinuation, extendFromSupport, hsupport]

/-- The expected one-step gain, with its conditional and outer guards derived
from the two consecutive root-run laws. -/
noncomputable def runBehavioralStepGain
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) (time : ℕ)
    (hcurrent : PayoffIntegrable (M.runBehavioral strategy time) value)
    (hnext : PayoffIntegrable (M.runBehavioral strategy (time + 1)) value) : ℝ := by
  classical
  let law := M.runBehavioral strategy time
  let kernel := fun history => M.runBehavioralFrom strategy 1 history
  have hbind : PayoffIntegrable (law.bind kernel) value := by
    simpa only [law, kernel, runBehavioral, M.runBehavioralFrom_add] using hnext
  let continuation := M.runBehavioralStepContinuation strategy value time hnext
  have hcontinuation : ∀ history, ∀ hs : history ∈ law.support,
      continuation history = expect (kernel history) value
        (payoffIntegrable_bind_conditional_on_support law kernel value hbind history hs) := by
    intro history hs
    exact M.runBehavioralStepContinuation_eq_on_support strategy value time hnext
      history (by simpa only [law] using hs)
  exact expect law (fun history => continuation history - value history)
    (payoffIntegrable_sub
      (payoffIntegrable_bind_conditionalValue_on_support law kernel value hbind
        continuation hcontinuation)
      hcurrent)

/-- Expected one-step changes telescope along the canonical behavioral run. -/
theorem runBehavioral_expect_sub_eq_sum_stepGains
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) (fuel : ℕ)
    (hintegrable : ∀ time, time ≤ fuel →
      PayoffIntegrable (M.runBehavioral strategy time) value) :
    expect (M.runBehavioral strategy fuel) value (hintegrable fuel le_rfl) -
        value E.initHistory =
      ∑ time : Fin fuel, M.runBehavioralStepGain strategy value time.val
        (hintegrable time.val (Nat.le_of_lt time.isLt))
        (hintegrable (time.val + 1) (Nat.succ_le_of_lt time.isLt)) := by
  induction fuel with
  | zero =>
      have hzero : expect (M.runBehavioral strategy 0) value
          (hintegrable 0 (Nat.zero_le _)) = value E.initHistory := by
        simp only [runBehavioral, runBehavioralFrom, E.runRandomizedFor_zero]
        exact expect_pure _ _ _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [hzero, sub_self]
  | succ fuel ih =>
    have hstep (time : ℕ) (htime : time < fuel + 1) :
        expect (M.runBehavioral strategy (time + 1)) value
            (hintegrable (time + 1) (by omega)) -
          expect (M.runBehavioral strategy time) value (hintegrable time (by omega)) =
        M.runBehavioralStepGain strategy value time
          (hintegrable time (by omega)) (hintegrable (time + 1) (by omega)) := by
      classical
      let law := M.runBehavioral strategy time
      let kernel := fun history => M.runBehavioralFrom strategy 1 history
      let continuation := M.runBehavioralStepContinuation strategy value time
        (hintegrable (time + 1) (by omega))
      have hbindLaw : law.bind kernel = M.runBehavioral strategy (time + 1) := by
        show (M.runBehavioralFrom strategy time E.initHistory).bind
          (M.runBehavioralFrom strategy 1) =
          M.runBehavioralFrom strategy (time + 1) E.initHistory
        exact (M.runBehavioralFrom_add strategy time 1 E.initHistory).symm
      have hbind : PayoffIntegrable (law.bind kernel) value := by
        rw [hbindLaw]
        exact hintegrable (time + 1) (by omega)
      have hcontinuation : ∀ history, ∀ hs : history ∈ law.support,
          continuation history = expect (kernel history) value
            (payoffIntegrable_bind_conditional_on_support law kernel value hbind
              history hs) := by
        intro history hs
        exact M.runBehavioralStepContinuation_eq_on_support strategy value time
          (hintegrable (time + 1) (by omega)) history
          (by simpa only [law] using hs)
      have htower := expect_bind_tower_on_support law kernel value hbind continuation
        hcontinuation
      have hnextEq :
          expect (M.runBehavioral strategy (time + 1)) value
              (hintegrable (time + 1) (by omega)) =
            expect (law.bind kernel) value hbind := by
        exact expect_congr_law hbindLaw.symm value _ hbind
      rw [hnextEq, htower]
      unfold runBehavioralStepGain
      simp only [law, continuation]
      rw [← expect_sub]
    have ih' := ih (fun time htime => hintegrable time (by omega))
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hlast := hstep fuel (by omega)
    linarith [ih', hlast]

/-- A nonterminal history can occur in a root run only at its own trace length. -/
theorem runBehavioral_prob_eq_zero_of_length_ne
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (history : E.History)
    (hterminal : ¬ E.terminal history.state)
    (hlength : history.trace.length ≠ fuel) :
    M.runBehavioral strategy fuel history = 0 := by
  apply (PMF.apply_eq_zero_iff _ _).2
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
    (∑ time ∈ Finset.range bound,
      expect (M.runBehavioral strategy time) value
        (payoffIntegrable_of_finite _ _)) =
      ∑ history : E.History,
        (M.historyReachWeight strategy history).toReal * value history := by
  classical
  simp_rw [expect_eq_sum _ _ (payoffIntegrable_of_finite _ _)]
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
        (Ne.symm htime)]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hlt))

/-- The finite occupation identity, with no synchrony assumption on the
histories being grouped by an information model. -/
theorem runBehavioral_expect_sub_eq_sum_historyStepGains
    [Fintype ι] [Fintype E.History]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (value : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    expect (M.runBehavioral strategy bound) value
        (payoffIntegrable_of_finite _ _) - value E.initHistory =
      ∑ history : E.History,
        (M.historyReachWeight strategy history).toReal *
          (expect (M.runBehavioralFrom strategy 1 history) value
              (payoffIntegrable_of_finite _ _) - value history) := by
  let delta : E.History → ℝ := fun history =>
    expect (M.runBehavioralFrom strategy 1 history) value
      (payoffIntegrable_of_finite _ _) - value history
  have hgain (time : ℕ) :
      M.runBehavioralStepGain strategy value time
          (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _) =
        expect (M.runBehavioral strategy time) delta
          (payoffIntegrable_of_finite _ _) := by
    unfold runBehavioralStepGain
    refine expect_congr_on_support ?_ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    · intro history hs
      dsimp [delta]
      rw [M.runBehavioralStepContinuation_eq_on_support strategy value time
        (payoffIntegrable_of_finite _ _) history hs]
  have hdelta (history : E.History) (hterm : E.terminal history.state) :
      delta history = 0 := by
    dsimp [delta]
    rw [M.runBehavioralFrom_of_terminal strategy 1 hterm, expect_pure]
    simp
  rw [M.runBehavioral_expect_sub_eq_sum_stepGains strategy value bound
    (fun time _ => payoffIntegrable_of_finite _ _)]
  rw [Fin.sum_univ_eq_sum_range (fun time =>
    M.runBehavioralStepGain strategy value time
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)) bound]
  simp_rw [hgain]
  exact M.sum_runBehavioral_expect_eq_sum_historyReach strategy delta hbound hdelta

/-- The supported one-step continuation values of a certified terminal payoff. -/
noncomputable def runBehavioralFromStepContinuation
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (history : E.History)
    (hpayoff : PayoffIntegrable
      (M.runBehavioralFrom strategy bound history) payoff) : E.History → ℝ := by
  classical
  let law := M.runBehavioralFrom strategy 1 history
  let kernel := M.runBehavioralFrom strategy bound
  have hlaw : law.bind kernel = M.runBehavioralFrom strategy bound history := by
    calc
      law.bind kernel = M.runBehavioralFrom strategy (1 + bound) history := by
        exact (M.runBehavioralFrom_add strategy 1 bound history).symm
      _ = M.runBehavioralFrom strategy (bound + 1) history := by
        rw [Nat.add_comm]
      _ = M.runBehavioralFrom strategy bound history :=
        M.runBehavioralFrom_bound_add strategy hbound 1 history
  have hbind : PayoffIntegrable (law.bind kernel) payoff :=
    payoffIntegrable_congr_law hlaw.symm hpayoff
  exact extendFromSupport law (fun next hn =>
    expect (kernel next) payoff
      (payoffIntegrable_bind_conditional_on_support law kernel payoff hbind next hn))

theorem runBehavioralFromStepContinuation_integrable
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (history : E.History)
    (hpayoff : PayoffIntegrable
      (M.runBehavioralFrom strategy bound history) payoff) :
    PayoffIntegrable (M.runBehavioralFrom strategy 1 history)
      (M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff) := by
  classical
  let law := M.runBehavioralFrom strategy 1 history
  let kernel := M.runBehavioralFrom strategy bound
  have hlaw : law.bind kernel = M.runBehavioralFrom strategy bound history := by
    calc
      law.bind kernel = M.runBehavioralFrom strategy (1 + bound) history := by
        exact (M.runBehavioralFrom_add strategy 1 bound history).symm
      _ = M.runBehavioralFrom strategy (bound + 1) history := by
        rw [Nat.add_comm]
      _ = M.runBehavioralFrom strategy bound history :=
        M.runBehavioralFrom_bound_add strategy hbound 1 history
  have hbind : PayoffIntegrable (law.bind kernel) payoff :=
    payoffIntegrable_congr_law hlaw.symm hpayoff
  have hcond : ∀ next, ∀ hn : next ∈ law.support,
      M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff next =
        expect (kernel next) payoff
          (payoffIntegrable_bind_conditional_on_support law kernel payoff hbind next hn) := by
    intro next hn
    simp [runBehavioralFromStepContinuation, extendFromSupport, law, kernel, hn]
  exact payoffIntegrable_bind_conditionalValue_on_support law kernel payoff hbind
    (M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff) hcond

theorem runBehavioralFrom_expect_continuation_eq
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (history : E.History)
    (hpayoff : PayoffIntegrable
      (M.runBehavioralFrom strategy bound history) payoff)
    (houter : PayoffIntegrable (M.runBehavioralFrom strategy 1 history)
      (M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff)) :
    expect (M.runBehavioralFrom strategy 1 history)
        (M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff)
        houter = expect (M.runBehavioralFrom strategy bound history) payoff hpayoff := by
  classical
  let law := M.runBehavioralFrom strategy 1 history
  let kernel := M.runBehavioralFrom strategy bound
  have hlaw : law.bind kernel = M.runBehavioralFrom strategy bound history := by
    calc
      law.bind kernel = M.runBehavioralFrom strategy (1 + bound) history := by
        exact (M.runBehavioralFrom_add strategy 1 bound history).symm
      _ = M.runBehavioralFrom strategy (bound + 1) history := by
        rw [Nat.add_comm]
      _ = M.runBehavioralFrom strategy bound history :=
        M.runBehavioralFrom_bound_add strategy hbound 1 history
  have hbind : PayoffIntegrable (law.bind kernel) payoff :=
    payoffIntegrable_congr_law hlaw.symm hpayoff
  have hcond : ∀ next, ∀ hn : next ∈ law.support,
      M.runBehavioralFromStepContinuation strategy payoff hbound history hpayoff next =
        expect (kernel next) payoff
          (payoffIntegrable_bind_conditional_on_support law kernel payoff hbind next hn) := by
    intro next hn
    simp [runBehavioralFromStepContinuation, extendFromSupport, law, kernel, hn]
  rw [← expect_bind_tower_on_support law kernel payoff hbind _ hcond]
  exact expect_congr_law hlaw payoff hbind hpayoff

/-- Under finite-history integration, the supported conditional continuation
can be replaced by the total expectation function. -/
theorem runBehavioralFrom_expect_raw_continuation_eq
    [Fintype ι] [Fintype E.History]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) (history : E.History) :
    expect (M.runBehavioralFrom strategy 1 history)
      (fun next => expect (M.runBehavioralFrom strategy bound next) payoff
        (payoffIntegrable_of_finite _ _)) (payoffIntegrable_of_finite _ _) =
      expect (M.runBehavioralFrom strategy bound history) payoff
        (payoffIntegrable_of_finite _ _) := by
  let helper := M.runBehavioralFromStepContinuation strategy payoff hbound history
    (payoffIntegrable_of_finite _ _)
  have hhelper : PayoffIntegrable (M.runBehavioralFrom strategy 1 history) helper :=
    M.runBehavioralFromStepContinuation_integrable strategy payoff hbound history
      (payoffIntegrable_of_finite _ _)
  have hpoint (next : E.History)
      (hnext : next ∈ (M.runBehavioralFrom strategy 1 history).support) :
      expect (M.runBehavioralFrom strategy bound next) payoff
        (payoffIntegrable_of_finite _ _) = helper next := by
    simp [helper, runBehavioralFromStepContinuation, extendFromSupport, hnext]
  calc
    expect (M.runBehavioralFrom strategy 1 history)
        (fun next => expect (M.runBehavioralFrom strategy bound next) payoff
          (payoffIntegrable_of_finite _ _)) (payoffIntegrable_of_finite _ _) =
      expect (M.runBehavioralFrom strategy 1 history) helper hhelper :=
        expect_congr_on_support hpoint (payoffIntegrable_of_finite _ _) hhelper
    _ = expect (M.runBehavioralFrom strategy bound history) payoff
        (payoffIntegrable_of_finite _ _) :=
      M.runBehavioralFrom_expect_continuation_eq strategy payoff hbound history
        (payoffIntegrable_of_finite _ _) hhelper

/-- The gain of replacing an entire profile is the alternative profile's
reach-weighted sum of one-step changes in the baseline continuation value. -/
theorem behavioralGain_eq_sum_historyStepGains
    [Fintype ι] [Fintype E.History]
    (baseline alternative : (i : ι) → M.BehavioralPolicy i)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound) :
    expect (M.runBehavioral alternative bound) payoff
        (payoffIntegrable_of_finite _ _) -
      expect (M.runBehavioral baseline bound) payoff
        (payoffIntegrable_of_finite _ _) =
      ∑ history : E.History,
        (M.historyReachWeight alternative history).toReal *
          (expect (M.runBehavioralFrom alternative 1 history)
              (fun next => expect (M.runBehavioralFrom baseline bound next) payoff
                (payoffIntegrable_of_finite _ _))
              (payoffIntegrable_of_finite _ _) -
            expect (M.runBehavioralFrom baseline bound history) payoff
              (payoffIntegrable_of_finite _ _)) := by
  let continuation : E.History → ℝ := fun next =>
    expect (M.runBehavioralFrom baseline bound next) payoff
      (payoffIntegrable_of_finite _ _)
  have hvalue :
      expect (M.runBehavioral alternative bound) continuation
          (payoffIntegrable_of_finite _ _) =
        expect (M.runBehavioral alternative bound) payoff
          (payoffIntegrable_of_finite _ _) := by
    apply expect_congr_on_support
    · intro next hnext
      have hterm := M.runBehavioralFrom_terminal_of_bound alternative hbound
        E.initHistory next hnext
      dsimp only [continuation]
      rw [M.runBehavioralFrom_of_terminal baseline bound hterm, expect_pure]
  have hid := M.runBehavioral_expect_sub_eq_sum_historyStepGains alternative
    continuation hbound
  rw [hvalue] at hid
  exact hid

/-- Installing one local law changes the current draw and then leaves the
baseline continuation unchanged, because perfect recall excludes a revisit. -/
private theorem supported_one_step_eq_extend_early
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (next : E.History) (hnext : next ∈ (M.runBehavioralFrom strategy 1 history).support) :
    ∃ (draw : {joint // E.Legal history.state joint}) (reached : E.State)
      (realized : reached ∈ (E.step history.state draw).support),
      next = history.extend draw.2 realized := by
  rw [M.runBehavioralFrom_succ_of_not_terminal strategy 0 hterm,
    PMF.support_bind] at hnext
  obtain ⟨draw, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
  rw [PMF.support_bindOnSupport] at hnext
  obtain ⟨reached, realized, hnext⟩ := Set.mem_iUnion₂.mp hnext
  refine ⟨draw, reached, realized, ?_⟩
  exact (PMF.mem_support_pure_iff _ _).mp hnext

theorem continuation_withLaw_eq_step_expect
    [Fintype ι] [DecidableEq ι]
    (hrecall : M.PerfectRecall)
    (baseline : (i : ι) → M.BehavioralPolicy i)
    (who : ι) [DecidableEq (M.InfoState who)]
    (alternative : M.BehavioralPolicy who)
    (history : E.History) (hactive : E.active history.state who)
    (payoff : E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound)
    (hpayoff : PayoffIntegrable
      (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) baseline who
          ((baseline who).withLaw (M.infoOf who history.trace)
            (alternative (M.infoOf who history.trace)))) bound history) payoff) :
    ∃ hbind : PayoffIntegrable
      ((M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) baseline who alternative)
            1 history).bind (M.runBehavioralFrom baseline bound)) payoff,
      expect (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) baseline who
            ((baseline who).withLaw (M.infoOf who history.trace)
              (alternative (M.infoOf who history.trace)))) bound history) payoff hpayoff =
        expect ((M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature) baseline who alternative)
              1 history).bind (M.runBehavioralFrom baseline bound)) payoff hbind := by
  by_cases hterm : E.terminal history.state
  · have hlaw :
        M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature) baseline who
              ((baseline who).withLaw (M.infoOf who history.trace)
                (alternative (M.infoOf who history.trace)))) bound history =
          (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) baseline who alternative)
                1 history).bind (M.runBehavioralFrom baseline bound) := by
      simp [M.runBehavioralFrom_of_terminal _ _ hterm]
    refine ⟨payoffIntegrable_congr_law hlaw hpayoff, ?_⟩
    exact expect_congr_law hlaw payoff hpayoff
      (payoffIntegrable_congr_law hlaw hpayoff)
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
  have hone : M.runBehavioralFrom changed 1 history =
      M.runBehavioralFrom other 1 history := by
    rw [M.runBehavioralFrom_succ_of_not_terminal changed 0 hterm,
      M.runBehavioralFrom_succ_of_not_terminal other 0 hterm, hjoint]
    simp [runBehavioralFrom]
  have hsplit : M.runBehavioralFrom changed bound history =
      (M.runBehavioralFrom changed 1 history).bind
        (M.runBehavioralFrom changed bound) := by
    calc
      M.runBehavioralFrom changed bound history =
          M.runBehavioralFrom changed (bound + 1) history :=
        (M.runBehavioralFrom_bound_add changed hbound 1 history).symm
      _ = M.runBehavioralFrom changed (1 + bound) history := by
        rw [Nat.add_comm]
      _ = (M.runBehavioralFrom changed 1 history).bind
          (M.runBehavioralFrom changed bound) :=
        M.runBehavioralFrom_add changed 1 bound history
  have hkernel (next : E.History)
      (hnext : next ∈ (M.runBehavioralFrom changed 1 history).support) :
      M.runBehavioralFrom changed bound next = M.runBehavioralFrom baseline bound next := by
    obtain ⟨draw, state, realized, rfl⟩ :=
      supported_one_step_eq_extend_early M changed history hterm next hnext
    exact hafter draw state realized
  have hlaw : M.runBehavioralFrom changed bound history =
      (M.runBehavioralFrom other 1 history).bind
        (M.runBehavioralFrom baseline bound) := by
    rw [hsplit, hone]
    apply bind_congr_on_support
    intro next hnext
    apply hkernel
    simpa only [hone] using hnext
  refine ⟨payoffIntegrable_congr_law hlaw hpayoff, ?_⟩
  exact expect_congr_law hlaw payoff hpayoff
    (payoffIntegrable_congr_law hlaw hpayoff)

/-- The focal player's own contribution to history reach is nonnegative. -/
theorem playerReachProbability_nonneg
    (strategy : (i : ι) → M.BehavioralPolicy i) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    0 ≤ M.playerReachProbability strategy who trace := by
  induction trace with
  | start => exact zero_le_one
  | extend prior joint isLegal realized ih =>
      exact mul_nonneg ih ENNReal.toReal_nonneg

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
        ((baseline who).withLaw site.1 (alternative site.1))
        (fun _ _ => payoffIntegrable_of_finite _ _)
        (fun _ _ => payoffIntegrable_of_finite _ _) ≤ 0) :
    expect (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) baseline who alternative)
          bound) payoff (payoffIntegrable_of_finite _ _) ≤
      expect (M.runBehavioral baseline bound) payoff (payoffIntegrable_of_finite _ _) := by
  classical
  let changed := Profile.update (sig := M.behavioralSignature) baseline who alternative
  let gain : E.History → ℝ := fun history =>
    expect (M.runBehavioralFrom changed 1 history)
        (fun next => expect (M.runBehavioralFrom baseline bound next) payoff
          (payoffIntegrable_of_finite _ _)) (payoffIntegrable_of_finite _ _) -
      expect (M.runBehavioralFrom baseline bound history) payoff
        (payoffIntegrable_of_finite _ _)
  have hterminal (history : E.History) (hterm : E.terminal history.state) :
      gain history = 0 := by
    dsimp [gain]
    have hchanged := M.runBehavioralFrom_of_terminal changed 1 hterm
    have hbase := M.runBehavioralFrom_of_terminal baseline bound hterm
    rw [hchanged, expect_pure, hbase, expect_pure]
    ring
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
    rw [hone]
    rw [M.runBehavioralFrom_expect_raw_continuation_eq baseline payoff hbound history]
    ring
  have hnonpos (info : M.InfoState who) :
      (∑ history : M.InformationHistory who info,
        (M.historyReachWeight changed history.1).toReal * gain history.1) ≤ 0 := by
    by_cases hsite : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info
    · let site : M.InformationSite who := ⟨info, hsite⟩
      have hgain (history : M.InformationHistory who info) :
          gain history.1 =
            expect (M.runBehavioralFrom
                (Profile.update (sig := M.behavioralSignature) baseline who
                  ((baseline who).withLaw info (alternative info)))
                  bound history.1) payoff (payoffIntegrable_of_finite _ _) -
              expect (M.runBehavioralFrom baseline bound history.1) payoff
                (payoffIntegrable_of_finite _ _) := by
        have heq := M.continuation_withLaw_eq_step_expect hrecall baseline who
          alternative history.1 (InformationSite.active M site history) payoff hbound
          (payoffIntegrable_of_finite _ _)
        rw [history.2] at heq
        have htower := expect_bind_tower
          (M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature) baseline who alternative)
            1 history.1)
          (M.runBehavioralFrom baseline bound) payoff
          (payoffIntegrable_of_finite _ _)
          (fun _ => payoffIntegrable_of_finite _ _)
        have hfirst :
            expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) baseline who alternative)
              1 history.1)
              (fun next => expect (M.runBehavioralFrom baseline bound next) payoff
                (payoffIntegrable_of_finite _ _)) (payoffIntegrable_of_finite _ _) =
            expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) baseline who
                ((baseline who).withLaw info (alternative info))) bound history.1)
              payoff (payoffIntegrable_of_finite _ _) := by
          rw [← htower]
          exact heq.2.symm
        exact congrArg (fun x => x -
          expect (M.runBehavioralFrom baseline bound history.1) payoff
            (payoffIntegrable_of_finite _ _)) hfirst
      let reach := M.playerReachProbability changed who site.2.choose.1.trace
      have hfactor (history : M.InformationHistory who info) :
          (M.historyReachWeight changed history.1).toReal =
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
            (M.historyReachWeight changed history.1).toReal * gain history.1) =
          reach * M.counterfactualRegret baseline who site payoff bound
            ((baseline who).withLaw info (alternative info))
            (fun history hreach => payoffIntegrable_of_finite _ _)
            (fun history hreach => payoffIntegrable_of_finite _ _) := by
        unfold counterfactualRegret counterfactualContinuationValue
          behavioralContinuationValue
        rw [Profile.update_eq_self, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro history _
        rw [hfactor, hgain]
        by_cases hcf :
            M.counterfactualReachProbability baseline who history.1.trace = 0
        · simp [hcf]
        · simp [hcf]
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
    (M.historyReachWeight changed history).toReal * gain history) ≤ 0
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
    PMF.support_bind] at hnext
  obtain ⟨draw, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
  rw [PMF.support_bindOnSupport] at hnext
  obtain ⟨reached, realized, hnext⟩ := Set.mem_iUnion₂.mp hnext
  refine ⟨draw, reached, realized, ?_⟩
  exact (PMF.mem_support_pure_iff _ _).mp hnext

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
    expect (M.runBehavioral
        (Profile.update (sig := M.behavioralSignature) baseline who
          ((baseline who).spliceAfter M alternative site.1)) bound)
      payoff (payoffIntegrable_of_finite _ _) -
        expect (M.runBehavioral baseline bound) payoff (payoffIntegrable_of_finite _ _) =
      ∑ history : M.InformationHistory who site.1,
        (M.historyReachWeight baseline history.1).toReal *
          (expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) baseline who alternative)
                bound history.1) payoff (payoffIntegrable_of_finite _ _) -
            expect (M.runBehavioralFrom baseline bound history.1) payoff
              (payoffIntegrable_of_finite _ _)) := by
  classical
  let changed := Profile.update (sig := M.behavioralSignature) baseline who
    ((baseline who).spliceAfter M alternative site.1)
  let difference : E.History → ℝ := fun history =>
    expect (M.runBehavioralFrom changed bound history) payoff
        (payoffIntegrable_of_finite _ _) -
      expect (M.runBehavioralFrom baseline bound history) payoff
        (payoffIntegrable_of_finite _ _)
  let stopped : E.History → ℝ := fun history =>
    if site.1 ∈ M.actedAt who history.trace then 0 else difference history
  have hterminal (history : E.History) (hterm : E.terminal history.state) :
      difference history = 0 := by
    dsimp [difference]
    have hchanged := M.runBehavioralFrom_of_terminal changed bound hterm
    have hbase := M.runBehavioralFrom_of_terminal baseline bound hterm
    rw [hchanged, hbase]
    ring
  have hstoppedTerminal (history : E.History) (hterm : E.terminal history.state) :
      stopped history = 0 := by
    simp [stopped, hterminal history hterm]
  have hresidual (history : E.History) :
      expect (M.runBehavioralFrom baseline 1 history) stopped
        (payoffIntegrable_of_finite _ _) - stopped history =
        if M.infoOf who history.trace = site.1 then -difference history else 0 := by
    by_cases hterm : E.terminal history.state
    · have hrun := M.runBehavioralFrom_of_terminal baseline 1 hterm
      rw [hrun, expect_pure, hterminal history hterm]
      simp
    by_cases hpast : site.1 ∈ M.actedAt who history.trace
    · have hinfo : M.infoOf who history.trace ≠ site.1 := by
        intro heq
        have hnot := M.infoOf_not_mem_actedAt_of_perfectRecall hrecall baseline who
          history hterm (InformationSite.active M site ⟨history, heq⟩)
        rw [heq] at hnot
        exact hnot hpast
      have hnext : expect (M.runBehavioralFrom baseline 1 history) stopped
          (payoffIntegrable_of_finite _ _) = 0 := by
        rw [← expect_constant (M.runBehavioralFrom baseline 1 history) 0
          (payoffIntegrable_of_finite _ _)]
        apply expect_congr_on_support
        · intro next hnext
          have hreach := E.runRandomizedFor_reachesWithin
            (M.randomizedChooser baseline) 1 history next hnext
          exact ite_eq_left ((M.actedAt_isSuffix_of_reachesWithin who hreach).subset hpast)
      rw [hnext, show stopped history = 0 from ite_eq_left hpast, ite_eq_right hinfo, sub_self]
    · by_cases hinfo : M.infoOf who history.trace = site.1
      · have hnext : expect (M.runBehavioralFrom baseline 1 history) stopped
            (payoffIntegrable_of_finite _ _) = 0 := by
          rw [← expect_constant (M.runBehavioralFrom baseline 1 history) 0
            (payoffIntegrable_of_finite _ _)]
          apply expect_congr_on_support
          · intro next hnext
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
        have hnext : expect (M.runBehavioralFrom baseline 1 history) stopped
              (payoffIntegrable_of_finite _ _) =
            expect (M.runBehavioralFrom baseline 1 history) difference
              (payoffIntegrable_of_finite _ _) := by
          apply expect_congr_on_support
          · intro next hnext
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
        have hdecomp := expect_sub
          (μ := M.runBehavioralFrom baseline 1 history)
          (f := fun next => expect (M.runBehavioralFrom changed bound next) payoff
            (payoffIntegrable_of_finite _ _))
          (g := fun next => expect (M.runBehavioralFrom baseline bound next) payoff
            (payoffIntegrable_of_finite _ _))
          (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
        rw [hdecomp]
        have hfirst := expect_congr_law hone
          (fun next => expect (M.runBehavioralFrom changed bound next) payoff
            (payoffIntegrable_of_finite _ _))
          (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
        rw [← hfirst,
          M.runBehavioralFrom_expect_raw_continuation_eq changed payoff hbound history,
          M.runBehavioralFrom_expect_raw_continuation_eq baseline payoff hbound history]
        ring
  have hsum :
      (∑ history : E.History,
        if M.infoOf who history.trace = site.1 then
          (M.historyReachWeight baseline history).toReal * difference history else 0) =
        ∑ history : M.InformationHistory who site.1,
          (M.historyReachWeight baseline history.1).toReal * difference history.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp)
      (fun history => (M.historyReachWeight baseline history).toReal * difference history)
  have hid := M.runBehavioral_expect_sub_eq_sum_historyStepGains baseline stopped hbound
  have hend : expect (M.runBehavioral baseline bound) stopped
      (payoffIntegrable_of_finite _ _) = 0 := by
    rw [← expect_constant (M.runBehavioral baseline bound) 0
      (payoffIntegrable_of_finite _ _)]
    apply expect_congr_on_support
    · intro history hhistory
      exact hstoppedTerminal history
        (M.runBehavioralFrom_terminal_of_bound baseline hbound E.initHistory history hhistory)
  have hstart : stopped E.initHistory = difference E.initHistory := by
    simp [stopped, ExecutionProtocol.initHistory, InfoSignals.actedAt]
  have hscores :
      (∑ history : E.History,
        (M.historyReachWeight baseline history).toReal *
          (expect (M.runBehavioralFrom baseline 1 history) stopped
            (payoffIntegrable_of_finite _ _) - stopped history)) =
        -(∑ history : M.InformationHistory who site.1,
          (M.historyReachWeight baseline history.1).toReal * difference history.1) := by
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
theorem BehavioralAssessment.continuationContext_integrable_iff_bayesContinuation
    [Fintype ι] [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass assessment.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt (M := M) assessment who site
      hantichain hmass)
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ) :
    (assessment.continuationContext site payoff fuel).IntegrableAt alternative ↔
      (Context.ofBelief
        (M.bayesBelief assessment.strategy who site hantichain hmass)
        (fun history _alternative => M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who _alternative)
          fuel history.1) payoff).IntegrableAt alternative := by
  have hbelief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site hantichain hmass := by
    apply PMF.ext
    intro history
    exact (hbayes history).trans
      (M.bayesBelief_apply assessment.strategy who site hantichain hmass history).symm
  have hlaw :
      (assessment.belief who site).bind (fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
          fuel history.1) =
      (M.bayesBelief assessment.strategy who site hantichain hmass).bind (fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
          fuel history.1) := by
    rw [hbelief]
  constructor
  · intro hctx
    exact payoffIntegrable_congr_law hlaw hctx
  · intro hctx
    exact payoffIntegrable_congr_law hlaw.symm hctx

theorem BehavioralAssessment.continuationContext_value_eq_bayesContinuationValue
    [Fintype ι] [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    (hantichain : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass assessment.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt (M := M) assessment who site
      hantichain hmass)
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ)
    (hctx : (assessment.continuationContext site payoff fuel).IntegrableAt alternative)
    :
    (assessment.continuationContext site payoff fuel).value alternative hctx =
      M.bayesContinuationValue assessment.strategy who site hantichain hmass
        alternative payoff fuel
          (assessment.continuationContext_integrable_iff_bayesContinuation M who site
            hantichain hmass hbayes alternative payoff fuel |>.mp hctx) := by
  have hbelief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site hantichain hmass := by
    apply PMF.ext
    intro history
    exact (hbayes history).trans
      (M.bayesBelief_apply assessment.strategy who site hantichain hmass history).symm
  have hlaw :
      (assessment.belief who site).bind (fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
          fuel history.1) =
      (M.bayesBelief assessment.strategy who site hantichain hmass).bind (fun history =>
        M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
          fuel history.1) := by
    rw [hbelief]
  rw [BehavioralAssessment.continuationContext_value]
  unfold bayesContinuationValue
  exact expect_congr_law hlaw payoff hctx
    ((assessment.continuationContext_integrable_iff_bayesContinuation M who site
      hantichain hmass hbayes alternative payoff fuel).mp hctx)

/-- Conditional payoff guards on a finite information fiber imply the
corresponding whole continuation-context guard. -/
theorem BehavioralAssessment.continuationContext_integrable_of_conditional
    [Fintype ι] [DecidableEq ι]
    (assessment : M.BehavioralAssessment)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ)
    (hcond : ∀ history : M.InformationHistory who site.1,
      PayoffIntegrable (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
        fuel history.1) payoff) :
    (assessment.continuationContext site payoff fuel).IntegrableAt alternative := by
  let belief := assessment.belief who site
  let kernel := fun history : M.InformationHistory who site.1 =>
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
      fuel history.1
  exact payoffIntegrable_bind_of_finite_support belief kernel payoff (Set.toFinite _)
    (fun history _ => hcond history)

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
    (alternative : M.BehavioralPolicy who) (payoff : E.History → ℝ) (fuel : ℕ)
    (hcondAlt : ∀ history : M.InformationHistory who site.1,
      PayoffIntegrable (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
        fuel history.1) payoff)
    (hcondBase : ∀ history : M.InformationHistory who site.1,
      PayoffIntegrable (M.runBehavioralFrom
        (Profile.update (sig := M.behavioralSignature) assessment.strategy who
          (assessment.strategy who)) fuel history.1) payoff) :
    (M.informationMass assessment.strategy who site).toReal *
        ((assessment.continuationContext site payoff fuel).value alternative
            (assessment.continuationContext_integrable_of_conditional M who site
              alternative payoff fuel hcondAlt) -
          (assessment.continuationContext site payoff fuel).value
            (assessment.strategy who)
            (assessment.continuationContext_integrable_of_conditional M who site
              (assessment.strategy who) payoff fuel hcondBase)) =
      ∑ history : M.InformationHistory who site.1,
        (M.historyReachWeight assessment.strategy history.1).toReal *
          (expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
                fuel history.1) payoff (hcondAlt history) -
            expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) assessment.strategy who
                (assessment.strategy who)) fuel history.1) payoff (hcondBase history)) := by
  let belief := assessment.belief who site
  let altKernel := fun history : M.InformationHistory who site.1 =>
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative)
      fuel history.1
  let baseKernel := fun history : M.InformationHistory who site.1 =>
    M.runBehavioralFrom
      (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        (assessment.strategy who)) fuel history.1
  have halt := assessment.continuationContext_integrable_of_conditional M who site
    alternative payoff fuel hcondAlt
  have hbase := assessment.continuationContext_integrable_of_conditional M who site
    (assessment.strategy who) payoff fuel hcondBase
  have hvalAlt : (assessment.continuationContext site payoff fuel).value alternative halt =
      ∑ history : M.InformationHistory who site.1,
        (belief history).toReal * expect (altKernel history) payoff
          (hcondAlt history) := by
    calc
      _ = expect (belief.bind altKernel) payoff halt :=
        BehavioralAssessment.continuationContext_value assessment site payoff fuel
          alternative halt
      _ = expect belief (fun history => expect (altKernel history) payoff
          (hcondAlt history))
          (payoffIntegrable_bind_conditionalExpectation belief altKernel payoff halt
            hcondAlt) :=
        expect_bind_tower belief altKernel payoff halt
          hcondAlt
      _ = ∑ history : M.InformationHistory who site.1,
          (belief history).toReal * expect (altKernel history) payoff
            (hcondAlt history) :=
        expect_eq_sum belief _ _
  have hvalBase : (assessment.continuationContext site payoff fuel).value
        (assessment.strategy who) hbase =
      ∑ history : M.InformationHistory who site.1,
        (belief history).toReal * expect (baseKernel history) payoff
          (hcondBase history) := by
    calc
      _ = expect (belief.bind baseKernel) payoff hbase :=
        BehavioralAssessment.continuationContext_value assessment site payoff fuel
          (assessment.strategy who) hbase
      _ = expect belief (fun history => expect (baseKernel history) payoff
          (hcondBase history))
          (payoffIntegrable_bind_conditionalExpectation belief baseKernel payoff hbase
            hcondBase) :=
        expect_bind_tower belief baseKernel payoff hbase
          hcondBase
      _ = ∑ history : M.InformationHistory who site.1,
          (belief history).toReal * expect (baseKernel history) payoff
            (hcondBase history) :=
        expect_eq_sum belief _ _
  rw [hvalAlt, hvalBase, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  have hmassRealPos : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos (ne_of_gt hmass) (ne_of_lt
      (lt_of_le_of_lt
        (M.informationMass_le_one assessment.strategy who site hantichain)
        ENNReal.one_lt_top))
  apply Finset.sum_congr rfl
  intro history _
  have hbelief : belief history = M.bayesBelief assessment.strategy who site
      hantichain hmass history := by
    dsimp [belief]
    exact (hbayes history).trans
      (M.bayesBelief_apply assessment.strategy who site hantichain hmass history).symm
  have hnormalized : (M.informationMass assessment.strategy who site).toReal *
      (belief history).toReal = (M.historyReachWeight assessment.strategy history.1).toReal := by
    rw [hbelief, M.bayesBelief_apply assessment.strategy who site hantichain hmass,
      ENNReal.toReal_div]
    exact mul_div_cancel₀ _ (ne_of_gt hmassRealPos)
  calc
    (M.informationMass assessment.strategy who site).toReal *
        ((belief history).toReal * expect (altKernel history) payoff (hcondAlt history)) -
      (M.informationMass assessment.strategy who site).toReal *
        ((belief history).toReal * expect (baseKernel history) payoff (hcondBase history)) =
        ((M.informationMass assessment.strategy who site).toReal *
            (belief history).toReal) * expect (altKernel history) payoff (hcondAlt history) -
          ((M.informationMass assessment.strategy who site).toReal *
            (belief history).toReal) * expect (baseKernel history) payoff (hcondBase history) := by
      rw [← mul_assoc, ← mul_assoc]
    _ = (M.historyReachWeight assessment.strategy history.1).toReal *
          (expect (altKernel history) payoff (hcondAlt history) -
            expect (baseKernel history) payoff (hcondBase history)) := by
      rw [hnormalized, ← mul_sub]

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
    (Allowed : (i : ι) → (info : M.InfoState i) → PMF (M.Choice i info) → Prop)
    (hfeasible : ∀ i info, Allowed i info (assessment.strategy i info))
    (payoff : ι → E.History → ℝ) {bound : ℕ}
    (hbound : E.BoundedHorizon bound)
    (hlocal : ∀ (i : ι) (site : M.InformationSite i)
      (law : PMF (M.Choice i site.1)), Allowed i site.1 law →
        (assessment.continuationContext site (payoff i) bound).value
            ((assessment.strategy i).withLaw site.1 law) (payoffIntegrable_of_finite _ _) ≤
          (assessment.continuationContext site (payoff i) bound).value
            (assessment.strategy i) (payoffIntegrable_of_finite _ _))
    (who : ι) (site : M.InformationSite who)
    (alternative : M.BehavioralPolicy who)
    (halternative : ∀ info, Allowed who info (alternative info)) :
    (assessment.continuationContext site (payoff who) bound).value alternative
      (payoffIntegrable_of_finite _ _) ≤
      (assessment.continuationContext site (payoff who) bound).value
        (assessment.strategy who) (payoffIntegrable_of_finite _ _) := by
  classical
  let spliced := (assessment.strategy who).spliceAfter M alternative site.1
  have hspliced (info : M.InfoState who) : Allowed who info (spliced info) := by
    dsimp [spliced, BehavioralPolicy.spliceAfter]
    split_ifs
    · exact halternative info
    · exact hfeasible who info
  have hcounterfactual (later : M.InformationSite who) :
      M.counterfactualRegret assessment.strategy who later (payoff who) bound
        ((assessment.strategy who).withLaw later.1 (spliced later.1))
        (fun _ _ => payoffIntegrable_of_finite _ _)
        (fun _ _ => payoffIntegrable_of_finite _ _) ≤ 0 := by
    have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who later
    have hantichain := M.decisionInformationAntichain_of_perfectRecall hrecall who later
    have hle := hlocal who later (spliced later.1) (hspliced later.1)
    have hguardAlt : (assessment.continuationContext later (payoff who) bound).IntegrableAt
        ((assessment.strategy who).withLaw later.1 (spliced later.1)) :=
      payoffIntegrable_of_finite _ _
    have hguardBase : (assessment.continuationContext later (payoff who) bound).IntegrableAt
        (assessment.strategy who) := payoffIntegrable_of_finite _ _
    rw [assessment.continuationContext_value_eq_bayesContinuationValue M who later
        hantichain hmass (hbayes who later hmass)
        ((assessment.strategy who).withLaw later.1 (spliced later.1)) (payoff who) bound
        hguardAlt,
      assessment.continuationContext_value_eq_bayesContinuationValue M who later
        hantichain hmass (hbayes who later hmass) (assessment.strategy who) (payoff who)
        bound hguardBase] at hle
    apply le_of_not_gt
    intro hpositive
    have hgain := (M.counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall hrecall
      assessment.strategy who later hantichain hmass
      ((assessment.strategy who).withLaw later.1 (spliced later.1)) (payoff who) bound
      (fun _ _ => payoffIntegrable_of_finite _ _)
      (fun _ _ => payoffIntegrable_of_finite _ _)).mp hpositive
    linarith
  have hroot := M.behavioralRootGain_nonpos_of_counterfactualLocalGain_nonpos hrecall
    assessment.strategy who spliced (payoff who) hbound hcounterfactual
  have hcut := M.rootGain_spliceAfter_eq_sum_informationGain hrecall assessment.strategy
    who site alternative (payoff who) hbound
  have hmass := M.informationMass_pos_of_fullSupport assessment.strategy hfull who site
  have hnormalized := assessment.informationMass_mul_continuationGain_eq_sum M who site
    (M.decisionInformationAntichain_of_perfectRecall hrecall who site)
    hmass (hbayes who site hmass) alternative (payoff who) bound
    (fun _ => payoffIntegrable_of_finite _ _)
    (fun _ => payoffIntegrable_of_finite _ _)
  have hgain : (M.informationMass assessment.strategy who site).toReal *
      ((assessment.continuationContext site (payoff who) bound).value alternative
          (payoffIntegrable_of_finite _ _) -
        (assessment.continuationContext site (payoff who) bound).value
          (assessment.strategy who) (payoffIntegrable_of_finite _ _)) ≤ 0 := by
    rw [hnormalized]
    simp only [Profile.update_eq_self]
    rw [← hcut]
    exact sub_nonpos.mpr hroot
  have hmassRealPos : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos (ne_of_gt hmass) (ne_of_lt
      (lt_of_le_of_lt
        (M.informationMass_le_one assessment.strategy who site
          (M.decisionInformationAntichain_of_perfectRecall hrecall who site))
        ENNReal.one_lt_top))
  apply le_of_not_gt
  intro hpositive
  have hpositiveDiff : 0 <
      (assessment.continuationContext site (payoff who) bound).value alternative
          (payoffIntegrable_of_finite _ _) -
        (assessment.continuationContext site (payoff who) bound).value
          (assessment.strategy who) (payoffIntegrable_of_finite _ _) :=
    sub_pos.mpr hpositive
  have hmulPositive := mul_pos hmassRealPos hpositiveDiff
  linarith

end InformationModel

end GameTheory.Protocol
