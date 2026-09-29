/-
# Expected payoffs under public monitoring

`signalHistoryLaw` gives a PMF at every finite horizon. This module first
integrates each reachable history's stage outcome law, then integrates the
resulting values under the actual history law. These two guards are separate:
conditional integration alone does not imply integration of a joint outcome
law. No law on infinite paths is constructed.
-/

import GameTheory.Repeated.MonitoringContinuation

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- Stage payoff at a public history. -/
def monitoredStageValue (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι)
    (history : M.SignalHistory t) : ℝ :=
  G.stagePayoff (fun i => profile i t history) who

/-- Exactly the two integrations used by one monitored stage: conditional
stage outcomes at supported histories, and those values under the actual
history law. -/
structure MonitoredStageIntegrable (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι) : Prop where
  conditional : ∀ history ∈ (M.signalHistoryLaw profile t).support,
    UtilityIntegrable G.utility who
      (G.form.play (fun i => profile i t history))
  history : PayoffIntegrable (M.signalHistoryLaw profile t)
    (M.monitoredStageValue profile t who)

/-- Expected stage payoff at time `t`, integrating the stage values under the
actual public-history law. -/
def monitoredStagePayoff (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι) : ℝ :=
  expect (M.signalHistoryLaw profile t)
    (M.monitoredStageValue profile t who)

/-- At time zero there is only the empty public history. -/
@[simp]
theorem monitoredStagePayoff_zero (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (who : ι) :
    M.monitoredStagePayoff profile 0 who =
      G.stagePayoff (fun i => profile i 0 (fun k => k.elim0)) who := by
  simp only [monitoredStagePayoff, signalHistoryLaw_zero]
  rw [expect_pure]
  rfl

/-- A finite public-history law through time `t` depends only on prescribed
actions strictly before `t`. -/
theorem signalHistoryLaw_congr_before
    (M : G.PublicMonitoring) (first second : M.MonitoredProfile) (t : ℕ)
    (h : ∀ s, s < t → ∀ history i,
      first i s history = second i s history) :
    M.signalHistoryLaw first t = M.signalHistoryLaw second t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [signalHistoryLaw_succ, signalHistoryLaw_succ]
      rw [ih (fun s hs => h s (by omega))]
      congr 1
      funext history
      have hprofile :
          (fun i => first i t history) = (fun i => second i t history) := by
        funext i
        exact h t (by omega) history i
      rw [hprofile]

/-- A supported continuation history extends to a supported full history
after any supported first signal. -/
theorem afterSignal_history_mem_support
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (signal : M.Signal)
    (hsignal : signal ∈
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support)
    (history : M.SignalHistory n)
    (hhistory : history ∈
      (M.signalHistoryLaw (M.afterSignal profile signal) n).support) :
    Fin.cons signal history ∈
      (M.signalHistoryLaw profile (n + 1)).support := by
  rw [M.signalHistoryLaw_succ_eq_bind_first profile n]
  apply (PMF.mem_support_bind_iff _ _ _).2
  refine ⟨signal, hsignal, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).2
  exact ⟨history, hhistory, rfl⟩

/-- Full-history conditional integrability restricts to every supported
first-signal continuation. -/
theorem afterSignal_stage_integrable
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (hstage : ∀ history ∈
      (M.signalHistoryLaw profile (n + 1)).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i (n + 1) history)))
    (signal : M.Signal)
    (hsignal : signal ∈
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support) :
    ∀ history ∈
      (M.signalHistoryLaw (M.afterSignal profile signal) n).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i =>
          M.afterSignal profile signal i n history)) := by
  intro history hhistory
  exact hstage (Fin.cons signal history)
    (M.afterSignal_history_mem_support profile n
      signal hsignal history hhistory)

/-- The whole public-history expectation guard supplies the actual outer
history-law guard in a supported first-signal continuation. -/
theorem afterSignal_outer_integrable
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (houter : PayoffIntegrable (M.signalHistoryLaw profile (n + 1))
      (M.monitoredStageValue profile (n + 1) who))
    (signal : M.Signal)
    (hsignal : signal ∈
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support) :
    PayoffIntegrable
      (M.signalHistoryLaw (M.afterSignal profile signal) n)
      (M.monitoredStageValue (M.afterSignal profile signal) n who) := by
  let firstLaw := M.signalLaw (fun i => profile i 0 (fun k => k.elim0))
  let kernel : M.Signal → PMF (M.SignalHistory (n + 1)) := fun signal =>
    (M.signalHistoryLaw (M.afterSignal profile signal) n).map (Fin.cons signal)
  have hbind : PayoffIntegrable (firstLaw.bind kernel)
      (M.monitoredStageValue profile (n + 1) who) := by
    rw [← M.signalHistoryLaw_succ_eq_bind_first profile n]
    exact houter
  have hmap := (payoffIntegrable_map_iff (Fin.cons (α := fun _ => M.Signal) signal) _ _).mp
    (payoffIntegrable_bind_conditional_on_support firstLaw kernel _ hbind signal hsignal)
  exact payoffIntegrable_congr_on_support (fun _ _ => rfl) hmap

/-- Restrict the two actual integrations to a supported first-signal
continuation. -/
theorem MonitoredStageIntegrable.afterSignal
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who)
    (signal : M.Signal)
    (hsignal : signal ∈
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support) :
    M.MonitoredStageIntegrable
      (M.afterSignal profile signal) n who :=
  ⟨M.afterSignal_stage_integrable profile n who h.conditional signal hsignal,
    M.afterSignal_outer_integrable profile n who h.history signal hsignal⟩

/-- The expected stage payoff after the first public signal. -/
def firstSignalContinuationValue
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι) : M.Signal → ℝ :=
  fun signal => M.monitoredStagePayoff (M.afterSignal profile signal) n who

/-- Each first-signal continuation value is the stage value integrated over the
histories that begin with that signal. -/
private theorem firstSignalContinuationValue_eq_expect_kernel
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι) (signal : M.Signal) :
    M.firstSignalContinuationValue profile n who signal =
      expect ((M.signalHistoryLaw (M.afterSignal profile signal) n).map
          (Fin.cons signal))
        (M.monitoredStageValue profile (n + 1) who) := by
  unfold firstSignalContinuationValue monitoredStagePayoff
  rw [expect_map]
  exact expect_congr_on_support (fun _ _ => rfl)

/-- The first-signal continuation value is integrable under its actual signal
law whenever the whole history-law stage value is integrable. -/
theorem firstSignalContinuationValue_integrable
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who) :
    PayoffIntegrable
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
      (M.firstSignalContinuationValue profile n who) := by
  have hbind := h.history
  rw [M.signalHistoryLaw_succ_eq_bind_first profile n] at hbind
  exact payoffIntegrable_bind_conditionalValue_on_support _ _ _ hbind _
    (fun signal _ => M.firstSignalContinuationValue_eq_expect_kernel profile n who signal)

/-- The monitored stage value obeys the first-signal tower. -/
theorem monitoredStagePayoff_succ_eq_expect_afterSignal
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who) :
    M.monitoredStagePayoff profile (n + 1) who =
      expect (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
        (M.firstSignalContinuationValue profile n who) := by
  have hbind := h.history
  rw [M.signalHistoryLaw_succ_eq_bind_first profile n] at hbind
  unfold monitoredStagePayoff
  rw [M.signalHistoryLaw_succ_eq_bind_first profile n]
  exact expect_bind_tower_on_support _ _ _ hbind _
    (fun signal _ => M.firstSignalContinuationValue_eq_expect_kernel profile n who signal)

/-- Expected stage payoff at time `t` depends only on prescribed play through
time `t`. -/
theorem monitoredStagePayoff_congr_before_succ
    (M : G.PublicMonitoring) (first second : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : ∀ s, s < t + 1 → ∀ history i,
      first i s history = second i s history) :
    M.monitoredStagePayoff first t who =
      M.monitoredStagePayoff second t who := by
  have hlaw := M.signalHistoryLaw_congr_before first second t
    (fun s hs => h s (by omega))
  let f := (M.monitoredStageValue first t who)
  let g := (M.monitoredStageValue second t who)
  have hvalues : ∀ history ∈ (M.signalHistoryLaw first t).support,
      f history = g history := by
    intro history hreach
    have hstageEq : (fun i => first i t history) =
        (fun i => second i t history) := by
      funext i
      exact h t (by omega) history i
    simp only [f, g, monitoredStageValue, stagePayoff]
    exact expectedUtility_congr_law G.utility who
      (congrArg G.form.play hstageEq)
  have hvaluesSecond : ∀ history ∈ (M.signalHistoryLaw second t).support,
      f history = g history := by
    intro history hreach
    exact hvalues history (by simpa [hlaw] using hreach)
  unfold monitoredStagePayoff
  exact (expect_congr_law hlaw f).trans
    (expect_congr_on_support hvaluesSecond)

/-- Before its cutoff, a truncated unilateral deviation induces the same
expected stage payoff as the full deviation. -/
theorem monitoredStagePayoff_update_truncatedDeviation_eq_of_lt
    (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι)
    (deviation : M.MonitoredStrategy who) {t count : ℕ}
    (ht : t < count) :
    M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count))
        t who =
      M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who deviation)
        t who := by
  refine M.monitoredStagePayoff_congr_before_succ
    _ _ t who ?_
  intro s hs history i
  have hsCount : s < count := by omega
  by_cases hi : i = who
  · subst hi
    simp [truncatedDeviation, hsCount]
  · simp [Profile.update_of_ne _ _ hi]

/-- A pointwise upper bound on every realized stage profile bounds the
monitored expected stage payoff. -/
theorem monitoredStagePayoff_le_const
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : M.MonitoredStageIntegrable profile t who)
    {bound : ℝ}
    (hle : ∀ history, history ∈ (M.signalHistoryLaw profile t).support →
      G.stagePayoff (fun i => profile i t history) who
         ≤ bound) :
    M.monitoredStagePayoff profile t who ≤ bound := by
  exact expect_le_const _ _ h.history bound (by
    intro history hreach
    simpa [monitoredStageValue] using hle history hreach)

/-- A uniform absolute stage-payoff bound also bounds each monitored expected
stage payoff. -/
theorem abs_monitoredStagePayoff_le
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : M.MonitoredStageIntegrable profile t who)
    {bound : ℝ}
    (hbound : ∀ history, history ∈ (M.signalHistoryLaw profile t).support →
      |G.stagePayoff (fun i => profile i t history) who| ≤ bound) :
    |M.monitoredStagePayoff profile t who| ≤ bound := by
  apply abs_le.mpr
  constructor
  · have hconst := payoffIntegrable_constant
      (M.signalHistoryLaw profile t) (-bound)
    have h := expect_mono (μ := M.signalHistoryLaw profile t)
      (f := fun _ => -bound)
      (g := (M.monitoredStageValue profile t who))
      (fun history hreach => by
        simpa [monitoredStageValue] using (abs_le.mp (hbound history hreach)).1)
      hconst h.history
    simpa [monitoredStagePayoff, expect_constant] using h
  · exact M.monitoredStagePayoff_le_const profile t who h
      (fun history hreach => (abs_le.mp (hbound history hreach)).2)

/-- A global stage-outcome integration certificate and a bound on expected
stage values supply the two actual integrations for any monitored stage. The
realized utility itself need not be bounded. -/
theorem monitoredStageIntegrable_of_expected_bound
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (hG : G.form.HasIntegrableUtility G.utility)
    {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    M.MonitoredStageIntegrable profile t who := by
  let hconditional : ∀ history ∈
      (M.signalHistoryLaw profile t).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i t history)) :=
    fun history _ => hG who (fun i => profile i t history)
  refine ⟨hconditional, ?_⟩
  apply payoffIntegrable_of_bounded_on_support
  intro history hreach
  simpa [monitoredStageValue] using hbound (fun i => profile i t history)

/-- Stationary monitored play has the fixed stage profile's payoff at every
time, independently of the signal law. -/
@[simp]
theorem monitoredStagePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (profile : Profile G.form.sig)
    (t : ℕ) (who : ι) :
    M.monitoredStagePayoff
        (M.stationaryMonitoredProfile profile) t who =
      G.stagePayoff profile who := by
  unfold monitoredStagePayoff
  let law := M.signalHistoryLaw (M.stationaryMonitoredProfile profile) t
  have heq : ∀ history ∈ law.support,
      (M.monitoredStageValue (M.stationaryMonitoredProfile profile)
          t who) history = G.stagePayoff profile who := by
    intro history _
    simp [monitoredStageValue, stationaryMonitoredProfile, stagePayoff]
  calc
    expect law _ =
        expect law (fun _ => G.stagePayoff profile who) :=
      expect_congr_on_support heq
    _ = _ := expect_constant law _

end UtilityGame.PublicMonitoring

end GameTheory
