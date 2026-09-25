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

/-- Stage payoff at a reachable public history, with its actual outcome-law
integration certificate. -/
def monitoredStageValue (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι)
    (hstage : ∀ history ∈ (M.signalHistoryLaw profile t).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i t history)))
    (history : M.SignalHistory t)
    (hreach : history ∈ (M.signalHistoryLaw profile t).support) : ℝ :=
  G.stagePayoff (fun i => profile i t history) who (hstage history hreach)

/-- Exactly the two integrations used by one monitored stage: conditional
stage outcomes at supported histories, and those values under the actual
history law. -/
structure MonitoredStageIntegrable (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι) : Prop where
  conditional : ∀ history ∈ (M.signalHistoryLaw profile t).support,
    UtilityIntegrable G.utility who
      (G.form.play (fun i => profile i t history))
  history : PayoffIntegrable (M.signalHistoryLaw profile t)
    (extendFromSupport (M.signalHistoryLaw profile t)
      (M.monitoredStageValue profile t who conditional))

/-- Expected stage payoff at time `t`, integrating supported conditional
stage values under the actual public-history law. -/
def monitoredStagePayoff (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι)
    (h : M.MonitoredStageIntegrable profile t who) : ℝ :=
  expect (M.signalHistoryLaw profile t)
    (extendFromSupport (M.signalHistoryLaw profile t)
      (M.monitoredStageValue profile t who h.conditional)) h.history

/-- At time zero there is only the empty public history. -/
@[simp]
theorem monitoredStagePayoff_zero (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (who : ι)
    (h : M.MonitoredStageIntegrable profile 0 who) :
    M.monitoredStagePayoff profile 0 who h =
      G.stagePayoff (fun i => profile i 0 (fun k => k.elim0)) who
        (h.conditional (fun k => k.elim0) (by simp)) := by
  simp only [monitoredStagePayoff, signalHistoryLaw_zero]
  rw [expect_pure]
  simp [extendFromSupport, monitoredStageValue]

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
    (hstage : ∀ history ∈
      (M.signalHistoryLaw profile (n + 1)).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i (n + 1) history)))
    (houter : PayoffIntegrable (M.signalHistoryLaw profile (n + 1))
      (extendFromSupport (M.signalHistoryLaw profile (n + 1))
        (M.monitoredStageValue profile (n + 1) who hstage)))
    (signal : M.Signal)
    (hsignal : signal ∈
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support)
    (hnext : ∀ history ∈
      (M.signalHistoryLaw (M.afterSignal profile signal) n).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i =>
          M.afterSignal profile signal i n history))) :
    PayoffIntegrable
      (M.signalHistoryLaw (M.afterSignal profile signal) n)
      (extendFromSupport
        (M.signalHistoryLaw (M.afterSignal profile signal) n)
        (M.monitoredStageValue (M.afterSignal profile signal) n who
          hnext)) := by
  let fullLaw := M.signalHistoryLaw profile (n + 1)
  let firstLaw := M.signalLaw (fun i => profile i 0 (fun k => k.elim0))
  let nextLaw : M.Signal → PMF (M.SignalHistory n) := fun signal =>
    M.signalHistoryLaw (M.afterSignal profile signal) n
  let kernel : M.Signal → PMF (M.SignalHistory (n + 1)) := fun signal =>
    (nextLaw signal).map (Fin.cons signal)
  let value := extendFromSupport fullLaw
    (M.monitoredStageValue profile (n + 1) who hstage)
  have hlaw : fullLaw = firstLaw.bind kernel :=
    M.signalHistoryLaw_succ_eq_bind_first profile n
  have hbind : PayoffIntegrable (firstLaw.bind kernel) value := by
    rw [← hlaw]
    exact houter
  have hkernel : PayoffIntegrable
      ((nextLaw signal).map
        (Fin.cons (α := fun _ => M.Signal) signal)) value :=
    payoffIntegrable_bind_conditional_on_support
      firstLaw kernel value hbind signal hsignal
  have hmap : PayoffIntegrable (nextLaw signal)
      (value ∘ Fin.cons (α := fun _ => M.Signal) signal) := by
    apply (payoffIntegrable_map_iff
      (Fin.cons (α := fun _ => M.Signal) signal)
      (nextLaw signal) value).mp
    exact hkernel
  apply payoffIntegrable_congr_on_support
    (μ := nextLaw signal)
    (f := value ∘ Fin.cons (α := fun _ => M.Signal) signal)
  · intro history hhistory
    have hfull := M.afterSignal_history_mem_support profile n
      signal hsignal history hhistory
    have hleft :
        value (Fin.cons signal history) =
          M.monitoredStageValue profile (n + 1) who hstage
            (Fin.cons signal history) hfull := by
      simp only [value, fullLaw, extendFromSupport, hfull, ↓reduceDIte]
    have hright :
        extendFromSupport (nextLaw signal)
          (M.monitoredStageValue (M.afterSignal profile signal) n who hnext)
          history =
            M.monitoredStageValue (M.afterSignal profile signal)
              n who hnext history hhistory := by
      simp only [nextLaw, extendFromSupport, hhistory, ↓reduceDIte]
    calc
      (value ∘ Fin.cons signal) history =
          value (Fin.cons signal history) := rfl
      _ = M.monitoredStageValue profile (n + 1) who hstage
          (Fin.cons signal history) hfull := hleft
      _ = M.monitoredStageValue (M.afterSignal profile signal)
          n who hnext history hhistory := rfl
      _ = extendFromSupport (nextLaw signal)
          (M.monitoredStageValue (M.afterSignal profile signal) n who hnext)
          history := hright.symm
  · exact hmap

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
      (M.afterSignal profile signal) n who := by
  let hnext := M.afterSignal_stage_integrable profile n who
    h.conditional signal hsignal
  exact ⟨hnext,
    M.afterSignal_outer_integrable profile n who
      h.conditional h.history signal hsignal hnext⟩

/-- The guarded continuation value after the first public signal, extended
by zero away from the actual first-signal support. -/
def firstSignalContinuationValue
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who) :
    M.Signal → ℝ :=
  extendFromSupport
    (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
    (fun signal hsignal =>
      M.monitoredStagePayoff (M.afterSignal profile signal) n who
        (h.afterSignal M profile n who signal hsignal))

private theorem firstSignal_tower_certificate
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (hstage : ∀ history ∈
      (M.signalHistoryLaw profile (n + 1)).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i (n + 1) history)))
    (houter : PayoffIntegrable (M.signalHistoryLaw profile (n + 1))
      (extendFromSupport (M.signalHistoryLaw profile (n + 1))
        (M.monitoredStageValue profile (n + 1) who hstage))) :
    ∃ hfirst : PayoffIntegrable
        (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
        (M.firstSignalContinuationValue profile n who ⟨hstage, houter⟩),
      M.monitoredStagePayoff profile (n + 1) who ⟨hstage, houter⟩ =
        expect (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
          (M.firstSignalContinuationValue profile n who ⟨hstage, houter⟩)
          hfirst := by
  let fullLaw := M.signalHistoryLaw profile (n + 1)
  let firstLaw := M.signalLaw (fun i => profile i 0 (fun k => k.elim0))
  let nextLaw : M.Signal → PMF (M.SignalHistory n) := fun signal =>
    M.signalHistoryLaw (M.afterSignal profile signal) n
  let kernel : M.Signal → PMF (M.SignalHistory (n + 1)) := fun signal =>
    (nextLaw signal).map (Fin.cons signal)
  let value := extendFromSupport fullLaw
    (M.monitoredStageValue profile (n + 1) who hstage)
  let continuation := M.firstSignalContinuationValue profile n who
    ⟨hstage, houter⟩
  have hlaw : fullLaw = firstLaw.bind kernel :=
    M.signalHistoryLaw_succ_eq_bind_first profile n
  have hbind : PayoffIntegrable (firstLaw.bind kernel) value := by
    rw [← hlaw]
    exact houter
  have hagree (signal : M.Signal) (hsignal : signal ∈ firstLaw.support) :
      continuation signal =
        expect (kernel signal) value
          (payoffIntegrable_bind_conditional_on_support
            firstLaw kernel value hbind signal hsignal) := by
    let hnext := M.afterSignal_stage_integrable profile n who
      hstage signal hsignal
    let houterNext := M.afterSignal_outer_integrable profile n who
      hstage houter signal hsignal hnext
    have hkernel : PayoffIntegrable
        ((nextLaw signal).map
          (Fin.cons (α := fun _ => M.Signal) signal)) value :=
      payoffIntegrable_bind_conditional_on_support
        firstLaw kernel value hbind signal hsignal
    have hmap : PayoffIntegrable (nextLaw signal)
        (value ∘ Fin.cons (α := fun _ => M.Signal) signal) :=
      (payoffIntegrable_map_iff
        (Fin.cons (α := fun _ => M.Signal) signal)
        (nextLaw signal) value).mp hkernel
    have hpoint : ∀ history ∈ (nextLaw signal).support,
        (value ∘ Fin.cons (α := fun _ => M.Signal) signal) history =
          extendFromSupport (nextLaw signal)
            (M.monitoredStageValue (M.afterSignal profile signal)
              n who hnext) history := by
      intro history hhistory
      have hfull := M.afterSignal_history_mem_support profile n
        signal hsignal history hhistory
      have hleft :
          value (Fin.cons signal history) =
            M.monitoredStageValue profile (n + 1) who hstage
              (Fin.cons signal history) hfull := by
        simp only [value, fullLaw, extendFromSupport,
          hfull, ↓reduceDIte]
      have hright :
          extendFromSupport (nextLaw signal)
            (M.monitoredStageValue (M.afterSignal profile signal)
              n who hnext) history =
                M.monitoredStageValue (M.afterSignal profile signal)
                  n who hnext history hhistory := by
        simp only [nextLaw, extendFromSupport, hhistory, ↓reduceDIte]
      calc
        (value ∘ Fin.cons signal) history =
            value (Fin.cons signal history) := rfl
        _ = M.monitoredStageValue profile (n + 1) who hstage
            (Fin.cons signal history) hfull := hleft
        _ = M.monitoredStageValue (M.afterSignal profile signal)
            n who hnext history hhistory := rfl
        _ = extendFromSupport (nextLaw signal)
            (M.monitoredStageValue (M.afterSignal profile signal)
              n who hnext) history := hright.symm
    calc
      continuation signal =
          M.monitoredStagePayoff (M.afterSignal profile signal)
            n who ⟨hnext, houterNext⟩ := by
          have hs : signal ∈
              (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support :=
            hsignal
          simp only [continuation, firstSignalContinuationValue,
            extendFromSupport]
          simp only [hs, ↓reduceDIte]
      _ = expect (nextLaw signal)
          (extendFromSupport (nextLaw signal)
            (M.monitoredStageValue (M.afterSignal profile signal)
              n who hnext)) houterNext := rfl
      _ = expect (nextLaw signal)
          (value ∘ Fin.cons (α := fun _ => M.Signal) signal) hmap :=
        (expect_congr_on_support hpoint hmap houterNext).symm
      _ = expect (kernel signal) value hkernel :=
        (expect_map (Fin.cons (α := fun _ => M.Signal) signal)
          (nextLaw signal) value hmap hkernel).symm
      _ = expect (kernel signal) value
          (payoffIntegrable_bind_conditional_on_support
            firstLaw kernel value hbind signal hsignal) := rfl
  have hfirst : PayoffIntegrable firstLaw continuation :=
    payoffIntegrable_bind_conditionalValue_on_support
      firstLaw kernel value hbind continuation hagree
  refine ⟨hfirst, ?_⟩
  calc
    M.monitoredStagePayoff profile (n + 1) who ⟨hstage, houter⟩ =
        expect fullLaw value houter := rfl
    _ = expect (firstLaw.bind kernel) value hbind :=
      expect_congr_law hlaw value houter hbind
    _ = expect firstLaw continuation hfirst :=
      expect_bind_tower_on_support
        firstLaw kernel value hbind continuation hagree

/-- The first-signal continuation value is integrable under its actual signal
law whenever the whole history-law stage value is integrable. -/
theorem firstSignalContinuationValue_integrable
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who) :
    PayoffIntegrable
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
      (M.firstSignalContinuationValue profile n who h) :=
  (M.firstSignal_tower_certificate profile n who
    h.conditional h.history).choose

/-- The monitored stage value obeys the guarded first-signal tower. -/
theorem monitoredStagePayoff_succ_eq_expect_afterSignal
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile) (n : ℕ)
    (who : ι)
    (h : M.MonitoredStageIntegrable profile (n + 1) who) :
    M.monitoredStagePayoff profile (n + 1) who h =
      expect (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
        (M.firstSignalContinuationValue profile n who h)
        (M.firstSignalContinuationValue_integrable
          profile n who h) :=
  (M.firstSignal_tower_certificate profile n who
    h.conditional h.history).choose_spec

/-- Expected stage payoff at time `t` depends only on prescribed play through
time `t`. -/
theorem monitoredStagePayoff_congr_before_succ
    (M : G.PublicMonitoring) (first second : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : ∀ s, s < t + 1 → ∀ history i,
      first i s history = second i s history)
    (hfirst : M.MonitoredStageIntegrable first t who)
    (hsecond : M.MonitoredStageIntegrable second t who) :
    M.monitoredStagePayoff first t who hfirst =
      M.monitoredStagePayoff second t who hsecond := by
  have hlaw := M.signalHistoryLaw_congr_before first second t
    (fun s hs => h s (by omega))
  let f := extendFromSupport (M.signalHistoryLaw first t)
    (M.monitoredStageValue first t who hfirst.conditional)
  let g := extendFromSupport (M.signalHistoryLaw second t)
    (M.monitoredStageValue second t who hsecond.conditional)
  have hvalues : ∀ history ∈ (M.signalHistoryLaw first t).support,
      f history = g history := by
    intro history hreach
    have hreachSecond : history ∈ (M.signalHistoryLaw second t).support := by
      simpa [hlaw] using hreach
    have hstageEq : (fun i => first i t history) =
        (fun i => second i t history) := by
      funext i
      exact h t (by omega) history i
    simp only [f, g]
    simp only [extendFromSupport]
    simp only [hreach, hreachSecond, ↓reduceDIte,
      monitoredStageValue, stagePayoff]
    exact expectedUtility_congr_law G.utility who
      (congrArg G.form.play hstageEq) _ _
  have hfSecond : PayoffIntegrable (M.signalHistoryLaw second t) f := by
    simpa [hlaw] using hfirst.history
  have hvaluesSecond : ∀ history ∈ (M.signalHistoryLaw second t).support,
      f history = g history := by
    intro history hreach
    exact hvalues history (by simpa [hlaw] using hreach)
  unfold monitoredStagePayoff
  exact (expect_congr_law hlaw f hfirst.history hfSecond).trans
    (expect_congr_on_support hvaluesSecond hfSecond hsecond.history)

/-- Before its cutoff, a truncated unilateral deviation induces the same
expected stage payoff as the full deviation. -/
theorem monitoredStagePayoff_update_truncatedDeviation_eq_of_lt
    (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι)
    (deviation : M.MonitoredStrategy who) {t count : ℕ}
    (ht : t < count)
    (htruncated : M.MonitoredStageIntegrable
      (Profile.update (sig := M.monitoredSignature) profile who
        (M.truncatedDeviation profile who deviation count)) t who)
    (hfull : M.MonitoredStageIntegrable
      (Profile.update (sig := M.monitoredSignature) profile who deviation)
        t who) :
    M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count))
        t who htruncated =
      M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who deviation)
        t who hfull := by
  refine M.monitoredStagePayoff_congr_before_succ
    _ _ t who ?_ htruncated hfull
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
    (hle : ∀ history, ∀ hreach :
      history ∈ (M.signalHistoryLaw profile t).support,
      G.stagePayoff (fun i => profile i t history) who
        (h.conditional history hreach) ≤ bound) :
    M.monitoredStagePayoff profile t who h ≤ bound := by
  exact expect_le_const _ _ h.history bound (by
    intro history hreach
    simpa [extendFromSupport, hreach, monitoredStageValue] using
      hle history hreach)

/-- A uniform absolute stage-payoff bound also bounds each monitored expected
stage payoff. -/
theorem abs_monitoredStagePayoff_le
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : M.MonitoredStageIntegrable profile t who)
    {bound : ℝ}
    (hbound : ∀ history, ∀ hreach :
      history ∈ (M.signalHistoryLaw profile t).support,
      |G.stagePayoff (fun i => profile i t history) who
        (h.conditional history hreach)| ≤ bound) :
    |M.monitoredStagePayoff profile t who h| ≤ bound := by
  apply abs_le.mpr
  constructor
  · have hconst := payoffIntegrable_constant
      (M.signalHistoryLaw profile t) (-bound)
    have h := expect_mono (μ := M.signalHistoryLaw profile t)
      (f := fun _ => -bound)
      (g := extendFromSupport (M.signalHistoryLaw profile t)
        (M.monitoredStageValue profile t who h.conditional))
      (fun history hreach => by
        simpa [extendFromSupport, hreach, monitoredStageValue] using
          (abs_le.mp (hbound history hreach)).1)
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
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    M.MonitoredStageIntegrable profile t who := by
  let hconditional : ∀ history ∈
      (M.signalHistoryLaw profile t).support,
      UtilityIntegrable G.utility who
        (G.form.play (fun i => profile i t history)) :=
    fun history _ => hG who (fun i => profile i t history)
  refine ⟨hconditional, ?_⟩
  apply payoffIntegrable_of_bounded_on_support
  intro history hreach
  simpa [extendFromSupport, hreach, monitoredStageValue] using
    hbound (fun i => profile i t history)

/-- Stationary monitored play has the fixed stage profile's payoff at every
time, independently of the signal law. -/
@[simp]
theorem monitoredStagePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (profile : Profile G.form.sig)
    (t : ℕ) (who : ι)
    (h : M.MonitoredStageIntegrable
      (M.stationaryMonitoredProfile profile) t who)
    (hfixed : UtilityIntegrable G.utility who (G.form.play profile)) :
    M.monitoredStagePayoff
        (M.stationaryMonitoredProfile profile) t who h =
      G.stagePayoff profile who hfixed := by
  unfold monitoredStagePayoff
  let law := M.signalHistoryLaw (M.stationaryMonitoredProfile profile) t
  have hconst := payoffIntegrable_constant law (G.stagePayoff profile who hfixed)
  have heq : ∀ history ∈ law.support,
      extendFromSupport law
        (M.monitoredStageValue (M.stationaryMonitoredProfile profile)
          t who h.conditional) history = G.stagePayoff profile who hfixed := by
    intro history hreach
    simp [law, extendFromSupport, hreach, monitoredStageValue,
      stationaryMonitoredProfile, stagePayoff]
  calc
    expect law _ h.history =
        expect law (fun _ => G.stagePayoff profile who hfixed) hconst :=
      expect_congr_on_support heq h.history hconst
    _ = _ := expect_constant law _ hconst

end UtilityGame.PublicMonitoring

end GameTheory
