/-
# Expected payoffs under finite public monitoring

`signalHistoryLaw` gives a finite-support law at every finite horizon.  This
module evaluates stage payoffs against that law and proves the tower property
through one public signal.  It still constructs no law on infinite paths.
-/

import GameTheory.Repeated.MonitoringContinuation

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- Expected stage payoff at time `t`, integrating over the finite law of
public signal histories. -/
def monitoredStagePayoff (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (t : ℕ) (who : ι) : ℝ :=
  (M.signalHistoryLaw profile t).expect fun history =>
    G.stagePayoff (fun i => profile i t history) who

/-- At time zero there is only the empty public history. -/
@[simp]
theorem monitoredStagePayoff_zero (M : G.PublicMonitoring)
    (profile : M.MonitoredProfile) (who : ι) :
    M.monitoredStagePayoff profile 0 who =
      G.stagePayoff (fun i => profile i 0 (fun k => k.elim0)) who := by
  simp [monitoredStagePayoff]

/-- The expected payoff next period is the expectation of the corresponding
continuation payoff after the first public signal. -/
theorem monitoredStagePayoff_succ_eq_expect_afterSignal
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (n : ℕ) (who : ι) :
    M.monitoredStagePayoff profile (n + 1) who =
      (M.signalLaw
        (fun i => profile i 0 (fun k => k.elim0))).expect fun signal =>
          M.monitoredStagePayoff (M.afterSignal profile signal) n who := by
  unfold monitoredStagePayoff
  rw [M.signalHistoryLaw_succ_eq_bind_first profile n, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro signal _
  rw [FinDist.expect_map]
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

/-- Expected stage payoff at time `t` depends only on prescribed play through
time `t`. -/
theorem monitoredStagePayoff_congr_before_succ
    (M : G.PublicMonitoring) (first second : M.MonitoredProfile)
    (t : ℕ) (who : ι)
    (h : ∀ s, s < t + 1 → ∀ history i,
      first i s history = second i s history) :
    M.monitoredStagePayoff first t who =
      M.monitoredStagePayoff second t who := by
  unfold monitoredStagePayoff
  rw [M.signalHistoryLaw_congr_before first second t
    (fun s hs => h s (by omega))]
  apply FinDist.expect_congr
  intro history _
  congr 2
  funext i
  exact h t (by omega) history i

/-- Before its cutoff, a truncated unilateral deviation induces the same
expected stage payoff as the full deviation. -/
theorem monitoredStagePayoff_update_truncatedDeviation_eq_of_lt
    (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : M.MonitoredProfile) (who : ι)
    (deviation : M.MonitoredStrategy who) {t count : ℕ}
    (ht : t < count) :
    M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count)) t who =
      M.monitoredStagePayoff
        (Profile.update (sig := M.monitoredSignature) profile who deviation)
        t who := by
  apply M.monitoredStagePayoff_congr_before_succ
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
    (t : ℕ) (who : ι) {bound : ℝ}
    (hle : ∀ history,
      G.stagePayoff (fun i => profile i t history) who ≤ bound) :
    M.monitoredStagePayoff profile t who ≤ bound := by
  rw [monitoredStagePayoff, ← FinDist.expect_const
    (M.signalHistoryLaw profile t) bound]
  exact FinDist.expect_mono fun history _ => hle history

/-- A uniform absolute stage-payoff bound also bounds each monitored expected
stage payoff. -/
theorem abs_monitoredStagePayoff_le
    (M : G.PublicMonitoring) (profile : M.MonitoredProfile)
    (t : ℕ) (who : ι) {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    |M.monitoredStagePayoff profile t who| ≤ bound := by
  apply abs_le.mpr
  constructor
  · rw [monitoredStagePayoff, ← FinDist.expect_const
      (M.signalHistoryLaw profile t) (-bound)]
    exact FinDist.expect_mono fun history _ =>
      (abs_le.mp (hbound (fun i => profile i t history))).1
  · exact M.monitoredStagePayoff_le_const profile t who fun history =>
      (abs_le.mp (hbound (fun i => profile i t history))).2

/-- Stationary monitored play has the fixed stage profile's payoff at every
time, independently of the signal law. -/
@[simp]
theorem monitoredStagePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) (profile : Profile G.form.sig)
    (t : ℕ) (who : ι) :
    M.monitoredStagePayoff (M.stationaryMonitoredProfile profile) t who =
      G.stagePayoff profile who := by
  simp [monitoredStagePayoff, stationaryMonitoredProfile]

end UtilityGame.PublicMonitoring

end GameTheory
