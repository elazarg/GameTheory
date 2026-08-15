/-
Hostile public-monitoring regression fixture.

This deliberately combines a genuinely noisy public kernel with a strict
current loss from deviating, and includes an off-support continuation.  The
discounted layer turns these local facts into PPE below.
-/

import GameTheory.Repeated.MonitoringOneShot

noncomputable section

namespace GameTheory.Tests.MonitoringEquilibrium

open GameTheory GameTheory.Math.Probability

@[reducible]
def coordinationForm : GameForm (Fin 2) where
  sig :=
    { Strategy := fun _ => Bool
      Outcome := Fin 2 → Bool }
  play profile := FinDist.pure profile

/-- Both players receive one precisely on agreement. -/
@[reducible]
def coordination : UtilityGame (Fin 2) where
  form := coordinationForm
  utility profile _ := if profile 0 = profile 1 then 1 else 0

def allFalse : Profile coordination.form.sig := fun _ => false
def allTrue : Profile coordination.form.sig := fun _ => true
def coordinated (b : Bool) : Profile coordination.form.sig := fun _ => b

/-- At the payoff-one coordinated profile, no coalition can make all of its
members strictly better because one is already the maximal stage payoff. -/
theorem allFalse_isStrongNash :
    IsStrongNash coordination.form (euPreference coordination.utility) allFalse := by
  rw [isStrongNash_iff]
  intro coalition hnonempty replacement
  obtain ⟨member, hmember⟩ := hnonempty
  refine ⟨member, hmember, ?_⟩
  simp only [euPreference_apply, coordinationForm, expectedUtility_pure]
  simp [allFalse]
  split <;> norm_num

def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

/-- Only the coordinated all-false stage has noisy monitoring. -/
def monitoring : coordination.PublicMonitoring where
  Signal := Bool
  signalLaw stage := if stage = allFalse then fairCoin else FinDist.pure true

/-- Start at `false`; after a public signal, coordinate on that signal. -/
def prescribed : monitoring.MonitoredProfile
  | _, 0, _ => false
  | _, _ + 1, history => history 0

def discount : ℝ := 1 / 2

@[simp]
theorem stagePayoff_eq_agreement (stage : Profile coordination.form.sig)
    (who : Fin 2) :
    coordination.stagePayoff stage who = if stage 0 = stage 1 then 1 else 0 := by
  simp [UtilityGame.stagePayoff, coordination, coordinationForm,
    expectedUtility]

/-- Coordination gives a uniform, sharp absolute stage-payoff bound. -/
theorem stagePayoff_abs_le_one (stage : Profile coordination.form.sig)
    (who : Fin 2) :
    |coordination.stagePayoff stage who| ≤ 1 := by
  rw [stagePayoff_eq_agreement]
  split <;> norm_num

theorem coordination_stagePayoff_bounded :
    ∀ who : Fin 2, ∃ bound : ℝ,
      ∀ stage : Profile coordination.form.sig,
        |coordination.stagePayoff stage who| ≤ bound := by
  intro who
  exact ⟨1, fun stage => stagePayoff_abs_le_one stage who⟩

/-- A current unilateral mismatch is a genuine strict loss, not a weak tie. -/
theorem unilateral_mismatch_strict_loss (who : Fin 2) :
    coordination.stagePayoff
        (Profile.update (sig := coordination.form.sig) allFalse who true) who <
      coordination.stagePayoff allFalse who := by
  fin_cases who <;>
    simp [stagePayoff_eq_agreement, allFalse, Profile.update]

@[simp]
theorem fairCoin_prob_false : fairCoin.prob false = 1 / 2 := by
  rw [fairCoin, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite]

@[simp]
theorem fairCoin_prob_true : fairCoin.prob true = 1 / 2 := by
  rw [fairCoin, FinDist.prob_mix]
  norm_num [FinDist.prob_pure_eq_ite]

theorem fairCoin_expect (u : Bool → ℝ) :
    fairCoin.expect u = (u false + u true) / 2 := by
  rw [fairCoin, FinDist.expect_mix]
  norm_num
  ring

/-- The root is the noisy all-false branch. -/
theorem root_signalLaw :
    monitoring.signalLaw
        (fun i => prescribed i 0 (fun k => k.elim0)) = fairCoin := by
  rfl

/-- Distinct signals select observably distinct successor kernels. -/
theorem signalLaw_after_false :
    monitoring.signalLaw
        (fun i => (monitoring.afterSignal prescribed false) i 0
          (fun k => k.elim0)) = fairCoin := by
  rfl

theorem signalLaw_after_true :
    monitoring.signalLaw
        (fun i => (monitoring.afterSignal prescribed true) i 0
          (fun k => k.elim0)) = FinDist.pure true := by
  rfl

/-- The two successor kernels are genuinely different. -/
theorem signalLaw_branches_ne :
    monitoring.signalLaw
        (fun i => (monitoring.afterSignal prescribed false) i 0
          (fun k => k.elim0)) ≠
      monitoring.signalLaw
        (fun i => (monitoring.afterSignal prescribed true) i 0
          (fun k => k.elim0)) := by
  rw [signalLaw_after_false, signalLaw_after_true]
  intro h
  have hprob := congrArg (fun law : FinDist Bool => law.prob false) h
  norm_num [fairCoin, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at hprob

/-- A typed off-support public history.  It will be used to test that the
continuation and incentive predicates quantify over histories, not reach mass. -/
def zeroProbabilityHistory : monitoring.SignalHistory 2 :=
  Fin.cons true (Fin.cons false (fun k => k.elim0))

/-- Once a signal is observed, its prescribed continuation is stationary. -/
theorem afterSignal_prescribed (b : Bool) :
    monitoring.afterSignal prescribed b =
      monitoring.stationaryMonitoredProfile (coordinated b) := by
  rfl

/-- The history `[true, false]` has zero generated mass: after the first
`true`, the next public signal is deterministically `true`. -/
theorem zeroProbabilityHistory_mass :
    (monitoring.signalHistoryLaw prescribed 2).prob
      zeroProbabilityHistory = 0 := by
  classical
  rw [monitoring.signalHistoryLaw_succ_eq_bind_first prescribed 1,
    root_signalLaw, FinDist.prob_bind]
  show fairCoin.expect (fun signal : Bool =>
    ((monitoring.signalHistoryLaw
      (monitoring.afterSignal prescribed signal) 1).map
      (Fin.cons (α := fun _ => Bool) signal)).prob
        zeroProbabilityHistory) = 0
  rw [fairCoin_expect]
  have hfalse :
      ((monitoring.signalHistoryLaw
          (monitoring.afterSignal prescribed false) 1).map
          (Fin.cons (α := fun _ => Bool) false)).prob
            zeroProbabilityHistory = 0 := by
    apply FinDist.prob_eq_zero_iff.mpr
    rw [FinDist.support_map]
    rintro ⟨history, _, heq⟩
    have h0 := congrFun heq 0
    exact Bool.noConfusion h0
  have htrueLaw :
      monitoring.signalHistoryLaw
          (monitoring.afterSignal prescribed true) 1 =
        FinDist.pure (fun _ : Fin 1 => true) := by
    rw [monitoring.signalHistoryLaw_succ,
      monitoring.signalHistoryLaw_zero]
    rw [afterSignal_prescribed]
    have hall : (fun _ : Fin 2 => true) ≠ allFalse := by
      intro h
      have h0 := congrFun h 0
      simp [allFalse] at h0
    simp [monitoring, coordinated,
      UtilityGame.PublicMonitoring.stationaryMonitoredProfile, hall]
    congr 1
  have htrue :
      ((monitoring.signalHistoryLaw
          (monitoring.afterSignal prescribed true) 1).map
          (Fin.cons (α := fun _ => Bool) true)).prob
            zeroProbabilityHistory = 0 := by
    apply FinDist.prob_eq_zero_iff.mpr
    rw [FinDist.support_map, htrueLaw]
    rintro ⟨history, hhistory, heq⟩
    rw [FinDist.mem_support_pure] at hhistory
    subst history
    have h1 := congrFun heq 1
    exact Bool.noConfusion h1
  rw [hfalse, htrue]
  norm_num

/-- The explicitly typed off-support history nevertheless has the all-true
continuation. -/
theorem zeroProbabilityHistory_continuation :
    monitoring.after prescribed zeroProbabilityHistory =
      monitoring.stationaryMonitoredProfile (coordinated true) := by
  unfold zeroProbabilityHistory
  rw [← monitoring.after_afterSignal prescribed true
    (Fin.cons false (fun k => k.elim0))]
  rw [afterSignal_prescribed]
  simp

@[simp]
theorem discountedPayoff_stationary_coordinated (b : Bool) (who : Fin 2) :
    monitoring.discountedPayoff discount
        (monitoring.stationaryMonitoredProfile (coordinated b)) who = 1 := by
  rw [monitoring.discountedPayoff_stationaryMonitoredProfile
    (by norm_num [discount]) (by norm_num [discount])]
  simp [stagePayoff_eq_agreement, coordinated]

/-- Prescribed play coordinates in every period, although its first public
signal is genuinely noisy. -/
@[simp]
theorem discountedPayoff_prescribed (who : Fin 2) :
    monitoring.discountedPayoff discount prescribed who = 1 := by
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount]) prescribed who
    (stagePayoff_abs_le_one · who)]
  simp_rw [afterSignal_prescribed, discountedPayoff_stationary_coordinated]
  rw [FinDist.expect_const]
  norm_num [discount, prescribed, stagePayoff_eq_agreement]

/-- At the noisy root, changing only the current action cannot improve the
discounted payoff. The strict stage loss above is offset only by returning to
coordinated continuation play. -/
theorem prescribed_hasNoProfitableOneShotDeviation :
    monitoring.HasNoProfitableOneShotDeviation discount prescribed := by
  intro who action
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    (Profile.update (sig := monitoring.monitoredSignature) prescribed who
      (monitoring.oneShotDeviation prescribed who action)) who
    (stagePayoff_abs_le_one · who)]
  rw [monitoring.currentProfile_update_oneShotDeviation]
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    afterSignal_prescribed, discountedPayoff_stationary_coordinated]
  rw [FinDist.expect_const]
  rw [discountedPayoff_prescribed]
  norm_num [discount] at ⊢
  split <;> norm_num

/-- Every stationary coordinated continuation is one-shot optimal. -/
theorem stationary_coordinated_hasNoProfitableOneShotDeviation (b : Bool) :
    monitoring.HasNoProfitableOneShotDeviation discount
      (monitoring.stationaryMonitoredProfile (coordinated b)) := by
  intro who action
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    (Profile.update (sig := monitoring.monitoredSignature)
      (monitoring.stationaryMonitoredProfile (coordinated b)) who
      (monitoring.oneShotDeviation
        (monitoring.stationaryMonitoredProfile (coordinated b)) who action))
    who (stagePayoff_abs_le_one · who)]
  rw [monitoring.currentProfile_update_oneShotDeviation]
  simp only [UtilityGame.PublicMonitoring.stationaryMonitoredProfile]
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    monitoring.afterSignal_stationaryMonitoredProfile,
    discountedPayoff_stationary_coordinated]
  rw [FinDist.expect_const]
  norm_num [discount] at ⊢
  split <;> norm_num

/-- One-shot optimality holds after every typed public history, not merely
histories in the generated law's support. -/
theorem prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory :
    monitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount prescribed := by
  intro t history
  cases t with
  | zero =>
      simpa [UtilityGame.PublicMonitoring.after] using
        prescribed_hasNoProfitableOneShotDeviation
  | succ t =>
      have hcontinuation :
          monitoring.after prescribed history =
            monitoring.stationaryMonitoredProfile (coordinated (history 0)) := by
        calc
          monitoring.after prescribed history =
              monitoring.after prescribed
                (Fin.cons (history 0) (Fin.tail history)) := by
            rw [Fin.cons_self_tail history]
          _ = monitoring.after
                (monitoring.afterSignal prescribed (history 0))
                (Fin.tail history) := by
            rw [monitoring.after_afterSignal]
          _ = monitoring.stationaryMonitoredProfile
                (coordinated (history 0)) := by
            rw [afterSignal_prescribed,
              monitoring.after_stationaryMonitoredProfile]
      rw [hcontinuation]
      exact stationary_coordinated_hasNoProfitableOneShotDeviation (history 0)

/-- The impossible `[true, false]` history is explicitly covered by the local
incentive condition. -/
theorem zeroProbabilityHistory_hasNoProfitableOneShotDeviation :
    monitoring.HasNoProfitableOneShotDeviation discount
      (monitoring.after prescribed zeroProbabilityHistory) :=
  prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory
    2 zeroProbabilityHistory

/-- The generic one-shot-deviation principle specializes to this finite noisy
fixture at discount one half. -/
theorem prescribed_ppe_iff_noProfitableOneShotDeviation :
    monitoring.IsPerfectPublicEquilibrium discount prescribed ↔
      monitoring.HasNoProfitableOneShotDeviationAfterEveryHistory discount prescribed := by
  exact monitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    (by norm_num [discount]) (by norm_num [discount]) prescribed
    coordination_stagePayoff_bounded

/-- The noisy branch-dependent prescribed profile is an actual PPE. -/
theorem prescribed_isPerfectPublicEquilibrium :
    monitoring.IsPerfectPublicEquilibrium discount prescribed :=
  prescribed_ppe_iff_noProfitableOneShotDeviation.mpr
    prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory

/-- The canonical exact-to-approximate Nash bridge lifts pointwise through
every public continuation. -/
theorem prescribed_isεPerfectPublicEquilibrium {ε : ℝ} (hε : 0 ≤ ε) :
    monitoring.IsεPerfectPublicEquilibrium discount ε prescribed :=
  prescribed_isPerfectPublicEquilibrium.isεPerfectPublicEquilibrium hε

/-! A stationary mismatched profile supplies the converse regression: player
zero can coordinate immediately, while the continuation stays mismatched. -/

def mismatched : Profile coordination.form.sig
  | 0 => false
  | 1 => true

def mismatchedProfile : monitoring.MonitoredProfile :=
  monitoring.stationaryMonitoredProfile mismatched

@[simp]
theorem discountedPayoff_mismatchedProfile (who : Fin 2) :
    monitoring.discountedPayoff discount mismatchedProfile who = 0 := by
  unfold mismatchedProfile
  rw [monitoring.discountedPayoff_stationaryMonitoredProfile
    (by norm_num [discount]) (by norm_num [discount])]
  fin_cases who <;> simp [mismatched, stagePayoff_eq_agreement]

@[simp]
theorem afterSignal_mismatchedProfile (signal : Bool) :
    monitoring.afterSignal mismatchedProfile signal = mismatchedProfile := by
  simp [mismatchedProfile]

/-- Player zero's one-shot switch to `true` is strictly profitable. -/
theorem mismatchedProfile_has_profitable_oneShotDeviation :
    ¬ monitoring.HasNoProfitableOneShotDeviation discount mismatchedProfile := by
  intro hno
  have hdeviation := hno 0 true
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    (Profile.update (sig := monitoring.monitoredSignature) mismatchedProfile 0
      (monitoring.oneShotDeviation mismatchedProfile 0 true)) 0
    (stagePayoff_abs_le_one · 0)] at hdeviation
  rw [monitoring.currentProfile_update_oneShotDeviation] at hdeviation
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    afterSignal_mismatchedProfile, discountedPayoff_mismatchedProfile] at hdeviation
  norm_num [discount, mismatchedProfile, mismatched, stagePayoff_eq_agreement,
    UtilityGame.PublicMonitoring.stationaryMonitoredProfile, Profile.update] at hdeviation

/-- The profitable root deviation falsifies perfect public equilibrium. -/
theorem mismatchedProfile_not_isPerfectPublicEquilibrium :
    ¬ monitoring.IsPerfectPublicEquilibrium discount mismatchedProfile := by
  intro hppe
  apply mismatchedProfile_has_profitable_oneShotDeviation
  have hall := hppe.hasNoProfitableOneShotDeviationAfterEveryHistory
  simpa [UtilityGame.PublicMonitoring.after] using
    hall 0 (fun k => k.elim0)

end GameTheory.Tests.MonitoringEquilibrium
