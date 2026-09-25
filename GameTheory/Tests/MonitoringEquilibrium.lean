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
  play profile := PMF.pure profile

/-- Both players receive one precisely on agreement. -/
@[reducible]
def coordination : UtilityGame (Fin 2) where
  form := coordinationForm
  utility profile _ := if profile 0 = profile 1 then 1 else 0

/-- Pure coordination stages have integrable utility in the finite fixture. -/
theorem coordination_integrable :
    coordination.form.HasIntegrableUtility coordination.utility := by
  intro who stage
  simpa [coordinationForm] using
    (payoffIntegrable_pure stage
      (fun outcome => coordination.utility outcome who))

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
  simp only [euPreference_apply]
  refine ⟨by simpa [coordinationForm] using
    (payoffIntegrable_pure allFalse
      (fun outcome => coordination.utility outcome member)),
    by simpa [coordinationForm] using
      (payoffIntegrable_pure
        (Profile.override coalition replacement allFalse)
        (fun outcome => coordination.utility outcome member)), ?_⟩
  simp [expectedUtility_pure, allFalse]
  split <;> norm_num

def fairCoin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

/-- Only the coordinated all-false stage has noisy monitoring. -/
@[reducible]
def monitoring : coordination.PublicMonitoring where
  Signal := Bool
  signalLaw stage := if stage = allFalse then fairCoin else PMF.pure true

/-- Start at `false`; after a public signal, coordinate on that signal. -/
def prescribed : monitoring.MonitoredProfile
  | _, 0, _ => false
  | _, _ + 1, history => history 0

def discount : ℝ := 1 / 2

@[simp]
theorem stagePayoff_eq_agreement (stage : Profile coordination.form.sig)
    (who : Fin 2) :
    coordination.stagePayoff stage who (coordination_integrable who stage) =
      if stage 0 = stage 1 then 1 else 0 := by
  simp [UtilityGame.stagePayoff, coordinationForm, expectedUtility_pure]

/-- Coordination gives a uniform, sharp absolute stage-payoff bound. -/
theorem stagePayoff_abs_le_one (stage : Profile coordination.form.sig)
    (who : Fin 2) :
    |coordination.stagePayoff stage who
      (coordination_integrable who stage)| ≤ 1 := by
  rw [stagePayoff_eq_agreement]
  split <;> norm_num

theorem coordination_stagePayoff_bounded :
    ∀ who : Fin 2, ∃ bound : ℝ,
      ∀ stage : Profile coordination.form.sig,
        |coordination.stagePayoff stage who
          (coordination_integrable who stage)| ≤ bound := by
  intro who
  exact ⟨1, fun stage => stagePayoff_abs_le_one stage who⟩

abbrev stageCert :
    ∀ profile : monitoring.MonitoredProfile, ∀ who t,
      monitoring.MonitoredStageIntegrable profile t who :=
  monitoring.discountedStageIntegrableOfBounded
    coordination_integrable coordination_stagePayoff_bounded

abbrev seriesCert :
    ∀ profile : monitoring.MonitoredProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        monitoring.monitoredStagePayoff profile t who
          (stageCert profile who t) :=
  monitoring.discountedSummableOfBounded
    (by norm_num [discount]) (by norm_num [discount])
    coordination_integrable coordination_stagePayoff_bounded

/-- A current unilateral mismatch is a genuine strict loss, not a weak tie. -/
theorem unilateral_mismatch_strict_loss (who : Fin 2) :
    coordination.stagePayoff
        (Profile.update (sig := coordination.form.sig) allFalse who true) who
        (coordination_integrable who _) <
      coordination.stagePayoff allFalse who
        (coordination_integrable who allFalse) := by
  fin_cases who <;>
    simp [stagePayoff_eq_agreement, allFalse, Profile.update]

@[simp]
theorem fairCoin_prob_false : fairCoin false = 1 / 2 := by
  norm_num [fairCoin, mix_apply]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

@[simp]
theorem fairCoin_prob_true : fairCoin true = 1 / 2 := by
  norm_num [fairCoin, mix_apply]
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem fairCoin_expect (u : Bool → ℝ) :
    expect fairCoin u (payoffIntegrable_of_finite fairCoin u) =
      (u false + u true) / 2 := by
  rw [expect_eq_sum]
  simp [fairCoin_prob_false, fairCoin_prob_true]
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
          (fun k => k.elim0)) = PMF.pure true := by
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
  have hprob := congrArg (fun law : PMF Bool => law false) h
  simp at hprob

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
    monitoring.signalHistoryLaw prescribed 2 zeroProbabilityHistory = 0 := by
  classical
  have htrueLaw :
      monitoring.signalHistoryLaw
          (monitoring.afterSignal prescribed true) 1 =
        PMF.pure (fun _ : Fin 1 => true) := by
    rw [monitoring.signalHistoryLaw_succ,
      monitoring.signalHistoryLaw_zero]
    rw [afterSignal_prescribed]
    have hall : (fun _ : Fin 2 => true) ≠ allFalse := by
      intro h
      have h0 := congrFun h 0
      simp [allFalse] at h0
    simp [monitoring, coordinated,
      UtilityGame.PublicMonitoring.stationaryMonitoredProfile, hall]
    rw [PMF.pure_map]
    apply congrArg PMF.pure
    funext i
    fin_cases i
    rfl
  by_contra hnonzero
  have hmem := (PMF.mem_support_iff _ _).2 hnonzero
  rw [monitoring.signalHistoryLaw_succ_eq_bind_first prescribed 1,
    root_signalLaw, PMF.mem_support_bind_iff] at hmem
  obtain ⟨signal, _, hmap⟩ := hmem
  obtain ⟨history, hhistory, heq⟩ :=
    (PMF.mem_support_map_iff _ _ _).1 hmap
  have hsignal : signal = true := by
    cases signal with
    | false =>
        have h0 := congrFun heq 0
        exact False.elim (Bool.noConfusion h0)
    | true => rfl
  subst signal
  rw [htrueLaw, PMF.mem_support_pure_iff] at hhistory
  subst history
  have h1 := congrFun heq 1
  exact Bool.noConfusion h1

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
    monitoring.discountedPayoffOfBounded (discount := discount)
        (by norm_num [discount]) (by norm_num [discount])
        coordination_integrable
        (monitoring.stationaryMonitoredProfile (coordinated b)) who
        (stagePayoff_abs_le_one · who) = 1 := by
  show monitoring.discountedPayoff discount
    (monitoring.stationaryMonitoredProfile (coordinated b)) who _ _ = 1
  rw [monitoring.discountedPayoff_stationaryMonitoredProfile
    (discount := discount)
    (by norm_num [discount]) (by norm_num [discount])
    (coordinated b) who (coordination_integrable who _)]
  simp [stagePayoff_eq_agreement, coordinated]

/-- Prescribed play coordinates in every period, although its first public
signal is genuinely noisy. -/
@[simp]
theorem discountedPayoff_prescribed (who : Fin 2) :
    monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable prescribed who
      (stagePayoff_abs_le_one · who) = 1 := by
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    coordination_integrable prescribed who
    (stagePayoff_abs_le_one · who)]
  simp_rw [afterSignal_prescribed, discountedPayoff_stationary_coordinated]
  rw [expect_constant]
  norm_num [discount, prescribed, stagePayoff_eq_agreement]

/-- At the noisy root, changing only the current action cannot improve the
discounted payoff. The strict stage loss above is offset only by returning to
coordinated continuation play. -/
theorem prescribed_hasNoProfitableOneShotDeviation :
    monitoring.HasNoProfitableOneShotDeviation discount
      stageCert seriesCert prescribed := by
  intro who action
  show monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable
      (Profile.update (sig := monitoring.monitoredSignature) prescribed who
        (monitoring.oneShotDeviation prescribed who action)) who
      (stagePayoff_abs_le_one · who) ≤
    monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable prescribed who
      (stagePayoff_abs_le_one · who)
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    coordination_integrable
    (Profile.update (sig := monitoring.monitoredSignature) prescribed who
      (monitoring.oneShotDeviation prescribed who action)) who
    (stagePayoff_abs_le_one · who)]
  simp only [monitoring.currentProfile_update_oneShotDeviation]
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    afterSignal_prescribed, discountedPayoff_stationary_coordinated]
  rw [expect_constant]
  rw [discountedPayoff_prescribed]
  norm_num [discount] at ⊢
  split <;> norm_num

/-- Every stationary coordinated continuation is one-shot optimal. -/
theorem stationary_coordinated_hasNoProfitableOneShotDeviation (b : Bool) :
    monitoring.HasNoProfitableOneShotDeviation discount
      stageCert seriesCert
      (monitoring.stationaryMonitoredProfile (coordinated b)) := by
  intro who action
  show monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable
      (Profile.update (sig := monitoring.monitoredSignature)
        (monitoring.stationaryMonitoredProfile (coordinated b)) who
        (monitoring.oneShotDeviation
          (monitoring.stationaryMonitoredProfile (coordinated b)) who action))
      who (stagePayoff_abs_le_one · who) ≤
    monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable
      (monitoring.stationaryMonitoredProfile (coordinated b)) who
      (stagePayoff_abs_le_one · who)
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    coordination_integrable
    (Profile.update (sig := monitoring.monitoredSignature)
      (monitoring.stationaryMonitoredProfile (coordinated b)) who
      (monitoring.oneShotDeviation
        (monitoring.stationaryMonitoredProfile (coordinated b)) who action))
    who (stagePayoff_abs_le_one · who)]
  simp only [monitoring.currentProfile_update_oneShotDeviation]
  simp only [UtilityGame.PublicMonitoring.stationaryMonitoredProfile]
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    monitoring.afterSignal_stationaryMonitoredProfile,
    discountedPayoff_stationary_coordinated]
  rw [expect_constant]
  norm_num [discount] at ⊢
  split <;> norm_num

/-- One-shot optimality holds after every typed public history, not merely
histories in the generated law's support. -/
theorem prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory :
    monitoring.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount stageCert seriesCert prescribed := by
  intro t history
  cases t with
  | zero =>
      exact prescribed_hasNoProfitableOneShotDeviation
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
      stageCert seriesCert
      (monitoring.after prescribed zeroProbabilityHistory) :=
  prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory
    2 zeroProbabilityHistory

/-- The generic one-shot-deviation principle specializes to this finite noisy
fixture at discount one half. -/
theorem prescribed_ppe_iff_noProfitableOneShotDeviation :
    monitoring.IsPerfectPublicEquilibrium discount
        stageCert seriesCert prescribed ↔
      monitoring.HasNoProfitableOneShotDeviationAfterEveryHistory discount
        stageCert seriesCert prescribed := by
  exact monitoring.isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    (by norm_num [discount]) (by norm_num [discount]) prescribed
    coordination_integrable coordination_stagePayoff_bounded

/-- The noisy branch-dependent prescribed profile is an actual PPE. -/
theorem prescribed_isPerfectPublicEquilibrium :
    monitoring.IsPerfectPublicEquilibrium discount
      stageCert seriesCert prescribed :=
  prescribed_ppe_iff_noProfitableOneShotDeviation.mpr
    prescribed_hasNoProfitableOneShotDeviationAfterEveryHistory

/-- The canonical exact-to-approximate Nash bridge lifts pointwise through
every public continuation. -/
theorem prescribed_isεPerfectPublicEquilibrium {ε : ℝ} (hε : 0 ≤ ε) :
    monitoring.IsεPerfectPublicEquilibrium discount
      stageCert seriesCert ε prescribed :=
  UtilityGame.PublicMonitoring.IsPerfectPublicEquilibrium.isεPerfectPublicEquilibrium
    monitoring discount stageCert seriesCert prescribed_isPerfectPublicEquilibrium hε

/-! A stationary mismatched profile supplies the converse regression: player
zero can coordinate immediately, while the continuation stays mismatched. -/

def mismatched : Profile coordination.form.sig
  | 0 => false
  | 1 => true

def mismatchedProfile : monitoring.MonitoredProfile :=
  monitoring.stationaryMonitoredProfile mismatched

@[simp]
theorem discountedPayoff_mismatchedProfile (who : Fin 2) :
    monitoring.discountedPayoffOfBounded (discount := discount)
        (by norm_num [discount]) (by norm_num [discount])
        coordination_integrable mismatchedProfile who
        (stagePayoff_abs_le_one · who) = 0 := by
  unfold mismatchedProfile
  show monitoring.discountedPayoff discount
    (monitoring.stationaryMonitoredProfile mismatched) who _ _ = 0
  rw [monitoring.discountedPayoff_stationaryMonitoredProfile
    (discount := discount)
    (by norm_num [discount]) (by norm_num [discount])
    mismatched who (coordination_integrable who _)]
  fin_cases who <;> simp [mismatched, stagePayoff_eq_agreement]

@[simp]
theorem afterSignal_mismatchedProfile (signal : Bool) :
    monitoring.afterSignal mismatchedProfile signal = mismatchedProfile := by
  simp [mismatchedProfile]

/-- Player zero's one-shot switch to `true` is strictly profitable. -/
theorem mismatchedProfile_has_profitable_oneShotDeviation :
    ¬ monitoring.HasNoProfitableOneShotDeviation discount
      stageCert seriesCert mismatchedProfile := by
  intro hno
  have hdeviation :
      monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable
      (Profile.update (sig := monitoring.monitoredSignature)
        mismatchedProfile 0
        (monitoring.oneShotDeviation mismatchedProfile 0 true)) 0
      (stagePayoff_abs_le_one · 0) ≤
    monitoring.discountedPayoffOfBounded (discount := discount)
      (by norm_num [discount]) (by norm_num [discount])
      coordination_integrable mismatchedProfile 0
      (stagePayoff_abs_le_one · 0) := hno 0 true
  rw [monitoring.discountedPayoff_eq_head_add_expected
    (by norm_num [discount]) (by norm_num [discount])
    coordination_integrable
    (Profile.update (sig := monitoring.monitoredSignature) mismatchedProfile 0
      (monitoring.oneShotDeviation mismatchedProfile 0 true)) 0
    (stagePayoff_abs_le_one · 0)] at hdeviation
  simp only [monitoring.currentProfile_update_oneShotDeviation] at hdeviation
  simp_rw [monitoring.afterSignal_update_oneShotDeviation,
    afterSignal_mismatchedProfile, discountedPayoff_mismatchedProfile] at hdeviation
  norm_num [discount, mismatchedProfile, mismatched, stagePayoff_eq_agreement,
    UtilityGame.PublicMonitoring.stationaryMonitoredProfile, Profile.update] at hdeviation
  rw [expect_constant] at hdeviation
  norm_num at hdeviation

/-- The profitable root deviation falsifies perfect public equilibrium. -/
theorem mismatchedProfile_not_isPerfectPublicEquilibrium :
    ¬ monitoring.IsPerfectPublicEquilibrium discount
      stageCert seriesCert mismatchedProfile := by
  intro hppe
  apply mismatchedProfile_has_profitable_oneShotDeviation
  have hall := hppe.hasNoProfitableOneShotDeviationAfterEveryHistory
  exact hall 0 (fun k => k.elim0)

end GameTheory.Tests.MonitoringEquilibrium
