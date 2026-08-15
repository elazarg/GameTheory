/-
# The one-shot-deviation principle for public monitoring

For bounded stage payoffs and `0 ≤ discount < 1`, sequential optimality
against one-period public deviations is equivalent to perfect-public
equilibrium among public strategies.  The proof first controls finite
truncations of an arbitrary deviation and then uses dominated convergence of
the ordinary real payoff series.  No probability law on infinite histories is
constructed.
-/

import GameTheory.Repeated.MonitoringDiscounted
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section

open scoped BigOperators

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- Sequential one-shot optimality is inherited after every finite public
history, including histories having zero probability. -/
theorem HasNoProfitableOneShotDeviationAfterEveryHistory.after
    {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} {profile : M.MonitoredProfile}
    (h : M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile)
    {t : ℕ} (history : M.SignalHistory t) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory discount
      (M.after profile history) := by
  intro n future
  rw [M.after_after]
  exact h (t + n) (Fin.append history future)

/-- Exact one-shot optimality rules out every finite truncation of an
arbitrary public deviation. -/
theorem truncatedDeviation_discountedPayoff_le_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hlocal :
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile)
    (who : ι) {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound)
    (deviation : M.MonitoredStrategy who) (count : ℕ) :
    M.discountedPayoff discount
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count)) who ≤
      M.discountedPayoff discount profile who := by
  induction count generalizing profile deviation with
  | zero =>
      simp
  | succ count ih =>
      let action : G.form.sig.Strategy who :=
        deviation 0 (fun k => k.elim0)
      let truncated : M.MonitoredProfile :=
        Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation (count + 1))
      let oneShot : M.MonitoredProfile :=
        Profile.update (sig := M.monitoredSignature) profile who
          (M.oneShotDeviation profile who action)
      have hroot :
          (fun i => truncated i 0 (fun k => k.elim0)) =
            (fun i => oneShot i 0 (fun k => k.elim0)) := by
        funext i
        by_cases hi : i = who
        · subst hi
          simp [truncated, oneShot, action]
        · simp [truncated, oneShot, Profile.update_of_ne _ _ hi]
      have htruncatedContinuation (signal : M.Signal) :
          M.afterSignal truncated signal =
            Profile.update (sig := M.monitoredSignature)
              (M.afterSignal profile signal) who
              (M.truncatedDeviation (M.afterSignal profile signal) who
                (M.strategyAfterSignal deviation signal) count) := by
        dsimp only [truncated]
        rw [M.afterSignal_update,
          M.strategyAfterSignal_truncatedDeviation_succ]
      have honeShotContinuation (signal : M.Signal) :
          M.afterSignal oneShot signal = M.afterSignal profile signal := by
        simp [oneShot]
      have hcontinuation (signal : M.Signal) :
          M.discountedPayoff discount
              (M.afterSignal truncated signal) who ≤
            M.discountedPayoff discount
              (M.afterSignal oneShot signal) who := by
        rw [htruncatedContinuation signal, honeShotContinuation signal]
        exact ih (hlocal.afterSignal signal)
          (M.strategyAfterSignal deviation signal)
      have hexpect :
          (M.signalLaw
              (fun i => truncated i 0 (fun k => k.elim0))).expect
              (fun signal => M.discountedPayoff discount
                (M.afterSignal truncated signal) who) ≤
            (M.signalLaw
              (fun i => truncated i 0 (fun k => k.elim0))).expect
              (fun signal => M.discountedPayoff discount
                (M.afterSignal oneShot signal) who) :=
        FinDist.expect_mono fun signal _ => hcontinuation signal
      have hfinite :
          M.discountedPayoff discount truncated who ≤
            M.discountedPayoff discount oneShot who := by
        calc
          M.discountedPayoff discount truncated who =
              (1 - discount) * G.stagePayoff
                  (fun i => truncated i 0 (fun k => k.elim0)) who +
                discount *
                  (M.signalLaw
                    (fun i => truncated i 0 (fun k => k.elim0))).expect
                    (fun signal => M.discountedPayoff discount
                      (M.afterSignal truncated signal) who) :=
            M.discountedPayoff_eq_head_add_expected
              hdiscount0 hdiscount1 truncated who hbound
          _ ≤ (1 - discount) * G.stagePayoff
                  (fun i => truncated i 0 (fun k => k.elim0)) who +
                discount *
                  (M.signalLaw
                    (fun i => truncated i 0 (fun k => k.elim0))).expect
                    (fun signal => M.discountedPayoff discount
                      (M.afterSignal oneShot signal) who) := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hexpect hdiscount0) _
          _ = M.discountedPayoff discount oneShot who := by
            rw [hroot]
            symm
            exact M.discountedPayoff_eq_head_add_expected
              hdiscount0 hdiscount1 oneShot who hbound
      show M.discountedPayoff discount truncated who ≤ _
      calc
        M.discountedPayoff discount truncated who ≤
            M.discountedPayoff discount oneShot who := hfinite
        _ ≤ M.discountedPayoff discount profile who := by
          apply hlocal 0 (fun k => k.elim0)

/-- Discounted payoffs of finite truncations converge to the payoff of the
full public deviation. -/
theorem tendsto_discountedPayoff_update_truncatedDeviation_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (profile : M.MonitoredProfile)
    (who : ι) (deviation : M.MonitoredStrategy who) {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    Filter.Tendsto
      (fun count => M.discountedPayoff discount
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count)) who)
      Filter.atTop
      (nhds (M.discountedPayoff discount
        (Profile.update (sig := M.monitoredSignature) profile who deviation)
        who)) := by
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  have hterm (t : ℕ) :
      Filter.Tendsto
        (fun count => discount ^ t * M.monitoredStagePayoff
          (Profile.update (sig := M.monitoredSignature) profile who
            (M.truncatedDeviation profile who deviation count)) t who)
        Filter.atTop
        (nhds (discount ^ t * M.monitoredStagePayoff
          (Profile.update (sig := M.monitoredSignature) profile who deviation)
          t who)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop t] with count ht
    rw [M.monitoredStagePayoff_update_truncatedDeviation_eq_of_lt
      profile who deviation ht]
  have hdom : ∀ count t,
      ‖discount ^ t * M.monitoredStagePayoff
          (Profile.update (sig := M.monitoredSignature) profile who
            (M.truncatedDeviation profile who deviation count)) t who‖ ≤
        bound * discount ^ t := by
    intro count t
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hdiscount0 t)]
    calc
      discount ^ t * |M.monitoredStagePayoff
          (Profile.update (sig := M.monitoredSignature) profile who
            (M.truncatedDeviation profile who deviation count)) t who| ≤
          discount ^ t * bound := by
        exact mul_le_mul_of_nonneg_left
          (M.abs_monitoredStagePayoff_le _ t who hbound)
          (pow_nonneg hdiscount0 t)
      _ = bound * discount ^ t := by ring
  have hsum := tendsto_tsum_of_dominated_convergence hgeom hterm
    (Filter.Eventually.of_forall hdom)
  simpa only [discountedPayoff] using
    (tendsto_const_nhds.mul hsum :
      Filter.Tendsto
        (fun count => (1 - discount) * ∑' t : ℕ,
          discount ^ t * M.monitoredStagePayoff
            (Profile.update (sig := M.monitoredSignature) profile who
              (M.truncatedDeviation profile who deviation count)) t who)
        Filter.atTop
        (nhds ((1 - discount) * ∑' t : ℕ,
          discount ^ t * M.monitoredStagePayoff
            (Profile.update (sig := M.monitoredSignature) profile who
              deviation) t who)))

/-- Sequential one-shot optimality rules out every public deviation at the
current continuation. -/
theorem HasNoProfitableOneShotDeviationAfterEveryHistory.isDiscountedPublicNash_of_bounded
    {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hlocal :
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    M.IsDiscountedPublicNash discount profile := by
  rw [M.isDiscountedPublicNash_iff]
  intro who deviation
  obtain ⟨bound, hwho⟩ := hbound who
  have hlimit :=
    M.tendsto_discountedPayoff_update_truncatedDeviation_of_bounded
      hdiscount0 hdiscount1 profile who deviation hwho
  apply le_of_tendsto' hlimit
  intro count
  exact M.truncatedDeviation_discountedPayoff_le_of_bounded
    hdiscount0 hdiscount1 hlocal who hwho deviation count

/-- In a bounded discounted game, sequential one-shot optimality implies PPE
among public strategies. -/
theorem HasNoProfitableOneShotDeviationAfterEveryHistory.isPerfectPublicEquilibrium_of_bounded
    {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hlocal :
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    M.IsPerfectPublicEquilibrium discount profile := by
  intro t history
  exact (hlocal.after history).isDiscountedPublicNash_of_bounded
    hdiscount0 hdiscount1 hbound

/-- **One-shot-deviation principle.** For bounded stage payoffs, a public
strategy profile is a perfect-public equilibrium exactly when no player has a
profitable one-period deviation after any finite public history. -/
theorem isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (profile : M.MonitoredProfile)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    M.IsPerfectPublicEquilibrium discount profile ↔
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile := by
  constructor
  · exact IsPerfectPublicEquilibrium.hasNoProfitableOneShotDeviationAfterEveryHistory
  · intro hlocal
    exact hlocal.isPerfectPublicEquilibrium_of_bounded
      hdiscount0 hdiscount1 hbound

end UtilityGame.PublicMonitoring

end GameTheory
