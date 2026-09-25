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
    {discount : ℝ}
    (hstage : ∀ profile : M.MonitoredProfile, ∀ who t,
      M.MonitoredStageIntegrable profile t who)
    (hsum : ∀ profile : M.MonitoredProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        M.monitoredStagePayoff profile t who (hstage profile who t))
    {profile : M.MonitoredProfile}
    (h : M.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount hstage hsum profile)
    {t : ℕ} (history : M.SignalHistory t) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount hstage hsum (M.after profile history) := by
  intro n future
  rw [M.after_after]
  exact h (t + n) (Fin.append history future)

/-- Exact one-shot optimality rules out every finite truncation of an
arbitrary public deviation. -/
theorem truncatedDeviation_discountedPayoff_le_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hG : G.form.HasIntegrableUtility G.utility)
    (who : ι) {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound)
    (hlocal : ∀ t (history : M.SignalHistory t)
      (action : G.form.sig.Strategy who),
      M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
          (Profile.update (sig := M.monitoredSignature)
            (M.after profile history) who
            (M.oneShotDeviation (M.after profile history) who action))
          who hbound ≤
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
          (M.after profile history) who hbound)
    (deviation : M.MonitoredStrategy who) (count : ℕ) :
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count)) who hbound ≤
      M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        profile who hbound := by
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
          M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              (M.afterSignal truncated signal) who hbound ≤
            M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              (M.afterSignal oneShot signal) who hbound := by
        rw [htruncatedContinuation signal, honeShotContinuation signal]
        exact ih (profile := M.afterSignal profile signal)
          (fun n history action => by
            simpa [M.after_afterSignal] using
              hlocal (n + 1) (Fin.cons signal history) action)
          (M.strategyAfterSignal deviation signal)
      have hafterOneShot : PayoffIntegrable
          (M.signalLaw (fun i => truncated i 0 (fun k => k.elim0)))
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal oneShot signal) who hbound) := by
        rw [hroot]
        exact M.discountedAfterSignal_integrable_of_expected_bound
          hdiscount0 hdiscount1 hG oneShot who hbound
      have hexpect :
          expect (M.signalLaw
            (fun i => truncated i 0 (fun k => k.elim0)))
            (fun signal => M.discountedPayoffOfBounded
              hdiscount0 hdiscount1 hG
              (M.afterSignal truncated signal) who hbound)
            (M.discountedAfterSignal_integrable_of_expected_bound
              hdiscount0 hdiscount1 hG truncated who hbound) ≤
          expect (M.signalLaw
            (fun i => truncated i 0 (fun k => k.elim0)))
            (fun signal => M.discountedPayoffOfBounded
              hdiscount0 hdiscount1 hG
              (M.afterSignal oneShot signal) who hbound)
            hafterOneShot :=
        expect_mono (fun signal _ => hcontinuation signal) _ _
      have hfinite :
          M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              truncated who hbound ≤
            M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              oneShot who hbound := by
        calc
          M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              truncated who hbound =
              (1 - discount) * G.stagePayoff
                  (fun i => truncated i 0 (fun k => k.elim0)) who
                  (hG who _) +
                discount * expect
                  (M.signalLaw
                    (fun i => truncated i 0 (fun k => k.elim0)))
                  (fun signal => M.discountedPayoffOfBounded
                    hdiscount0 hdiscount1 hG
                    (M.afterSignal truncated signal) who hbound)
                  (M.discountedAfterSignal_integrable_of_expected_bound
                    hdiscount0 hdiscount1 hG truncated who hbound) :=
            M.discountedPayoff_eq_head_add_expected
              hdiscount0 hdiscount1 hG truncated who hbound
          _ ≤ (1 - discount) * G.stagePayoff
                  (fun i => truncated i 0 (fun k => k.elim0)) who
                  (hG who _) +
                discount * expect
                  (M.signalLaw
                    (fun i => truncated i 0 (fun k => k.elim0)))
                  (fun signal => M.discountedPayoffOfBounded
                    hdiscount0 hdiscount1 hG
                    (M.afterSignal oneShot signal) who hbound)
                  hafterOneShot := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hexpect hdiscount0) _
          _ = M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              oneShot who hbound := by
            simpa only [hroot] using
              (M.discountedPayoff_eq_head_add_expected
                hdiscount0 hdiscount1 hG oneShot who hbound).symm
      show M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        truncated who hbound ≤ _
      calc
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
            truncated who hbound ≤
            M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              oneShot who hbound := hfinite
        _ ≤ M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
              profile who hbound := by
          simpa [oneShot, after, afterSignals] using
            hlocal 0 (fun k => k.elim0) action

/-- Discounted payoffs of finite truncations converge to the payoff of the
full public deviation. -/
theorem tendsto_discountedPayoff_update_truncatedDeviation_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (profile : M.MonitoredProfile)
    (hG : G.form.HasIntegrableUtility G.utility)
    (who : ι) (deviation : M.MonitoredStrategy who) {bound : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    Filter.Tendsto
      (fun count => M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        (Profile.update (sig := M.monitoredSignature) profile who
          (M.truncatedDeviation profile who deviation count)) who hbound)
      Filter.atTop
      (nhds (M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        (Profile.update (sig := M.monitoredSignature) profile who deviation)
        who hbound)) := by
  let truncated (count : ℕ) : M.MonitoredProfile :=
    Profile.update (sig := M.monitoredSignature) profile who
      (M.truncatedDeviation profile who deviation count)
  let full : M.MonitoredProfile :=
    Profile.update (sig := M.monitoredSignature) profile who deviation
  let cert (p : M.MonitoredProfile) (t : ℕ) :
      M.MonitoredStageIntegrable p t who :=
    M.monitoredStageIntegrable_of_expected_bound p t who hG hbound
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  have hterm (t : ℕ) :
      Filter.Tendsto
        (fun count => discount ^ t * M.monitoredStagePayoff
          (truncated count) t who (cert (truncated count) t))
        Filter.atTop
        (nhds (discount ^ t * M.monitoredStagePayoff
          full t who (cert full t))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop t] with count ht
    rw [M.monitoredStagePayoff_update_truncatedDeviation_eq_of_lt
      profile who deviation ht (cert (truncated count) t) (cert full t)]
  have hdom : ∀ count t,
      ‖discount ^ t * M.monitoredStagePayoff
          (truncated count) t who (cert (truncated count) t)‖ ≤
        bound * discount ^ t := by
    intro count t
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hdiscount0 t)]
    calc
      discount ^ t * |M.monitoredStagePayoff
          (truncated count) t who (cert (truncated count) t)| ≤
          discount ^ t * bound := by
        exact mul_le_mul_of_nonneg_left
          (M.abs_monitoredStagePayoff_le _ t who
            (cert (truncated count) t)
            (fun history _ =>
              hbound (fun i => truncated count i t history)))
          (pow_nonneg hdiscount0 t)
      _ = bound * discount ^ t := by ring
  have hsum := tendsto_tsum_of_dominated_convergence hgeom hterm
    (Filter.Eventually.of_forall hdom)
  simpa only [discountedPayoffOfBounded, discountedPayoff,
    GameTheory.Math.normalizedDiscountedSum, truncated, full, cert] using
    (tendsto_const_nhds.mul hsum :
      Filter.Tendsto
        (fun count => (1 - discount) * ∑' t : ℕ,
          discount ^ t * M.monitoredStagePayoff
            (truncated count) t who (cert (truncated count) t))
        Filter.atTop
        (nhds ((1 - discount) * ∑' t : ℕ,
          discount ^ t * M.monitoredStagePayoff
            full t who (cert full t))))

/-- Sequential one-shot optimality rules out every public deviation at the
current continuation. -/
theorem HasNoProfitableOneShotDeviationAfterEveryHistory.isDiscountedPublicNash_of_bounded
    {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound)
    (hlocal :
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound) profile) :
    M.IsDiscountedPublicNash discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound) profile := by
  rw [M.isDiscountedPublicNash_iff]
  intro who deviation
  obtain ⟨bound, hwho⟩ := hbound who
  have hlimit :=
    M.tendsto_discountedPayoff_update_truncatedDeviation_of_bounded
      hdiscount0 hdiscount1 profile hG who deviation hwho
  apply le_of_tendsto' hlimit
  intro count
  apply M.truncatedDeviation_discountedPayoff_le_of_bounded
    hdiscount0 hdiscount1 hG who hwho
  · intro t history action
    simpa [HasNoProfitableOneShotDeviation, discountedUtility,
      discountedPayoffOfBounded] using
      hlocal t history who action

/-- In a bounded discounted game, sequential one-shot optimality implies PPE
among public strategies. -/
theorem HasNoProfitableOneShotDeviationAfterEveryHistory.isPerfectPublicEquilibrium_of_bounded
    {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : M.MonitoredProfile}
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound)
    (hlocal :
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound) profile) :
    M.IsPerfectPublicEquilibrium discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound) profile := by
  intro t history
  have hafter := HasNoProfitableOneShotDeviationAfterEveryHistory.after
    (M.discountedStageIntegrableOfBounded hG hbound)
    (M.discountedSummableOfBounded
      hdiscount0 hdiscount1 hG hbound) hlocal history
  exact hafter.isDiscountedPublicNash_of_bounded
    hdiscount0 hdiscount1 hG hbound

/-- **One-shot-deviation principle.** For bounded stage payoffs, a public
strategy profile is a perfect-public equilibrium exactly when no player has a
profitable one-period deviation after any finite public history. -/
theorem isPerfectPublicEquilibrium_iff_noProfitableOneShotDeviation_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (profile : M.MonitoredProfile)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    M.IsPerfectPublicEquilibrium discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound) profile ↔
      M.HasNoProfitableOneShotDeviationAfterEveryHistory discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound) profile := by
  constructor
  · exact IsPerfectPublicEquilibrium.hasNoProfitableOneShotDeviationAfterEveryHistory
      M discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded hdiscount0 hdiscount1 hG hbound)
  · intro hlocal
    exact hlocal.isPerfectPublicEquilibrium_of_bounded
      hdiscount0 hdiscount1 hG hbound

end UtilityGame.PublicMonitoring

end GameTheory
