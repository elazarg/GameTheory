/-
# Discounted public monitoring

Normalized discounted payoffs and equilibrium predicates for finite public
monitoring. Equilibria and deviations range over public strategies only;
private-action or private-randomization histories are outside this model. The
one-shot-deviation sufficiency argument lives separately.
-/

import GameTheory.Repeated.MonitoringPayoff
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section

open scoped BigOperators

namespace GameTheory

open Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- The deterministic strategic form whose outcomes are monitored profiles. -/
@[reducible]
def monitoredForm (M : G.PublicMonitoring) : GameForm ι where
  sig := M.monitoredSignature
  play profile := FinDist.pure profile

/-- Normalized discounted expected payoff under public monitoring. -/
def discountedPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : M.MonitoredProfile) (who : ι) : ℝ :=
  (1 - discount) * ∑' t : ℕ, discount ^ t * M.monitoredStagePayoff profile t who

/-- Discounted payoff after a specified, possibly off-path, public history. -/
def discountedContinuationPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : M.MonitoredProfile) {t : ℕ} (history : M.SignalHistory t)
    (who : ι) : ℝ :=
  M.discountedPayoff discount (M.after profile history) who

/-- Discounted utility on the canonical monitored strategic form. -/
def discountedUtility (M : G.PublicMonitoring) (discount : ℝ) :
    Utility M.monitoredSignature :=
  fun profile who => M.discountedPayoff discount profile who

theorem summable_discounted_monitoredStagePayoff_of_abs_bound
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {profile : M.MonitoredProfile} (who : ι)
    (hbound : ∀ t, |M.monitoredStagePayoff profile t who| ≤ bound) :
    Summable fun t : ℕ => discount ^ t * M.monitoredStagePayoff profile t who := by
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |discount ^ t * M.monitoredStagePayoff profile t who| =
        discount ^ t * |M.monitoredStagePayoff profile t who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 t)]
    _ ≤ discount ^ t * bound :=
      mul_le_mul_of_nonneg_left (hbound t) (pow_nonneg hdiscount0 t)
    _ = bound * discount ^ t := by ring

theorem discountedPayoff_le_of_forall_monitoredStagePayoff_le
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {first second : M.MonitoredProfile} (who : ι)
    (hfirst : ∀ t, |M.monitoredStagePayoff first t who| ≤ bound)
    (hsecond : ∀ t, |M.monitoredStagePayoff second t who| ≤ bound)
    (hle : ∀ t, M.monitoredStagePayoff first t who ≤
      M.monitoredStagePayoff second t who) :
    M.discountedPayoff discount first who ≤ M.discountedPayoff discount second who := by
  have hsFirst := M.summable_discounted_monitoredStagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hfirst
  have hsSecond := M.summable_discounted_monitoredStagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hsecond
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hdiscount1.le)
  exact hsFirst.tsum_le_tsum
    (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hdiscount0 t)) hsSecond

theorem abs_discountedPayoff_le_of_abs_stagePayoff_bound
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : M.MonitoredProfile) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    |M.discountedPayoff discount profile who| ≤ bound := by
  have hstage : ∀ t, |M.monitoredStagePayoff profile t who| ≤ bound :=
    fun t => M.abs_monitoredStagePayoff_le profile t who hbound
  have habs : Summable fun t : ℕ =>
      |discount ^ t * M.monitoredStagePayoff profile t who| := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound)
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), abs_mul,
      abs_of_nonneg (pow_nonneg hdiscount0 t)]
    calc
      discount ^ t * |M.monitoredStagePayoff profile t who| ≤ discount ^ t * bound :=
        mul_le_mul_of_nonneg_left (hstage t) (pow_nonneg hdiscount0 t)
      _ = bound * discount ^ t := by ring
  have hnorm : Summable fun t : ℕ =>
      ‖discount ^ t * M.monitoredStagePayoff profile t who‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  have hne : 1 - discount ≠ 0 := by linarith
  unfold discountedPayoff
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hdiscount1.le)]
  calc
    (1 - discount) * |∑' t : ℕ, discount ^ t * M.monitoredStagePayoff profile t who| ≤
        (1 - discount) * ∑' t : ℕ, |discount ^ t * M.monitoredStagePayoff profile t who| := by
      gcongr
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ (1 - discount) * ∑' t : ℕ, bound * discount ^ t := by
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hdiscount1.le)
      exact habs.tsum_le_tsum (fun t => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 t)]
        calc
          discount ^ t * |M.monitoredStagePayoff profile t who| ≤ discount ^ t * bound :=
            mul_le_mul_of_nonneg_left (hstage t) (pow_nonneg hdiscount0 t)
          _ = bound * discount ^ t := by ring) hgeom
    _ = bound := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hdiscount0 hdiscount1]
      calc
        (1 - discount) * (bound * (1 - discount)⁻¹) =
            bound * ((1 - discount) * (1 - discount)⁻¹) := by ring
        _ = bound := by rw [mul_inv_cancel₀ hne, mul_one]

private theorem tsum_expect_of_abs_bound {α : Type*} (law : FinDist α)
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (f : α → ℕ → ℝ) (hbound : ∀ a n, |f a n| ≤ bound) :
    (∑' n : ℕ, discount ^ n * law.expect (fun a => f a n)) =
      law.expect (fun a => ∑' n : ℕ, discount ^ n * f a n) := by
  let support := law.supportFinset
  have hs (a : α) : Summable fun n : ℕ => discount ^ n * f a n := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 n)]
    calc
      discount ^ n * |f a n| ≤ discount ^ n * bound :=
        mul_le_mul_of_nonneg_left (hbound a n) (pow_nonneg hdiscount0 n)
      _ = bound * discount ^ n := by ring
  calc
    (∑' n : ℕ, discount ^ n * law.expect (fun a => f a n)) =
        ∑' n : ℕ, ∑ a ∈ support, law.prob a * (discount ^ n * f a n) := by
      apply tsum_congr
      intro n
      rw [FinDist.expect_eq_sum_support]
      dsimp [support]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ a ∈ support, ∑' n : ℕ, law.prob a * (discount ^ n * f a n) := by
      apply Summable.tsum_finsetSum
      intro a ha
      exact (hs a).mul_left _
    _ = law.expect (fun a => ∑' n : ℕ, discount ^ n * f a n) := by
      rw [FinDist.expect_eq_sum_support]
      dsimp [support]
      apply Finset.sum_congr rfl
      intro a ha
      rw [tsum_mul_left]

theorem discountedPayoff_eq_head_add_expected
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : M.MonitoredProfile) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    M.discountedPayoff discount profile who =
      (1 - discount) * G.stagePayoff (fun i => profile i 0 (fun k => k.elim0)) who +
        discount * (M.signalLaw fun i => profile i 0 (fun k => k.elim0)).expect
          (fun signal => M.discountedPayoff discount (M.afterSignal profile signal) who) := by
  let law := M.signalLaw fun i => profile i 0 (fun k => k.elim0)
  let term : ℕ → ℝ := fun n => discount ^ n * M.monitoredStagePayoff profile n who
  have hstage : ∀ n, |M.monitoredStagePayoff profile n who| ≤ bound :=
    fun n => M.abs_monitoredStagePayoff_le profile n who hbound
  have hs : Summable term := by
    simpa [term] using M.summable_discounted_monitoredStagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who hstage
  have hsplit : term 0 + (∑' n : ℕ, term (n + 1)) = ∑' n : ℕ, term n := by
    simpa using hs.sum_add_tsum_nat_add 1
  have hinterchange :
      (∑' n : ℕ, discount ^ n * M.monitoredStagePayoff profile (n + 1) who) =
        law.expect (fun signal => ∑' n : ℕ,
          discount ^ n * M.monitoredStagePayoff (M.afterSignal profile signal) n who) := by
    calc
      (∑' n : ℕ, discount ^ n * M.monitoredStagePayoff profile (n + 1) who) =
          ∑' n : ℕ, discount ^ n * law.expect (fun signal =>
            M.monitoredStagePayoff (M.afterSignal profile signal) n who) := by
        apply tsum_congr
        intro n
        rw [M.monitoredStagePayoff_succ_eq_expect_afterSignal profile n who]
      _ = _ := by
        apply tsum_expect_of_abs_bound law hdiscount0 hdiscount1
        intro signal n
        exact M.abs_monitoredStagePayoff_le (M.afterSignal profile signal) n who hbound
  have htail : (∑' n : ℕ, term (n + 1)) =
      discount * law.expect (fun signal => ∑' n : ℕ,
        discount ^ n * M.monitoredStagePayoff (M.afterSignal profile signal) n who) := by
    calc
      (∑' n : ℕ, term (n + 1)) =
          ∑' n : ℕ, discount * (discount ^ n *
            M.monitoredStagePayoff profile (n + 1) who) := by
        apply tsum_congr
        intro n
        dsimp [term]
        rw [pow_succ]
        ring
      _ = discount * ∑' n : ℕ, discount ^ n *
          M.monitoredStagePayoff profile (n + 1) who := by rw [tsum_mul_left]
      _ = _ := by rw [hinterchange]
  unfold discountedPayoff
  rw [show (∑' n : ℕ,
      discount ^ n * M.monitoredStagePayoff profile n who) =
      ∑' n : ℕ, term n by rfl]
  rw [← hsplit, htail]
  simp only [term, pow_zero, one_mul, M.monitoredStagePayoff_zero]
  rw [FinDist.expect_smul]
  dsimp [law]
  ring

theorem discountedContinuationPayoff_eq_head_add_expected
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : M.MonitoredProfile) {t : ℕ} (history : M.SignalHistory t) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig, |G.stagePayoff stage who| ≤ bound) :
    M.discountedContinuationPayoff discount profile history who =
      (1 - discount) * G.stagePayoff (fun i => M.after profile history i 0 (fun k => k.elim0)) who +
        discount * (M.signalLaw fun i => M.after profile history i 0 (fun k => k.elim0)).expect
          (fun signal => M.discountedContinuationPayoff discount profile
            (Fin.snoc history signal) who) := by
  unfold discountedContinuationPayoff
  simpa only [← M.afterSignal_after profile history] using
    M.discountedPayoff_eq_head_add_expected hdiscount0 hdiscount1
      (M.after profile history) who hbound

@[simp]
theorem discountedPayoff_stationaryMonitoredProfile (M : G.PublicMonitoring)
    {discount : ℝ} (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (who : ι) :
    M.discountedPayoff discount (M.stationaryMonitoredProfile profile) who =
      G.stagePayoff profile who := by
  have hne : 1 - discount ≠ 0 := by linarith
  simp [discountedPayoff, tsum_mul_right,
    tsum_geometric_of_lt_one hdiscount0 hdiscount1, hne]

/-- Exact discounted Nash equilibrium in public strategies. -/
def IsDiscountedPublicNash (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : M.MonitoredProfile) : Prop :=
  IsNash M.monitoredForm (euPreference (M.discountedUtility discount)) profile

/-- Discounted public Nash equilibrium allowing an additive payoff loss. -/
def IsεDiscountedPublicNash (M : G.PublicMonitoring) [DecidableEq ι]
    (discount ε : ℝ) (profile : M.MonitoredProfile) : Prop :=
  IsNash M.monitoredForm (euPreferenceWithin ε (M.discountedUtility discount)) profile

theorem isDiscountedPublicNash_iff (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : M.MonitoredProfile) :
    M.IsDiscountedPublicNash discount profile ↔ ∀ who deviation,
      M.discountedPayoff discount (Profile.update (sig := M.monitoredSignature)
        profile who deviation) who ≤ M.discountedPayoff discount profile who := by
  rw [IsDiscountedPublicNash, isNash_iff]
  simp [monitoredForm, discountedUtility]

theorem isεDiscountedPublicNash_iff (M : G.PublicMonitoring) [DecidableEq ι]
    (discount ε : ℝ) (profile : M.MonitoredProfile) :
    M.IsεDiscountedPublicNash discount ε profile ↔ ∀ who deviation,
      M.discountedPayoff discount (Profile.update (sig := M.monitoredSignature)
        profile who deviation) who ≤ M.discountedPayoff discount profile who + ε := by
  rw [IsεDiscountedPublicNash, isNash_iff]
  simp [monitoredForm, discountedUtility]

def IsPerfectPublicEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t), M.IsDiscountedPublicNash discount (M.after profile history)

def IsεPerfectPublicEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (discount ε : ℝ) (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t), M.IsεDiscountedPublicNash discount ε (M.after profile history)

def HasNoProfitableOneShotDeviation (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : M.MonitoredProfile) : Prop :=
  ∀ who action, M.discountedPayoff discount
    (Profile.update (sig := M.monitoredSignature) profile who
      (M.oneShotDeviation profile who action)) who ≤ M.discountedPayoff discount profile who

def HasNoProfitableOneShotDeviationAfterEveryHistory
    (M : G.PublicMonitoring) [DecidableEq ι] (discount : ℝ)
    (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t),
    M.HasNoProfitableOneShotDeviation discount (M.after profile history)

theorem IsDiscountedPublicNash.hasNoProfitableOneShotDeviation
    {M : G.PublicMonitoring} [DecidableEq ι] {discount : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsDiscountedPublicNash discount profile) :
    M.HasNoProfitableOneShotDeviation discount profile := by
  rw [isDiscountedPublicNash_iff] at h
  intro who action
  exact h who (M.oneShotDeviation profile who action)

theorem IsPerfectPublicEquilibrium.hasNoProfitableOneShotDeviationAfterEveryHistory
    {M : G.PublicMonitoring} [DecidableEq ι] {discount : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount profile) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile := by
  intro t history
  exact (h t history).hasNoProfitableOneShotDeviation

theorem IsPerfectPublicEquilibrium.afterSignal {M : G.PublicMonitoring} [DecidableEq ι]
    {discount : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount profile) (signal : M.Signal) :
    M.IsPerfectPublicEquilibrium discount (M.afterSignal profile signal) := by
  intro t history
  rw [M.after_afterSignal]
  exact h (t + 1) (Fin.cons signal history)

theorem HasNoProfitableOneShotDeviationAfterEveryHistory.afterSignal
    {M : G.PublicMonitoring} [DecidableEq ι] {discount : ℝ} {profile : M.MonitoredProfile}
    (h : M.HasNoProfitableOneShotDeviationAfterEveryHistory discount profile)
    (signal : M.Signal) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory discount (M.afterSignal profile signal) := by
  intro t history
  rw [M.after_afterSignal]
  exact h (t + 1) (Fin.cons signal history)

end UtilityGame.PublicMonitoring

end GameTheory
