/-
# Discounted public monitoring

Normalized discounted payoffs and equilibrium predicates for public
monitoring. Equilibria and deviations range over public strategies only;
private-action or private-randomization histories are outside this model. The
one-shot-deviation sufficiency argument lives separately.
-/

import GameTheory.Repeated.MonitoringPayoff
import GameTheory.Math.Probability.ExpectationSeries
import GameTheory.Core.Approximate
import GameTheory.Math.Discounted
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section

open scoped BigOperators

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- The deterministic strategic form whose outcomes are monitored profiles. -/
@[reducible]
def monitoredForm (M : G.PublicMonitoring) : GameForm ι where
  sig := M.monitoredSignature
  play profile := PMF.pure profile

/-- Normalized discounted expected payoff under public monitoring. Every
stage uses its actual conditional and history-law integration guards, and the
weighted sequence of stage expectations has an explicit summability guard. -/
def discountedPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : M.MonitoredProfile) (who : ι)
    (hstage : ∀ t, M.MonitoredStageIntegrable profile t who)
    (_hsum : Summable fun t : ℕ =>
      discount ^ t * M.monitoredStagePayoff profile t who
        (hstage t)) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount fun t =>
    M.monitoredStagePayoff profile t who (hstage t)

/-- Discounted payoff after a specified, possibly off-path, public history. -/
def discountedContinuationPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : M.MonitoredProfile) {t : ℕ} (history : M.SignalHistory t)
    (who : ι)
    (hstage : ∀ n,
      M.MonitoredStageIntegrable (M.after profile history) n who)
    (hsum : Summable fun n : ℕ =>
      discount ^ n * M.monitoredStagePayoff
        (M.after profile history) n who (hstage n)) : ℝ :=
  M.discountedPayoff discount (M.after profile history) who
    hstage hsum

/-- Discounted utility on the canonical monitored strategic form. -/
def discountedUtility (M : G.PublicMonitoring) (discount : ℝ)
    (hstage : ∀ profile : M.MonitoredProfile, ∀ who t,
      M.MonitoredStageIntegrable profile t who)
    (hsum : ∀ profile : M.MonitoredProfile, ∀ who,
      Summable fun t : ℕ =>
        discount ^ t * M.monitoredStagePayoff profile t who
          (hstage profile who t)) :
    Utility M.monitoredSignature :=
  fun profile who => M.discountedPayoff discount profile who
    (hstage profile who) (hsum profile who)

theorem summable_discounted_monitoredStagePayoff_of_abs_bound
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {profile : M.MonitoredProfile} (who : ι)
    (hstage : ∀ t, M.MonitoredStageIntegrable profile t who)
    (hbound : ∀ t,
      |M.monitoredStagePayoff profile t who
        (hstage t)| ≤ bound) :
    Summable fun t : ℕ => discount ^ t *
      M.monitoredStagePayoff profile t who (hstage t) := by
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |discount ^ t * M.monitoredStagePayoff profile t who (hstage t)| =
        discount ^ t * |M.monitoredStagePayoff profile t who
          (hstage t)| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 t)]
    _ ≤ discount ^ t * bound :=
      mul_le_mul_of_nonneg_left (hbound t) (pow_nonneg hdiscount0 t)
    _ = bound * discount ^ t := by ring

theorem discountedPayoff_le_of_forall_monitoredStagePayoff_le
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {first second : M.MonitoredProfile} (who : ι)
    (hfirst : ∀ t, M.MonitoredStageIntegrable first t who)
    (hsecond : ∀ t, M.MonitoredStageIntegrable second t who)
    (hsFirst : Summable fun t : ℕ =>
      discount ^ t * M.monitoredStagePayoff first t who (hfirst t))
    (hsSecond : Summable fun t : ℕ =>
      discount ^ t * M.monitoredStagePayoff second t who (hsecond t))
    (hle : ∀ t, M.monitoredStagePayoff first t who (hfirst t) ≤
      M.monitoredStagePayoff second t who (hsecond t)) :
    M.discountedPayoff discount first who hfirst hsFirst ≤
      M.discountedPayoff discount second who hsecond hsSecond := by
  exact GameTheory.Math.normalizedDiscountedSum_le hdiscount0 hdiscount1
    hsFirst hsSecond hle

theorem abs_discountedPayoff_le_of_abs_stagePayoff_bound
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : M.MonitoredProfile) (who : ι)
    (hstage : ∀ t, M.MonitoredStageIntegrable profile t who)
    (hbound : ∀ t,
      |M.monitoredStagePayoff profile t who (hstage t)| ≤ bound) :
    let hsum := M.summable_discounted_monitoredStagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who hstage hbound
    |M.discountedPayoff discount profile who hstage hsum| ≤ bound := by
  have hsum := M.summable_discounted_monitoredStagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hstage hbound
  have hgeom : Summable fun t : ℕ => discount ^ t :=
    summable_geometric_of_lt_one hdiscount0 hdiscount1
  have hconst (c : ℝ) :
      GameTheory.Math.normalizedDiscountedSum discount (fun _ => c) = c := by
    have hne : 1 - discount ≠ 0 := by linarith
    simp [GameTheory.Math.normalizedDiscountedSum,
      tsum_mul_right, tsum_geometric_of_lt_one hdiscount0 hdiscount1, hne]
  have hlower := GameTheory.Math.normalizedDiscountedSum_le
    hdiscount0 hdiscount1 (hgeom.mul_right (-bound)) hsum
    (fun t => (abs_le.mp (hbound t)).1)
  have hupper := GameTheory.Math.normalizedDiscountedSum_le
    hdiscount0 hdiscount1 hsum (hgeom.mul_right bound)
    (fun t => (abs_le.mp (hbound t)).2)
  exact abs_le.mpr
    ⟨by simpa [discountedPayoff, hconst] using hlower,
     by simpa [discountedPayoff, hconst] using hupper⟩

/-- A bounded expected-stage specialization of the canonical discounted
payoff. The bound is on guarded stage expectations, not realized utility. -/
abbrev discountedPayoffOfBounded
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) : ℝ :=
  let hstage : ∀ t, M.MonitoredStageIntegrable profile t who :=
    fun t => M.monitoredStageIntegrable_of_expected_bound
      profile t who hG hbound
  M.discountedPayoff discount profile who hstage
    (M.summable_discounted_monitoredStagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who hstage (fun t =>
        M.abs_monitoredStagePayoff_le profile t who (hstage t)
          (fun history _ =>
            hbound (fun i => profile i t history))))

/-- Total monitored utility when every stage outcome is integrable and each
player's expected stage values have a uniform bound. -/
abbrev discountedUtilityOfBounded
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    Utility M.monitoredSignature :=
  fun profile who =>
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
      profile who (hbound who).choose_spec

/-- Actual monitored-stage integration supplied by a bound on each player's
guarded expected stage payoff. -/
abbrev discountedStageIntegrableOfBounded
    (M : G.PublicMonitoring)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    ∀ profile : M.MonitoredProfile, ∀ who t,
      M.MonitoredStageIntegrable profile t who :=
  fun profile who t =>
    M.monitoredStageIntegrable_of_expected_bound
      profile t who hG (hbound who).choose_spec

/-- Actual weighted-series summability supplied by the same expected-stage
bounds, for every monitored profile and player. -/
abbrev discountedSummableOfBounded
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    ∀ profile : M.MonitoredProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        M.monitoredStagePayoff profile t who
          (M.discountedStageIntegrableOfBounded hG hbound profile who t) :=
  fun profile who =>
    M.summable_discounted_monitoredStagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who
      (M.discountedStageIntegrableOfBounded hG hbound profile who)
      (fun t => M.abs_monitoredStagePayoff_le profile t who
        (M.discountedStageIntegrableOfBounded hG hbound profile who t)
        (fun history _ =>
          (hbound who).choose_spec (fun i => profile i t history)))

/-- A bound on stage expectations also bounds the normalized monitored
discounted payoff, independently of the signal support size. -/
theorem abs_discountedPayoffOfBounded_le
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    |M.discountedPayoffOfBounded hdiscount0 hdiscount1
      hG profile who hbound| ≤ bound := by
  let hc : ∀ t, M.MonitoredStageIntegrable profile t who := fun t =>
    M.monitoredStageIntegrable_of_expected_bound profile t who hG hbound
  have hb (t : ℕ) :
      |M.monitoredStagePayoff profile t who (hc t)| ≤ bound :=
    M.abs_monitoredStagePayoff_le profile t who (hc t)
      (fun history _ => hbound (fun i => profile i t history))
  exact M.abs_discountedPayoff_le_of_abs_stagePayoff_bound
    hdiscount0 hdiscount1 profile who hc hb

/-- The supported first-signal continuation payoff has an actual integration
certificate under its signal law. -/
theorem discountedAfterSignal_integrable_of_expected_bound
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    PayoffIntegrable
      (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
      (fun signal => M.discountedPayoffOfBounded
        hdiscount0 hdiscount1 hG (M.afterSignal profile signal) who
        hbound) := by
  apply payoffIntegrable_of_bounded
  intro signal
  exact M.abs_discountedPayoffOfBounded_le hdiscount0 hdiscount1
    hG (M.afterSignal profile signal) who hbound

private theorem tsum_firstSignalContinuationValue
    (M : G.PublicMonitoring) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : M.MonitoredProfile) (who : ι)
    (hstage : ∀ t, M.MonitoredStageIntegrable profile t who)
    (hbound : ∀ n signal, ∀ _hsignal :
      signal ∈ (M.signalLaw
        (fun i => profile i 0 (fun k => k.elim0))).support,
      |M.firstSignalContinuationValue profile n who
        (hstage (n + 1)) signal| ≤ bound) :
    ∃ houter : PayoffIntegrable
        (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
        (fun signal => ∑' n : ℕ,
          discount ^ n * M.firstSignalContinuationValue
            profile n who (hstage (n + 1)) signal),
      (∑' n : ℕ, discount ^ n *
        M.monitoredStagePayoff profile (n + 1) who (hstage (n + 1))) =
        expect (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
          (fun signal => ∑' n : ℕ,
            discount ^ n * M.firstSignalContinuationValue
              profile n who (hstage (n + 1)) signal) houter := by
  let law := M.signalLaw (fun i => profile i 0 (fun k => k.elim0))
  let term : ℕ → M.Signal → ℝ := fun n signal =>
    discount ^ n * M.firstSignalContinuationValue profile n who
      (hstage (n + 1)) signal
  let majorant : ℕ → ℝ := fun n => bound * discount ^ n
  have hmajor : Summable majorant :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  have htermBound : ∀ n, ∀ signal ∈ law.support,
      |term n signal| ≤ majorant n := by
    intro n signal hsignal
    simp only [term, majorant, abs_mul,
      abs_of_nonneg (pow_nonneg hdiscount0 n)]
    calc
      discount ^ n *
          |M.firstSignalContinuationValue profile n who
            (hstage (n + 1)) signal| ≤
          discount ^ n * bound :=
        mul_le_mul_of_nonneg_left
          (hbound n signal hsignal) (pow_nonneg hdiscount0 n)
      _ = bound * discount ^ n := by ring
  let houter := payoffIntegrable_tsum_of_majorant
    law term majorant hmajor htermBound
  refine ⟨houter, ?_⟩
  calc
    (∑' n : ℕ, discount ^ n *
        M.monitoredStagePayoff profile (n + 1) who (hstage (n + 1))) =
        ∑' n : ℕ, expect law (term n)
          (payoffIntegrable_of_bounded_on_support law (term n)
            (htermBound n)) := by
      apply tsum_congr
      intro n
      have htower := M.monitoredStagePayoff_succ_eq_expect_afterSignal
        profile n who (hstage (n + 1))
      have hscale := expect_const_mul
        (μ := law) (c := discount ^ n)
        (M.firstSignalContinuationValue_integrable profile n who
          (hstage (n + 1)))
      calc
        discount ^ n *
            M.monitoredStagePayoff profile (n + 1) who
              (hstage (n + 1)) =
            discount ^ n * expect law
              (M.firstSignalContinuationValue profile n who
                (hstage (n + 1)))
              (M.firstSignalContinuationValue_integrable
                profile n who (hstage (n + 1))) := congrArg _ htower
        _ = expect law (term n)
            (payoffIntegrable_of_bounded_on_support law
              (term n) (htermBound n)) := hscale.symm
    _ = expect law (fun signal => ∑' n, term n signal) houter :=
      expect_tsum_of_majorant law term majorant hmajor htermBound

theorem discountedPayoff_eq_head_add_expected
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        profile who hbound =
      (1 - discount) *
          G.stagePayoff (fun i => profile i 0 (fun k => k.elim0))
            who (hG who (fun i => profile i 0 (fun k => k.elim0))) +
        discount * expect
          (M.signalLaw (fun i => profile i 0 (fun k => k.elim0)))
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal profile signal) who hbound)
          (M.discountedAfterSignal_integrable_of_expected_bound
            hdiscount0 hdiscount1 hG profile who hbound) := by
  let law := M.signalLaw (fun i => profile i 0 (fun k => k.elim0))
  let hstage : ∀ t, M.MonitoredStageIntegrable profile t who :=
    fun t => M.monitoredStageIntegrable_of_expected_bound
      profile t who hG hbound
  have hstageBound (t : ℕ) :
      |M.monitoredStagePayoff profile t who (hstage t)| ≤ bound :=
    M.abs_monitoredStagePayoff_le profile t who (hstage t)
      (fun history _ => hbound (fun i => profile i t history))
  have hsum := M.summable_discounted_monitoredStagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who hstage hstageBound
  let continuation : M.Signal → ℕ → ℝ := fun signal n =>
    M.firstSignalContinuationValue profile n who (hstage (n + 1)) signal
  have hcontinuationBound (n : ℕ) (signal : M.Signal)
      (hsignal : signal ∈ law.support) :
      |continuation signal n| ≤ bound := by
    have hnext := (hstage (n + 1)).afterSignal M profile n who
      signal hsignal
    have hnextBound :
        |M.monitoredStagePayoff (M.afterSignal profile signal)
          n who hnext| ≤ bound :=
      M.abs_monitoredStagePayoff_le
        (M.afterSignal profile signal) n who hnext
        (fun history _ =>
          hbound (fun i => M.afterSignal profile signal i n history))
    have hs : signal ∈
        (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support := by
      simpa only [law] using hsignal
    have hne : (M.signalLaw
        (fun i => profile i 0 (fun k => k.elim0))) signal ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hs
    simpa [continuation, firstSignalContinuationValue,
      extendFromSupport, hne] using hnextBound
  obtain ⟨hseries, hseriesEq⟩ :=
    M.tsum_firstSignalContinuationValue hdiscount0 hdiscount1
      profile who hstage (fun n signal hsignal =>
        hcontinuationBound n signal hsignal)
  have hpoint (signal : M.Signal) (hsignal : signal ∈ law.support) :
      (1 - discount) *
          (∑' n : ℕ, discount ^ n * continuation signal n) =
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
          (M.afterSignal profile signal) who hbound := by
    have hterm (n : ℕ) :
        continuation signal n =
          M.monitoredStagePayoff (M.afterSignal profile signal) n who
            (M.monitoredStageIntegrable_of_expected_bound
              (M.afterSignal profile signal) n who hG hbound) := by
      have hs : signal ∈
          (M.signalLaw (fun i => profile i 0 (fun k => k.elim0))).support := by
        simpa only [law] using hsignal
      have hne : (M.signalLaw
          (fun i => profile i 0 (fun k => k.elim0))) signal ≠ 0 :=
        (PMF.mem_support_iff _ _).mp hs
      simp [continuation, firstSignalContinuationValue,
        extendFromSupport, hne]
    unfold discountedPayoffOfBounded discountedPayoff
      GameTheory.Math.normalizedDiscountedSum
    congr 1
    apply tsum_congr
    intro n
    exact congrArg (fun value : ℝ => discount ^ n * value) (hterm n)
  have hscaled : PayoffIntegrable law
      (fun signal => (1 - discount) *
        ∑' n : ℕ, discount ^ n * continuation signal n) :=
    payoffIntegrable_const_mul hseries
  have hafter := M.discountedAfterSignal_integrable_of_expected_bound
    hdiscount0 hdiscount1 hG profile who hbound
  have hexpect :
      (1 - discount) *
          expect law
            (fun signal => ∑' n : ℕ,
              discount ^ n * continuation signal n) hseries =
        expect law
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal profile signal) who hbound) hafter := by
    calc
      (1 - discount) * expect law
          (fun signal => ∑' n : ℕ,
            discount ^ n * continuation signal n) hseries =
          expect law
            (fun signal => (1 - discount) *
              ∑' n : ℕ, discount ^ n * continuation signal n)
            hscaled := (expect_const_mul hseries).symm
      _ = _ := expect_congr_on_support hpoint hscaled hafter
  have hsplit :
      M.monitoredStagePayoff profile 0 who (hstage 0) +
        ∑' n : ℕ, discount ^ (n + 1) *
          M.monitoredStagePayoff profile (n + 1) who (hstage (n + 1)) =
        ∑' n : ℕ, discount ^ n *
          M.monitoredStagePayoff profile n who (hstage n) := by
    simpa only [Finset.sum_range_one, pow_zero, one_mul] using
      hsum.sum_add_tsum_nat_add 1
  have hhead :
      M.monitoredStagePayoff profile 0 who (hstage 0) =
        G.stagePayoff (fun i => profile i 0 (fun k => k.elim0))
          who (hG who (fun i => profile i 0 (fun k => k.elim0))) := by
    exact M.monitoredStagePayoff_zero profile who (hstage 0)
  unfold discountedPayoffOfBounded discountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  calc
    (1 - discount) *
        (∑' n : ℕ, discount ^ n *
          M.monitoredStagePayoff profile n who (hstage n)) =
        (1 - discount) *
          (M.monitoredStagePayoff profile 0 who (hstage 0) +
            ∑' n : ℕ, discount ^ (n + 1) *
              M.monitoredStagePayoff profile (n + 1) who
                (hstage (n + 1))) := by rw [hsplit]
    _ = (1 - discount) *
          M.monitoredStagePayoff profile 0 who (hstage 0) +
        discount * ((1 - discount) *
          ∑' n : ℕ, discount ^ n *
            M.monitoredStagePayoff profile (n + 1) who
              (hstage (n + 1))) := by
      rw [show (∑' n : ℕ, discount ^ (n + 1) *
          M.monitoredStagePayoff profile (n + 1) who
            (hstage (n + 1))) =
          discount * ∑' n : ℕ, discount ^ n *
            M.monitoredStagePayoff profile (n + 1) who
              (hstage (n + 1)) by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring]
      ring
    _ = (1 - discount) *
          G.stagePayoff (fun i => profile i 0 (fun k => k.elim0))
            who (hG who (fun i => profile i 0 (fun k => k.elim0))) +
        discount * expect law
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal profile signal) who hbound) hafter := by
      rw [hhead, hseriesEq, hexpect]
    _ = _ := rfl

/-- The bounded continuation specialization supplies the actual stage and
series certificates to the canonical continuation payoff. -/
abbrev discountedContinuationPayoffOfBounded
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) {t : ℕ}
    (history : M.SignalHistory t) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) : ℝ :=
  M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
    (M.after profile history) who hbound

theorem discountedContinuationPayoff_eq_head_add_expected
    (M : G.PublicMonitoring) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (profile : M.MonitoredProfile) {t : ℕ}
    (history : M.SignalHistory t) (who : ι)
    {bound : ℝ} (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who (hG who stage)| ≤ bound) :
    M.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
        hG profile history who hbound =
      (1 - discount) *
        G.stagePayoff
          (fun i => M.after profile history i 0 (fun k => k.elim0))
          who (hG who
            (fun i => M.after profile history i 0 (fun k => k.elim0))) +
        discount * expect
          (M.signalLaw
            (fun i => M.after profile history i 0 (fun k => k.elim0)))
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal (M.after profile history) signal) who hbound)
          (M.discountedAfterSignal_integrable_of_expected_bound
            hdiscount0 hdiscount1 hG
            (M.after profile history) who hbound) :=
  M.discountedPayoff_eq_head_add_expected hdiscount0 hdiscount1
    hG (M.after profile history) who hbound

@[simp]
theorem discountedPayoff_stationaryMonitoredProfile (M : G.PublicMonitoring)
    {discount : ℝ} (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (who : ι)
    (hfixed : UtilityIntegrable G.utility who (G.form.play profile))
    (hstage : ∀ t,
      M.MonitoredStageIntegrable (M.stationaryMonitoredProfile profile) t who)
    (hsum : Summable fun t : ℕ => discount ^ t *
      M.monitoredStagePayoff (M.stationaryMonitoredProfile profile)
        t who (hstage t)) :
    M.discountedPayoff discount (M.stationaryMonitoredProfile profile)
      who hstage hsum = G.stagePayoff profile who hfixed := by
  have hne : 1 - discount ≠ 0 := by linarith
  simp [discountedPayoff, GameTheory.Math.normalizedDiscountedSum,
    M.monitoredStagePayoff_stationaryMonitoredProfile
      profile _ who (hstage _) hfixed,
    tsum_mul_right, tsum_geometric_of_lt_one hdiscount0 hdiscount1, hne]

section GuardedEquilibria

variable (M : G.PublicMonitoring) (discount : ℝ)
  (hstage : ∀ profile : M.MonitoredProfile, ∀ who t,
    M.MonitoredStageIntegrable profile t who)
  (hsum : ∀ profile : M.MonitoredProfile, ∀ who,
    Summable fun t : ℕ => discount ^ t *
      M.monitoredStagePayoff profile t who (hstage profile who t))

/-- Exact discounted Nash equilibrium in public strategies. -/
def IsDiscountedPublicNash [DecidableEq ι]
    (profile : M.MonitoredProfile) : Prop :=
  IsNash M.monitoredForm
    (euPreference (M.discountedUtility discount hstage hsum)) profile

/-- Discounted public Nash equilibrium allowing an additive payoff loss. This
is the canonical approximate-Nash predicate on the monitored strategic form. -/
def IsεDiscountedPublicNash [DecidableEq ι]
    (ε : ℝ) (profile : M.MonitoredProfile) : Prop :=
  IsεNash M.monitoredForm
    (M.discountedUtility discount hstage hsum) ε profile

theorem isDiscountedPublicNash_iff [DecidableEq ι]
    (profile : M.MonitoredProfile) :
    M.IsDiscountedPublicNash discount hstage hsum profile ↔
      ∀ who deviation,
        M.discountedPayoff discount
          (Profile.update (sig := M.monitoredSignature) profile who deviation)
          who (hstage _ who) (hsum _ who) ≤
        M.discountedPayoff discount profile who
          (hstage profile who) (hsum profile who) := by
  rw [IsDiscountedPublicNash, isNash_iff]
  constructor
  · intro h who deviation
    simpa [monitoredForm, expectedUtility, expect_pure,
      discountedUtility] using (h who deviation).2.2
  · intro h who deviation
    refine ⟨payoffIntegrable_pure _ _, payoffIntegrable_pure _ _, ?_⟩
    simpa [monitoredForm, expectedUtility, expect_pure,
      discountedUtility] using h who deviation

theorem isεDiscountedPublicNash_iff [DecidableEq ι]
    (ε : ℝ) (profile : M.MonitoredProfile) :
    M.IsεDiscountedPublicNash discount hstage hsum ε profile ↔
      ∀ who deviation,
        M.discountedPayoff discount
          (Profile.update (sig := M.monitoredSignature) profile who deviation)
          who (hstage _ who) (hsum _ who) ≤
        M.discountedPayoff discount profile who
          (hstage profile who) (hsum profile who) + ε := by
  rw [IsεDiscountedPublicNash, isεNash_iff]
  constructor
  · intro h who deviation
    simpa [monitoredForm, expectedUtility, expect_pure,
      discountedUtility] using (h who deviation).2.2
  · intro h who deviation
    refine ⟨payoffIntegrable_pure _ _, payoffIntegrable_pure _ _, ?_⟩
    simpa [monitoredForm, expectedUtility, expect_pure,
      discountedUtility] using h who deviation

/-- Exact public Nash implies approximate public Nash for every nonnegative
error allowance. -/
theorem IsDiscountedPublicNash.isεDiscountedPublicNash
    [DecidableEq ι] {ε : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsDiscountedPublicNash discount hstage hsum profile)
    (hε : 0 ≤ ε) :
    M.IsεDiscountedPublicNash discount hstage hsum ε profile :=
  IsεNash.of_isNash M.monitoredForm
    (M.discountedUtility discount hstage hsum) h hε

/-- Zero approximation error recovers exact discounted public Nash. -/
theorem isDiscountedPublicNash_iff_isεDiscountedPublicNash_zero
    [DecidableEq ι] (profile : M.MonitoredProfile) :
    M.IsDiscountedPublicNash discount hstage hsum profile ↔
      M.IsεDiscountedPublicNash discount hstage hsum 0 profile :=
  isNash_iff_isεNash_zero M.monitoredForm
    (M.discountedUtility discount hstage hsum)

/-- A perfect public equilibrium is discounted Nash after every finite public
signal history, including histories assigned zero probability on path.  The
deviations remain within public strategies over `M.SignalHistory`. -/
def IsPerfectPublicEquilibrium [DecidableEq ι]
    (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t),
    M.IsDiscountedPublicNash discount hstage hsum (M.after profile history)

/-- Approximate perfect public equilibrium with the same additive tolerance
after every finite public signal history. -/
def IsεPerfectPublicEquilibrium [DecidableEq ι]
    (ε : ℝ) (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t),
    M.IsεDiscountedPublicNash discount hstage hsum ε (M.after profile history)

/-- Exact perfect public equilibrium implies its approximate form for every
nonnegative error allowance. -/
theorem IsPerfectPublicEquilibrium.isεPerfectPublicEquilibrium
    [DecidableEq ι] {ε : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount hstage hsum profile)
    (hε : 0 ≤ ε) :
    M.IsεPerfectPublicEquilibrium discount hstage hsum ε profile :=
  fun t history =>
    IsDiscountedPublicNash.isεDiscountedPublicNash
      M discount hstage hsum (h t history) hε

/-- Approximate perfect public equilibrium is preserved by continuation after
one public signal. -/
theorem IsεPerfectPublicEquilibrium.afterSignal
    [DecidableEq ι] {ε : ℝ} {profile : M.MonitoredProfile}
    (h : M.IsεPerfectPublicEquilibrium discount hstage hsum ε profile)
    (signal : M.Signal) :
    M.IsεPerfectPublicEquilibrium discount hstage hsum ε
      (M.afterSignal profile signal) := by
  intro t history
  rw [M.after_afterSignal]
  exact h (t + 1) (Fin.cons signal history)

/-- No public deviation that changes only the current stage action improves
the deviator's normalized discounted payoff. -/
def HasNoProfitableOneShotDeviation [DecidableEq ι]
    (profile : M.MonitoredProfile) : Prop :=
  ∀ who action,
    M.discountedUtility discount hstage hsum
      (Profile.update (sig := M.monitoredSignature) profile who
        (M.oneShotDeviation profile who action)) who ≤
    M.discountedUtility discount hstage hsum profile who

/-- The one-shot condition holds after every finite public signal history. -/
def HasNoProfitableOneShotDeviationAfterEveryHistory
    [DecidableEq ι] (profile : M.MonitoredProfile) : Prop :=
  ∀ t (history : M.SignalHistory t),
    M.HasNoProfitableOneShotDeviation discount hstage hsum
      (M.after profile history)

theorem IsDiscountedPublicNash.hasNoProfitableOneShotDeviation
    [DecidableEq ι] {profile : M.MonitoredProfile}
    (h : M.IsDiscountedPublicNash discount hstage hsum profile) :
    M.HasNoProfitableOneShotDeviation discount hstage hsum profile := by
  rw [M.isDiscountedPublicNash_iff discount hstage hsum] at h
  intro who action
  exact h who (M.oneShotDeviation profile who action)

theorem IsPerfectPublicEquilibrium.hasNoProfitableOneShotDeviationAfterEveryHistory
    [DecidableEq ι] {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount hstage hsum profile) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount hstage hsum profile := by
  intro t history
  exact (h t history).hasNoProfitableOneShotDeviation

/-- Perfect public equilibrium includes discounted public Nash at the empty
history. -/
theorem IsPerfectPublicEquilibrium.isDiscountedPublicNash
    [DecidableEq ι] {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount hstage hsum profile) :
    M.IsDiscountedPublicNash discount hstage hsum profile := by
  simpa [after] using h 0 (fun index => index.elim0)

theorem IsPerfectPublicEquilibrium.afterSignal [DecidableEq ι]
    {profile : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium discount hstage hsum profile)
    (signal : M.Signal) :
    M.IsPerfectPublicEquilibrium discount hstage hsum
      (M.afterSignal profile signal) := by
  intro t history
  rw [M.after_afterSignal]
  exact h (t + 1) (Fin.cons signal history)

theorem HasNoProfitableOneShotDeviationAfterEveryHistory.afterSignal
    [DecidableEq ι] {profile : M.MonitoredProfile}
    (h : M.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount hstage hsum profile)
    (signal : M.Signal) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory
      discount hstage hsum (M.afterSignal profile signal) := by
  intro t history
  rw [M.after_afterSignal]
  exact h (t + 1) (Fin.cons signal history)

end GuardedEquilibria

end UtilityGame.PublicMonitoring

end GameTheory
